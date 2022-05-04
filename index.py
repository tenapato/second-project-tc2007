'''
Created May 2, 2022

@Authors:
- Emilio Popovits Blake (A01027265)
- Patricio Tena (A01027293)
- Maximiliano Sapién Fernández (A01027541)
- Rodrigo Benavente (A01026973)
- Karen Isabel Morgado Castillo (A01027446)
'''

from os import listdir, path
import matplotlib.pyplot as plt
import numpy as np

graphUnsatisfactory = []

def selectProblem():
    """
    Finds all 3SAT problems found in the ./problems/ directory and 
    prompts user to select a problem to solve.

    :returns: The selected file name of the 3SAT problem.
    :rtype: String
    """

    print('Files in ./problems/ directory:')
    fileArray = []
    count = 1
    for file in listdir('./problems'):
        if file.endswith('.txt'):
            print(path.join(str(count) + '. ', file))
            fileArray.append(file)
            count += 1

    prompt = input('\nWhich file number contains the 3SAT problem that you want to solve?')
    selectedFile = fileArray[int(prompt) - 1]
    
    return selectedFile


def loadProblem(file):
    """
    Loads 3SAT problem from selected file, and parses its clauses into a 
    list of lists.

    :returns: A tuple with the parsed 3SAT clauses in a list of lists, 
        the number of variables in the 3SAT problem, and the number of 
        clauses in the 3SAT problem.
    """
    file = open('./problems/' + file, 'r')

    fileLines = []
    for line in file:
        fileLines.append(line)
    file.close()

    clauses = []
    for index, line in enumerate(fileLines):
        if index > 1:
            currentLine = fileLines[index]
            currentLine = ''.join(line.split('\n'))
            currentLine = currentLine.replace('  ', ' ').split(' ')
            
            if len(currentLine) == 1 and currentLine[0] == '%':
                break

            if len(currentLine) > 4:
                currentLine.pop(0)
            
            currentLine.remove('0')
            clauses.append([int(i) - 1 if int(i) > 0 else int(i) + 1 for i in currentLine])

    variables, num_clauses = (int(fileLines[1].split(' ')[2]), int(fileLines[1].split(' ')[4]))
    return (clauses, variables, num_clauses)

def checkSatisfied(bitstring, clauses):
    """
    Recevies the 3SAT problem's clauses and evalutes them with a bitstring.

    :param bitstring: The bitstring to test against the 3SAT clauses
    :param claues: A list of lists containing the clauses of the 3SAT problem
    :returns: A tupple with a boolean specifying if the 3SAT problem was satisfied with the 
        bitstring, the number of satisfied claues, and the number of unsatisfied 
        clauses
    :rtype: bool, int, int
    """
    # Convert bitstring into booleans
    bool_bitstring = [True if i == 1 else False for i in bitstring]

    satisfactory_clauses = 0
    unsatisfactory_clauses = 0

    result = None
    for clause in clauses:
        result_clause = None
        for var in clause:
            current_var = bool_bitstring[var if var > 0 else var * -1]
            result_clause = current_var if result_clause == None else result_clause or current_var 

        if result_clause == True:
            satisfactory_clauses += 1
        else:
            unsatisfactory_clauses += 1

        result = result_clause if result == None else result and result_clause
    #pushback a los unsatisfactory_clauses
    graphUnsatisfactory.append(unsatisfactory_clauses)
    return (result, satisfactory_clauses, unsatisfactory_clauses)

def updateSolution(file_path, iteration, satisfactory_clauses, unsatisfactory_clauses, variable_to_change, new_assignment, found=False):
    """
    Recevies each step of the algorithm and saves it to a file in the ./solutions/ 
    directory.

    :param file_path: The path to the file
    :param iteration: A number refering to the step of the iteration
    :param satisfactory_clauses: Number of staisfactory clauses found in the evaluation
    :param unsatisfactory_clauses: The number of unsatisfactory clauses found in the evaluation
    :param variable_to_change: The number of the variable to change in the bitstring
    :param new_assignment: A bitstring containing the new bitstring assignment after variable change
    :param found: (Default = False) A boolean specifying if the solution was found
    :returns: Void
    """
    file = open(file_path, 'a')

    file.write('\n*********************************************** iteration no.' + str(iteration))
    if found == False:
        file.write('\nSatisfactory Clauses: ' + str(satisfactory_clauses))
        file.write('\nUnsatisfactory Clauses: ' + str(unsatisfactory_clauses))
        file.write('\n - Variable to Change: ' + str(variable_to_change))
        file.write('\nNew assignment: ' + str(new_assignment))
        file.write('\n')
    else:
        file.write('\nSolution Found: ' + str(new_assignment))

    file.close()

def shoningAlgorithm(clauses, variables, num_clauses, file):
    """
    Performs Shoning's algorithm to solve the provided 3SAT problem.

    :param clauses: A list of lists containing the clauses for the 3SAT problem to solve
    :param variables: The number of variables the 3SAT problem uses
    :param num_clauses: The number of clauses in the 3SAT problem
    :param file: The file name of the selected 3SAT problem under the ./problems/ directory
    :returns: 0 If a solution to the 3SAT problem was not found, and a list containing the bitstring
        of the solution if it was found.
    :rtype: int, list
    """
    
    '''
        Sample Output
        For each iteration:
            - The binary string that was tested in the corresponding instance as well as the numbers of the satisfied
            and unsatisfied clauses. 
            - The clause and the variable that will be modified. 
            - The new string to test in the next iteration. 
    '''
    '''
        Algorithm:
        [x] input: a formula in  -CNF with variables
        [x] Guess an initial assignment , uniformly at random
        Repeat 3n times:
            [x] If the formula is satisfied by the actual assignment: stop and accept
            [x1] Let be some clause not being satisfied by the actual assignment,
            pick one of the literals in the clause at random and flip its value in the current assignment
    '''
    
    # Generate a bitstring pulling the integers from a discrete uniform distribution
    initial_assignment = np.random.randint(2, size=variables)

    # Initialize the solution file
    solution_file_path = './solutions/solution_' + file
    solution_file = open(solution_file_path, 'w')
    solution_file.write('Initial assignment: ' + str(initial_assignment))
    solution_file.write('\nNumber of variables: ' + str(variables))
    solution_file.write('\nNumber of clauses: ' + str(num_clauses))
    solution_file.write('\n')
    solution_file.close()

    # Begin algorithm
    current_assignment = initial_assignment
    for i in range(3 * variables):
        # Check if the current assignment satisfies the 3SAT problem
        satisfied, satisfactory_clauses, unsatisfactory_clauses = checkSatisfied(current_assignment, clauses)
        # (Guard clause) If the current assignment satisfies the 3SAT problem, update the solution file and return the current assignment
        if satisfied == True:
            updateSolution(solution_file_path, i, satisfactory_clauses, unsatisfactory_clauses, 'N/A', current_assignment, found=True)
            #graph the Unsat
            graph(graphUnsatisfactory,i)
            return current_assignment

        # Randomly select a bit to update in the bitstring from a discrete random distribution
        random_selection = np.random.randint(variables)
        # Flip the randomly selected bit in the bitstring
        current_assignment[random_selection] = 1 if current_assignment[random_selection] == 0 else 0

        # Print iteration to the solution file
        updateSolution(solution_file_path, i, satisfactory_clauses, unsatisfactory_clauses, random_selection + 1, current_assignment)
    #graph the Unsat
    graph(graphUnsatisfactory,(3 * variables-1))
    # If no solution was found, report it in the solution file and return 0
    solution_file = open(solution_file_path, 'a')
    solution_file.write('\n***********************************************')
    solution_file.write('\nNo solution found in ' + str(3 * variables) + ' iterations')
    solution_file.close()
    return 0
  
def graph(unsatisfactoryC,iterations):
  x = []
  iterations += 1
  
  for z in range(0, iterations):
    x.append(z)
  
  #area = 150 
  fig, ax = plt.subplots()  
  #grahp = plt.scatter(x, unsatisfactoryC, s=area, c=unsatisfactoryC, cmap='cool', alpha=1)
  plt.plot(x, unsatisfactoryC)
  
  for i, txt in enumerate(x):
      ax.annotate(txt + 1, (x[i], unsatisfactoryC[i]))
  
  # nombre del txt file seleccionado
  plt.title('graph_solution_' + file)
  plt.savefig('./graphs/graph_solution_' + file + '.png')
  
if __name__ == '__main__':
    file = selectProblem()
    clauses, variables, num_clauses = loadProblem(file)
    
    solution = shoningAlgorithm(clauses, variables, num_clauses, file)
  
    if isinstance (solution,int):
        print('No solution found: 0')
        print('Steps were saved in ./solutions/solution_' + file)
    else:
        print('Solution found: ' + str(solution))
        print('Solution steps were saved in ./solutions/solution_' + file)