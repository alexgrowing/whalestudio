import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

def LemmaAOf : Prop := OrbitSubSum → RestrictRoots → LemmaA

def IrredOf : Prop := LemmaA → Irred

def ShareNOf : Prop := ShareBound → ShareN

def NoSolvableOf : Prop :=
  PowerPCycle → PrimitiveOfPCycle → JordanPrime → AltNotSolvable → NoSolvableTransitive

def BBOf : Prop := FewLargeParts → BBAtMostThree

end Formalism.GaloisIrreducibility
