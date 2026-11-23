import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces

open GroundTheory.LocalField
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open Classical in

def intInd (x : F) : ℂ := if x ∈ 𝒪[F] then 1 else 0

def phiS (p : F × F) : ℂ := intInd p.1 * intInd p.2

open Classical in

def mRow (g : GL (Fin 2) F) : F :=
  if modulus (g.val 1 0) < modulus (g.val 1 1) then g.val 1 1 else g.val 1 0

open Classical in

def xRow (g : GL (Fin 2) F) : F :=
  if modulus (g.val 1 0) < modulus (g.val 1 1) then g.val 0 1 / g.val 1 1 else g.val 0 0 / g.val 1 0

end

end GlobalTheory.CompanionTheory.SphTheta
