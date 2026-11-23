import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DiagAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

set_option autoImplicit false

noncomputable section

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

def invPol {F : Type} [Field F] (P : F[X]) : F[X] := C (P.coeff 0)⁻¹ * P.reverse

def IsHExp {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ)
    (h : Fin n → ℕ) : Prop :=
  (∃ m, (∀ i, lam (ComplexEmbedding.conjugate t₀) i = m) ∧ ∀ i, h i = ((n - 1) * m +
      ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ j, lam τ j) +
        (lam t₀ i + (n - 1 - (i : ℕ)))) ∨
  (∃ m, (∀ i, lam t₀ i = m) ∧ ∀ i, h i = (m +
      ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ j, lam τ j) +
        (∑ j ∈ Finset.univ.erase i, lam (ComplexEmbedding.conjugate t₀) j + (i : ℕ)))

def Lists {F : Type} [Field F] [NumberField F] {n : ℕ} (χ : F[X]) (g : (F →+* ℂ) → Fin n → ℂ) : Prop :=
  ∀ τ, UpperTheory.Gal.W2.rts χ τ = Finset.univ.val.map (g τ)

def schW {F : Type} [Field F] [NumberField F] {n : ℕ} (lam : (F →+* ℂ) → Fin n → ℕ) (χ : F[X]) : ℂ :=
  if h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g then ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (h.choose τ) else 0

def conjWt {F : Type} [Field F] {n : ℕ} (σ : ℂ ≃+* ℂ) (lam : (F →+* ℂ) → Fin n → ℕ) : (F →+* ℂ) → Fin n → ℕ :=
  fun τ => lam ((σ.symm : ℂ →+* ℂ).comp τ)

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def epsOf (D : Datum p) (τ : D.F →+* ℂ) : ℕ := if τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc then 1 else 0

def endPol (L : GlobalTheory.LKGeo.Link D G) (P : G.F[X]) : D.F[X] := invPol (P.map (L.e.symm : G.F →+* D.F))

def markOf (L : GlobalTheory.LKGeo.Link D G) (v : InfinitePlace G.F) (μ : ℂ) : ℂ :=
  if v.embedding (L.e (D.ω : D.F)) = D.ρc then μ⁻¹ else ((starRingEnd ℂ) μ)⁻¹

def cW (L : GlobalTheory.LKGeo.Link D G) (i₀ : Fin D.a) (v : InfinitePlace G.F) {k : ℕ} (α : Fin k → 𝓞 D.F) (y : ℂ) (P : G.F[X])
    (μ : ℂ) : ℂ :=
  UpperTheory.Gal.W2.locW (D.tau i₀) (epsOf D) α y (endPol L P) (markOf L v μ)

abbrev Kp (G : HTGroup p) : Subgroup (Gr G 1) := KHT p G.m G.n 1 G.Fw

def oneP (G : HTGroup p) : Gr G 1 → ℂ := Set.indicator (Kp G : Set (Gr G 1)) 1

def IsWt (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) : Prop :=
  ∀ (B : DForm G) (y : grp G B.β), (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable →
    LinearMap.trace ℂ V (ξ y.1) = schW lam (endPol L (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)))

structure Good (G : HTGroup p) (K : Subgroup G.GAf) (f : G.GAf → ℂ) : Prop where
  reg : ∀ g, f g ≠ 0 → RegAf G g
  pairs : ∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → P.term K f 1 (Kp G) (oneP G) = 0
  forms : ∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) (y : grp G B.β),
    ¬ RegIrr G ((y.1.1 : G.Cˣ) : G.C) →
    GlobalTheory.LKCount.orbK (MonoidHom.id _) (K.prod (Kp G)) (B.embAt x t hx y) (fun h => f h.1 * oneP G h.2) = 0

structure Scope (D : Datum p) (G : HTGroup p) (gb : GBase D.toG ℂ) (N : ℕ) : Prop where
  a1 : D.a = 1
  m1 : D.m = 1
  ga : G.a = 1
  odd : Odd G.n
  cpt : D.CompactB
  three : 3 ≤ N
  cop : N.Coprime p
  rho : gb.ρ = D.ρc
  tau : ∀ (i : Fin D.a) (c : 𝓞 D.F), gb.t i c = D.tau i (c : D.F)

abbrev PtsOf (G : HTGroup p) (v : InfinitePlace G.F) (K : Subgroup G.GAf) (q : FCls G) : Type :=
  Pts G v (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
    (Quot.out q).trivAf.choose_spec.choose_spec K (Kp G)

def Seen (G : HTGroup p) (v : InfinitePlace G.F) (K : Subgroup G.GAf) (f : G.GAf → ℂ) (q : FCls G) (a : PtsOf G v K q)
    (y : grp G (Quot.out q).β) : Prop :=
  FixL G v (Quot.out q).β y (Quot.out a).2.1 ∧
    f ((Quot.out a).1.1⁻¹ * toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
      (Quot.out q).trivAf.choose_spec.choose_spec y * (Quot.out a).1.1) ≠ 0 ∧
    oneP G ((Quot.out a).1.2⁻¹ * toP1 G (Quot.out q).β y * (Quot.out a).1.2) ≠ 0

def CxFin (G : HTGroup p) (v : InfinitePlace G.F) (K : Subgroup G.GAf) (f : G.GAf → ℂ) : Prop :=
  {z : Σ q : FCls G, PtsOf G v K q × grp G (Quot.out q).β | Seen G v K f z.1 z.2.1 z.2.2}.Finite

example (K : Subgroup G.GAf) (v : InfinitePlace G.F) : CxFin G v K 0 :=
  Set.finite_empty.subset fun _ hz => (hz.2.1 rfl).elim

end UpperTheory.Gal.LocalSmoothExtension
