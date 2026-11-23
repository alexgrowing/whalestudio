import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
