import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

theorem alg_eq {R F : Type} [CommRing R] [IsDomain R] [Field F] (i₁ i₂ : Algebra (FractionRing R) F)
    (h : ∀ r, @algebraMap _ _ _ _ i₁ (algebraMap R (FractionRing R) r) =
      @algebraMap _ _ _ _ i₂ (algebraMap R (FractionRing R) r)) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro x
  have e := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := FractionRing R)
    (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext h)
  exact RingHom.congr_fun e x

theorem qk_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {q q' : QkPt D F k} (hy : q.y = q'.y) (hg : q.g = q'.g) : q = q' := by
  cases q; cases q'; cases hy; cases hg; rfl

theorem tor_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {τ : Multiplicative D.X →* Fˣ} {g : GtPtF D F} (h : GlobalTheory.UT.IsTor τ g) :
    g = GlobalTheory.TorusExt.torusPt D F (Additive.ofMul τ) :=
  (GlobalTheory.TorusExt.isTorusPtF_iff_eq g τ).1 ((GlobalTheory.UT.isTor_iff τ g).1 h)

theorem one_le_of_isUnit {R : Type} [CommRing R] [IsDomain R] {k : ℕ} (hk : IsUnit (k : R)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hk
  · exact h

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem tors_fun (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {k : ℕ} (hk : IsUnit (k : R)) :
    ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧
      (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') := by
  haveI := hR.2
  obtain ⟨f, ⟨h1, -, h3, h4, -⟩, -⟩ :=
    GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR.1 D A G hG U F k (one_le_of_isUnit hk)
  exact ⟨f, h1, h3, h4⟩

theorem push {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    (U : Unif (maximalIdeal R) D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ e : (TFK (R := R) F ⟶ A.A) ≃* (Over.mk (jFK (R := R) F ≫ jK R) ⟶ G), ∀ x, (e x).left = x.left ≫ genMap U :=
  GlobalTheory.LiePull.exists_pushEquiv (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre) (TFK (R := R) F) _ rfl

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem torMatch_id (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) :
    TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, -, -⟩ := tors_fun hR hG U F hk
  have e : τ = τ' := MonoidHom.ext fun x => hρ (Multiplicative.toAdd x)
  subst e
  have hqq : q = q' := qk_eq (hy.trans hy'.symm) ((tor_eq hτ).trans (tor_eq hτ').symm)
  subst hqq
  rw [(h1 q a).1 hq, (h1 q a').1 hq', Category.comp_id]

theorem torMatch_one (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') :
    TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ _ _ hq _
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  have e : τ = 1 := MonoidHom.ext fun x => by
    rw [MonoidHom.one_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.zero_apply, ofAdd_zero, map_one]
  subst e
  have hg : q.g = 0 := by rw [tor_eq hτ, ofMul_one, map_zero]
  have hadd : QkAdd q q q := ⟨q, by rw [hy, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (by rw [hg, add_zero]),
    (h3 q q).1 rfl⟩
  have ha : a = 1 := by
    rw [(h1 q a).1 hq]
    exact mul_eq_left.1 (h4 q q q hadd).symm
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have key : eU a = eU' a' ≫ (1 : G' ⟶ G) := by rw [comp_one, ha, map_one]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

theorem torMatch_mul (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') (p p' : G' ⟶ G) (ρ ρ' : D.toPre.X →+ D'.toPre.X)
    (hp : TorMatch U U' (RingHom.id R) p.left ρ) (hp' : TorMatch U U' (RingHom.id R) p'.left ρ') :
    TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' hτk hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
  let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
  have pw : ∀ σ : D.toPre.X →+ D'.toPre.X, (τ'.comp (AddMonoidHom.toMultiplicative σ)) ^ k = 1 := fun σ =>
    MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hτk, MonoidHom.one_apply,
        MonoidHom.one_apply]
  obtain ⟨q₁, hy₁, hτ₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₁ (pw ρ)
  obtain ⟨q₂, hy₂, hτ₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₂ (pw ρ')
  have e₁ := hp F hF k hk τ₁ τ' q₁ q' (f q₁) a' hτk (fun _ => rfl) hy₁ hτ₁ hy' hτ' ((h1 q₁ _).2 rfl) hq'
  have e₂ := hp' F hF k hk τ₂ τ' q₂ q' (f q₂) a' hτk (fun _ => rfl) hy₂ hτ₂ hy' hτ' ((h1 q₂ _).2 rfl) hq'
  have hτe : τ = τ₁ * τ₂ := MonoidHom.ext fun x => by
    rw [MonoidHom.mul_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    rfl
  have hg : q.g = q₁.g + q₂.g := by
    rw [tor_eq hτ, tor_eq hτ₁, tor_eq hτ₂, hτe, ofMul_mul, map_add]
  have hadd : QkAdd q₁ q₂ q := ⟨q, by rw [hy, hy₁, hy₂, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 hg,
    (h3 q q).1 rfl⟩
  have ha : a = f q₁ * f q₂ := by rw [(h1 q a).1 hq]; exact h4 q₁ q₂ q hadd
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have k₁ : eU (f q₁) = eU' a' ≫ p := Over.OverMorphism.ext (by rw [heU, e₁, Over.comp_left, heU', Category.assoc])
  have k₂ : eU (f q₂) = eU' a' ≫ p' := Over.OverMorphism.ext (by rw [heU, e₂, Over.comp_left, heU', Category.assoc])
  have key : eU a = eU' a' ≫ (p * p') := by rw [comp_mul, ha, map_mul, k₁, k₂]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8

open TorMatchLaws in

theorem torMatch_id_one_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G'), TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) ∧ TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 ∧ ∀ (p p' : G' ⟶ G) ρ ρ', TorMatch U U' (RingHom.id R) p.left ρ → TorMatch U U' (RingHom.id R) p'.left ρ' → TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ _ D' A' U'
  exact ⟨torMatch_id hR hG U, torMatch_one hR hG U U', fun p p' ρ ρ' hp hp' => torMatch_mul hR hG U U' p p' ρ ρ' hp hp'⟩

end GlobalTheory.Poinc.Eq8
