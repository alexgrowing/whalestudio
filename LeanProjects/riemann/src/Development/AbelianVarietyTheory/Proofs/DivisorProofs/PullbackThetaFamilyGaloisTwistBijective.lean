import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj.FamBij

open GlobalTheory.FieldBaseChange

variable {R : Type} [CommRing R] [IsDomain R]

def famMapTw (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) : DegPre.BF D (Kb R) ⟶ DegPre.BF D (Kb R) :=
  (famMap D (Kb R) (TwF σ) : DegPre.BF D (TwF σ) ⟶ DegPre.BF D (Kb R))

theorem famMapTw_eq (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    famMapTw D σ = lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) := rfl

theorem twF_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    twF τ ≫ twF σ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap τ.toRingHom ≫ spMap σ.toRingHom = 𝟙 _
  have e : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext h
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]

theorem famMapTw_comp_eq_id (D : DegPre R) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    famMapTw D τ ≫ famMapTw D σ = 𝟙 _ := by
  have : lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF τ) (snd (TF (R := R) (Kb R)) D.P.A) ≫
      lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst_assoc, Category.assoc, twF_comp_eq_id h, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  exact this

theorem sval_famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) (α : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D (Kb R)).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    sval ((famTw D N σ s).s α) r z J = sval (s.s α) (r ≫ (famMapTw D σ).left) z J :=
  sval_pullOver (isPullback_famMap D (Kb R) (TwF σ)).w (famφ_famMap D (Kb R) (TwF σ) α) (s.s α) r hJ

theorem famTw_famTw_eq (D : DegPre R) (N : ℕ) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x)
    (s : Fam D (Kb R) N) : famTw D N τ (famTw D N σ s) = s := by
  refine ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) ?_
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  rw [sval_famTw D N τ _ α _ hJ, sval_famTw D N σ _ α _ hJ, Category.assoc, ← Over.comp_left,
    famMapTw_comp_eq_id D h, Over.id_left, Category.comp_id]

theorem famTw_bijective (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (famTw D N σ) := by
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  refine Function.bijective_iff_has_inverse.2 ⟨famTw D N (e.symm : Kb R →ₐ[FractionRing R] Kb R), ?_, ?_⟩
  · exact famTw_famTw_eq D N fun x => e.symm_apply_apply x
  · exact famTw_famTw_eq D N fun x => e.apply_symm_apply x

end GlobalTheory.Mum.Conj.FamBij
