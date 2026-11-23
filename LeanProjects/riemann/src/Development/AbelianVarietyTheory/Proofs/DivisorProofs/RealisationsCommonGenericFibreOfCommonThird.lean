import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.SameComb

theorem sp_endo_eq_id {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp K ⟶ Sp K)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  rw [← Spec.map_preimage g] at h ⊢
  set ψ := Spec.preimage g
  have h' : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]; exact h
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    have ea := congrArg (fun f => f.hom ⟨a, ha⟩) h'
    have eb := congrArg (fun f => f.hom ⟨b, hb⟩) h'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at ea eb
    change ψ.hom (a / b) = a / b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ea eb
  rw [hψ, Spec.map_id]

theorem lbIso_pull_along {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso M (L.pull φ)) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso (M.pull r) (L.pull ψ) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M r r rfl) (chartPullSame L (fun _ => ψ) (fun _ => φ) _ r fun _ => e)

theorem sec_of_pt {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) {Q : PolAV (Sp K)} {P : PolAV (Sp R)} {a : Q.A.left ⟶ P.A.left}
    (ha : IsGrpPullback Q.A P.A (spMap R.val.toRingHom) a) (t : baseOver (Sp R) ⟶ P.A) (w : Sp K ⟶ Q.A.left)
    (hw : w ≫ a = spMap R.val.toRingHom ≫ t.left) : w ≫ Q.A.hom = 𝟙 _ := by
  apply sp_endo_eq_id R frac
  have e := congrArg (· ≫ P.A.hom) hw
  simp only [Category.assoc, ha.1.w, Over.w t] at e
  simpa using e

theorem combine : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  intro o Ω o₁ o₂ Ω' _ _ _ _ _ _ _ _ S S₁ S₂ ρ ρ₁ ρ₂ ε ε₁ ε₂ lab₁ lab₂ φ h₁ h₂
  obtain ⟨P₀, a, a₁, ε₀, ha, ha₁, hLa, hLa₁, hε, hw⟩ := h₁
  obtain ⟨P₀', b, b₂, ε₀', hb, hb₂, hLb, hLb₂, hε', hw'⟩ := h₂
  obtain ⟨θ, hθm, hθ⟩ := grpPullback_iso ha hb
  haveI := hθm

  have ext : ∀ {T : Scheme.{0}} (u v : T ⟶ P₀'.A.left), u ≫ b = v ≫ b → u ≫ P₀'.A.hom = v ≫ P₀'.A.hom → u = v :=
    fun u v e₁ e₂ => hb.1.hom_ext e₁ e₂
  refine ⟨P₀, a₁, θ.hom.left ≫ b₂, ha₁, ((isGrpPullback_of_iso θ).comp hb₂).congr (Category.id_comp _) rfl, hLa₁, ?_,
    fun E => ⟨ε₀ E, (hε E).2, ?_⟩, fun x => ?_⟩
  · refine LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB ρ₂.P.isLB _) hLa ?_
    refine LBIso.trans (pull_isLB ρ.P.isLB _) (pull_isLB P₀'.isLB θ.hom.left) (pull_isLB ρ₂.P.isLB _)
      (lbIso_pull_along hLb θ.hom.left hθ.symm).symm (lbIso_pull_along hLb₂ θ.hom.left rfl)
  · have key : (ε₀ E).left ≫ θ.hom.left = θ.hom.left ≫ (ε₀' E).left := by
      apply ext
      · rw [Category.assoc, hθ, (hε E).1, Category.assoc, (hε' E).1, ← Category.assoc, hθ]
      · simp only [Category.assoc, Over.w]
    rw [← Category.assoc, key, Category.assoc, (hε' E).2, Category.assoc]
  · obtain ⟨w, hwa, hwa₁⟩ := hw x
    obtain ⟨w', hwb, hwb₂⟩ := hw' x
    refine ⟨w, hwa₁, ?_⟩
    have s₁ := sec_of_pt S₁.R S₁.frac ha₁ _ w hwa₁
    have s₂ := sec_of_pt S₂.R S₂.frac hb₂ _ w' hwb₂
    have hww : w ≫ θ.hom.left = w' := by
      apply ext
      · rw [Category.assoc, hθ, hwa, hwb]
      · rw [Category.assoc, Over.w, s₁, s₂]
    rw [← Category.assoc, hww, hwb₂]

end GlobalTheory.Poinc.SameComb
