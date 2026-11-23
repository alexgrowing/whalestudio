import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.FormalGeneric GlobalTheory.SectionRingIso GlobalTheory.FormalPoint in

theorem GlobalTheory.GenericIso.cross_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), ∀ (B : Type) [CommRing B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) → ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' → ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL → (∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) → ∀ (k : ℕ) (σ τ : H0 U.LG.L k) (σ' τ' : H0 U'.LG.L k), GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ' → GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k τ τ' → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z), gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (τ'.f (fun _ => jL')) = gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (τ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL')) := by
  intro R _ _ I _ D D' A A' G G' _ _ _ _ _ _ U U' hD j B _ _ g' g jL jL' hB hg' c' c hgg k σ τ σ' τ' hσ hτ Z ρ z
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have ex : ∀ s : H0 U.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g) z (fun _ => jL) := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g (ch U.LG.L fun _ => jL) ⊤ (fun _ _ => mem_ch.2 (c trivial)) ρ z trivial _⟩
  have ex' : ∀ s : H0 U'.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g') z (fun _ => jL') := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g' (ch U'.LG.L fun _ => jL') ⊤ (fun _ _ => mem_ch.2 (c' trivial)) ρ z trivial _⟩
  choose b hb using ex
  choose b' hb' using ex'
  have pr : ∀ (s : H0 U.LG.L k) (s' : H0 U'.LG.L k) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ (b s * b' s') = vl s (ρ ≫ g) z (fun _ => jL) * vl s' (ρ ≫ g') z (fun _ => jL') :=
    fun s s' Z ρ z => (gs_mul ρ z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (hb s Z ρ z) (hb' s' Z ρ z))
  have key : ∀ {T : Type} [CommRing T] (u : Tˣ) (v x y x' y' : T), u.val * x = v * x' → u.val * y = v * y' →
      x * y' = y * x' := fun u v x y x' y' h₁ h₂ => by
    refine (Units.mul_right_inj u).1 ?_
    linear_combination y' * h₁ - x' * h₂
  have E : b σ * b' τ' = b τ * b' σ' := fn_ext_germs (I.map (algebraMap R B)) fun e z => by
    obtain ⟨jM, a₁⟩ := exists_chart D.toPre.P.isLB
      (GlobalTheory.FamFieldPull.prA hD ((U'.gt e).pG.left (reduction I y e z)))
    obtain ⟨jM', a₂⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left (reduction I y e z))
    have a₄ : (fstG I e G').left (reduction I y e z) ∈ U'.LG.L.U jL' :=
      (congrArg (fun q => q z ∈ U'.LG.L.U jL') (hy e)).mpr (c' trivial)
    have a₃ : (fstG I e G).left ((j e).hom.left (reduction I y e z)) ∈ U.LG.L.U jL :=
      (congrArg (fun q => q z ∈ U.LG.L.U jL) (hgg e _ _ _ (hy e))).mpr (c trivial)
    have H₁ := hσ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    have H₂ := hτ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    rw [pr, pr, ← hgg e _ _ _ (hy e), ← hy]
    exact key _ _ _ _ _ _ H₁ H₂
  exact (pr σ τ' Z ρ z).symm.trans ((congrArg (gs ρ z ⊤) E).trans (pr τ σ' Z ρ z))
