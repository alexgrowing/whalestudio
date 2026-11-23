import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldCommutesPointTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightPullbackPointTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionRelOfTranslateSectionValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.HeatTrans in

theorem GlobalTheory.HeatTrans.exists_heat_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), ∃ h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D, h₁.Θ = h.Θ ∧ h₁.u = h.u ∧ (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) ∧ ∀ (k : ℕ) (τ τ' : SecM Y.q.left Q.P.L k) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → h.Acts k τ τ' → h₁.Acts k σ σ' := by
  intro R _ _ Q O _ _ _ oa Y n v dd hinv D h hB x
  have hTeq : (𝟙 Y.H * (toUnit Y.H ≫ x)).left = tr Y.H x := rfl
  rw [hTeq]
  have hTS := tr_tr_inv Y.H x
  have hST := tr_inv_tr Y.H x
  have hT := tr_hom Y.H x
  have hS := tr_hom Y.H x⁻¹
  set T := tr Y.H x with hTd
  set S := tr Y.H x⁻¹ with hSd
  have hdd : ∀ a (O O' : Y.H.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(Y.H.left, O),
      dd a O' (pbT T f O') = pbT T (dd a O f) O' := fun a => GlobalTheory.T.invariantVectorField_commutes_pointTranslation R Y.H (v a) (dd a) (hinv a) x
  have hpre : ∀ U : Y.H.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : Y.H.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  refine ⟨⟨h.Θ, h.symm, h.u, h.J, (fun i => T ⁻¹ᵁ h.W i), h.j, (fun i => conjF T S (h.d i)),
    (fun i => pbT T (h.p i) (T ⁻¹ᵁ h.W i)), (fun i => pbT T (h.p' i) (T ⁻¹ᵁ h.W i)), ?_, ?_, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    have hz : T z ∈ ⨆ i, h.W i := h.cover ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    rw [Scheme.Hom.comp_preimage]
    exact T.preimage_mono (h.le i)
  · intro i
    exact isLift_conjF Y.H D hTS hST hT hS (h.lift i)
  · intro k i i' O₁ hO f
    have hOi : O₁ ≤ T ⁻¹ᵁ h.W i := hO.trans inf_le_left
    have hOi' : O₁ ≤ T ⁻¹ᵁ h.W i' := hO.trans inf_le_right
    have hSO : S ⁻¹ᵁ O₁ ≤ h.W i ⊓ h.W i' :=
      le_inf ((S.preimage_mono hOi).trans (hpre _).le) ((S.preimage_mono hOi').trans (hpre _).le)
    have hg : S ⁻¹ᵁ O₁ ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) :=
      le_inf (hSO.trans (inf_le_left.trans (h.le i))) (hSO.trans (inf_le_right.trans (h.le i')))
    have hg' : O₁ ≤ (T ≫ Y.q.left) ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := by
      rw [Scheme.Hom.comp_preimage, ← hpre' O₁]
      exact T.preimage_mono hg
    have hOO : O₁ ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O₁) := (hpre' O₁).ge
    rw [op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k hOi,
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i') (h.p i') (h.p' i') k hOi',
      GlobalTheory.KS.pbT_mul, pbT_pow S le_rfl _ _, pbT_pbT S (T ≫ Y.q.left) hg' le_rfl]
    have hSTq : S ≫ T ≫ Y.q.left = Y.q.left := by rw [← Category.assoc, hST, Category.id_comp]
    rw [hSTq, h.glue k i i' _ hSO, GlobalTheory.KS.pbT_mul, pbT_pow T hOO, pbT_pbT T Y.q.left hg hOO]
  · intro i
    obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
    refine ⟨?_, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp', ?_⟩
    · exact ⟨_, (congrArg (T ⁻¹ᵁ ·) hV).trans (preimage_tr_q Y x V)⟩
    · intro α V₁ hV₁ f hf
      obtain ⟨V₂, hV₂⟩ : ∃ V₂, S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) = Y.q.left ⁻¹ᵁ V₂ := ⟨_, preimage_tr_q Y x⁻¹ V₁⟩
      have hle : S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) ≤ h.W i := (S.preimage_mono hV₁).trans (hpre _).le
      have hf' : IsWt Y α (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁)) (pbT S f (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁))) :=
        GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x⁻¹ α _ _ le_rfl f hf
      have gen : ∀ (U : Y.H.left.Opens), U = Y.q.left ⁻¹ᵁ V₂ → ∀ g : Γ(Y.H.left, U), U ≤ h.W i → IsWt Y α U g →
          IsWt Y α U (h.d i U g) := by
        rintro U rfl g hU hg
        exact hd α V₂ hU g hg
      exact GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x α _ _ (hpre' _).ge _ (gen _ hV₂ _ hle hf')
  · intro k τ τ' σ σ' hσ hσ' hA i
    have hW : S ⁻¹ᵁ (T ⁻¹ᵁ h.W i) ≤ h.W i := (hpre _).le
    show rsT (σ'.f fun _ => h.j i) (T ⁻¹ᵁ h.W i) = op Y.H dd h.Θ h.u (conjF T S (h.d i)) (pbT T (h.p i) (T ⁻¹ᵁ h.W i))
      (pbT T (h.p' i) (T ⁻¹ᵁ h.W i)) k (T ⁻¹ᵁ h.W i) (rsT (σ.f fun _ => h.j i) (T ⁻¹ᵁ h.W i))
    rw [GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ' τ' hσ' (h.j i) (h.W i) (h.le i), GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ τ hσ (h.j i) (h.W i) (h.le i),
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (le_rfl : T ⁻¹ᵁ h.W i ≤ T ⁻¹ᵁ h.W i),
      pbT_pbT S T le_rfl le_rfl, hST, pbT_id hW,
      op_rsT Y.H dd (fun a => (hinv a).1) h.Θ h.u (h.d i) (h.lift i).1 (h.p i) (h.p' i) k hW le_rfl,
      GlobalTheory.KS.pbT_rsT T hW (hpre' _).ge, hA i]
