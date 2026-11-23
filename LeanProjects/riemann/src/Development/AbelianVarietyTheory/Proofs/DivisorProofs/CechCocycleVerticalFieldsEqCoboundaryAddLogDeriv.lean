import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalVectorFieldUniqueCombinationBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffineStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSCocycle

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_appLE le_preimage_mono)

theorem resG_resG' {Z : Scheme.{0}} {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun k => k.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem exists_coboundary_add_dlog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
  intro E _ _ _ H X t hP hA hK U n v hv hb J W j hWa hcov hj e he hev hcoc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => (le_iSup W i).trans hcov.le
  choose dd hdF hd0 hdv using fun a => exists_invField U (hv a)
  have hsp := fun i i' => GlobalTheory.T.verticalVectorField_unique_combination_basis E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i') (inf_le_left.trans (hWU i))
    (e i i') (he i i') (fun r => hev i i' _ r)
  choose c hc using fun i i' => (hsp i i').exists
  have hcc : ∀ a i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i' a) +
      resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'' a) =
      resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
        (c i i'' a) := by
    intro a i i' i''
    have h1 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have h2 : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h3 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT : W i ⊓ W i' ⊓ W i'' ≤ t.G.hom ⁻¹ᵁ U.1 := h3.trans (inf_le_left.trans (hWU i))
    have hu := (GlobalTheory.T.verticalVectorField_unique_combination_basis E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i' ⊓ W i'') hT (e i i'')
      (isField_mono h3 (he i i'')) (fun r => ?_)).unique
      (y₁ := fun a => resG _ h1 (c i i' a) + resG _ h2 (c i' i'' a)) (y₂ := fun a => resG _ h3 (c i i'' a)) ?_ ?_
    · exact congrFun hu a
    · rw [← resG_appLE U (inf_le_left.trans (hWU i)) h3 r, (he i i'').2.2 _ _ h3 le_rfl, hev, map_zero]
    · intro O hO f
      rw [← hcoc i i' i'' O hO f, hc i i' O (hO.trans h1) f, hc i' i'' O (hO.trans h2) f]
      simp only [map_add, resG_resG', add_mul, Finset.sum_add_distrib]
    · intro O hO f
      rw [hc i i'' O (hO.trans h3) f]
      simp only [resG_resG']
  choose θ hh hθ using fun a => GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_affine E H X t hP hA hK U n v hv hb dd hdF hd0 hdv J W j hWa hcov hWU hj
    (fun i i' => c i i' a) (hcc a)
  refine ⟨Matrix.of fun a b => θ a b, fun i O f => ∑ a, smulFld (hh a i) (dd a) O f,
    fun i => isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a)), fun i hW r => ?_,
    fun i i' O hO f S _ φ g₀ w hg hgO hw => ?_⟩
  · simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero]
  · have hO1 : O ≤ W i := hO.trans inf_le_left
    have hO2 : O ≤ W i' := hO.trans inf_le_right
    have hPU : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1 := inf_le_left.trans (hWU i)
    have hgP : ⊤ ≤ g₀ ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g₀ hO hgO
    have hred := fun a => translate_red (hv a) hg (hw a)
    have key : ∀ a, valR g₀ O (resG t.G.left hO (c i i' a) * dd a O f) =
        valR g₀ (W i) (hh a i) * (valR (w a) O f).snd - valR g₀ (W i') (hh a i') * (valR (w a) O f).snd +
          ∑ b, φ (θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd *
            valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
      intro a
      rw [valR_mul _ _ hgO, valR_res _ hO hgO, hdv a O (hO.trans hPU) f S φ g₀ (w a) hg hgO (hw a), hθ a i i',
        valR_add _ _ hgP, GlobalTheory.CechInv.valR_sub _ _ hgP, valR_res _ _ hgP, valR_res _ _ hgP, valR_eq _ _ hgP,
        map_sum, add_mul, sub_mul, Finset.sum_mul]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgP, valR_mul _ _ hgP, valR_mul _ _ hgP, valR_base U _ hg hgP, valR_res _ _ hgP,
        hdv b _ hPU _ S φ g₀ (w b) hg hgP (hw b),
        valR_res _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b) hgP)]
    have hsm : ∀ k (hk : O ≤ W k), valR g₀ O (∑ a, smulFld (hh a k) (dd a) O f) =
        ∑ a, valR g₀ (W k) (hh a k) * (valR (w a) O f).snd := by
      intro k hk
      rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hk, valR_mul _ _ hgO, valR_res _ hk hgO,
        hdv a O (hk.trans (hWU k)) f S φ g₀ (w a) hg hgO (hw a)]
    beta_reduce
    rw [hc i i' O hO f, GlobalTheory.CechInv.valR_sub _ _ hgO, hsm i hO1, hsm i' hO2, valR_eq _ _ hgO, map_sum]
    simp only [← valR_eq _ _ hgO, key, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end GlobalTheory.KSCocycle
