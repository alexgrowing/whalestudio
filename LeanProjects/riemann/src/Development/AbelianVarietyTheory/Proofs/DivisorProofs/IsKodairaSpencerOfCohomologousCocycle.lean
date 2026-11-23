import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSCoh

open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res le_preimage_mono)

theorem isKS_of_cohomologous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (a : ∀ i, Γ(t.G.left, W i)ˣ) (u : ∀ i i', Γ(t.G.left, W i ⊓ W i')ˣ), ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) → (∀ i, IsField (W i) (d i)) → (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) → (∀ i i', (u i i').val * resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i') (a i').val = resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i) (a i).val * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) → (∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ b, IsTranslate t φ g₀ (v b) (w b)) → valR g₀ O (d i O f - d i' O f) = ∑ b, ∑ b', φ (Θ b b') * ((valR (w b') (W i ⊓ W i') (u i i').val).snd * valR g₀ (W i ⊓ W i') (u i i')⁻¹.val) * (valR (w b) O f).snd) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U n v hv D Θ J W j d hj α u hcov hF hD hu hc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  choose dd hdF hd0 hdv using fun b => exists_invField U (hv b)
  let cf : ∀ i, Fin n → Γ(t.G.left, W i) := fun i a => -∑ b, (t.G.hom.appLE U.1 (W i) (hWU i)).hom (Θ a b) *
    (dd b (W i) (α i).val * (α i)⁻¹.val)
  refine ⟨J, W, j, fun i O f => d i O f + ∑ a, smulFld (cf i a) (dd a) O f, hcov, hj,
    fun i => isField_add (hF i) (isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a))),
    fun i h s => ?_, fun i i' O hO f S _ φ g w hg hgO hw => ?_⟩
  · beta_reduce
    simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hD i h s
  · have hi : O ≤ W i := hO.trans inf_le_left
    have hi' : O ≤ W i' := hO.trans inf_le_right
    have hred := fun b => translate_red (hv b) hg (hw b)
    have hcf : ∀ r, O ≤ W r → valR g O (∑ a, smulFld (cf r a) (dd a) O f) = ∑ a, -∑ b, φ (Θ a b) *
        ((valR (w b) (W r) (α r).val).snd * valR g (W r) (α r)⁻¹.val) * (valR (w a) O f).snd := by
      intro r hr
      have hgr := le_preimage_mono g hr hgO
      rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hr, valR_mul _ _ hgO, valR_res _ hr hgO,
        hdv a O (hr.trans (hWU r)) f S φ g (w a) hg hgO (hw a), valR_eq _ _ hgr, map_neg, map_sum, neg_mul,
        Finset.sum_mul]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgr, valR_mul _ _ hgr, valR_mul _ _ hgr, valR_base U _ hg hgr,
        hdv b _ (hWU r) _ S φ g (w b) hg hgr (hw b)]
    have hgii : ⊤ ≤ g ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g hO hgO
    have hLL : W i ⊓ W i' ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := inf_le_inf (hj i) (hj i')
    have e : ∀ b, (valR (w b) _ (u i i').val).snd * valR g _ (u i i')⁻¹.val =
        (valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g _ (t.PP.L.g (j i) (j i'))⁻¹.val +
        ((valR (w b) _ (α i).val).snd * valR g _ (α i)⁻¹.val -
          (valR (w b) _ (α i').val).snd * valR g _ (α i')⁻¹.val) := by
      intro b
      have hwb := GlobalTheory.CechKS.le_preimage_of_red (hred b) hgii
      have h0 := congrArg (valR (w b) (W i ⊓ W i')) (hu i i')
      rw [valR_mul _ _ hwb, valR_mul _ _ hwb] at h0
      erw [valR_res _ _ hwb, valR_res _ _ hwb, valR_res _ _ hwb] at h0
      refine GlobalTheory.CechKS.dlog_of_mul_eq _ _ _ _ _ _ _ _ (by rw [h0])
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi hgO) (α i))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hi' hgO) (α i'))
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) (le_preimage_mono g hLL hgii) _)
        (GlobalTheory.CechKS.valR_fst_mul_inv (hred b) hgii (u i i'))
    beta_reduce
    rw [show d i O f + ∑ a, smulFld (cf i a) (dd a) O f - (d i' O f + ∑ a, smulFld (cf i' a) (dd a) O f) =
        (d i O f - d i' O f) + ∑ a, smulFld (cf i a) (dd a) O f - ∑ a, smulFld (cf i' a) (dd a) O f by ring,
      GlobalTheory.CechInv.valR_sub _ _ hgO, valR_add _ _ hgO, hc i i' O hO f S φ g w hg hgO hw, hcf i hi, hcf i' hi']
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (φ (Θ a b) * (valR (w a) O f).snd) * e b

end GlobalTheory.LogKSCoh
