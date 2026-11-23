import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeLinearFormPositivityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFormsRegularInConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConeExistenceAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimZeroStalkTrivialPeriodStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRegularGermRepresentativeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem associated_pow_of_map {W W' : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
    [IsDomain W'] [IsDiscreteValuationRing W'] (ι : W →+* W') {ϖ : W} (hϖ : Irreducible ϖ) (hι : Irreducible (ι ϖ))
    {x : W} {n : ℕ} (h : Associated (ι x) (ι ϖ ^ n)) : Associated x (ϖ ^ n) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact pow_ne_zero n hι.ne_zero (h.symm.eq_zero_iff.2 rfl)
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨v, hv⟩ := h
  have hk : k = n := by
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hι hι (Units.map ι.toMonoidHom u * v) 1 k n ?_
    rw [Units.val_one, one_mul, ← hv, map_mul, map_pow]
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  subst hk
  exact (associated_unit_mul_left _ _ u.isUnit)

theorem isUnit_of_ringKrullDim_le_zero {A : Type} [CommRing A] [IsDomain A] (hd : ringKrullDim A ≤ 0) {s : A}
    (hs : s ≠ 0) : IsUnit s := by
  haveI : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  obtain ⟨b, hb⟩ := (Ring.KrullDimLE.isField_of_isDomain (R := A)).mul_inv_cancel hs
  exact IsUnit.of_mul_eq_one b hb

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem exists_regularFn_traitOrdPt_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ z : Z.X, ∃ (U : Z.X.Opens) (_ : z ∈ U) (f : Γ(Z.X, U)), IsRegularFn f ∧ TraitOrdPt φ Z U f z ∧ ∀ q ∈ U, q ⤳ z → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q := by
  intro E _ _ _ H D l Xo c Z Cn φ hC hL z
  obtain ⟨R, _, _, _, ξ, t, mξ, P, m, γ, hCN, hξ, hEt, hFU, hTI, hCn, hIn⟩ := hC z
  obtain ⟨ℓ, hℓ⟩ := hL P.D.toPre.X m γ hCn
  subst hξ
  obtain ⟨h, hh0, hh⟩ := GlobalTheory.T.cone_linear_form_positivity t P γ ℓ hCN hTI hIn (fun be hs c hc e => (hℓ be hs c hc e).1)
  obtain ⟨a, ha⟩ := GlobalTheory.T.local_forms_regular_in_cone Z Cn φ hC hL ξ t mξ P γ ℓ hCN hEt hFU hTI hCn hIn hℓ h hh0 hh
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact hh0 (ha.eq_zero_iff.1 rfl)
  obtain ⟨U, hzU, f, hfa, hreg⟩ := GlobalTheory.T.exists_regular_germ_representative Z _ a ha0
  have key : ∀ (q : Z.X) (hq : q ∈ U) (hs : q ⤳ ξ (closedPoint R)),
      (q = ξ (closedPoint R) ∨ ringKrullDim (Z.X.presheaf.stalk q) ≤ 1) → TraitOrdPt φ Z U f q := by
    intro q hq hs hd W _ _ _ hW ϖ hϖ χ tW mW PW hχ be hbe hmon hU hcq
    subst hcq
    have hgerm : (Z.X.presheaf.germ U _ hU).hom f = (Z.X.presheaf.stalkSpecializes hs).hom a := by
      rw [← hfa, ← CommRingCat.comp_apply, Z.X.presheaf.germ_stalkSpecializes]
    by_cases h0 : ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) ≤ 0
    · haveI := GlobalTheory.T.dim_zero_stalk_trivial_period Z W hW χ tW mW PW hχ h0
      refine ⟨0, ?_, ?_⟩
      · simp only [Nat.cast_zero]
        exact (φ.eval_of_subsingleton _).symm
      · rw [pow_zero, associated_one_iff_isUnit]
        refine IsUnit.map _ ?_
        haveI := (Z.normal (χ (closedPoint W))).1
        refine isUnit_of_ringKrullDim_le_zero h0 ?_
        intro h00
        have := isRegularFn_iff_germ.1 hreg _ hU
        rw [h00] at this
        exact zero_notMem_nonZeroDivisors this
    · have h0' : 0 < ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) := lt_of_not_ge h0
      obtain ⟨W', _, _, _, ι, g, e, hW', hιϖ, he, hcomm, hform⟩ :=
        GlobalTheory.T.local_cone_existence_at_point Z Cn hC ξ t mξ P hCN hEt hFU hTI W hW ϖ hϖ χ tW mW PW hχ be hbe hmon hs hd h0'
      have hsym : ∀ y z, (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) y z =
          (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) z y := fun y z =>
        hbe.1 (e y) (e z)
      obtain ⟨n, hn, hgh⟩ := hh W' hW' (ι ϖ) hιϖ g _ hsym hform
      refine ⟨n, ?_, ?_⟩
      · obtain ⟨cc, hcc, hce⟩ := hIn W' hW' (ι ϖ) hιϖ g _ hsym hform
        have h2 := (hℓ _ hsym cc hcc hce).2
        rw [← hn] at h2
        rw [show ((n : ℤ) : ℝ) = (n : ℝ) by norm_cast] at h2
        rw [h2]
        exact φ.eval_comp he (fun y z => (be y z : ℝ))
      · haveI := hW.1
        haveI := hW'.1
        refine associated_pow_of_map ι hϖ hιϖ ?_
        rw [hgerm, ← hcomm a]
        exact (ha.map g).trans hgh
  exact ⟨U, hzU, f, hreg, key _ hzU specializes_rfl (Or.inl rfl), fun q hq hqz hd => key q hq hqz (Or.inr hd)⟩

end GlobalTheory.TorRef
