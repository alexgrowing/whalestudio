import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex

noncomputable section

section Push
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal

namespace GlobalTheory.KeyTransport

theorem eq_comp_of_isLieComb {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n : ℕ} {c : Fin n → ℂ}
    {v' : Fin n → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)} (hv : ∀ i, (v i).left = (v' i).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb c v w) : w = w' ≫ ψ := by
  obtain ⟨a', ha', rfl⟩ := hw'
  obtain ⟨a, ha, rfl⟩ := hw
  let m : (epsR ℂ ⟶ A') →* (epsR ℂ ⟶ A) := MonoidHom.mk' (fun p => p ≫ ψ) hm
  have e : a = m ∘ a' := by
    funext i
    ext
    change _ = (a' i).left ≫ ψ.left
    rw [ha, ha', hv, Category.assoc]
  rw [e, ← List.map_ofFn, ← map_list_prod]
  rfl

theorem eq_comp_of_isLieComb_cast {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (hm : ∀ a b : epsR ℂ ⟶ A', (a * b) ≫ ψ = (a ≫ ψ) * (b ≫ ψ)) {n n' : ℕ} (h : n = n') {c : Fin n' → ℂ}
    {v' : Fin n' → (epsR ℂ ⟶ A')} {v : Fin n → (epsR ℂ ⟶ A)}
    (hv : ∀ i, (v i).left = (v' (i.cast h)).left ≫ ψ.left)
    {w' : epsR ℂ ⟶ A'} {w : epsR ℂ ⟶ A} (hw' : IsLieComb c v' w') (hw : IsLieComb (fun i => c (i.cast h)) v w) :
    w = w' ≫ ψ := by
  subst h
  exact eq_comp_of_isLieComb ψ hm hv hw' hw

theorem exists_push_key {x x' : KeyIn ℂ} (H : KeyPB x' x (RingHom.id ℂ)) {g : ℕ} (u' : HolUnif x'.P.A x'.P.L g) :
    ∃ u : HolUnif x.P.A x.P.L g, u.Λ = u'.Λ ∧ (∀ Hm χ', u'.IsAH Hm χ' → ∃ χ, u.IsAH Hm χ) ∧
      (u'.IsRig x'.rig → u.IsRig x.rig) ∧ (∀ θ, u'.IsFn x'.th θ → u.IsFn x.th θ) ∧
      ∀ (h : x.P.g = x'.P.g) (c : Fin x'.P.g → ℂ) (w' : epsR ℂ ⟶ x'.P.A) (w : epsR ℂ ⟶ x.P.A) (W : Fin g → ℂ),
        IsLieComb c x'.v w' → IsLieComb (fun i => c (i.cast h)) x.v w → u'.IsDiff W w' → u.IsDiff W w := by
  obtain ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hFid : spMap F = 𝟙 _ := by
    rw [KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]
    exact Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  let ψ : x'.P.A ⟶ x.P.A := Over.homMk φ (hc'.1.w.trans (Category.comp_id _))
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push x.P.isLB x'.P.isLB ψ hc' w ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨u, hΛ, fun Hm χ' hA => ⟨fun l => χ' ⟨l.1, hΛ ▸ l.2⟩, hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩,
    fun h₄ j hj => ?_, fun θ h₅ j z hz => ?_, fun h c q' q W hq' hq h₆ U hU f => ?_⟩
  · rw [hex] at hz
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have hl : u'.ex (z + l.1) = u'.ex z := by
      rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
    have e := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ k z ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hfr j k z hj hk, hfr j k (z + l.1) (hl ▸ hj) (hl ▸ hk), hl, e]
    ring
  · have h0 : (u'.ex 0).left = eSec x'.P.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB (eSec x'.P.A pt)
    have hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have e₀ : q = q' ≫ ψ := eq_comp_of_isLieComb_cast ψ (fun a b => comp_mul_of_isGrpPullback ψ hc' a b) h
      (fun i => by
        change _ = _ ≫ φ
        rw [hv, hFid, Category.id_comp]
        rfl) hq' hq
    have e : q.left = q'.left ≫ φ := by
      rw [e₀]
      rfl
    have := h₆ (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)
    simp only [valAt'_comp, ← hex] at this
    rw [← this]
    congr 2
    generalize q.left = p at e hU
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl

end GlobalTheory.KeyTransport
end Push

section Main
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyTransport

theorem uniformisation_transport : ∀ (x x' : KeyIn ℂ), KeyPB x' x (RingHom.id ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (RingHom.id ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (RingHom.id ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (RingHom.id ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (RingHom.id ℂ) (W i)) w' := by
  intro x x' H hg g u Hm χ θ Fd ⟨h₁, h₂, h₃, h₄⟩
  have H' : KeyPB x x' (RingHom.id ℂ) :=
    KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)
  have hH : Hm.map (RingHom.id ℂ) = Hm := rfl
  obtain ⟨u', hΛ, hA, hR, hF, hD⟩ := exists_push_key H' u
  obtain ⟨χ', hχ⟩ := hA Hm χ h₁
  exact ⟨u', χ', θ, Fd, hχ, hR h₂, hF θ h₃, hΛ ▸ h₄, rfl, fun cf w w' W hw hw' hW => hD hg cf w w' W hw hw' hW⟩

end GlobalTheory.KeyTransport
end Main
end
