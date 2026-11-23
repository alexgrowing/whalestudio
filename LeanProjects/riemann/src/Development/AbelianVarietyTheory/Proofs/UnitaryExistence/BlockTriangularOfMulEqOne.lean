import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FibreFlag

theorem blockTriangular_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (f : n → ℕ) (A C : Matrix n n ℂ)
    (h : A * C = 1) (hC : C.BlockTriangular f) : A.BlockTriangular f := by
  haveI : Invertible C := C.invertibleOfIsUnitDet (Matrix.isUnit_det_of_left_inverse h)
  rw [← Matrix.inv_eq_left_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hC

theorem upper_of_blocks {r : ℕ} (q : ℕ) (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h1 : ∀ a c : Fin r, (c : ℕ) < q → c < a → B a c = 0)
    (h2 : ∀ a c : Fin r, q ≤ (c : ℕ) → c < a → B⁻¹ a c = 0) (a c : Fin r) (hca : c < a) : B a c = 0 := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have t1 : B.BlockTriangular (fun a => min (a : ℕ) q) := fun a c h =>
    h1 a c (by simp only at h; omega) (by simp only at h; rw [Fin.lt_def]; omega)
  have t2 := blockTriangular_of_mul_eq_one _ _ _ (Matrix.nonsing_inv_mul B hu) t1
  have t3 : B⁻¹.BlockTriangular (fun a => (a : ℕ)) := fun a c h => by
    by_cases hc : (c : ℕ) < q
    · exact t2 (by simp only at h ⊢; omega)
    · exact h2 a c (not_lt.1 hc) h
  exact blockTriangular_of_mul_eq_one _ _ _ (Matrix.mul_nonsing_inv B hu) t3 hca

set_option maxHeartbeats 1000000 in

theorem fibTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → FibTri e F M := by
  classical
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hneg k k' x x' Pm Pm' v v' hP hP' hu hv hv' hcf
  have hper : ∀ (k) (x : (M.X k).dom) (Pm : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm := by
    intro k x Pm hP
    obtain ⟨⟨idx, hty, -, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
    have hlat := (hφ ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun _ => rfl)).2
    exact ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ (hM.type k).2 g idx _ hty hξ hpos hlat hr).2 x.1
      (hp0 ▸ x.2)).2 Pm fun a j => (hP a j).trans (hfr _ _ _)
  have p := hper k x Pm hP
  have p' := hper k' x' Pm' hP'
  obtain rfl := F.disj k k' _ _ p p' hu
  obtain ⟨⟨idx, hty, hix, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
  obtain ⟨φ, hφe⟩ : ∃ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ a = (M.φ k a : Fin r → E) :=
    ⟨(M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap, fun _ => rfl⟩
  obtain ⟨hΛ, hlat⟩ := hφ φ hφe
  have hΨ := (hM.type k).2
  have hx : x.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x.2
  have hx' : x'.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x'.2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ := (F.fibre k _ _ p p').1 hu
  obtain ⟨γ, hγ⟩ := FrameFibre.exists_gl φ hlat.1 hlat.2.1 gam
  have hun := FrameFibre.herm_of_trace φ hlat.2.1 (M.X k).Gm γ _ (neg_ne_zero.2 (M.X k).ξ0_ne) fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hγΓ : γ ∈ (M.X k).Γ := by
    rw [hM.gam]
    refine ⟨⟨hun, fun y => hΛ ▸ (?_ : y ∈ LinearMap.range φ ↔ _ ∈ LinearMap.range φ)⟩, fun a ha => ?_, fun a => ?_⟩
    · constructor
      · rintro ⟨v, rfl⟩
        exact ⟨gam v, (hγ v).symm⟩
      · rintro ⟨v, hv⟩
        refine ⟨gam.symm v, ?_⟩
        apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
        rw [hγ, LinearEquiv.apply_symm_apply, hv]
    · obtain ⟨b, hb⟩ := hhalf a ha
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add, map_nsmul]⟩
    · obtain ⟨b, hb⟩ := hA a
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add, map_nsmul]⟩
  have hγx := FrameFibre.lact_mem_GG hun hx
  obtain ⟨Pg, hPg⟩ := ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ hΨ g idx _ hty hξ hpos hlat hr).2 _ hγx).1
  have hP1 := fun a j => (hP a j).trans (hfr x.1 _ j)
  have hP2 := fun a j => (hP' a j).trans (hfr x'.1 _ j)
  simp only [← hφe] at hP1 hP2
  have hmove := (per_move E H (F.Di k) r _ _ φ _ hΨ g idx _ hty hξ hpos hlat).2.1 x.1 γ Pm Pg hun hP1 hPg
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨b, hb, hb0, hb1, hb2, -⟩ := FramePeriod.frame_of_period_linear E H (F.Di k) r _ _ φ _ hΨ g idx _ hty
    hξ hpos hlat Pg _ hγx x'.1 hx' hPg Pm' hP2 A fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [hAv, hh, hmove a (gam a) (hγ a).symm]
  have hrig := (FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F k Pm Pm' gam A p p' hiso hhalf hA
    fun a => by rw [hAv, hh]).2.2
  choose cf hcf1 hcf2 hcf3 using hcf
  have hcol : ∀ τ i, A *ᵥ (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ, i⟩) 1 := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k Pm p _ (v τ) _ (hv τ) (cf τ i) (v' τ i)).1
      (hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k Pm p k Pm' h.toLinearMap p'
      (fun z => by rw [← hrig z, hAv]; rfl) _ _).1 d1
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k Pm' p'
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hv' τ i)
  let C : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun j j' =>
    (∑ i, (show ℂ from cf (e j').1 (e j').2 i) • (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ)) j
  have hAC : A * C = 1 := by
    ext j j'
    have := congrFun (hcol (e j').1 (e j').2) j
    rw [Sigma.eta, Equiv.symm_apply_apply, Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  have hC : C.BlockTriangular (fun j => ((e j).2 : ℕ)) := by
    intro j j' hj
    simp only [C, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : j = e.symm ⟨(e j').1, i⟩
    · have h3 : (((e j).2 : ℕ)) = i := by rw [hi, Equiv.apply_symm_apply]
      have h4 : cf (e j').1 (e j').2 i = 0 := hcf2 _ _ i (by rw [Fin.lt_def, ← h3]; exact hj)
      rw [h4]
      exact zero_mul _
    · have h5 : (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ) j = 0 := Pi.single_eq_of_ne hi _
      exact mul_eq_zero_of_right (M₀ := ℂ) _ h5
  have hT := blockTriangular_of_mul_eq_one _ _ _ hAC hC
  have hdet : ∀ τ, (mat b τ).det ≠ 0 := fun τ h0 => (hx' τ).1 (by
    have e1 : mat x'.1 τ = mat (lact γ x.1) τ * mat b τ := by rw [hb]; rfl
    rw [e1, Matrix.det_mul, h0, mul_zero])
  refine ⟨γ, hγΓ, b, fun τ => ⟨hdet τ, upper_of_blocks (F.Di k).q (mat b τ) (hdet τ) ?_ ?_⟩, by rw [← hb]⟩
  · intro a c' hc hca
    by_cases ha : (a : ℕ) < (F.Di k).q
    · have h1 := hb1 (idx.symm (τ, c')) (idx.symm (τ, a))
      have i1 := hix (idx.symm (τ, c'))
      have i2 := hix (idx.symm (τ, a))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
      rw [Equiv.apply_symm_apply] at i1 i2
      simp only [hc, ha, if_true] at i1 i2
      rw [Fin.lt_def] at hca
      exact (h1 rfl hc ha).symm.trans (hT (by simp only; omega))
    · exact hb0 τ a c' hc (not_lt.1 ha)
  · intro a c' hc hca
    rw [Fin.lt_def] at hca
    have ha : (F.Di k).q ≤ (a : ℕ) := by omega
    have h1 := hb2 (idx.symm (τ, a)) (idx.symm (τ, c'))
    have i1 := hix (idx.symm (τ, c'))
    have i2 := hix (idx.symm (τ, a))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    rw [Equiv.apply_symm_apply] at i1 i2
    simp only [not_lt.2 hc, not_lt.2 ha, if_false] at i1 i2
    exact (h1 rfl ha hc).symm.trans (hT (by simp only; omega))

end GlobalTheory.FibreFlag
