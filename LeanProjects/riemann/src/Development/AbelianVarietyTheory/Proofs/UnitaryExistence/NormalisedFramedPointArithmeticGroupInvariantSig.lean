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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMapStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem wchar_ex_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {S : Type} [CommRing S] (t : Ix Dw → Sˣ) (h0 : (t none : S) ^ 2 = 1)
    (h1 : ∀ p, t (some p) = 1) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) : wchar (ex Dw a n) t = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold wchar
  rw [Fintype.prod_option]
  simp only [h1, Units.val_one, one_pow, Finset.prod_const_one, mul_one]
  show (t none : S) ^ (m + m) = 1
  rw [← two_mul, pow_mul, h0, one_pow]

theorem normUn_gamma : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hσ hM hN hun γ hγ x h
  obtain ⟨gam, hgam, hP⟩ := GlobalTheory.per_gam E H Dw l Xo c σ g e F r M hσ hM hN k T.Pf T.per γ hγ
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun ⟨_, h⟩
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm (lact γ x.1) ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm (lact γ x.1)) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact h
  obtain ⟨hx, hd, t₀, hsec, ht⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un k x)
    (un k ⟨_, h⟩) gam 1 hy hy' hgam (fun a => by
      rw [T.co.apply_symm_apply, T.co.apply_symm_apply, Matrix.one_mulVec]; exact hP x.1 x.2 a)
  have hu : ∀ τ i, (un k ⟨_, h⟩).u τ i = (un k x).u τ i := fun τ i => by
    have h1 := hd τ i
    rw [inv_one, Matrix.one_mulVec] at h1
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (T.isPer _ hb)).2.1 _).unique h1 (hy.2.1 τ i)
  have hC : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have ht2 : toC (t₀ : CAt σ) ^ 2 = 1 := by
    have d1 := (T.norm _ hb).1.ne_zero
    have d2 := (T.norm _ hb').1.ne_zero
    rw [hκ, hκ', Matrix.det_one, mul_one] at ht
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d1) d2) ?_
    rw [ht]; ring
  refine ⟨fun i => i.elim t₀ fun _ => 1, ?_, fun a n hn => ?_⟩
  · refine (frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hsec⟩
    rw [hu]
    exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) (un k x) (un k x) (un k x)).1.2.1 τ i
  · exact wchar_ex_sign Dw _ ht2 (fun _ => rfl) a n hn.2

end GlobalTheory.FrameUnif
