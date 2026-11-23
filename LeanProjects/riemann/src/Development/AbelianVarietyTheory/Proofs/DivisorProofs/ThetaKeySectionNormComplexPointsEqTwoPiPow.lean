import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

noncomputable section

namespace GlobalTheory.KeyArchNorm

section Value

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth

theorem norm_rule_of_coord {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) (x : KeyIn ℂ) {g : ℕ}
    (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {θ : (Fin g → ℂ) → ℂ} {Fd : Set (Fin g → ℂ)} {ξ : ℝ} (hξ : 0 < ξ) (p : Fin x.P.g ≃ Fin g)
    (hA : u.IsAH Hm χ) (hR : u.IsRig x.rig) (hF : u.IsFn x.th θ) (hD : ∀ i, u.IsDiff (Pi.single (p i) 1) (x.v i))
    (hFd : IsAddFundamentalDomain u.Λ Fd volume)
    (hN : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1)
    (hH : Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    ‖(κ ℂ x : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  subst hg
  obtain ⟨⟨Ef, hE, hb⟩, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  have := u.discrete
  have hv := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 hE hb hFd
  have hd : Hm.det.re = (2 * ξ) ^ x.P.g := by
    rw [hH, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  let W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => Pi.single (p i) 1
  have hW : ‖W.det‖ = 1 := by
    have e : W = (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ).submatrix p id := by
      ext i j
      simp [W, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [e, Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have key := hκ x u Hm W χ θ Fd 1 _ hA hR hF hD hFd hN.symm rfl
  rw [hd] at hv
  rw [hW, eq_inv_of_mul_eq_one_left hv] at key
  have hπ := Real.pi_pos
  simp only [mul_one, one_pow] at key
  rw [← key]
  simp only [mul_pow, pow_mul']
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem norm_rule_of_isOrtho {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (h0 : 0 < ξ)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ)
    (hx : (U.X k).IsOrtho x.1) (Φ : FibKey Xo ℂ (U.un k x).x)
    (hΦ : Tied (S := ℂ) e (U.un k x).s (U.un k x).u Φ) :
    ‖(κ ℂ Φ.key : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  obtain ⟨ht, hg, hv⟩ := hΦ
  subst hg
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have key := norm_rule_of_coord hκ Φ.key hg u h0 (e.trans W.e.symm) hA hR hF (fun i => by
    obtain ⟨w, hw, hd⟩ := hD _ _ ((U.un k x).tan (e i).1 (e i).2) (W.der (e i).1 (e i).2)
    have hwv : w = Φ.v i :=
      Over.OverMorphism.ext (Φ.m.cart.1.hom_ext (hw.trans (hv i).symm) ((Over.w w).trans (Over.w (Φ.v i)).symm))
    rw [hwv] at hd
    exact hd) hFd Wu.c9 hH
  rw [hg] at key
  exact key

end Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 (-4)).1 (τ, i) = 4 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
    rw [wtOf_big _ _ ⟨τ, h⟩ i hp]
    simp
  · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
    have e := wtOf_small (Dw := Dw) 0 (-4) ⟨conjEmb τ, conj_mem h⟩ i hq
    simp only [conjEmb_conjEmb] at e
    rw [e]
    simp

theorem exZ_wtOf : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact wtOf_fst τ i i.2

theorem lieFacZ_mul {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {x : ℝ} (hx : 0 < x) :
    lieFacZ Dw x (wtOf Dw 0 (-4)) * (2 * Real.pi * x) ^ (2 * g) = 1 := by
  have hg : ∑ τ : E →+* ℂ, Dw.mult τ = g := by
    have := Fintype.card_congr e
    simpa using this.symm
  have hs : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), ((wtOf Dw 0 (-4)).1 (τ, i) : ℝ)) = 4 * g := by
    rw [← hg, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl fun (i : Fin (Dw.mult τ)) _ => by rw [wtOf_fst τ i i.2]]
    simp [mul_comm]
  have hπ : 0 < 2 * Real.pi * x := by positivity
  rw [lieFacZ, hs, ← Real.exp_log (pow_pos hπ (2 * g)), ← Real.exp_add, Real.log_pow, Real.exp_eq_one_iff]
  push_cast
  ring

end Weight

theorem homN_key_const : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  intro κ _ _ hκ E _ _ _ H Dw l Xo c g e σ r U x K hσ hU hx hS hpq hK hval
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ (2 * g), by positivity, ?_, fun k y hy => ?_⟩
  · rw [abs_of_nonneg (Real.log_nonneg (one_le_pow₀ hπ)), Real.log_pow]
    push_cast
    exact le_rfl
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r U hS hσ hU hpq (wtOf Dw 0 (-4)) (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_fst τ j hj, wtOf_fst τ i (hij.trans_lt hj)]) K (exZ_wtOf (Dw := Dw) ▸ hK) k
  have hb := FrameDegreeData.bOf_mem (U.X k) hy
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) hy hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) hy
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 y hy _ hb
  generalize rmul y (FrameDegreeData.bOf (U.X k) y) = z at hz ho hp
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : 0 < x := hx k τ₀ ▸ norm_pos_iff.2 ((map_ne_zero τ₀).2 (U.X k).ξ0_ne)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : FibKey Xo ℂ (U.un k ⟨z, hz⟩).x, Tied (S := ℂ) e (U.un k ⟨z, hz⟩).s (U.un k ⟨z, hz⟩).u Φ :=
    @GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) hpq
  have hv : rdU U (K : Rul Xo c) k z = (κ ℂ Φ.key : ℂ) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact @hval ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) Φ hΦ
  have hn : (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) z = ‖(κ ℂ Φ.key : ℂ)‖ := by
    simp [Data.pnorm, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho, hv]
  show lieFacZ Dw x _ * (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) y = _
  rw [← hp, hn, norm_rule_of_isOrtho hκ e h0 hσ hU k ⟨z, hz⟩ (hx k) ho Φ hΦ, mul_left_comm, lieFacZ_mul e h0, mul_one]

end GlobalTheory.KeyArchNorm
