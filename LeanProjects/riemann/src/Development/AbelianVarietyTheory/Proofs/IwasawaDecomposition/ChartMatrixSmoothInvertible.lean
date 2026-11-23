import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.MatSmooth

open ReciprocityTheory.L2DbarEstimates

theorem exists_herm {d : ℕ} (b : Matrix (Fin d) (Fin d) ℂ) :
    ∃ B : Matrix (Fin d) (Fin d) ℂ, B.IsHermitian ∧ ∀ ξ : Fin d → ℂ,
      ∑ k, ∑ l, B k l * ξ k * starRingEnd ℂ (ξ l) =
        (((∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)).re / Real.pi : ℝ) : ℂ) := by
  refine ⟨Matrix.of fun k l => (b k l + starRingEnd ℂ (b l k)) / (2 * Real.pi), ?_, fun ξ => ?_⟩
  · ext k l
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_div₀, star_add, RCLike.star_def,
      Complex.conj_conj, map_mul, Complex.conj_ofReal, map_ofNat]
    ring
  · set S := ∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)
    have hT : ∑ k, ∑ l, starRingEnd ℂ (b l k) * ξ k * starRingEnd ℂ (ξ l) = starRingEnd ℂ S := by
      simp only [S, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e : ∑ k, ∑ l, (Matrix.of fun k l => (b k l + starRingEnd ℂ (b l k)) / (2 * Real.pi) :
        Matrix (Fin d) (Fin d) ℂ) k l * ξ k * starRingEnd ℂ (ξ l) =
        (S + ∑ k, ∑ l, starRingEnd ℂ (b l k) * ξ k * starRingEnd ℂ (ξ l)) / (2 * Real.pi) := by
      simp only [S, Matrix.of_apply, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, hT, Complex.add_conj]
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp

theorem contDiffOn_wirt {d : ℕ} {O : Set (V d)} (hO : IsOpen O) {h : V d → ℂ} (hh : ContDiffOn ℝ ∞ h O)
    (j : Fin d) : ContDiffOn ℝ ∞ (wd d j h) O ∧ ContDiffOn ℝ ∞ (wdb d j h) O := by
  have hf : ContDiffOn ℝ ∞ (fun v => fderiv ℝ h v) O :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hO).1 hh).2
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ h v (bas d j)) O := hf.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ h v (Complex.I • bas d j)) O := hf.clm_apply contDiffOn_const
  exact ⟨(h1.sub (contDiffOn_const.mul h2)).div_const _, (h1.add (contDiffOn_const.mul h2)).div_const _⟩

theorem contDiffOn_leviV {d : ℕ} {O : Set (V d)} (hO : IsOpen O) {g : V d → ℂ} (hg : ContDiffOn ℝ ∞ g O)
    (ξ : Fin d → ℂ) : ContDiffOn ℝ ∞ (fun v => leviV d g v ξ) O := by
  unfold leviV
  exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    ((contDiffOn_wirt hO (contDiffOn_wirt hO hg k).2 j).1.mul contDiffOn_const).mul contDiffOn_const

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem contDiffOn_form {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d)
    (ξ : Fin d → ℂ) : ContDiffOn ℝ ∞ (fun v => a c (c.e.symm v) ξ) c.e.target := by
  intro v hv
  obtain ⟨W, φ, hyW, hWo, hs, e⟩ := ha.1 (c.e.symm v)
  have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' W) := GlobalTheory.ChartGlue.isOpen_over c.e hWo
  have hvO : v ∈ c.e.target ∩ c.e.symm ⁻¹' W := ⟨hv, hyW⟩
  have hg : ContDiffOn ℝ ∞ (fun u => ((φ (c.e.symm u) : ℝ) : ℂ)) (c.e.target ∩ c.e.symm ⁻¹' W) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hs.chart hWo c)
  have hL : ContDiffOn ℝ ∞ (fun u => (leviV d (fun u => ((φ (c.e.symm u) : ℝ) : ℂ)) u ξ).re / Real.pi)
      (c.e.target ∩ c.e.symm ⁻¹' W) :=
    (Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_leviV hO hg ξ)).div_const _
  have hE : ContDiffOn ℝ ∞ (fun v => a c (c.e.symm v) ξ) (c.e.target ∩ c.e.symm ⁻¹' W) :=
    hL.congr fun u hu => by
      rw [e c _ (c.e.map_target hu.1) hu.2 ξ, ddcForm, AlgChart.levi, c.e.right_inv hu.1]
  exact (hE.contDiffAt (hO.mem_nhds hvO)).contDiffWithinAt

theorem matIn_spec {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (c : AlgChart p σ d)
    {v : V d} (hv : v ∈ c.e.target) : (matIn a c v).IsHermitian ∧ ∀ ξ : Fin d → ℂ,
      (a c (c.e.symm v) ξ : ℂ) = (ξ ᵥ* matIn a c v) ⬝ᵥ star ξ := by
  obtain ⟨b, eb⟩ := exists_eq_sum ha (c.e.map_target hv)
  obtain ⟨B, hB, eB⟩ := exists_herm b
  have hq : a c (c.e.symm v) = fun ξ => (∑ k, ∑ l, B k l * ξ k * starRingEnd ℂ (ξ l)).re := by
    rw [eb]
    funext ξ
    rw [eB ξ, Complex.ofReal_re]
  have hM : matIn a c v = B := by rw [matIn, hq, polMat_form hB]
  refine ⟨hM ▸ hB, fun ξ => ?_⟩
  rw [hM, eb, ← eB ξ]
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem matIn_smooth_unit_form (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)
    (R : AnRead p σ d) (a : ChartForm p σ d) (ha : IsKaehlerForm R a) (c : AlgChart p σ d) :
    (∀ i j, ContDiffOn ℝ ∞ (fun v => matIn a c v i j) c.e.target) ∧ (∀ v ∈ c.e.target, IsUnit (matIn a c v).det) ∧
      ∀ v ∈ c.e.target, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d,
        (a c (c.e.symm v) ξ.ofLp : ℂ) = (ξ.ofLp ᵥ* matIn a c v) ⬝ᵥ star ξ.ofLp := by
  refine ⟨fun i j => ?_, fun v hv => ?_, fun v hv ξ => (matIn_spec ha c hv).2 ξ.ofLp⟩
  · have hF := fun ξ => Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_form ha c ξ)
    unfold matIn polMat
    exact ((((hF _).sub (hF _)).add (contDiffOn_const.mul (hF _))).sub (contDiffOn_const.mul (hF _))).div_const _
  · rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨w, hw, hwM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have e := (matIn_spec ha c hv).2 w
    rw [hwM, zero_dotProduct, Complex.ofReal_eq_zero] at e
    exact (ha.2 c _ (c.e.map_target hv) w hw).ne' e

end GlobalTheory.ChernReg.MatSmooth
