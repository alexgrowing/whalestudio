import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLinesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPureTensorsSeparateTensorProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.UnitPairing

def IsPolyFn (f : ℝ → ℂ) : Prop := ∃ p : Polynomial ℂ, ∀ s : ℝ, f s = p.eval (s : ℂ)

theorem IsPolyFn.const (c : ℂ) : IsPolyFn fun _ => c := ⟨Polynomial.C c, fun s => by simp⟩

theorem IsPolyFn.coe : IsPolyFn fun s => (s : ℂ) := ⟨Polynomial.X, fun s => by simp⟩

theorem IsPolyFn.add {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s + g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.mul {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s * g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.sum {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∑ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∑ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_finsetSum]⟩

theorem IsPolyFn.prod {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∏ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∏ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_prod]⟩

variable {D : D7} {V V' : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S')

theorem ellT_pure (w v : ∀ τ, M.H τ) : ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  simp [ellT]

theorem isPolyFn_ellT (a b : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    IsPolyFn fun s => ellT M (fun τ => ((a + (s : ℂ) • b) τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      inner_add_left, inner_smul_left, Complex.conj_ofReal]
    exact (IsPolyFn.const _).mul (IsPolyFn.prod _ fun τ => (IsPolyFn.const _).add (IsPolyFn.coe.mul (IsPolyFn.const _)))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

theorem ellT_smul (c : D.what₂.Tau → ℝ) (a : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    ellT M (fun τ => (((c τ : ℂ) • a τ : M.sm τ) : M.H τ)) x = (∏ τ, (c τ : ℂ)) * ellT M (fun τ => (a τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      Finset.prod_mul_distrib]
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add]

noncomputable def pairing (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) : ℂ :=
  ellT M (fun τ => (w τ : M.H τ)) (inclT M (L (PiTensorProduct.tprod ℂ v)))

theorem isPolyFn_pairing (L : SmT M' →ₗ[ℂ] SmT M) (a b : M.Vec) (a' b' : M'.Vec) :
    IsPolyFn fun s => pairing M M' L (a + (s : ℂ) • b) (a' + (s : ℂ) • b') := by
  classical
  have h : ∀ s : ℝ, PiTensorProduct.tprod ℂ (a' + (s : ℂ) • b') = ∑ t : Finset D.what₂.Tau,
      (∏ τ, if τ ∈ t then (1 : ℂ) else (s : ℂ)) • PiTensorProduct.tprod ℂ (t.piecewise a' b') := fun s => by
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← MultilinearMap.map_smul_univ]
    congr 1
    funext τ
    by_cases hτ : τ ∈ t <;> simp [Finset.piecewise, hτ]
  simp only [pairing, h, map_sum, map_smul, smul_eq_mul]
  refine IsPolyFn.sum _ fun t => IsPolyFn.mul (IsPolyFn.prod _ fun τ => ?_) (isPolyFn_ellT M a b _)
  by_cases hτ : τ ∈ t
  · simpa [hτ] using IsPolyFn.const 1
  · simpa [hτ] using IsPolyFn.coe

noncomputable def nrm (a : M.Vec) : M.Vec := fun τ => ((‖(a τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • a τ

theorem smul_nrm (a : M.Vec) : (fun τ => ((‖(a τ : M.H τ)‖ : ℝ) : ℂ) • nrm M a τ) = a := by
  funext τ
  by_cases h : a τ = 0
  · simp [nrm, h]
  · have : ‖(a τ : M.H τ)‖ ≠ 0 := by simpa using h
    rw [nrm, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one, one_smul]

theorem norm_nrm (a : M.Vec) (h : (∏ τ, ((‖(a τ : M.H τ)‖ : ℝ) : ℂ)) ≠ 0) (τ : D.what₂.Tau) : ‖(nrm M a τ : M.H τ)‖ = 1 := by
  have h1 : ‖(a τ : M.H τ)‖ ≠ 0 := Complex.ofReal_ne_zero.1 (Finset.prod_ne_zero_iff.1 h τ (Finset.mem_univ τ))
  rw [nrm, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ h1]

theorem pairing_nrm (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) :
    pairing M M' L w v = (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ((∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) *
      pairing M M' L (nrm M w) (nrm M' v)) := by
  have h1 : PiTensorProduct.tprod ℂ v = (∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) • PiTensorProduct.tprod ℂ (nrm M' v) := by
    rw [← MultilinearMap.map_smul_univ, smul_nrm]
  have h2 : ∀ x, ellT M (fun τ => (w τ : M.H τ)) x =
      (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ellT M (fun τ => (nrm M w τ : M.H τ)) x := fun x => by
    rw [← ellT_smul M (fun τ => ‖(w τ : M.H τ)‖)]
    exact congrArg (fun u : M.Vec => ellT M (fun τ => (u τ : M.H τ)) x) (smul_nrm M w).symm
  rw [pairing, pairing, h1, h2, map_smul, map_smul, map_smul, smul_eq_mul]

theorem unit_of_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (φ : P) (w : M.Vec) (v : M'.Vec)
    (h : pairing M M' (It φ) w v ≠ 0) :
    (∀ τ, ‖(nrm M w τ : M.H τ)‖ = 1) ∧ (∀ τ, ‖(nrm M' v τ : M'.H τ)‖ = 1) ∧
      ∃ φ', pairing M M' (It φ') (nrm M w) (nrm M' v) = 1 := by
  rw [pairing_nrm] at h
  obtain ⟨h1, h⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.1 h
  refine ⟨norm_nrm M w h1, norm_nrm M' v h2, (pairing M M' (It φ) (nrm M w) (nrm M' v))⁻¹ • φ, ?_⟩
  rw [← inv_mul_cancel₀ h3]
  simp only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem exists_pairing_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (h : It ≠ 0) :
    ∃ φ w v, pairing M M' (It φ) w v ≠ 0 := by
  have : ∃ φ v, It φ (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hn
    push Not at hn
    refine h (LinearMap.ext fun φ => ?_)
    exact PiTensorProduct.ext (MultilinearMap.ext fun v => hn φ v)
  obtain ⟨φ, v, hv⟩ := this
  obtain ⟨w, hw⟩ := GlobalTheory.T.smoothPureTensors_separate_tensorProduct D V S M _ hv
  exact ⟨φ, w, v, hw⟩

theorem exists_common (U : Type) [AddCommGroup U] [Module ℂ U] (ι : Type) [Finite ι] (f : ι → U → ℂ)
    (h : ∀ i a b, IsPolyFn fun s => f i (a + (s : ℂ) • b)) (h' : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 :=
  @GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines U _ (Module.complexToReal U) ι _ f h h'

theorem exists_unit_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hY hX
  classical
  have hm := D.R.two_le_m
  have e1 : ∀ k, ∃ φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      ∃ w v, pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ) w v ≠ 0 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨φ, h⟩ := exists_pairing_ne _ _ (R.ItY k) (hY k hk)
      exact ⟨φ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ hφ using e1
  obtain ⟨φX, wX, vX, hφX⟩ := exists_pairing_ne _ _ R.ItX hX
  let f : Option (Fin (D.R.m - 1)) → (∀ j, (R.MY j).Vec) × R.MX.Vec → ℂ := fun i u =>
    match i with
    | none => pairing (R.MY (D.R.m - 1)) R.MX (R.ItX φX) (u.1 (D.R.m - 1)) u.2
    | some k => pairing (R.MY k) (R.MY (k + 1)) (R.ItY k (φ k)) (u.1 k) (u.1 (k + 1))
  obtain ⟨u, hu⟩ := exists_common _ _ f (fun i a b => by
      cases i with
      | none => exact isPolyFn_pairing _ _ _ _ _ _ _
      | some k => exact isPolyFn_pairing _ _ _ _ _ _ _) (fun i => by
      cases i with
      | none =>
        refine ⟨(Function.update 0 (D.R.m - 1) wX, vX), ?_⟩
        simpa only [f, Function.update_self] using hφX
      | some k =>
        obtain ⟨w, v, h⟩ := hφ k (by omega)
        refine ⟨(Function.update (Function.update 0 (k : ℕ) w) (k + 1) v, 0), ?_⟩
        simpa only [f, Function.update_self, Function.update_of_ne (Nat.succ_ne_self (k : ℕ)).symm] using h)
  obtain ⟨x1, x2, φX', x3⟩ := unit_of_ne _ _ R.ItX φX _ _ (hu none)
  have e2 : ∀ k, ∃ φ' : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      (∀ τ, ‖(nrm (R.MY k) (u.1 k) τ : (R.MY k).H τ)‖ = 1) ∧
      pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ') (nrm _ (u.1 k)) (nrm _ (u.1 (k + 1))) = 1 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨y1, -, φ', y3⟩ := unit_of_ne _ _ (R.ItY k) (φ k) _ _ (hu (some ⟨k, by omega⟩))
      exact ⟨φ', fun _ => ⟨y1, y3⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ' hφ' using e2
  refine ⟨fun j => nrm _ (u.1 j), nrm _ u.2, φ', φX', fun j hj => ?_, x2, fun k hk => (hφ' k hk).2, x3⟩
  by_cases hk : j + 1 < D.R.m
  · exact (hφ' j hk).1
  · obtain rfl : j = D.R.m - 1 := by omega
    exact x1

end GlobalTheory.Mem.UnitPairing
