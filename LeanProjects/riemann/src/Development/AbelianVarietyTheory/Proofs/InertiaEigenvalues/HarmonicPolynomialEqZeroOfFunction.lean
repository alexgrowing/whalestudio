import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
import Formalism.LocalToGlobal.Columns.FockNormSubstitutionBound

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmInj

open GlobalTheory.JointHarm GlobalTheory.JointHarm.DeltaEig

def sgnOf {D : D7} (m : ℕ) (p : D.what₂.Tau → ℕ) : D.what₂.Tau → Fin m → Bool := fun τ a => decide ((a : ℕ) < p τ)

theorem fockSubst_eq_fsub {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (u : GLR D n) :
    (fockSubst p u : PolF D m n →ₐ[ℂ] PolF D m n) = fsub (sgnOf m p) 1 (fun τ => (u τ).val) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [fockSubst, fsub, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : v.2.1.val < p v.1
  · rw [if_pos h, Finset.sum_eq_single v.2.1]
    · simp [sgnOf, h, Matrix.coe_units_inv]
    · intro a _ ha
      simp [sgnOf, h, Matrix.one_apply_ne ha]
    · simp
  · rw [if_neg h, Finset.sum_eq_single v.2.1]
    · simp [sgnOf, h]
    · intro a _ ha
      simp [sgnOf, h, Matrix.one_apply_ne (Ne.symm ha)]
    · simp

theorem one_mem_KC {m : ℕ} (ε : Fin m → Bool) : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp⟩
  simp [Matrix.mem_unitaryGroup_iff]

theorem fockL_fockSubst_adj : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (u u' : GLR D n), (∀ τ, (u' τ).val = (u τ).valᴴ) → ∀ F G : PolF D m n, fockL (fockSubst p u F) G = fockL F (fockSubst p u' G) := by
  intro D m n p u u' h F G
  classical
  have e : FMul.fmat (sgnOf m p) (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (fun τ => (u' τ).val) =
      (FMul.fmat (sgnOf m p) (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (fun τ => (u τ).val))ᴴ := by
    rw [← FMul.fmat_conj (sgnOf m p) (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (fun τ => (u τ).val) (fun τ => one_mem_KC _)]
    congr 1
    · funext τ
      simp
    · funext τ
      exact h τ
  rw [fockSubst_eq_fsub, fockSubst_eq_fsub, fsub_eq_lsub, fsub_eq_lsub, e]
  exact FMul.fockL_lsub_adj _ _ _

theorem sub_minorPlus {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hsn : s ≤ n) (hp : p ≤ m) (hs : s ≤ p)
    (hε : ∀ a, ε τ a = decide ((a : ℕ) < p))
    (hk : ∀ a b, k τ a b ≠ 0 → ((b : ℕ) < p → a ≤ b) ∧ (p ≤ (b : ℕ) → b ≤ a))
    (hu : IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fsub ε k u (minorPlus τ s : PolF D m n) =
      (∏ a ∈ Finset.range s, (dg (k τ) a * (dg (u τ) a)⁻¹)) • (minorPlus τ s : PolF D m n) := by
  have hsm : s ≤ m := by omega
  have hv : ∀ α β : Fin s, (varF τ β α : PolF D m n) =
      MvPolynomial.X (τ, Fin.castLE hsm β, Fin.castLE hsn α) := fun α β => by
    rw [varF, dif_pos ⟨by omega, by omega⟩]; rfl
  have hui := inv_tri (u τ) hu.1 _ (lo_tri hu.2)
  have key := det_subst (R := PolF D m n) (fun a b => MvPolynomial.X (τ, a, b)) (k τ) (u τ)⁻¹
    (Fin.castLE hsm) (Fin.castLE hsn) (Fin.castLE_injective _) (Fin.castLE_injective _)
    (fun a β h => by
      have := (hk _ _ h).1 (by simp; omega)
      rw [Fin.le_def] at this
      exact ⟨⟨a, by simp at this; omega⟩, rfl⟩)
    (fun α b h => by
      have := hui _ _ h
      exact ⟨⟨b, by simp at this; omega⟩, rfl⟩)
  rw [Matrix.det_of_upperTriangular (M := (k τ).submatrix _ _) (fun i j hij => by
      by_contra h
      have := (hk _ _ h).1 (by simp; omega)
      exact absurd hij (by simpa using this)),
    Matrix.det_of_lowerTriangular (((u τ)⁻¹).submatrix _ _) (fun i j hij => by
      by_contra h
      have := hui _ _ h
      exact absurd hij (by simpa using this)), ← Finset.prod_mul_distrib] at key
  simp only [minorPlus, hv]
  rw [AlgHom.map_det, Finset.prod_range]
  convert key using 2
  · ext1 α β
    have : ε τ (Fin.castLE hsm β) = true := by rw [hε]; simp; omega
    simp [fsub, this]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [show dg (k τ) a = _ from dg_fin _ (Fin.castLE hsm a), show dg (u τ) a = _ from dg_fin _ (Fin.castLE hsn a),
      Matrix.submatrix_apply, Matrix.submatrix_apply, eq_inv_of_mul_eq_one_left (lo_diag hu _)]

theorem sub_minorMinus {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hsn : s ≤ n) (hs : p + s ≤ m)
    (hε : ∀ a, ε τ a = decide ((a : ℕ) < p)) (hk0 : IsUnit (k τ))
    (hk : ∀ a b, k τ a b ≠ 0 → ((b : ℕ) < p → a ≤ b) ∧ (p ≤ (b : ℕ) → b ≤ a))
    (hu : IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fsub ε k u (minorMinus τ p s : PolF D m n) =
      (∏ a ∈ Finset.range s, ((dg (k τ) (p + a))⁻¹ * dg (u τ) (n - 1 - a))) • (minorMinus τ p s : PolF D m n) := by
  let e : Fin s → Fin m := fun β => ⟨p + β, by omega⟩
  let f : Fin s → Fin n := fun α => ⟨n - s + α, by omega⟩
  have hv : ∀ α β : Fin s, (varF τ (p + β) (n - s + α) : PolF D m n) =
      MvPolynomial.X (τ, e β, f α) := fun α β => by
    rw [varF, dif_pos ⟨by omega, by omega⟩]
  let w : Fin m → ℤ := fun a => if (a : ℕ) < p then ((a : ℕ) : ℤ) else 2 * m - ((a : ℕ) : ℤ)
  have hw : Function.Injective w := fun a b h => by
    simp only [w] at h
    apply Fin.ext
    split_ifs at h <;> omega
  have hkw : ∀ a b, k τ a b ≠ 0 → w a ≤ w b := fun a b h => by
    have := hk a b h
    simp only [w, Fin.le_def] at this ⊢
    split_ifs <;> omega
  have hki : ∀ β a, (k τ)⁻¹ (e β) a ≠ 0 → p ≤ a ∧ (a : ℕ) ≤ p + β := fun β a h => by
    have := inv_tri (k τ) hk0 _ hkw _ _ h
    simp only [w, e] at this
    split_ifs at this <;> omega
  have key := det_subst (R := PolF D m n) (fun a b => MvPolynomial.X (τ, a, b)) ((k τ)⁻¹)ᵀ (u τ)ᵀ
    e f (fun a b h => Fin.ext (by simpa [e] using h)) (fun a b h => Fin.ext (by simpa [f] using h))
    (fun a β h => by
      have := hki _ _ h
      exact ⟨⟨a - p, by omega⟩, Fin.ext (by simp only [e]; omega)⟩)
    (fun α b h => by
      have := lo_tri hu.2 _ _ h
      simp only [f] at this
      exact ⟨⟨b - (n - s), by omega⟩, Fin.ext (by simp only [f]; omega)⟩)
  rw [Matrix.det_of_upperTriangular (M := ((k τ)⁻¹)ᵀ.submatrix _ _) (fun i j hij => by
      by_contra h
      have := (hki _ _ h).2
      exact absurd hij (by simpa [e] using this)),
    Matrix.det_of_upperTriangular (M := (u τ)ᵀ.submatrix _ _) (fun i j hij => by
      by_contra h
      have := lo_tri hu.2 _ _ h
      exact absurd hij (by simpa [f] using this))] at key
  simp only [minorMinus, hv]
  rw [AlgHom.map_det, Finset.prod_mul_distrib, ← Finset.prod_range_reflect (fun a => dg (u τ) (n - 1 - a)),
    Finset.prod_range, Finset.prod_range]
  convert key using 2
  · ext1 α β
    have : ε τ (e β) = false := by rw [hε]; simp [e]
    simp [fsub, this]
  · congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [show dg (k τ) (p + a) = _ from dg_fin _ (e a), Matrix.submatrix_apply, Matrix.transpose_apply,
        eq_inv_of_mul_eq_one_left (inv_diag _ hk0 w hw hkw _)]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [show n - 1 - (s - 1 - a) = n - s + a by omega]
      exact dg_fin _ (f a)

section Eig

variable {R : Type} [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] R) (h : Prop)

def Eig (x : R) : Prop := ∃ c : ℂ, φ x = c • x ∧ (h → c = 1)

variable {φ h}

theorem Eig.one : Eig φ h (1 : R) := ⟨1, by simp, fun _ => rfl⟩

theorem Eig.mul {x y : R} (hx : Eig φ h x) (hy : Eig φ h y) : Eig φ h (x * y) := by
  obtain ⟨c, h1, h2⟩ := hx
  obtain ⟨d, h3, h4⟩ := hy
  exact ⟨c * d, by rw [map_mul, h1, h3, smul_mul_smul_comm], fun hh => by rw [h2 hh, h4 hh, one_mul]⟩

theorem Eig.pow {x : R} (hx : Eig φ h x) (k : ℕ) : Eig φ h (x ^ k) := by
  induction k with
  | zero => simpa using Eig.one
  | succ k ih => rw [pow_succ]; exact ih.mul hx

theorem Eig.prod {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, Eig φ h (x i)) : Eig φ h (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Eig.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hx a (Finset.mem_insert_self _ _)).mul (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

end Eig

theorem fockSubst_delta_eig : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (l : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (∀ τ (a b : Fin n), a < b → (l τ).val a b = 0) → ∃ c : ℂ, fockSubst w.p l (w.delta m) = c • w.delta m ∧ ((∀ τ a, (l τ).val a a = 1) → c = 1) := by
  intro D m n w l hG hm hl
  rw [fockSubst_eq_fsub]
  have hu : ∀ τ, IsUnit (l τ).val ∧ GlobalTheory.Dec.IsLo (l τ).val := fun τ => ⟨(l τ).isUnit, fun i j hij => hl τ i j hij⟩
  have h1k : ∀ (τ : D.what₂.Tau) (pp : ℕ) (a b : Fin m), (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ a b ≠ 0 →
      ((b : ℕ) < pp → a ≤ b) ∧ (pp ≤ (b : ℕ) → b ≤ a) := fun τ pp a b h => by
    have : a = b := by
      by_contra hab
      exact h (by simp [Matrix.one_apply_ne hab])
    subst this
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have hdg1 : ∀ (a : ℕ), dg (1 : Matrix (Fin m) (Fin m) ℂ) a = 1 := fun a => by
    unfold dg
    split_ifs <;> simp
  have hdgl : (∀ τ a, (l τ).val a a = 1) → ∀ τ (a : ℕ), dg (l τ).val a = 1 := fun h τ a => by
    unfold dg
    split_ifs
    · exact h _ _
    · rfl
  refine Eig.prod (h := ∀ τ a, (l τ).val a a = 1) Finset.univ _ fun τ _ => ?_
  have hle := hG.le τ
  have hmτ := hm τ
  refine Eig.mul (Eig.prod _ _ fun i hi => Eig.pow ?_ _) (Eig.prod _ _ fun i hi => Eig.pow ?_ _)
  · have hi := Finset.mem_range.1 hi
    refine ⟨_, sub_minorPlus (sgnOf m w.p) 1 (fun τ => (l τ).val) τ (w.p τ) (i + 1) (by omega) (by omega) (by omega)
      (fun a => rfl) (h1k τ _) (hu τ), fun h => ?_⟩
    refine Finset.prod_eq_one fun a _ => ?_
    rw [Pi.one_apply, hdg1, hdgl h, inv_one, mul_one]
  · have hi := Finset.mem_range.1 hi
    refine ⟨_, sub_minorMinus (sgnOf m w.p) 1 (fun τ => (l τ).val) τ (w.p τ) (i + 1) (by omega) (by omega)
      (fun a => rfl) isUnit_one (h1k τ _) (hu τ), fun h => ?_⟩
    refine Finset.prod_eq_one fun a _ => ?_
    rw [Pi.one_apply, hdg1, hdgl h, inv_one, mul_one]

theorem up_inv {n : ℕ} (M : GL (Fin n) ℂ) (h0 : ∀ (a b : Fin n), b < a → M.val a b = 0) (h1 : ∀ a, M.val a a = 1) :
    (∀ (a b : Fin n), b < a → (M⁻¹).val a b = 0) ∧ ∀ a, (M⁻¹).val a a = 1 := by
  have hw : ∀ a b : Fin n, M.val a b ≠ 0 → ((a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) := fun a b h => by
    by_contra hc
    exact h (h0 a b (by rw [Fin.lt_def]; omega))
  rw [Matrix.coe_units_inv]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · by_contra hc
    have := inv_tri M.val M.isUnit (fun a => ((a : ℕ) : ℤ)) hw a b hc
    rw [Fin.lt_def] at hab
    omega
  · have := inv_diag M.val M.isUnit (fun a => ((a : ℕ) : ℤ)) (fun a b h => Fin.ext (by simpa using h)) hw a
    rwa [h1, mul_one] at this

theorem aeval_varF_plus {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) (i c : ℕ) (hi : i < p τ)
    (him : i < m) (hin : i < n) (hc : c < n) :
    MvPolynomial.aeval (fockPt p y) (varF τ i c : PolF D m n) = (y τ).val ⟨c, hc⟩ ⟨i, hin⟩ := by
  rw [varF, dif_pos ⟨him, hc⟩, MvPolynomial.aeval_X]
  simp [fockPt, hi, hin]

theorem aeval_varF_minus {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) (j c : ℕ)
    (him : p τ + j < m) (hjn : j < n) (hc : c < n) :
    MvPolynomial.aeval (fockPt p y) (varF τ (p τ + j) c : PolF D m n) =
      ((y τ)⁻¹).val (Fin.rev ⟨j, hjn⟩) ⟨c, hc⟩ := by
  rw [varF, dif_pos ⟨him, hc⟩, MvPolynomial.aeval_X]
  simp [fockPt, hjn]

theorem val_plus {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) (k : ℕ) (hk : k ≤ p τ) (hkm : k ≤ m)
    (hkn : k ≤ n) (h0 : ∀ (a b : Fin n), b < a → (y τ).val a b = 0) (h1 : ∀ a, (y τ).val a a = 1) :
    MvPolynomial.aeval (fockPt p y) (minorPlus τ k : PolF D m n) = 1 := by
  have e : (MvPolynomial.aeval (fockPt p y) : PolF D m n →ₐ[ℂ] ℂ).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ β α : PolF D m n)) =
      ((y τ).val).submatrix (Fin.castLE hkn) (Fin.castLE hkn) := by
    ext α β
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply]
    exact aeval_varF_plus p y τ β α (by omega) (by omega) (by omega) (by omega)
  rw [minorPlus, AlgHom.map_det, e, Matrix.det_of_upperTriangular (M := ((y τ).val).submatrix (Fin.castLE hkn) (Fin.castLE hkn))
    (fun i j hij => h0 _ _ (by simpa using hij))]
  exact Finset.prod_eq_one fun a _ => h1 _

def revSign (k : ℕ) : ℂ := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℂ)

theorem revSign_ne (k : ℕ) : revSign k ≠ 0 := by
  unfold revSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k))) with h | h <;> simp [h]

theorem val_minus {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) (k : ℕ) (hkm : p τ + k ≤ m)
    (hkn : k ≤ n) (h0 : ∀ (a b : Fin n), b < a → ((y τ)⁻¹).val a b = 0) (h1 : ∀ a, ((y τ)⁻¹).val a a = 1) :
    MvPolynomial.aeval (fockPt p y) (minorMinus τ (p τ) k : PolF D m n) = revSign k := by
  let f : Fin k → Fin n := fun α => ⟨n - k + α, by omega⟩
  let N : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun α β => ((y τ)⁻¹).val (f β) (f α)
  have e : (MvPolynomial.aeval (fockPt p y) : PolF D m n →ₐ[ℂ] ℂ).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (p τ + β) (n - k + α) : PolF D m n)) =
      N.submatrix id (Fin.revPerm : Equiv.Perm (Fin k)) := by
    ext α β
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply, N, id]
    rw [aeval_varF_minus p y τ β (n - k + α) (by omega) (by omega) (by omega)]
    rw [show (Fin.rev ⟨(β : ℕ), by omega⟩ : Fin n) = f (Fin.revPerm β) from Fin.ext (by
      simp only [f, Fin.revPerm_apply, Fin.val_rev]
      omega)]
  have hN : N.det = 1 := by
    rw [Matrix.det_of_lowerTriangular N (fun i j hij => h0 _ _ (by
      have : i < j := by simpa using hij
      simp only [f, Fin.lt_def] at this ⊢
      omega))]
    exact Finset.prod_eq_one fun a _ => h1 _
  rw [minorMinus, AlgHom.map_det, e, Matrix.det_permute', hN, mul_one]
  rfl

theorem val_delta {D : D7} {m n : ℕ} (w : Weight D n) (hG : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (y : GLR D n)
    (h0 : ∀ τ (a b : Fin n), b < a → (y τ).val a b = 0) (h1 : ∀ τ a, (y τ).val a a = 1)
    (h0' : ∀ τ (a b : Fin n), b < a → ((y τ)⁻¹).val a b = 0) (h1' : ∀ τ a, ((y τ)⁻¹).val a a = 1) :
    MvPolynomial.aeval (fockPt w.p y) (w.delta m) = ∏ τ, ∏ i ∈ Finset.range (w.q τ),
      revSign (i + 1) ^ (w.am τ i - if i + 1 < w.q τ then w.am τ (i + 1) else 0) := by
  rw [Weight.delta, delta, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hle := hG.le τ
  have hmτ := hm τ
  rw [deltaAt, map_mul, map_prod, map_prod, Finset.prod_eq_one, one_mul]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [map_pow, val_minus w.p y τ (i + 1) (by omega) (by omega) (h0' τ) (h1' τ)]
  · intro i hi
    have hi := Finset.mem_range.1 hi
    rw [map_pow, val_plus w.p y τ (i + 1) (by omega) (by omega) (by omega) (h0 τ) (h1 τ), one_pow]

theorem aeval_delta_unitri : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (u : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (∀ τ (a b : Fin n), b < a → (u τ).val a b = 0) → (∀ τ a, (u τ).val a a = 1) → MvPolynomial.aeval (fockPt w.p u⁻¹) (w.delta m) = MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) ∧ MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) ≠ 0 := by
  intro D m n w u hG hm hu hu1
  have hi := fun τ => up_inv (u τ) (hu τ) (hu1 τ)
  have h1 := val_delta (m := m) w hG hm (1 : GLR D n) (fun τ a b hab => by simp [Matrix.one_apply_ne (ne_of_gt hab)])
    (fun τ a => by simp) (fun τ a b hab => by simp [Matrix.one_apply_ne (ne_of_gt hab)]) (fun τ a => by simp)
  have h2 := val_delta (m := m) w hG hm u⁻¹ (fun τ => (hi τ).1) (fun τ => (hi τ).2)
    (fun τ a b hab => by simpa using hu τ a b hab) (fun τ a => by simpa using hu1 τ a)
  refine ⟨h2.trans h1.symm, ?_⟩
  rw [h1]
  exact Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (revSign_ne _)

theorem exists_ul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (hT : ∀ i : Fin n, (A.submatrix (Subtype.val : {j : Fin n // i < j} → Fin n) Subtype.val).det ≠ 0) :
    ∃ u l : GL (Fin n) ℂ, (∀ a b : Fin n, b < a → u.val a b = 0) ∧ (∀ a, u.val a a = 1) ∧
      (∀ a b : Fin n, a < b → l.val a b = 0) ∧ A = (u * l).val := by
  classical
  let T : ∀ i : Fin n, Matrix {j : Fin n // i < j} {j : Fin n // i < j} ℂ := fun i => A.submatrix Subtype.val Subtype.val
  let r : ∀ i : Fin n, {j : Fin n // i < j} → ℂ := fun i => -((fun c : {j : Fin n // i < j} => A i c.1) ᵥ* (T i)⁻¹)
  have hr : ∀ i, r i ᵥ* T i = -(fun c : {j : Fin n // i < j} => A i c.1) := fun i => by
    have hu : IsUnit (T i).det := isUnit_iff_ne_zero.2 (hT i)
    simp only [r]
    rw [Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  let v : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if h : i < j then r i ⟨j, h⟩ else if i = j then 1 else 0
  have h0 : ∀ a b : Fin n, b < a → v a b = 0 := fun a b hab => by
    simp [v, not_lt.2 hab.le, hab.ne']
  have h1 : ∀ a, v a a = 1 := fun a => by simp [v]
  have hdet : v.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (M := v) (fun i j hij => h0 _ _ (by simpa using hij))]
    simp [h1]
  have hL : ∀ i c : Fin n, i < c → (v * A) i c = 0 := fun i c hic => by
    have hv : ∀ j, v i j * A j c = (if h : i < j then r i ⟨j, h⟩ * A j c else 0) + (if i = j then A j c else 0) := fun j => by
      simp only [v, Matrix.of_apply]
      by_cases h : i < j
      · simp [h, h.ne]
      · by_cases h' : i = j <;> simp [h, h']
    have e := congrFun (hr i) ⟨c, hic⟩
    simp only [Matrix.vecMul, dotProduct, T, Matrix.submatrix_apply, Pi.neg_apply] at e
    have e2 : (∑ x, if h : i < x then r i ⟨x, h⟩ * A x c else 0) = ∑ j : {j : Fin n // i < j}, r i j * A j c := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun x => i < x) Finset.univ) (fun x _ hx => by
        rw [dif_neg (by simpa using hx)]), Finset.sum_subtype (p := fun x => i < x) _ (fun x => by simp)]
      exact Finset.sum_congr rfl fun j _ => dif_pos j.2
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => hv j, Finset.sum_add_distrib, Finset.sum_ite_eq, e2, e]
    simp
  let V : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero v hdet
  let G : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  have hi := up_inv V h0 h1
  refine ⟨V⁻¹, V * G, hi.1, hi.2, hL, ?_⟩
  rw [inv_mul_cancel_left]
  rfl

theorem continuousAt_lsub {σ : Type} [Fintype σ] (M : ℂ → Matrix σ σ ℂ) (hM : ∀ v w, ContinuousAt (fun t => M t v w) 0)
    (P : MvPolynomial σ ℂ) : ∀ ξ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, ContinuousAt (fun t => ξ (FMul.lsub (M t) P)) 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro ξ
    simp only [AlgHom.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C]
    exact continuousAt_const
  | add p q hp hq =>
    intro ξ
    simp only [map_add]
    exact (hp ξ).add (hq ξ)
  | mul_X p v hp =>
    intro ξ
    have e : ∀ t, ξ (FMul.lsub (M t) (p * MvPolynomial.X v)) =
        ∑ w, M t w v * (ξ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X w)) (FMul.lsub (M t) p) := fun t => by
      rw [map_mul, FMul.lsub_X, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      rfl
    simp only [e]
    exact tendsto_finset_sum _ fun w _ => (hM w v).mul (hp _)

theorem ev_det {ι : Type} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι ℂ) (hY : Y.det ≠ 0) :
    ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ((1 - t) • X + t • Y).det ≠ 0 := by
  let Q : Polynomial ℂ := ((1 - Polynomial.X : Polynomial ℂ) • X.map Polynomial.C +
    (Polynomial.X : Polynomial ℂ) • Y.map Polynomial.C).det
  have hQ : ∀ t, Q.eval t = ((1 - t) • X + t • Y).det := fun t => by
    have := RingHom.map_det (Polynomial.evalRingHom t) ((1 - Polynomial.X : Polynomial ℂ) • X.map Polynomial.C +
      (Polynomial.X : Polynomial ℂ) • Y.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at this
    refine this.trans (congrArg _ ?_)
    ext a b
    simp
    ring
  have hQ0 : Q ≠ 0 := fun h => hY (by
    have := hQ 1
    rw [h] at this
    simpa using this.symm)
  have hfin : ({t | Q.IsRoot t} \ {0}).Finite := (Polynomial.finite_setOf_isRoot hQ0).subset Set.diff_subset
  filter_upwards [nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin] with t h1 h2
  rw [← hQ]
  intro h3
  exact h1 ⟨h3, h2⟩

theorem eq_zero_of_triangular : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (ξ : PolF D m n →ₗ[ℂ] ℂ) (P : PolF D m n), (∀ u l : GLR D n, (∀ τ (a b : Fin n), b < a → (u τ).val a b = 0) → (∀ τ a, (u τ).val a a = 1) → (∀ τ (a b : Fin n), a < b → (l τ).val a b = 0) → ξ (fockSubst p (u * l) P) = 0) → ∀ g : GLR D n, ξ (fockSubst p g P) = 0 := by
  intro D m n p ξ P H g
  classical
  let A : D.what₂.Tau → ℂ → Matrix (Fin n) (Fin n) ℂ := fun τ t => (1 - t) • (g τ).val + t • 1
  have hgood : ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∀ τ, (A τ t).det ≠ 0 ∧
      ∀ i : Fin n, ((A τ t).submatrix (Subtype.val : {j : Fin n // i < j} → Fin n) Subtype.val).det ≠ 0 := by
    rw [Filter.eventually_all]
    intro τ
    refine (ev_det _ 1 (by simp)).and ?_
    rw [Filter.eventually_all]
    intro i
    have e : ∀ t, (A τ t).submatrix (Subtype.val : {j : Fin n // i < j} → Fin n) Subtype.val =
        (1 - t) • ((g τ).val).submatrix Subtype.val Subtype.val + t • (1 : Matrix {j : Fin n // i < j} {j : Fin n // i < j} ℂ) := fun t => by
      ext a b
      simp [A, Matrix.one_apply, Subtype.ext_iff]
    simp only [e]
    exact ev_det _ 1 (by simp)
  have hAc : ∀ τ, Continuous fun t => A τ t := fun τ =>
    ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hA0 : ∀ τ, A τ 0 = (g τ).val := fun τ => by simp [A]
  have hInv : ∀ τ a b, ContinuousAt (fun t => (A τ t)⁻¹ a b) 0 := fun τ a b => by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    refine ContinuousAt.mul (ContinuousAt.inv₀ (hAc τ).matrix_det.continuousAt ?_)
      ((hAc τ).matrix_adjugate.matrix_elem a b).continuousAt
    rw [hA0]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit).ne_zero
  let f : ℂ → ℂ := fun t => ξ (FMul.lsub (FMul.fmat (sgnOf m p) 1 fun τ => A τ t) P)
  have hcont : ContinuousAt f 0 := by
    refine continuousAt_lsub _ (fun w v => ?_) P ξ
    simp only [FMul.fmat, Matrix.of_apply]
    split_ifs
    · exact continuousAt_const.mul (hInv _ _ _)
    · exact continuousAt_const.mul ((hAc _).matrix_elem _ _).continuousAt
    · exact continuousAt_const
  have hf0 : f 0 = ξ (fockSubst p g P) := by
    simp only [f, hA0]
    rw [fockSubst_eq_fsub, fsub_eq_lsub]
  have hz : ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, f t = 0 := by
    filter_upwards [hgood] with t ht
    choose u l hu hu1 hl hA using fun τ => exists_ul (A τ t) (ht τ).1 (ht τ).2
    have := H u l hu hu1 hl
    rw [fockSubst_eq_fsub, fsub_eq_lsub] at this
    have e : (fun τ => ((u * l) τ).val) = fun τ => A τ t := funext fun τ => (hA τ).symm
    rw [e] at this
    exact this
  have h1 : Filter.Tendsto f (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (f 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto f (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm)
  rw [← hf0]
  exact tendsto_nhds_unique h1 h2

theorem fock_pos {σ : Type} (f : MvPolynomial σ ℂ) (h : fockL f f = 0) : f = 0 := by
  by_contra hf
  have h1 := Formalism.L2.Col.fockN_pos f hf
  rw [Formalism.L2.Col.fockL_self] at h
  exact absurd (Complex.ofReal_eq_zero.1 h) h1.ne'

theorem star_val {D : D7} {n : ℕ} (g : GLR D n) (τ) : ((star g) τ).val = (g τ).valᴴ := rfl

theorem val_star {D : D7} {n : ℕ} (g : GLR D n) (τ) : (g τ).val = ((star g) τ).valᴴ := by
  rw [star_val, Matrix.conjTranspose_conjTranspose]

theorem compare (D : D7) (m n : ℕ) (w : Weight D n) (hG : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (g : GLR D n) :
    MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) * fockL (w.delta m) (fockSubst w.p g (w.delta m)) -
      fockL (w.delta m) (w.delta m) * MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (fockSubst w.p g (w.delta m)) = 0 := by
  refine eq_zero_of_triangular D m n w.p ((MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) : ℂ) • (fockL (w.delta m)) -
    (fockL (w.delta m) (w.delta m)) • (MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) : PolF D m n →ₐ[ℂ] ℂ).toLinearMap) (w.delta m)
    (fun u l hu hu1 hl => ?_) g
  obtain ⟨c, hc, -⟩ := fockSubst_delta_eig D m n w l hG hm hl
  have e1 : fockSubst w.p (u * l) (w.delta m) = c • fockSubst w.p u (w.delta m) := by
    rw [fockSubst_mul, AlgHom.comp_apply, hc, map_smul]
  have hsl : ∀ τ (a b : Fin n), a < b → ((star u) τ).val a b = 0 := fun τ a b hab => by
    rw [star_val, Matrix.conjTranspose_apply, hu τ b a hab, star_zero]
  have hs1 : ∀ τ a, ((star u) τ).val a a = 1 := fun τ a => by
    rw [star_val, Matrix.conjTranspose_apply, hu1, star_one]
  obtain ⟨c', hc', hc1⟩ := fockSubst_delta_eig D m n w (star u) hG hm hsl
  have e2 : fockL (w.delta m) (fockSubst w.p u (w.delta m)) = fockL (w.delta m) (w.delta m) := by
    rw [← fockL_fockSubst_adj D m n w.p (star u) u (val_star u), hc', hc1 hs1, one_smul]
  have e3 : MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (fockSubst w.p u (w.delta m)) =
      MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) := by
    rw [aeval_fockPt_fockSubst, mul_one]
    exact (aeval_delta_unitri D m n w u hG hm hu hu1).1
  rw [e1, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, e2, e3]
  simp only [smul_eq_mul]
  rw [mul_comm (MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) : ℂ), sub_self, mul_zero]

theorem orth_end {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] [Star G]
    (L : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (ev : V →ₗ[ℂ] ℂ) (T : G →* Module.End ℂ V) (Δ P : V) (e A : ℂ) (he : e ≠ 0)
    (hpos : ∀ f, L f f = 0 → f = 0) (hadj : ∀ g F F', L (T g F) F' = L F (T (star g) F'))
    (hcmp : ∀ g, e * L Δ (T g Δ) - A * ev (T g Δ) = 0)
    (hP : P ∈ Submodule.span ℂ (Set.range fun g => T g Δ)) (hv : ∀ g, ev (T g P) = 0) : P = 0 := by
  have hcmpH : ∀ Q ∈ Submodule.span ℂ (Set.range fun g => T g Δ), e * L Δ Q - A * ev Q = 0 := fun Q hQ => by
    induction hQ using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact hcmp g
    | zero => simp
    | add x y _ _ h1 h2 =>
      rw [map_add, map_add, mul_add, mul_add, add_sub_add_comm, h1, h2, add_zero]
    | smul c x _ h1 =>
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm, mul_left_comm A, ← mul_sub, h1, mul_zero]
  have hstab : ∀ g, ∀ Q ∈ Submodule.span ℂ (Set.range fun g => T g Δ),
      T g Q ∈ Submodule.span ℂ (Set.range fun g => T g Δ) := fun g Q hQ => by
    induction hQ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨g', rfl⟩ := h
      exact Submodule.subset_span ⟨g * g', by simp [map_mul]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul c x _ h1 => rw [map_smul]; exact Submodule.smul_mem _ _ h1
  have hz : ∀ g, L Δ (T g P) = 0 := fun g => by
    have h1 := hcmpH _ (hstab g P hP)
    rw [hv g, mul_zero, sub_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left he
  have hall : ∀ Q ∈ Submodule.span ℂ (Set.range fun g => T g Δ), L Q P = 0 := fun Q hQ => by
    induction hQ using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; beta_reduce; rw [hadj]; exact hz _
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul c x _ h1 => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  exact hpos _ (hall P hP)

noncomputable def substRep (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) : GLR D n →* Module.End ℂ (PolF D m n) where
  toFun g := (fockSubst p g).toLinearMap
  map_one' := by rw [fockSubst_one]; rfl
  map_mul' g g' := by rw [fockSubst_mul]; rfl

theorem harm_inj : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) →
    ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  intro D m n w B hG hm P hP h0
  have hv : ∀ y : GLR D n, MvPolynomial.aeval (fockPt w.p y) P = 0 := fun y => by
    have h1 := congrFun h0 (B * y)
    rw [harmFn_apply, inv_mul_cancel_left] at h1
    exact (mul_eq_zero.1 h1).resolve_left (Units.ne_zero _)
  have he : MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (w.delta m) ≠ 0 :=
    (aeval_delta_unitri D m n w 1 hG hm (fun τ a b hab => by simp [Matrix.one_apply_ne (ne_of_gt hab)]) (fun τ a => by simp)).2
  refine orth_end fockL (MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) : PolF D m n →ₐ[ℂ] ℂ).toLinearMap (substRep D m n w.p)
    (w.delta m) P _ (fockL (w.delta m) (w.delta m)) he fock_pos (fun g F F' => fockL_fockSubst_adj D m n w.p g (star g) (star_val g) F F')
    (fun g => compare D m n w hG hm g) ?_ (fun g => ?_)
  · refine (Submodule.span_le.2 ?_ : harm m w B ≤ _) hP
    rintro _ ⟨u, rfl⟩
    beta_reduce
    rw [fockGL_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · change MvPolynomial.aeval (fockPt w.p (1 : GLR D n)) (fockSubst w.p g P) = 0
    rw [aeval_fockPt_fockSubst]
    exact hv _

end GlobalTheory.ExportSeries.HarmInj
