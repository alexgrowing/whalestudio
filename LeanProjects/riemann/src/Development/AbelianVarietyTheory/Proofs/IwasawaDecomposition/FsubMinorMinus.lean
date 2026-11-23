import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.DeltaEig

theorem det_subst {R : Type} [CommRing R] [Algebra ℂ R] {m n s : ℕ} (F : Fin m → Fin n → R)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (e : Fin s → Fin m) (f : Fin s → Fin n)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hA : ∀ a β, A a (e β) ≠ 0 → ∃ γ, e γ = a) (hB : ∀ α b, B (f α) b ≠ 0 → ∃ γ, f γ = b) :
    (Matrix.of fun α β : Fin s => ∑ a, ∑ b, algebraMap ℂ R (A a (e β) * B (f α) b) * F a b).det =
      ((A.submatrix e e).det * (B.submatrix f f).det) • (Matrix.of fun α β : Fin s => F (e β) (f α)).det := by
  have key : (Matrix.of fun α β : Fin s => ∑ a, ∑ b, algebraMap ℂ R (A a (e β) * B (f α) b) * F a b) =
      (algebraMap ℂ R).mapMatrix (B.submatrix f f) * (Matrix.of fun α β : Fin s => F (e β) (f α)) *
        (algebraMap ℂ R).mapMatrix (A.submatrix e e) := by
    ext α β
    simp only [Matrix.mul_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.submatrix_apply, Finset.sum_mul]
    symm
    refine Fintype.sum_of_injective e he _ _ (fun a ha => ?_) (fun γ => ?_)
    · have : A a (e β) = 0 := by
        by_contra h
        exact ha (hA a β h)
      simp [this]
    · refine Fintype.sum_of_injective f hf _ _ (fun b hb => ?_) (fun δ => ?_)
      · have : B (f α) b = 0 := by
          by_contra h
          exact hb (hB α b h)
        simp [this]
      · rw [map_mul]; ring
  rw [key, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det, Algebra.smul_def, map_mul]
  ring

theorem inv_tri {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : IsUnit M) (w : Fin m → ℤ)
    (h : ∀ a b, M a b ≠ 0 → w a ≤ w b) (a b : Fin m) (hab : M⁻¹ a b ≠ 0) : w a ≤ w b := by
  obtain ⟨_⟩ := hM.nonempty_invertible
  have h1 : M.BlockTriangular w := fun i j hij => by
    by_contra h0
    exact absurd (h i j h0) (not_le.2 hij)
  have h2 := Matrix.blockTriangular_inv_of_blockTriangular h1
  by_contra h3
  exact hab (h2 (not_le.1 h3))

theorem inv_diag {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : IsUnit M) (w : Fin m → ℤ)
    (hw : Function.Injective w) (h : ∀ a b, M a b ≠ 0 → w a ≤ w b) (a : Fin m) : M⁻¹ a a * M a a = 1 := by
  have h1 : (M⁻¹ * M) a a = 1 := by
    rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM)]; simp
  rw [← h1, Matrix.mul_apply]
  symm
  refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
  by_contra h0
  exact hb (hw (le_antisymm (h _ _ (right_ne_zero_of_mul h0)) (inv_tri M hM w h _ _ (left_ne_zero_of_mul h0))))

theorem telescope (x : ℕ → ℂ) (p : ℕ) (ap : ℕ → ℕ) (h : ∀ a b, a ≤ b → b < p → ap b ≤ ap a) :
    ∏ i ∈ Finset.range p, (∏ a ∈ Finset.range (i + 1), x a) ^ (ap i - if i + 1 < p then ap (i + 1) else 0) =
      ∏ a ∈ Finset.range p, x a ^ ap a := by
  have key : ∀ r, r ≤ p → (∏ i ∈ Finset.range r, (∏ a ∈ Finset.range (i + 1), x a) ^
      (ap i - if i + 1 < p then ap (i + 1) else 0)) * (∏ a ∈ Finset.range r, x a) ^ (if r < p then ap r else 0) =
      ∏ a ∈ Finset.range r, x a ^ ap a := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro hr
      have hle : (if r + 1 < p then ap (r + 1) else 0) ≤ ap r := by
        split_ifs with h1
        · exact h _ _ (Nat.le_succ r) h1
        · exact Nat.zero_le _
      rw [Finset.prod_range_succ, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, Finset.prod_range_succ x,
        Finset.prod_range_succ (fun a => x a ^ ap a), ← ih (by omega), if_pos (show r < p by omega), mul_pow,
        mul_assoc]
  simpa using key p le_rfl

theorem regroup (K U : ℕ → ℂ) (hU : ∀ j, U j ≠ 0) (p q n : ℕ) (hn : p + q ≤ n) (ap am : ℕ → ℕ) :
    (∏ a ∈ Finset.range p, (K a * (U a)⁻¹) ^ ap a) *
      ∏ a ∈ Finset.range q, ((K (p + a))⁻¹ * U (n - 1 - a)) ^ am a =
    (∏ a ∈ Finset.range (p + q), K a ^ (if a < p then (ap a : ℤ) else -(am (a - p) : ℤ))) *
      ∏ j ∈ Finset.range n, U j ^ (-(if j < p then (ap j : ℤ) else 0) +
        (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + 0) := by
  have e1 : ∏ a ∈ Finset.range (p + q), K a ^ (if a < p then (ap a : ℤ) else -(am (a - p) : ℤ)) =
      (∏ a ∈ Finset.range p, K a ^ ap a) * ∏ a ∈ Finset.range q, (K (p + a))⁻¹ ^ am a := by
    rw [Finset.prod_range_add]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_range.1 ha), zpow_natCast]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [if_neg (by omega), Nat.add_sub_cancel_left, _root_.zpow_neg, zpow_natCast, inv_pow]
  have e2 : ∏ j ∈ Finset.range n, U j ^ (-(if j < p then (ap j : ℤ) else 0)) =
      ∏ a ∈ Finset.range p, (U a)⁻¹ ^ ap a := by
    symm
    rw [← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ n by omega))]
    · refine Finset.prod_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_range.1 ha), _root_.zpow_neg, zpow_natCast, inv_pow]
    · intro a _ ha
      rw [if_neg (by simpa using ha)]; simp
  have e3 : ∏ j ∈ Finset.range n, U j ^ (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) =
      ∏ a ∈ Finset.range q, U (n - 1 - a) ^ am a := by
    symm
    rw [← Finset.prod_range_reflect _ n, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ n by omega))]
    · refine Finset.prod_congr rfl fun a ha => ?_
      have ha := Finset.mem_range.1 ha
      rw [show n - 1 - (n - 1 - a) = a by omega, if_pos ha, zpow_natCast]
    · intro a ha' ha
      have ha' := Finset.mem_range.1 ha'
      rw [show n - 1 - (n - 1 - a) = a by omega, if_neg (by simpa using ha)]; simp
  simp only [add_zero, zpow_add₀ (hU _), Finset.prod_mul_distrib, mul_pow, e1, e2, e3]
  ring

noncomputable def dg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (a : ℕ) : ℂ :=
  if h : a < m then M ⟨a, h⟩ ⟨a, h⟩ else 1

theorem dg_fin {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) : dg M a = M a a := by
  simp [dg]

theorem lo_tri {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : GlobalTheory.Dec.IsLo u) (a b : Fin n) (h : u a b ≠ 0) :
    -((a : ℕ) : ℤ) ≤ -((b : ℕ) : ℤ) := by
  by_contra h0
  exact h (hu a b (by rw [Fin.lt_def]; omega))

theorem lo_diag {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u ∧ GlobalTheory.Dec.IsLo u) (a : Fin n) :
    u⁻¹ a a * u a a = 1 :=
  inv_diag u hu.1 (fun a => -((a : ℕ) : ℤ)) (fun a b h => Fin.ext (by simpa using h)) (lo_tri hu.2) a

variable {D : D7} {m n : ℕ}

theorem fsub_minorPlus (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hmn : m ≤ n) (hp : p ≤ m) (hs : s ≤ p)
    (hε : ∀ a, ε τ a = decide ((a : ℕ) < p))
    (hk : ∀ a b, k τ a b ≠ 0 → ((b : ℕ) < p → a ≤ b) ∧ (p ≤ (b : ℕ) → b ≤ a))
    (hu : IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fsub ε k u (minorPlus τ s : PolF D m n) =
      (∏ a ∈ Finset.range s, (dg (k τ) a * (dg (u τ) a)⁻¹)) • (minorPlus τ s : PolF D m n) := by
  have hsm : s ≤ m := by omega
  have hsn : s ≤ n := by omega
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

theorem fsub_minorMinus (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (p s : ℕ) (hmn : m ≤ n) (hs : p + s ≤ m)
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

theorem map_prod_pow {R : Type} [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] R) (S : Finset ℕ) (x : ℕ → R) (c : ℕ → ℂ)
    (d : ℕ → ℕ) (h : ∀ i ∈ S, φ (x i) = c i • x i) :
    φ (∏ i ∈ S, x i ^ d i) = (∏ i ∈ S, c i ^ d i) • ∏ i ∈ S, x i ^ d i := by
  rw [map_prod, ← Finset.prod_smul]
  exact Finset.prod_congr rfl fun i hi => by rw [map_pow, h i hi, smul_pow]

theorem fsub_delta : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ a b, k τ a b ≠ 0 → ((b : ℕ) < p τ → a ≤ b) ∧ (p τ ≤ (b : ℕ) → b ≤ a)) → (∀ τ, IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) → fsub ε k u (delta p q ap am : PolF D m n) = (∏ τ, (∏ a : Fin m, k τ a a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) else -(am τ (a - p τ) : ℤ))) * ∏ j : Fin n, u τ j j ^ wtU (p τ) (q τ) (ap τ) (am τ) 0 j) • (delta p q ap am : PolF D m n) := by
  intro D m n ε p q ap am hmn hpq hε hap ham k u hk0 hk hu
  rw [delta, map_prod, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm := hpq τ
  rw [deltaAt, map_mul,
    map_prod_pow _ _ (fun i => minorPlus τ (i + 1)) _ _ (fun i hi =>
      fsub_minorPlus ε k u τ (p τ) (i + 1) hmn (by omega) (Finset.mem_range.1 hi) (hε τ) (hk τ) (hu τ)),
    map_prod_pow _ _ (fun i => minorMinus τ (p τ) (i + 1)) _ _ (fun i hi =>
      fsub_minorMinus ε k u τ (p τ) (i + 1) hmn (by have := Finset.mem_range.1 hi; omega) (hε τ) (hk0 τ).1
        (hk τ) (hu τ)),
    smul_mul_smul_comm, telescope _ _ _ (hap τ), telescope _ _ _ (ham τ),
    regroup (dg (k τ)) (dg (u τ)) (fun j => by
      unfold dg
      split_ifs
      · exact right_ne_zero_of_mul_eq_one (lo_diag (hu τ) _)
      · exact one_ne_zero) _ _ n (by omega), hm, Finset.prod_range, Finset.prod_range]
  simp only [dg_fin, wtU]

end GlobalTheory.JointHarm.DeltaEig
