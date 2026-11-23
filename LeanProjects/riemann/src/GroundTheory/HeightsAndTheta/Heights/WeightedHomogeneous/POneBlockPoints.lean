import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem exists_int_smul_mem_latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG)
    (v : Fin m → K) : ∃ D : ℤ, D ≠ 0 ∧ D • v ∈ latticeDual L := by
  classical
  obtain ⟨S, hS⟩ := hL
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : K) := fun k ↦ by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K k))
  have h1 : ∀ s : Fin m → K, ∃ D : ℤ, D ≠ 0 ∧ IsIntegral ℤ ((D : K) * (v ⬝ᵥ s)) := by
    intro s
    have halg : IsAlgebraic ℤ (v ⬝ᵥ s) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨D, hD, hD'⟩ := halg.exists_integral_multiple
    exact ⟨D, hD, by rwa [zsmul_eq_mul] at hD'⟩
  choose D hD0 hDint using h1
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hD0 s, ?_⟩
  intro u hu
  rw [← hS] at hu
  rw [Set.mem_range, ← IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)]
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rw [smul_dotProduct, zsmul_eq_mul, ← Finset.mul_prod_erase S D hx, Int.cast_mul,
      mul_comm (D x : K), mul_assoc]
    exact (hint _).mul (hDint x)
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add x y _ _ hx hy => rw [dotProduct_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [dotProduct_smul, Algebra.smul_def]
    exact ((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨c, rfl⟩).mul hx

variable {r N : ℕ}

theorem exists_int_comb {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (v : Fin (r + 1) → K) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = D • v := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg v
  have h : D • v ∈ Submodule.span ℤ (Set.range φ) := by rw [hφ.span_eq]; exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  exact ⟨D, hD, c, hc⟩

omit [NumberField K] in
theorem sum_single_mul {m : ℕ} (σ : K →+* ℂ) (w : Fin m → ℂ) (j : Fin m) (a : K) :
    ∑ j', σ ((Pi.single j a : Fin m → K) j') * w j' = σ a * w j := by
  rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp

theorem sum_latticePoint {φ : Fin (N + 1) → Fin (r + 1) → K} (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ)
    {D : ℤ} {c : Fin (N + 1) → ℤ} {v : Fin (r + 1) → K} (hc : ∑ b, c b • φ b = D • v) :
    ∑ b, (c b : ℂ) * latticePoint φ σ w () b = D * ∑ j, σ (v j) * w j := by
  have h : ∀ j, ∑ b, (c b : K) * φ b j = D * v j := fun j ↦ by
    simpa [Finset.sum_apply, zsmul_eq_mul] using congrFun hc j
  simp only [latticePoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h' := congrArg σ (h j)
  simp only [map_sum, map_mul, map_intCast] at h'
  rw [← mul_assoc, ← h', Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

theorem latticePoint_ne_zero {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w () ≠ 0 := by
  intro h0
  apply hw
  funext j
  obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ (Pi.single j 1)
  have h := sum_latticePoint σ w hc
  rw [h0, sum_single_mul] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, map_one, one_mul] at h
  change w j = 0
  exact (mul_eq_zero.mp h.symm).resolve_left (Int.cast_ne_zero.mpr hD)

theorem latticePoint_mem {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w ∈ conePoints (latticeIdeal φ) ℂ := by
  refine ⟨fun _ ↦ latticePoint_ne_zero hφ σ hw, fun f hf ↦ ?_⟩
  have hf' : latticeMap φ f = 0 := hf
  have key : (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (fun _ : Unit ↦ N) ↦ latticePoint φ σ w v.1 v.2) =
      (eval w).comp ((map σ).comp (latticeMap φ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro v; simp [latticeMap, latticeForm, latticePoint]
  have h := congrArg (fun g ↦ g f) key
  simp only [RingHom.comp_apply, hf', map_zero] at h
  exact h

theorem embedding_unique {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) {σ σ' : K →+* ℂ} {w w' : Fin (r + 1) → ℂ} (hw : w ≠ 0)
    (h : latticePoint φ σ w = latticePoint φ σ' w') : σ = σ' := by
  have key : ∀ j a, σ a * w j = σ' a * w' j := by
    intro j a
    obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ (Pi.single j a)
    have h1 := sum_latticePoint σ w hc
    have h2 := sum_latticePoint σ' w' hc
    rw [h, h2, sum_single_mul, sum_single_mul] at h1
    exact (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD) h1).symm
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw (funext hc)
  have hw' : w j = w' j := by simpa using key j 1
  ext a
  have h3 := key j a
  rw [← hw'] at h3
  exact mul_right_cancel₀ hj h3

omit [NumberField K] in

theorem exists_embedding_of_mul {m : ℕ} (L : (Fin m → K) → ℂ)
    (hadd : ∀ u v, L (u + v) = L u + L v)
    (hmul : ∀ (j j' : Fin m) (a b a' b' : K), a * b = a' * b' →
      L (Pi.single j a) * L (Pi.single j' b) = L (Pi.single j a') * L (Pi.single j' b'))
    (hne : ∃ v, L v ≠ 0) :
    ∃ (σ : K →+* ℂ) (w : Fin m → ℂ), w ≠ 0 ∧ ∀ v, L v = ∑ j, σ (v j) * w j := by
  let Lh : (Fin m → K) →+ ℂ := AddMonoidHom.mk' L hadd
  have h0 : L 0 = 0 := Lh.map_zero
  have hsum : ∀ v, L v = ∑ j, L (Pi.single j (v j)) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    exact map_sum Lh (fun j ↦ Pi.single j (v j)) Finset.univ
  have hj : ∃ j, L (Pi.single j 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨v, hv⟩ := hne
    apply hv
    rw [hsum v]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have h := hmul j j (v j) (v j) (v j * v j) 1 (by ring)
    rw [hc j, mul_zero] at h
    exact mul_self_eq_zero.mp h
  obtain ⟨j₁, hc⟩ := hj
  let σ : K →+* ℂ :=
    { toFun := fun a ↦ L (Pi.single j₁ a) / L (Pi.single j₁ 1)
      map_one' := div_self hc
      map_mul' := fun a b ↦ by
        have h := hmul j₁ j₁ (a * b) 1 a b (by ring)
        field_simp
        linear_combination h
      map_zero' := by simp [h0]
      map_add' := fun a b ↦ by simp only [Pi.single_add, hadd, add_div] }
  refine ⟨σ, fun j ↦ L (Pi.single j 1), fun h ↦ hc (congrFun h j₁), fun v ↦ ?_⟩
  rw [hsum v]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := hmul j j₁ (v j) 1 1 (v j) (by ring)
  change L (Pi.single j (v j)) = L (Pi.single j₁ (v j)) / L (Pi.single j₁ 1) * L (Pi.single j 1)
  field_simp
  linear_combination h

omit [NumberField K] in
theorem latticeForm_add {m : ℕ} (u v : Fin m → K) :
    latticeForm (u + v) = latticeForm u + latticeForm v := by
  simp [latticeForm, add_mul, Finset.sum_add_distrib]

omit [NumberField K] in
theorem latticeForm_single {m : ℕ} (j : Fin m) (a : K) :
    latticeForm (Pi.single j a : Fin m → K) = C a * X j := by
  rw [latticeForm, Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp

omit [NumberField K] in
theorem latticeMap_intComb (φ : Fin (N + 1) → Fin (r + 1) → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, (c b : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩) =
      latticeForm (∑ b, c b • φ b) := by
  let Lf : (Fin (r + 1) → K) →+ MvPolynomial (Fin (r + 1)) K := AddMonoidHom.mk' latticeForm latticeForm_add
  have h : latticeForm (∑ b, c b • φ b) = ∑ b, c b • latticeForm (φ b) := by
    change Lf _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ ↦ map_zsmul Lf (c b) (φ b)
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, map_intCast, zsmul_eq_mul]
  simp [latticeMap]

theorem exists_latticePoint_eq {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) {z : Cone (fun _ : Unit ↦ N) ℂ}
    (hz : z ∈ conePoints (latticeIdeal φ) ℂ) :
    ∃ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 ∧ z = latticePoint φ σ w := by
  choose D hD c hc using exists_int_comb hφ
  let ev : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* ℂ :=
    eval₂Hom (Int.castRingHom ℂ) fun v ↦ z v.1 v.2
  have key : ∀ f, latticeMap φ f = 0 → ev f = 0 := fun f hf ↦ hz.2 f hf
  let P : (Fin (r + 1) → K) → MvPolynomial (Coord fun _ : Unit ↦ N) ℤ :=
    fun v ↦ ∑ b, (c v b : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩
  have hP : ∀ v, latticeMap φ (P v) = (D v : MvPolynomial (Fin (r + 1)) K) * latticeForm v := by
    intro v
    have h := congrArg latticeForm (hc v)
    simp only [P, latticeMap_intComb, h]
    let Lf : (Fin (r + 1) → K) →+ MvPolynomial (Fin (r + 1)) K :=
      AddMonoidHom.mk' latticeForm latticeForm_add
    rw [← zsmul_eq_mul]
    exact map_zsmul Lf (D v) v
  have hDc : ∀ v, (D v : ℂ) ≠ 0 := fun v ↦ Int.cast_ne_zero.mpr (hD v)
  let L : (Fin (r + 1) → K) → ℂ := fun v ↦ ev (P v) / D v
  have hE : ∀ v, ev (P v) = D v * L v := fun v ↦ by
    simp only [L]
    field_simp [hDc v]
  have hadd : ∀ u v, L (u + v) = L u + L v := by
    intro u v
    have h := key ((D u * D v : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P (u + v) -
      (D (u + v) * D v : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P u -
      (D (u + v) * D u : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P v) (by
        simp only [map_sub, map_mul, map_intCast, hP, latticeForm_add]
        ring)
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : ((D u * D v * D (u + v) : ℤ) : ℂ) * (L (u + v) - (L u + L v)) = 0 := by
      push_cast
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left
      (Int.cast_ne_zero.mpr (mul_ne_zero (mul_ne_zero (hD u) (hD v)) (hD (u + v)))))
  have hmul : ∀ (j j' : Fin (r + 1)) (a b a' b' : K), a * b = a' * b' →
      L (Pi.single j a) * L (Pi.single j' b) = L (Pi.single j a') * L (Pi.single j' b') := by
    intro j j' a b a' b' hab
    have hC : (C a * C b : MvPolynomial (Fin (r + 1)) K) = C a' * C b' := by
      rw [← C_mul, ← C_mul, hab]
    have h := key
      ((D (Pi.single j a') * D (Pi.single j' b') : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) *
          (P (Pi.single j a) * P (Pi.single j' b)) -
        (D (Pi.single j a) * D (Pi.single j' b) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) *
          (P (Pi.single j a') * P (Pi.single j' b'))) (by
        simp only [map_sub, map_mul, map_intCast, hP, latticeForm_single]
        linear_combination
          ((D (Pi.single j a') * D (Pi.single j' b') * D (Pi.single j a) * D (Pi.single j' b) :
            MvPolynomial (Fin (r + 1)) K) * X j * X j') * hC)
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : ((D (Pi.single j a) * D (Pi.single j' b) * D (Pi.single j a') * D (Pi.single j' b') : ℤ) : ℂ) *
        (L (Pi.single j a) * L (Pi.single j' b) - L (Pi.single j a') * L (Pi.single j' b')) = 0 := by
      push_cast
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (Int.cast_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hD _) (hD _)) (hD _)) (hD _))))
  have hφb : ∀ b, L (φ b) = z () b := by
    intro b
    have h := key (P (φ b) - (D (φ b) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩) (by
      simp only [map_sub, map_mul, map_intCast, hP]
      simp [latticeMap])
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : (D (φ b) : ℂ) * (L (φ b) - z () b) = 0 := by
      simp only [ev, eval₂Hom_X'] at h
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (hDc _))
  have hne : ∃ v, L v ≠ 0 := by
    obtain ⟨b, hb⟩ : ∃ b, z () b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz.1 () (funext hcon)
    exact ⟨φ b, by rw [hφb]; exact hb⟩
  obtain ⟨σ, w, hw, hL⟩ := exists_embedding_of_mul L hadd hmul hne
  refine ⟨σ, w, hw, ?_⟩
  funext u b
  rw [← hφb b, hL]
  rfl

open Classical in

theorem exists_left_inverse {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) (j₀ : Fin (r + 1)) :
    ∃ R : Fin (N + 1) → ℂ, ∀ (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0 := by
  let row : Fin (N + 1) → ((K →+* ℂ) × Fin (r + 1)) → ℂ := fun b p ↦ p.1 (φ b p.2)
  have htop : Submodule.span ℂ (Set.range row) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ :=
      (Submodule.span ℂ (Set.range row)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    apply hf0
    have hrow : ∀ b, f (row b) = 0 := fun b ↦ hle (Submodule.subset_span ⟨b, rfl⟩)
    let g : (K →+* ℂ) × Fin (r + 1) → ℂ := fun p ↦ f (Pi.single p 1)
    have hf : ∀ x, f x = ∑ p, g p * x p := by
      intro x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [show (Pi.single p (x p) : (K →+* ℂ) × Fin (r + 1) → ℂ) =
          x p • Pi.single p (1 : ℂ) by
        funext q; by_cases hq : q = p <;> simp [hq],
        map_smul, smul_eq_mul, mul_comm]
    have hzero : ∀ b, ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b = 0 := by
      intro b
      rw [← hrow b, hf, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [row]
      ring
    have hv : ∀ v : Fin (r + 1) → K, ∑ τ : K →+* ℂ, ∑ j, τ (v j) * g (τ, j) = 0 := by
      intro v
      obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ v
      have h1 : ∑ b, (c b : ℂ) * ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b =
          D * ∑ τ : K →+* ℂ, ∑ j, τ (v j) * g (τ, j) := by
        calc ∑ b, (c b : ℂ) * ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b
            = ∑ τ : K →+* ℂ, ∑ b, (c b : ℂ) * latticePoint φ τ (fun j ↦ g (τ, j)) () b := by
              simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
          _ = ∑ τ : K →+* ℂ, (D : ℂ) * ∑ j, τ (v j) * g (τ, j) :=
              Finset.sum_congr rfl fun τ _ ↦ sum_latticePoint τ _ hc
          _ = _ := (Finset.mul_sum _ _ _).symm
      simp only [hzero, mul_zero, Finset.sum_const_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (Int.cast_ne_zero.mpr hD)
    have hind : LinearIndependent ℂ (fun τ : K →+* ℂ ↦ ((τ : K →* ℂ) : K → ℂ)) :=
      (linearIndependent_monoidHom K ℂ).comp (fun τ : K →+* ℂ ↦ (τ : K →* ℂ))
        (fun τ τ' h ↦ RingHom.ext fun a ↦ DFunLike.congr_fun h a)
    have hg : ∀ p, g p = 0 := by
      rintro ⟨τ, j⟩
      refine Fintype.linearIndependent_iff.mp hind (fun τ ↦ g (τ, j)) ?_ τ
      funext a
      have h := hv (Pi.single j a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      rw [sum_single_mul τ (fun j ↦ g (τ, j)) j a, mul_comm]
      rfl
    refine LinearMap.ext fun x ↦ ?_
    rw [hf]
    simp [hg]
  have hmem : (Pi.single (σ, j₀) 1 : (K →+* ℂ) × Fin (r + 1) → ℂ) ∈ Submodule.span ℂ (Set.range row) :=
    htop ▸ Submodule.mem_top
  obtain ⟨R, hR⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨R, fun τ j ↦ ?_⟩
  have h := congrFun hR (τ, j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row] at h
  rw [h, Pi.single_apply]
  exact if_congr (Iff.of_eq (Prod.mk.injEq _ _ _ _)) rfl rfl

theorem OneBlockPoints.proof : OneBlockPoints.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨fun z hz ↦ ?_, fun σ w hw ↦ latticePoint_mem hφ σ hw, fun σ j₀ ↦ exists_left_inverse hφ σ j₀⟩
  obtain ⟨σ, w, hw, rfl⟩ := exists_latticePoint_eq hφ hz
  exact ⟨σ, ⟨w, hw, rfl⟩, fun σ' ⟨w', hw', h⟩ ↦ embedding_unique hφ hw' h.symm⟩

end

end GroundTheory.Heights₂.Heights
