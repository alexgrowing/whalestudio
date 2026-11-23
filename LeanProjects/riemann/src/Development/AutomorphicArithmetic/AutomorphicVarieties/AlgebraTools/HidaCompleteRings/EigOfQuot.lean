import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent
    {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (U : Submodule K Y) :
    U ≠ ⊥ → (∀ i, ∀ y ∈ U, T i y ∈ U) → (∀ i, ∀ y ∈ U, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → V ≠ ⊥ →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → (∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv hnil
  by_cases hall : ∀ i, ∀ y ∈ V, T i y = 0
  · obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    exact ⟨y, hy0, fun i => hall i y hyV⟩
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  have hpowmem : ∀ k : ℕ, (T i ^ k) z ∈ V := by
    intro k
    induction k with
    | zero => simpa using hzV
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hinv i _ ihk
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i)
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWne : W ≠ ⊥ := by
    classical
    have hex : ∃ n : ℕ, (T i ^ n) z = 0 := hnil i z hzV
    have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hz0 this
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hspec := Nat.find_spec hex
    rw [hm] at hspec
    have hmin : (T i ^ m) z ≠ 0 := Nat.find_min hex (by omega)
    rw [Submodule.ne_bot_iff]
    refine ⟨(T i ^ m) z, Submodule.mem_inf.mpr ⟨hpowmem m, ?_⟩, hmin⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
    exact hspec
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, hyk, map_zero]
  have hWnil : ∀ j, ∀ y ∈ W, ∃ n : ℕ, (T j ^ n) y = 0 :=
    fun j y hy => hnil j y (hWle hy)
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWne hWinv hWnil

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot
    {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (φ : Y →ₗ[K] Z)
    (hφ : ∀ i y, φ (T i y) = 0) (U : Submodule K Y) :
    (∃ u ∈ U, φ u ≠ 0) → (∀ i, ∀ y ∈ U, T i y ∈ U) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  intro hu hinv
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → (∃ u ∈ V, φ u ≠ 0) →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl hu hinv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv
  obtain ⟨u, huV, hu⟩ := hV
  have hVne : V ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨u, huV, fun h0 => hu (by rw [h0, map_zero])⟩
  by_cases hall : ∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0
  · exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent T hc V hVne hinv hall
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  let f : Module.End K V := (T i).restrict (hinv i)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_codisjoint_ker_pow_range_pow f)
  have hcod := hn (n + 1) (by omega)
  have hfpow : ∀ (k : ℕ) (w : V), ((f ^ k) w : Y) = (T i ^ k) (w : Y) := by
    intro k w
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
      rfl
  have hmem : (⟨u, huV⟩ : V) ∈ LinearMap.ker (f ^ (n + 1)) ⊔ LinearMap.range (f ^ (n + 1)) := by
    rw [codisjoint_iff.mp hcod]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hb
  have hφb : φ (((f ^ (n + 1)) c : V) : Y) = 0 := by
    rw [hfpow, pow_succ', Module.End.mul_apply, hφ]
  have hab' : (a : Y) + (((f ^ (n + 1)) c : V) : Y) = u := by
    have := congrArg Subtype.val hab
    simpa using this
  have hφa : φ (a : Y) ≠ 0 := by
    have h2 := congrArg φ hab'
    rw [map_add, hφb, add_zero] at h2
    rw [h2]
    exact hu
  have haker : (T i ^ (n + 1)) (a : Y) = 0 := by
    rw [← hfpow]
    rw [LinearMap.mem_ker.mp ha]
    rfl
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i ^ (n + 1))
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (n + 1) (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, ((hc i j).pow_left (n + 1)).eq, Module.End.mul_apply, hyk,
      map_zero]
  have hWu : ∃ w ∈ W, φ w ≠ 0 :=
    ⟨(a : Y), Submodule.mem_inf.mpr ⟨a.2, LinearMap.mem_ker.mpr haker⟩, hφa⟩
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWu hWinv

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot :
    ∀ {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] [AddCommGroup Z] [Module K Z] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (φ : Y →ₗ[K] Z), φ ≠ 0 → (∀ i y, φ (A i y) = x i • φ y) → ∃ y : Y, y ≠ 0 ∧ ∀ i, A i y = x i • y := by
  intro K Y Z ι _ _ _ _ _ _ A hA x φ hφ0 hφ
  let T : ι → Module.End K Y := fun i => A i - x i • (1 : Module.End K Y)
  have hT : ∀ i y, T i y = A i y - x i • y := by
    intro i y
    simp [T]
  have hc : ∀ i j, Commute (T i) (T j) := by
    intro i j
    exact ((hA i j).sub_right ((Commute.one_right (A i)).smul_right (x j))).sub_left
      (((Commute.one_left (A j)).smul_left (x i)).sub_right
        (((Commute.one_left 1).smul_left (x i)).smul_right (x j)))
  have hφT : ∀ i y, φ (T i y) = 0 := by
    intro i y
    rw [hT, map_sub, map_smul, hφ, sub_self]
  have hu : ∃ u ∈ (⊤ : Submodule K Y), φ u ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hφ0 (LinearMap.ext fun y => by simpa using hno y Submodule.mem_top)
  obtain ⟨y, hy0, hy⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot T hc φ hφT ⊤ hu
    (fun _ _ _ => Submodule.mem_top)
  refine ⟨y, hy0, fun i => ?_⟩
  have := hy i
  rw [hT, sub_eq_zero] at this
  exact this
