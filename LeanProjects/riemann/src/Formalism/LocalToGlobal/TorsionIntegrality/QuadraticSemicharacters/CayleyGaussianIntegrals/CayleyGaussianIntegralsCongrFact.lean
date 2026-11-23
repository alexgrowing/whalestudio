import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H.Inh

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)

theorem block_diag_smul_one {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) :
    blk4 (c • (1 : Matrix n n ℂ)) = c • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) := by
  ext ⟨a, i⟩ ⟨a', i'⟩
  simp only [blk4, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h1 : a = a' <;> by_cases h2 : i = i' <;> simp [h1, h2]

theorem fourth_power_standard_lattice (L : PeriodPair) (n : Type) [Fintype n] : pow4 (stdLat L n) = stdLat L (Fin 4 × n) := by
  ext z
  rw [mem_stdLat]
  constructor
  · intro hz w
    exact (mem_stdLat L n _).1 (hz w.1) w.2
  · intro hz a
    exact (mem_stdLat L n _).2 fun i => hz (a, i)

theorem relIdx_ne_zero_of_fg {V : Type} [AddCommGroup V] [Module ℂ V] (M M' : AddSubgroup V) [AddGroup.FG M]
    (N : ℕ) (hN : 0 < N) (h : ∀ x ∈ M, N • x ∈ M') : relIdx M' M ≠ 0 := by
  have ht : IsAddTorsion (M ⧸ M'.addSubgroupOf M) := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨N, hN, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact h x x.2
  have := AddCommGroup.finite_of_fg_isAddTorsion _ ht
  exact AddSubgroup.index_ne_zero_of_finite

instance stdLat_fg (L : PeriodPair) (m : Type) [Finite m] : AddGroup.FG (stdLat L m) := by
  rw [← Module.Finite.iff_addGroup_fg]
  have : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice
  let e : (m → L.lattice) ≃+ stdLat L m :=
    { toFun := fun f => ⟨fun i => (f i : ℂ), (mem_stdLat L m _).2 fun i => (f i).2⟩
      invFun := fun x i => ⟨x.1 i, (mem_stdLat L m _).1 x.2 i⟩
      left_inv := fun f => rfl
      right_inv := fun x => rfl
      map_add' := fun f g => rfl }
  exact Module.Finite.equiv e.toIntLinearEquiv

instance imgLat_fg {V : Type} [AddCommGroup V] [Module ℂ V] (g : V →ₗ[ℂ] V) (M : AddSubgroup V) [AddGroup.FG M] :
    AddGroup.FG (imgLat g M) :=
  AddGroup.fg_of_surjective (f := g.toAddMonoidHom.addSubgroupMap M) (g.toAddMonoidHom.addSubgroupMap_surjective M)

abbrev L7 : PeriodPair := cmL 1 1 7 one_pos (by norm_num) 1 one_ne_zero
abbrev th : ℂ := cmTheta 1 7

def uu : ℂ := th ^ 2 / 2

theorem mem7 (z : ℂ) : z ∈ L7.lattice ↔ z ∈ (cmPair 1 1 7 one_pos (by norm_num)).lattice := by
  rw [show L7 = Formalism.L2.Th1.F.scalePair (cmPair 1 1 7 one_pos (by norm_num)) 1 one_ne_zero from rfl,
    (Formalism.L2.Th1.F.homogeneity _ 1 one_ne_zero).1 z, inv_one, one_mul]

theorem th_rel : th ^ 2 = th - 2 ∧ th + conj th = 1 ∧ th * conj th = 2 := by
  have h := Formalism.L2.Th1.F.cmThetaEq 1 1 2 7 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have := h.1; push_cast at this; rw [this]; ring
  · have := h.2.1; push_cast at this; exact this
  · have := h.2.2; push_cast at this; rw [this]; ring

theorem uu_norm : uu * conj uu = 1 := by
  have h := th_rel.2.2
  simp only [uu, map_div₀, map_pow, map_ofNat]
  have : th ^ 2 / 2 * (conj th ^ 2 / 2) = (th * conj th) ^ 2 / 4 := by ring
  rw [this, h]; norm_num

theorem uu_ne : uu ≠ 0 := fun h => by have := uu_norm; rw [h] at this; simp at this

theorem th_im : th.im = Real.sqrt 7 / 2 := by
  simp [th, cmTheta]

theorem uu_ne_one : uu ≠ 1 := by
  intro h
  have h2 : th ^ 2 = 2 := by
    have := congrArg (· * 2) h
    simp only [uu] at this
    linear_combination this
  have h4 : th = 4 := by linear_combination h2 - th_rel.1
  have h5 := congrArg Complex.im h4
  rw [th_im] at h5
  have : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  norm_num at h5

theorem th_stable {x : ℂ} (hx : x ∈ L7.lattice) : th * x ∈ L7.lattice := by
  rw [mem7] at hx ⊢
  have := Formalism.L2.Th1.F.cmStable 1 1 2 7 one_pos (by norm_num) (by norm_num) 0 1 x hx
  simpa using this

theorem thbar_stable {x : ℂ} (hx : x ∈ L7.lattice) : conj th * x ∈ L7.lattice := by
  rw [mem7] at hx ⊢
  have := Formalism.L2.Th1.F.cmStable 1 1 2 7 one_pos (by norm_num) (by norm_num) 1 (-1) x hx
  have h2 : conj th = 1 - th := by rw [← th_rel.2.1]; ring
  rw [h2]
  simpa [sub_eq_add_neg] using this

theorem cayleyGaussianIntegrals_one_fact : (1 : ℂ) ∈ L7.lattice := by
  have h := L7.ω₁_mem_lattice
  have e : L7.ω₁ = 1 := by show (1 : ℂ) * ((1 : ℕ) : ℂ) = 1; simp
  rwa [e] at h

theorem thHalf_not : th / 2 ∉ L7.lattice := by
  have e : L7.ω₂ / 2 = th / 2 := by show (1 : ℂ) * cmTheta 1 7 / 2 = cmTheta 1 7 / 2; ring
  rw [← e]
  exact L7.ω₂_div_two_notMem_lattice

def smulU (m : Type) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.smulOfNeZero ℂ _ uu uu_ne

theorem smulU_apply {m : Type} (x : m → ℂ) : smulU m x = uu • x := rfl

theorem smul_isom (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (c : ℂ) (hc : c * conj c = 1) :
    ∀ x y : m → ℂ, stdH L m (c • x) (c • y) = stdH L m x y := by
  intro x y
  rw [stdH_apply, stdH_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Formalism.L2.Th1.F.herm, Pi.smul_apply, smul_eq_mul, map_mul]
  calc c * x i * (conj c * conj (y i)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)
      = (c * conj c) * (x i * conj (y i) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hc, one_mul]

theorem smulU_isom (m : Type) [Fintype m] [DecidableEq m] :
    IsIsom (stdH L7 m) (stdH L7 m) (smulU m : (m → ℂ) →ₗ[ℂ] (m → ℂ)) :=
  fun x y => smul_isom L7 m uu uu_norm x y

theorem th_stable_std {m : Type} {x : m → ℂ} (hx : x ∈ stdLat L7 m) : cmTheta 1 7 • x ∈ stdLat L7 m := by
  rw [mem_stdLat] at hx ⊢
  exact fun i => th_stable (hx i)

theorem idxU₁ (m : Type) [Finite m] :
    relIdx (stdLat L7 m) (imgLat (smulU m : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat L7 m)) ≠ 0 := by
  refine relIdx_ne_zero_of_fg _ _ 2 two_pos ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_stdLat]
  intro w
  have hx' := (mem_stdLat _ _ _).1 hx w
  have : (2 • (smulU m x)) w = th * (th * x w) := by
    simp only [smulU_apply, Pi.smul_apply, smul_eq_mul, uu, nsmul_eq_mul]
    push_cast; ring
  show (2 • (smulU m x)) w ∈ _
  rw [this]
  exact th_stable (th_stable hx')

theorem idxU₂ (m : Type) [Finite m] :
    relIdx (imgLat (smulU m : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat L7 m)) (stdLat L7 m) ≠ 0 := by
  refine relIdx_ne_zero_of_fg _ _ 2 two_pos ?_
  intro x hx
  refine ⟨fun w => conj th * (conj th * x w), ?_, ?_⟩
  · exact (mem_stdLat _ _ _).2 fun w => thbar_stable (thbar_stable ((mem_stdLat _ _ _).1 hx w))
  · ext w
    show uu * (conj th * (conj th * x w)) = (2 • x) w
    have h := th_rel.2.2
    simp only [uu, Pi.smul_apply, nsmul_eq_mul]
    have : th ^ 2 / 2 * (conj th * (conj th * x w)) = (th * conj th) ^ 2 / 2 * x w := by ring
    rw [this, h]; push_cast; ring

theorem smulU_ne (m : Type) [Nonempty m] :
    imgLat (smulU m : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat L7 m) ≠ stdLat L7 m := by
  intro h
  have h1 : (fun _ => (1 : ℂ)) ∈ stdLat L7 m := by
    rw [mem_stdLat]
    intro _
    exact cayleyGaussianIntegrals_one_fact
  have h2 : smulU m (fun _ => (1 : ℂ)) ∈ stdLat L7 m := by
    rw [← h]; exact ⟨_, h1, rfl⟩
  obtain ⟨i⟩ := ‹Nonempty m›
  have h3 := (mem_stdLat _ _ _).1 h2 i
  have h4 : smulU m (fun _ => (1 : ℂ)) i = th / 2 - 1 := by
    simp only [smulU_apply, Pi.smul_apply, smul_eq_mul, uu, th_rel.1]; ring
  rw [h4] at h3
  have h6 : th / 2 ∈ L7.lattice := by simpa using add_mem h3 cayleyGaussianIntegrals_one_fact
  exact thHalf_not h6

variable (n : Type) [Fintype n] [DecidableEq n]

def gU : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) := smulU (Fin 4 × n)

theorem gU_isom : IsIsom (matH (blk4 (((Formalism.L2.Th1.F.area L7 : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))))
    (stdH L7 (Fin 4 × n)) (gU n : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  intro x y
  rw [block_diag_smul_one]
  exact smulU_isom (Fin 4 × n) x y

theorem stdData_seven :
    StdData L7 1 (((Formalism.L2.Th1.F.area L7 : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ)) (stdLat L7 n)
      (alphaQ (Real.sqrt (7 : ℕ) / 2) (matH (((Formalism.L2.Th1.F.area L7 : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))))
      (alphaQ (Real.sqrt (7 : ℕ) / 2) (stdH L7 (Fin 4 × n))) (gU n) := by
  have h := CmData.stdData_cm 1 1 2 7 one_pos (by norm_num) 1 one_ne_zero (by norm_num) (by decide) (by norm_num)
    _ _ _ (gU_isom n) (stdSelfDual L7 n) (fun x hx => th_stable_std hx)
    (by rw [fourth_power_standard_lattice]; exact idxU₁ _) (by rw [fourth_power_standard_lattice]; exact idxU₂ _)
  have e : (1 : ℂ) * ((1 : ℕ) : ℂ) = 1 := by norm_num
  rw [e] at h
  exact h

theorem seven_nontrivial [Nonempty n] :
    imgLat (gU n : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 (stdLat L7 n)) ≠ stdLat L7 (Fin 4 × n) := by
  rw [fourth_power_standard_lattice]
  exact smulU_ne (Fin 4 × n)

def alpha7 (m : Type) [Fintype m] [DecidableEq m] : (m → ℂ) → ℂ := alphaQ (Real.sqrt (7 : ℕ) / 2) (stdH L7 m)

theorem one_sub_inv_uu_ne : (1 : ℂ) - uu⁻¹ ≠ 0 := by
  intro h
  apply uu_ne_one
  have : uu⁻¹ = 1 := by linear_combination -h
  exact inv_eq_one.1 this

def AeU (m : Type) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.smulOfNeZero ℂ _ (1 - uu⁻¹) one_sub_inv_uu_ne

def w3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((3 : ℕ) : ℂ))

def phi3 (x : ZMod 3) : ℂ := w3 ^ (x.val ^ 2)

def b3 (x y : ZMod 3) : ℂ := w3 ^ (2 * x.val * y.val)

end Formalism.L2.Th1.H.Inh
