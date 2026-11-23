import Formalism.LocalToGlobal.InertKernelTheory.DefsMMOnb
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageTrivialLevel

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace Formalism.L2.KerInert.MMOnb

variable {D : D7}

theorem hYY_add_left {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  rw [← map_add]
  congr 1
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hYY_smul_left {N N' : ℕ} (c : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = c * hYY D x y := by
  unfold hYY
  rw [← smul_eq_mul, ← LinearMap.map_smul]
  congr 1
  simp only [Matrix.smul_apply, Finset.smul_sum, smul_mul_assoc]

theorem hYY_zero_left {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D 0 y = 0 := by
  unfold hYY
  simp

theorem hYY_sum_left {N N' : ℕ} {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ i ∈ s, f i) y = ∑ i ∈ s, hYY D (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hYY_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hYY_add_left, ih]

theorem linInd_of_orthonormal {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : Orthonormal D b) :
    LinearIndependent D.host.K b := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have e := congrArg (fun z => hYY D z (b j)) hg
  rw [hYY_sum_left, hYY_zero_left] at e
  simp only [hYY_smul_left] at e
  rw [Finset.sum_congr rfl (fun x _ => by rw [hb x j])] at e
  simpa using e

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dif_pos (IntermediateField.one_mem _)]
  exact map_one lam

theorem lamC_zero {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 0 = 0 := by
  unfold lamC
  rw [dif_pos (IntermediateField.zero_mem _)]
  exact map_zero lam

theorem lamC_phi_K_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    lamC lam (D.host.φ₀ (((1 : D.host.K) : D.host.E))) = 1 := by
  rw [IntermediateField.coe_one, map_one, lamC_one]

theorem lamC_phi_K_zero {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    lamC lam (D.host.φ₀ (((0 : D.host.K) : D.host.E))) = 0 := by
  rw [IntermediateField.coe_zero, map_zero, lamC_zero]

theorem isLocONB_of_orthonormal (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (σ : ℂ_[p] →+* ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : LocBasis D p Y b) (ho : Orthonormal D b) :
    IsLocONB D p lam Y σ (fun i k => lamC lam (embT D k.1 (b i k.2.1 k.2.2))) := by
  refine ⟨b, 1, hb, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · rw [Matrix.one_apply, if_pos h]
      refine ⟨by simp [IsIntP], subset_closure ⟨1, lamC_phi_K_one lam⟩⟩
    · rw [Matrix.one_apply, if_neg h]
      refine ⟨by simp [IsIntP], subset_closure ⟨0, lamC_phi_K_zero lam⟩⟩
  · rw [Matrix.det_one, norm_one]
  · intro i j
    have h1 : ∀ m : Fin r, ∑ n : Fin r, (1 : Matrix (Fin r) (Fin r) ℂ_[p]) i m *
        lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E)) * σ ((1 : Matrix (Fin r) (Fin r) ℂ_[p]) j n) =
        (1 : Matrix (Fin r) (Fin r) ℂ_[p]) i m * lamC lam (D.host.φ₀ ((hYY D (b m) (b j) : D.host.K) : D.host.E)) := by
      intro m
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · rw [Matrix.one_apply_eq, map_one, mul_one]
      · intro n _ hn
        rw [Matrix.one_apply_ne (Ne.symm hn), map_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => h1 m)]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [Matrix.one_apply_eq, one_mul, ho i j]
      by_cases h : i = j
      · rw [if_pos h, if_pos h, lamC_phi_K_one]
      · rw [if_neg h, if_neg h, lamC_phi_K_zero]
    · intro m _ hm
      rw [Matrix.one_apply_ne (Ne.symm hm), zero_mul]
  · intro i k
    simp [Matrix.one_apply]

abbrev IsInt (x : D.host.E) : Prop := x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)

theorem isInt_mul {x y : D.host.E} (hx : IsInt (D := D) x) (hy : IsInt (D := D) y) : IsInt (D := D) (x * y) := by
  have := Submodule.mul_mem_mul hx hy
  rwa [one_mul] at this

theorem isInt_one : IsInt (D := D) 1 := Submodule.mem_one.2 ⟨1, map_one _⟩

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) : x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N ↔ ∀ i, IsInt (D := D) (x i) := by
  unfold Formalism.MainNotions.StandardLatticesGL3.stdL
  rw [Submodule.mem_pi]
  simp

def intS (N N' : ℕ) : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) where
  carrier := {A | ∀ a c, IsInt (D := D) (A a c)}
  zero_mem' := fun a c => by simp
  add_mem' := fun {A B} hA hB a c => by simpa using Submodule.add_mem _ (hA a c) (hB a c)
  smul_mem' := fun r A hA a c => by simpa using Submodule.smul_mem _ r (hA a c)

theorem homL_le_intS (N N' : ℕ) : homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') ≤ intS (D := D) N N' := by
  unfold homL
  rw [Submodule.span_le]
  intro A hA a c
  have h1 : Pi.single c (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    rw [mem_stdL]
    intro i
    by_cases h : i = c
    · subst h; simpa using (isInt_one (D := D))
    · simp [Pi.single_apply, h]
  have h2 := (mem_stdL _).1 (hA _ h1) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

def pos : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

theorem sum_pos {M : Type*} [AddCommMonoid M] (g : Fin 4 → M) : ∑ a : Fin 2, ∑ c : Fin 2, g (pos (a, c)) = ∑ j, g j := by
  rw [← Fintype.sum_prod_type' (fun a c => g (pos (a, c)))]
  exact Equiv.sum_comp pos g

def prj (a c : Fin 2) : Matrix (Fin 2) (Fin 2) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin 1) (Fin 1) D.host.E where
  toFun y := Matrix.of fun _ _ => y a c
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def plc (j : Fin 4) : Matrix (Fin 1) (Fin 1) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin 2) (Fin 2) D.host.E where
  toFun x := Matrix.of fun a c => if pos (a, c) = j then x 0 0 else 0
  map_add' _ _ := by ext a c; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' _ _ := by ext a c; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem prj_mem (a c : Fin 2) {y : Matrix (Fin 2) (Fin 2) D.host.E}
    (hy : y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) :
    prj a c y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  have key : YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) ≤
      (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)).comap (prj (D := D) a c) := by
    conv_lhs => unfold YYl
    rw [Submodule.span_le]
    rintro B ⟨a', ha', A, hA, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    have hAi := homL_le_intS (D := D) 2 2 hA
    have hmem : prj a c A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
      apply Submodule.subset_span
      intro x hx
      rw [mem_stdL] at hx ⊢
      intro i
      change (∑ j, (prj (D := D) a c A) i j * x j) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      simp only [prj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Fin.sum_univ_one]
      exact isInt_mul (hAi a c) (hx 0)
    have e : prj (D := D) a c (a' • A) = a' • prj (D := D) a c A := by
      ext; simp [prj]
    rw [e]
    unfold YYl
    exact Submodule.subset_span ⟨a', ha', _, hmem, rfl⟩
  exact key hy

theorem plc_mem (j : Fin 4) {x : Matrix (Fin 1) (Fin 1) D.host.E}
    (hx : x ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) :
    plc j x ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) := by
  have key : YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) ≤
      (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)).comap (plc (D := D) j) := by
    conv_lhs => unfold YYl
    rw [Submodule.span_le]
    rintro B ⟨a', ha', A, hA, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    have hAi := homL_le_intS (D := D) 1 1 hA
    have hmem : plc j A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) := by
      apply Submodule.subset_span
      intro x hx
      rw [mem_stdL] at hx ⊢
      intro i
      change (∑ c, (plc (D := D) j A) i c * x c) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      refine Submodule.sum_mem _ (fun c _ => ?_)
      simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
      split_ifs
      · exact isInt_mul (hAi 0 0) (hx c)
      · simp
    have e : plc (D := D) j (a' • A) = a' • plc (D := D) j A := by
      ext a c; simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
    rw [e]
    unfold YYl
    exact Submodule.subset_span ⟨a', ha', _, hmem, rfl⟩
  exact key hx

def qMat (a b c d : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![a, -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

theorem qMat_row (a b c d : ℤ) (k l : Fin 4) :
    ∑ j, qMat a b c d k j * qMat a b c d l j = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * if k = l then 1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp [qMat, Fin.sum_univ_four] <;> ring

theorem qMat_col (a b c d : ℤ) (j j' : Fin 4) :
    ∑ k, qMat a b c d k j * qMat a b c d k j' = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * if j = j' then 1 else 0 := by
  fin_cases j <;> fin_cases j' <;> simp [qMat, Fin.sum_univ_four] <;> ring

theorem hYY_one (x y : Matrix (Fin 1) (Fin 1) D.host.E) :
    hYY D x y = Algebra.trace D.host.K D.host.E (x 0 0 * D.host.conj (y 0 0)) := by
  unfold hYY
  simp

def bq {m : ℕ} (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n : Fin m → ℕ) (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ)
    (ik : Fin m × Fin 4) : Matrix (Fin 2) (Fin 2) D.host.E :=
  Matrix.of fun a c => ((Q ik.1 ik.2 (pos (a, c)) : D.host.E) / (n ik.1 : D.host.E)) * e ik.1 0 0

theorem hYY_bq {m : ℕ} (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n : Fin m → ℕ)
    (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ) (ik jl : Fin m × Fin 4) :
    hYY D (bq e n Q ik) (bq e n Q jl) =
      (((∑ j, (Q ik.1 ik.2 j : ℚ) * (Q jl.1 jl.2 j : ℚ)) / ((n ik.1 : ℚ) * (n jl.1 : ℚ)) : ℚ) : D.host.K) *
        hYY D (e ik.1) (e jl.1) := by
  rw [hYY_one]
  unfold hYY
  have inner : ∑ a, ∑ c, bq e n Q ik a c * D.host.conj (bq e n Q jl a c) =
      algebraMap D.host.K D.host.E
        (((∑ j, (Q ik.1 ik.2 j : ℚ) * (Q jl.1 jl.2 j : ℚ)) / ((n ik.1 : ℚ) * (n jl.1 : ℚ)) : ℚ) : D.host.K) *
        (e ik.1 0 0 * D.host.conj (e jl.1 0 0)) := by
    rw [map_ratCast]
    simp only [bq, Matrix.of_apply, map_mul, map_div₀, map_intCast, map_natCast]
    rw [sum_pos (fun j => (Q ik.1 ik.2 j : D.host.E) / (n ik.1 : D.host.E) * e ik.1 0 0 *
      ((Q jl.1 jl.2 j : D.host.E) / (n jl.1 : D.host.E) * D.host.conj (e jl.1 0 0)))]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [inner, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem orth_bq {m : ℕ} (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n dn : Fin m → ℕ)
    (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ) (hn0 : ∀ i, n i ≠ 0) (hd0 : ∀ i, dn i ≠ 0)
    (hQ : ∀ i k l, ∑ j, Q i k j * Q i l j = ((n i * dn i : ℕ) : ℤ) * if k = l then 1 else 0)
    (horth : ∀ i j, i ≠ j → hYY D (e i) (e j) = 0)
    (hval : ∀ i, hYY D (e i) (e i) = (((n i : ℚ) / (dn i : ℚ) : ℚ) : D.host.K)) (ik jl : Fin m × Fin 4) :
    hYY D (bq e n Q ik) (bq e n Q jl) = if ik = jl then 1 else 0 := by
  obtain ⟨i, k⟩ := ik
  obtain ⟨i', l⟩ := jl
  rw [hYY_bq]
  by_cases hi : i = i'
  · subst hi
    rw [hval, ← Rat.cast_mul]
    have hs : (∑ j, (Q i k j : ℚ) * (Q i l j : ℚ)) = (((n i * dn i : ℕ) : ℤ) : ℚ) * if k = l then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℚ) (hQ i k l)
      push_cast at this ⊢
      rw [← this]
    have hn : (n i : ℚ) ≠ 0 := by exact_mod_cast hn0 i
    have hd : (dn i : ℚ) ≠ 0 := by exact_mod_cast hd0 i
    simp only [hs]
    by_cases hkl : k = l
    · subst hkl
      have hq : ((((n i * dn i : ℕ) : ℤ) : ℚ) * 1 / ((n i : ℚ) * (n i : ℚ)) * ((n i : ℚ) / (dn i : ℚ))) = 1 := by
        push_cast; field_simp
      rw [if_pos rfl, if_pos rfl, hq, Rat.cast_one]
    · have hne : (i, k) ≠ (i, l) := fun h => hkl (congrArg Prod.snd h)
      rw [if_neg hkl, if_neg hne]
      simp
  · have hne : (i, k) ≠ (i', l) := fun h => hi (congrArg Prod.fst h)
    rw [horth i i' hi, mul_zero, if_neg hne]

theorem smul_bq {m : ℕ} (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n : Fin m → ℕ)
    (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ) (hn0 : ∀ i, n i ≠ 0) (ik : Fin m × Fin 4) (s : ℕ) :
    ((n ik.1 * s : ℕ) : D.host.E) • bq e n Q ik = ∑ j, Q ik.1 ik.2 j • plc j ((s : D.host.E) • e ik.1) := by
  have hn : (n ik.1 : D.host.E) ≠ 0 := by exact_mod_cast hn0 ik.1
  refine Matrix.ext fun a c => ?_
  rw [Matrix.sum_apply, Finset.sum_eq_single (pos (a, c))]
  · simp only [bq, plc, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, if_pos rfl,
      zsmul_eq_mul, ite_true, if_true]
    rw [Nat.cast_mul]
    field_simp
  · intro j _ hj
    simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.smul_apply, if_neg (Ne.symm hj), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mem_bq {m : ℕ} (p : ℕ) (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n : Fin m → ℕ)
    (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ) (hn0 : ∀ i, n i ≠ 0) (hncop : ∀ i, Nat.Coprime (n i) p)
    (he : ∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • e i ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1))
    (ik : Fin m × Fin 4) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • bq e n Q ik ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) := by
  obtain ⟨s, hs, hmem⟩ := he ik.1
  refine ⟨n ik.1 * s, Nat.Coprime.mul (hncop ik.1) hs, ?_⟩
  rw [smul_bq e n Q hn0 ik s]
  exact Submodule.sum_mem _ (fun j _ => zsmul_mem (plc_mem j hmem) _)

theorem col_sum {F : Type*} [Field F] (Q : Matrix (Fin 4) (Fin 4) ℤ) (N : ℤ)
    (hQ : ∀ j j', ∑ k, Q k j * Q k j' = N * if j = j' then 1 else 0) (T : Fin 2 × Fin 2 → F) (ac : Fin 2 × Fin 2) (z : F) :
    ∑ k, (∑ pc, T pc * (Q k (pos pc) : F)) * ((Q k (pos ac) : F) * z) = T ac * (N : F) * z := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ pc, ∑ k, T pc * (Q k (pos pc) : F) * ((Q k (pos ac) : F) * z) =
      T pc * z * ((∑ k, Q k (pos pc) * Q k (pos ac) : ℤ) : F) := by
    intro pc
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun pc _ => h pc)]
  simp_rw [hQ]
  push_cast
  simp only [EmbeddingLike.apply_eq_iff_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem span_bq {m : ℕ} (p : ℕ) (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (n dn : Fin m → ℕ)
    (Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ) (hn0 : ∀ i, n i ≠ 0)
    (hQc : ∀ i j j', ∑ k, Q i k j * Q i k j' = ((n i * dn i : ℕ) : ℤ) * if j = j' then 1 else 0)
    (hdcop : ∀ i, Nat.Coprime (dn i) p)
    (he : ∀ y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1), ∃ s : ℕ, Nat.Coprime s p ∧
      ∃ c : Fin m → 𝓞 D.host.K, (s : D.host.E) • y = ∑ i, (((c i : D.host.K) : D.host.E)) • e i)
    (y : Matrix (Fin 2) (Fin 2) D.host.E) (hy : y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin m × Fin 4 → 𝓞 D.host.K,
      (s : D.host.E) • y = ∑ ik, (((c ik : D.host.K) : D.host.E)) • bq e n Q ik := by
  choose s hs c hc using fun pc : Fin 2 × Fin 2 => he _ (prj_mem (D := D) pc.1 pc.2 hy)
  let φ : 𝓞 D.host.K →+* D.host.E := (algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)
  have hφ : ∀ z : 𝓞 D.host.K, (((z : D.host.K) : D.host.E)) = φ z := fun z => rfl
  have hc' : ∀ pc : Fin 2 × Fin 2, (s pc : D.host.E) * y pc.1 pc.2 = ∑ i, φ (c pc i) * e i 0 0 := by
    intro pc
    have h1 := congrArg (fun M : Matrix (Fin 1) (Fin 1) D.host.E => M 0 0) (hc pc)
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hφ] at h1
    exact h1
  have hsd : ∀ pc, s pc ∣ ∏ pc', s pc' := fun pc => Finset.dvd_prod_of_mem _ (Finset.mem_univ pc)
  have hdd : ∀ i, dn i ∣ ∏ i', dn i' := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨(∏ pc, s pc) * ∏ i, dn i,
    Nat.Coprime.mul (Nat.Coprime.prod_left fun pc _ => hs pc) (Nat.Coprime.prod_left fun i _ => hdcop i),
    fun ik => ∑ pc, (((∏ pc', s pc') / s pc * ((∏ i', dn i') / dn ik.1) : ℕ) : 𝓞 D.host.K) *
      ((Q ik.1 ik.2 (pos pc) : ℤ) : 𝓞 D.host.K) * c pc ik.1, ?_⟩
  refine Matrix.ext fun a c' => ?_
  rw [Matrix.smul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Matrix.smul_apply, smul_eq_mul, bq, Matrix.of_apply]
  simp only [hφ]
  simp only [map_sum, map_mul, map_natCast, map_intCast]
  have key : ∀ i, ∑ k, (∑ pc, (((∏ pc', s pc') / s pc * ((∏ i', dn i') / dn i) : ℕ) : D.host.E) *
      ((Q i k (pos pc) : ℤ) : D.host.E) * φ (c pc i)) *
      (((Q i k (pos (a, c')) : ℤ) : D.host.E) / (n i : D.host.E) * e i 0 0) =
      (((∏ pc', s pc') / s (a, c') : ℕ) : D.host.E) * ((∏ i', dn i' : ℕ) : D.host.E) * (φ (c (a, c') i) * e i 0 0) := by
    intro i
    have hn : (n i : D.host.E) ≠ 0 := by exact_mod_cast hn0 i
    have hD : (((∏ i', dn i') / dn i : ℕ) : D.host.E) * (dn i : D.host.E) = ((∏ i', dn i' : ℕ) : D.host.E) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdd i)]
    have h1 := col_sum (F := D.host.E) (Q i) ((n i * dn i : ℕ) : ℤ) (hQc i)
      (fun pc => (((∏ pc', s pc') / s pc * ((∏ i', dn i') / dn i) : ℕ) : D.host.E) * φ (c pc i)) (a, c')
      (e i 0 0 / (n i : D.host.E))
    calc _ = ∑ k, (∑ pc, (((∏ pc', s pc') / s pc * ((∏ i', dn i') / dn i) : ℕ) : D.host.E) * φ (c pc i) *
          ((Q i k (pos pc) : ℤ) : D.host.E)) * (((Q i k (pos (a, c')) : ℤ) : D.host.E) * (e i 0 0 / (n i : D.host.E))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_congr rfl (fun pc _ => (mul_right_comm _ _ _ :
            (((∏ pc', s pc') / s pc * ((∏ i', dn i') / dn i) : ℕ) : D.host.E) * ((Q i k (pos pc) : ℤ) : D.host.E) *
              φ (c pc i) = _))]
          ring
      _ = _ := h1
      _ = _ := by
          simp only [Nat.cast_mul, Int.cast_natCast, Int.cast_mul]
          rw [← hD]
          field_simp
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, ← hc' (a, c')]
  have hS : (((∏ pc', s pc') / s (a, c') : ℕ) : D.host.E) * (s (a, c') : D.host.E) = ((∏ pc', s pc' : ℕ) : D.host.E) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (hsd _)]
  rw [Nat.cast_mul, ← hS]
  ring

theorem globONB_of (h : OneCopyOrth) : GlobONB := by
  intro D p _ hp hin lam
  obtain ⟨m, e, u, hloc, horth, hu⟩ := h D p hp hin
  have hnum : ∀ i, 0 < (u i).num := fun i => Rat.num_pos.2 (hu i).1
  let n : Fin m → ℕ := fun i => (u i).num.toNat
  let dn : Fin m → ℕ := fun i => (u i).den
  have hnZ : ∀ i, ((n i : ℕ) : ℤ) = (u i).num := fun i => Int.toNat_of_nonneg (hnum i).le
  have hn0 : ∀ i, n i ≠ 0 := by
    intro i h0
    have h1 := hnZ i
    rw [h0, Nat.cast_zero] at h1
    exact (hnum i).ne h1
  have hd0 : ∀ i, dn i ≠ 0 := fun i => (u i).den_nz
  have hpp : p.Prime := Fact.out
  have hncop : ∀ i, Nat.Coprime (n i) p := by
    intro i
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro hd
    apply (hu i).2.1
    rw [← hnZ i]
    exact Int.natCast_dvd_natCast.2 hd
  have hdcop : ∀ i, Nat.Coprime (dn i) p := by
    intro i
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    exact (hu i).2.2.1
  have hval : ∀ i, hYY D (e i) (e i) = (((n i : ℚ) / (dn i : ℚ) : ℚ) : D.host.K) := by
    intro i
    rw [(hu i).2.2.2]
    congr 1
    have h1 : ((n i : ℚ)) = ((u i).num : ℚ) := by exact_mod_cast hnZ i
    rw [h1]
    exact (Rat.num_div_den (u i)).symm
  choose A B C Dq hsq using fun i => Nat.sum_four_squares (n i * dn i)
  let Q : Fin m → Matrix (Fin 4) (Fin 4) ℤ := fun i => qMat (A i) (B i) (C i) (Dq i)
  have hN : ∀ i, ((A i : ℤ) ^ 2 + (B i : ℤ) ^ 2 + (C i : ℤ) ^ 2 + (Dq i : ℤ) ^ 2) = ((n i * dn i : ℕ) : ℤ) := by
    intro i
    rw [← hsq i]
    push_cast
    ring
  have hQr : ∀ i k l, ∑ j, Q i k j * Q i l j = ((n i * dn i : ℕ) : ℤ) * if k = l then 1 else 0 := by
    intro i k l
    rw [← hN i]
    exact qMat_row _ _ _ _ k l
  have hQc : ∀ i j j', ∑ k, Q i k j * Q i k j' = ((n i * dn i : ℕ) : ℤ) * if j = j' then 1 else 0 := by
    intro i j j'
    rw [← hN i]
    exact qMat_col _ _ _ _ j j'
  let b : Fin (m * 4) → Matrix (Fin 2) (Fin 2) D.host.E := fun r => bq e n Q (finProdFinEquiv.symm r)
  have hon : Orthonormal D b := by
    intro r r'
    show hYY D (bq e n Q _) (bq e n Q _) = _
    rw [orth_bq e n dn Q hn0 hd0 hQr horth hval]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  have hlb : LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) b := by
    refine ⟨linInd_of_orthonormal b hon, fun r => mem_bq p e n Q hn0 hncop hloc.2.1 _, ?_⟩
    intro y hy
    obtain ⟨s, hs, c, hc⟩ := span_bq p e n dn Q hn0 hQc hdcop hloc.2.2 y hy
    refine ⟨s, hs, fun r => c (finProdFinEquiv.symm r), ?_⟩
    rw [hc]
    exact (Equiv.sum_comp finProdFinEquiv.symm (fun ik => (((c ik : D.host.K) : D.host.E)) • bq e n Q ik)).symm
  exact ⟨m * 4, b, hlb, hon, fun σ _ => isLocONB_of_orthonormal p lam _ σ b hlb hon⟩

section unit

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.FrobeniusOrbits

abbrev AAs (D : D7) : Submodule (𝓞 D.host.E) D.host.E := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)

theorem mem_one_by_one_lattice_iff (x : Matrix (Fin 1) (Fin 1) D.host.E) :
    x ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) ↔ x 0 0 ∈ AAs D := by
  constructor
  · intro hx
    let ev : Matrix (Fin 1) (Fin 1) D.host.E →ₗ[𝓞 D.host.E] D.host.E :=
      { toFun := fun M => M 0 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have key : YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) ≤ (AAs D).comap ev := by
      unfold YYl
      rw [Submodule.span_le]
      rintro B ⟨a, ha, A, hA, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      have hAi := homL_le_intS (D := D) 1 1 hA 0 0
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 hAi
      show (a • A) 0 0 ∈ AAs D
      rw [Matrix.smul_apply, smul_eq_mul, ← hr, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r ha
    exact key hx
  · intro hx
    have h1 : (1 : Matrix (Fin 1) (Fin 1) D.host.E) ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) :=
      Submodule.subset_span (fun v hv => by simpa using hv)
    have e : x = x 0 0 • (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
      refine Matrix.ext fun i j => ?_
      fin_cases i; fin_cases j; simp
    rw [e]
    unfold YYl
    exact Submodule.subset_span ⟨x 0 0, hx, 1, h1, rfl⟩

theorem trace_natCast_mul (s : ℕ) (z : D.host.E) :
    Algebra.trace D.host.K D.host.E ((s : D.host.E) * z) = (s : D.host.K) * Algebra.trace D.host.K D.host.E z := by
  rw [← map_natCast (algebraMap D.host.K D.host.E) s, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

def Good (p : ℕ) {k : ℕ} (e : Fin k → D.host.E) : Prop :=
  (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * e i ∈ AAs D) ∧
  (∀ i j, i ≠ j → Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) = 0) ∧
  (∀ i, ∃ u : ℚ, 0 < u ∧ ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den ∧
    Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u : ℚ) : D.host.K))

theorem orth_symm {x y : D.host.E} (h : Algebra.trace D.host.K D.host.E (x * D.host.conj y) = 0) :
    Algebra.trace D.host.K D.host.E (y * D.host.conj x) = 0 := by
  have := (G0.herm D).symm x y
  simp only [G0.hK] at this
  rw [this, h, map_zero]

theorem loop (hU : UnitVec) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) :
    ∀ k, k ≤ Module.finrank D.host.K D.host.E → ∃ e : Fin k → D.host.E, Good (D := D) p e := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨e, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨z, hz1, hz2, hz3⟩ := hU D p hp hin k e h1 h2 h3 (by omega)
    refine ⟨Fin.cons z e, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hz1
      · simpa using h1 i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hz2 j
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa using orth_symm (D := D) (hz2 i)
        | succ j =>
          simp only [Fin.cons_succ]
          exact h2 i j (fun h => hij (by rw [h]))
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hz3
      · simpa using h3 i

theorem oneCopyOrth_of (hU : UnitVec) : OneCopyOrth := by
  intro D p _ hp hin
  set f := Module.finrank D.host.K D.host.E with hf
  obtain ⟨e, hMp, horth, hdiag⟩ := loop (D := D) hU p hp hin f le_rfl
  choose u hu using hdiag
  have hpp : p.Prime := Fact.out
  have hne : ∀ i, e i ≠ 0 := by
    intro i h0
    have h := (hu i).2.2.2
    rw [h0, zero_mul, map_zero] at h
    have : ((u i : ℚ) : D.host.K) ≠ 0 := Rat.cast_ne_zero.2 (hu i).1.ne'
    exact this h.symm
  have hli : LinearIndependent D.host.K e :=
    FS.Herm4.linInd (G0.herm D) e hne (fun i j hij => horth i j hij)
  have hsp : ⊤ ≤ Submodule.span D.host.K (Set.range e) :=
    le_of_eq (hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin])).symm
  let bs : Module.Basis (Fin f) D.host.K D.host.E := Module.Basis.mk hli hsp
  have hbs : ∀ i, bs i = e i := fun i => Module.Basis.mk_apply hli hsp i
  let L : D.host.E →ₗ[D.host.K] Matrix (Fin 1) (Fin 1) D.host.E :=
    { toFun := fun x => Matrix.of fun _ _ => x
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }
  have hLker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) D.host.E => M 0 0) hx
    simpa [L] using this
  refine ⟨f, fun i => Matrix.of fun _ _ => e i, u, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hli.map' L hLker
  · intro i
    obtain ⟨s, hs, hmem⟩ := hMp i
    refine ⟨s, hs, (mem_one_by_one_lattice_iff _).2 ?_⟩
    simpa using hmem
  · intro y hy
    have hy0 : y 0 0 ∈ AAs D := (mem_one_by_one_lattice_iff y).1 hy
    choose s hs hsm using hMp

    have hint : ∀ j, ∃ w : 𝓞 D.host.K, (w : D.host.K) =
        (s j : D.host.K) * Algebra.trace D.host.K D.host.E (y 0 0 * D.host.conj (e j)) := by
      intro j
      have h1 := (factMMUnimodular D.R D.host (y 0 0)).1 hy0 _ (hsm j)
      obtain ⟨w, hw⟩ := h1
      refine ⟨w, ?_⟩
      have e1 : ((w : D.host.K)) = algebraMap (𝓞 D.host.K) D.host.K w := rfl
      have e2 : D.host.conj ((s j : D.host.E) * e j) = (s j : D.host.E) * D.host.conj (e j) := by
        rw [map_mul, map_natCast]
      rw [e1, hw, e2, mul_left_comm, trace_natCast_mul]
    choose w hw using hint
    let n : Fin f → ℕ := fun i => (u i).num.toNat
    have hnZ : ∀ i, ((n i : ℕ) : ℤ) = (u i).num := fun i => Int.toNat_of_nonneg (Rat.num_pos.2 (hu i).1).le
    have hn0 : ∀ i, n i ≠ 0 := by
      intro i h0
      have h1 := hnZ i
      rw [h0, Nat.cast_zero] at h1
      exact (Rat.num_pos.2 (hu i).1).ne h1
    have hncop : ∀ i, Nat.Coprime (n i) p := by
      intro i
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
      intro hd
      apply (hu i).2.1
      rw [← hnZ i]
      exact Int.natCast_dvd_natCast.2 hd
    have hu' : ∀ i, (u i : D.host.K) = (n i : D.host.K) / ((u i).den : D.host.K) := by
      intro i
      have h1 : ((n i : ℚ)) = ((u i).num : ℚ) := by exact_mod_cast hnZ i
      have h2 : (n i : ℚ) / ((u i).den : ℚ) = u i := by rw [h1]; exact Rat.num_div_den (u i)
      conv_lhs => rw [← h2]
      push_cast
      ring
    set S := ∏ j, (s j * n j) with hS
    have hdv : ∀ j, s j * n j ∣ S := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    refine ⟨S, Nat.Coprime.prod_left (fun j _ => Nat.Coprime.mul (hs j) (hncop j)),
      fun j => w j * (((u j).den : ℕ) : 𝓞 D.host.K) * ((S / (s j * n j) : ℕ) : 𝓞 D.host.K), ?_⟩

    have hexp : y 0 0 = ∑ j, bs.repr (y 0 0) j • e j := by
      conv_lhs => rw [← bs.sum_repr (y 0 0)]
      simp only [hbs]
    have hcoef : ∀ j, bs.repr (y 0 0) j * (u j : D.host.K) =
        Algebra.trace D.host.K D.host.E (y 0 0 * D.host.conj (e j)) := by
      intro j
      have h1 := congrArg (fun x => (G0.herm D).hl (e j) x) hexp
      simp only [map_sum, map_smul, smul_eq_mul] at h1
      show _ = (G0.herm D).hl (e j) (y 0 0)
      rw [h1, Finset.sum_eq_single j]
      · show _ = bs.repr (y 0 0) j * G0.hK D (e j) (e j)
        simp only [G0.hK]
        rw [(hu j).2.2.2]
      · intro i _ hij
        show bs.repr (y 0 0) i * G0.hK D (e i) (e j) = 0
        simp only [G0.hK]
        rw [horth i j hij, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    refine Matrix.ext fun a c => ?_
    fin_cases a; fin_cases c
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]
    show (S : D.host.E) * y 0 0 = ∑ j, (((w j * (((u j).den : ℕ) : 𝓞 D.host.K) *
      ((S / (s j * n j) : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K) : D.host.E) * e j
    conv_lhs => rw [hexp]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, ← mul_assoc]
    congr 1
    show (S : D.host.E) * algebraMap D.host.K D.host.E (bs.repr (y 0 0) j) = algebraMap D.host.K D.host.E
      (((w j * (((u j).den : ℕ) : 𝓞 D.host.K) * ((S / (s j * n j) : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K)) : D.host.K)
    rw [← map_natCast (algebraMap D.host.K D.host.E) S, ← map_mul]
    congr 1
    have hc : (((w j * (((u j).den : ℕ) : 𝓞 D.host.K) * ((S / (s j * n j) : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K)) : D.host.K) =
        (w j : D.host.K) * ((u j).den : D.host.K) * ((S / (s j * n j) : ℕ) : D.host.K) := by
      show algebraMap (𝓞 D.host.K) D.host.K _ = _
      rw [map_mul, map_mul, map_natCast, map_natCast]
    have hu0 : (u j : D.host.K) ≠ 0 := Rat.cast_ne_zero.2 (hu j).1.ne'
    have hr : bs.repr (y 0 0) j = Algebra.trace D.host.K D.host.E (y 0 0 * D.host.conj (e j)) / (u j : D.host.K) := by
      rw [← hcoef j]; field_simp
    have hsn : ((S / (s j * n j) : ℕ) : D.host.K) * ((s j : D.host.K) * (n j : D.host.K)) = (S : D.host.K) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.div_mul_cancel (hdv j)]
    have hs0 : (s j : D.host.K) ≠ 0 := by
      have : s j ≠ 0 := by
        intro h0; have := hs j; rw [h0, Nat.coprime_zero_left] at this; exact hpp.one_lt.ne' this
      exact_mod_cast this
    have hn0' : (n j : D.host.K) ≠ 0 := by exact_mod_cast hn0 j
    have hd0 : (((u j).den : ℕ) : D.host.K) ≠ 0 := by exact_mod_cast (u j).den_nz
    rw [hc, hw j, hr, hu' j, ← hsn]
    field_simp
  · intro i j hij
    rw [hYY_one]
    exact horth i j hij
  · intro i
    refine ⟨(hu i).1, (hu i).2.1, (hu i).2.2.1, ?_⟩
    rw [hYY_one]
    exact (hu i).2.2.2

def Zp (p : ℕ) (r : ℚ) : Prop := ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ r = a / b

def PZ (p : ℕ) (r : ℚ) : Prop := ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ r = p * a / b

section padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem PZ_zero : PZ p 0 := ⟨0, 1, fun h => hp.out.one_lt.ne' (Nat.dvd_one.1 h), by simp⟩

theorem PZ_add {r r' : ℚ} (h : PZ p r) (h' : PZ p r') : PZ p (r + r') := by
  obtain ⟨a, b, hb, rfl⟩ := h
  obtain ⟨a', b', hb', rfl⟩ := h'
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h0; apply hb; rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero p
  have hb0' : (b' : ℚ) ≠ 0 := by
    intro h0; apply hb'; rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero p
  refine ⟨a * b' + a' * b, b * b', fun h => (hp.out.dvd_mul.1 h).elim hb hb', ?_⟩
  push_cast
  field_simp

theorem PZ_zmul (m : ℤ) {r : ℚ} (h : PZ p r) : PZ p (m * r) := by
  obtain ⟨a, b, hb, rfl⟩ := h
  exact ⟨m * a, b, hb, by push_cast; ring⟩

theorem PZ_sub {r r' : ℚ} (h : PZ p r) (h' : PZ p r') : PZ p (r - r') := by
  have := PZ_add p h (by simpa using PZ_zmul p (-1) h')
  simpa [sub_eq_add_neg] using this

theorem PZ_int {m : ℤ} (h : PZ p (m : ℚ)) : (p : ℤ) ∣ m := by
  obtain ⟨a, b, hb, hab⟩ := h
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h0; apply hb; rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero p
  have e : (m * b : ℤ) = p * a := by
    have : (m : ℚ) * b = p * a := by rw [hab]; field_simp
    exact_mod_cast this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hpz.dvd_or_dvd (show (p : ℤ) ∣ m * b from ⟨a, e⟩) with h1 | h1
  · exact h1
  · exact absurd (Int.natCast_dvd_natCast.1 h1) hb

theorem unit_or_PZ {q : ℚ} (hz : Zp p q) : (¬ (p : ℤ) ∣ q.num ∧ ¬ p ∣ q.den) ∨ PZ p q := by
  obtain ⟨a, b, hb, hq⟩ := hz
  have hden : ¬ p ∣ q.den := by
    intro h
    have h1 : ((q.den : ℤ)) ∣ (b : ℤ) := by
      have := Rat.den_dvd a b
      rw [Rat.divInt_eq_div] at this
      rw [hq]
      exact this
    exact hb (Int.natCast_dvd_natCast.1 ((Int.natCast_dvd_natCast.2 h).trans h1))
  by_cases hn : (p : ℤ) ∣ q.num
  · right
    obtain ⟨c, hc⟩ := hn
    refine ⟨c, q.den, hden, ?_⟩
    conv_lhs => rw [← Rat.num_div_den q, hc]
    push_cast
    ring
  · exact Or.inl ⟨hn, hden⟩

theorem Zp_div_pow {q : ℚ} (hq : 0 < q) (h : ∀ j : ℕ, Zp p (q / (p : ℚ) ^ (2 * j))) : False := by
  have hnum : 0 < q.num := Rat.num_pos.2 hq
  set N := q.num.toNat with hN
  have hNZ : (N : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hN1 : 1 ≤ N := by omega
  obtain ⟨a, b, hb, hab⟩ := h N
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h0; apply hb; rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero p
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hqN : q = (N : ℚ) / q.den := by
    have : (N : ℚ) = (q.num : ℚ) := by exact_mod_cast hNZ
    rw [this]; exact (Rat.num_div_den q).symm
  have e : ((N : ℤ) * b : ℤ) = a * q.den * (p : ℤ) ^ (2 * N) := by
    have : (N : ℚ) * b = a * q.den * (p : ℚ) ^ (2 * N) := by
      rw [hqN] at hab
      field_simp at hab
      linear_combination hab
    exact_mod_cast this
  have hcop : IsCoprime ((p : ℤ) ^ (2 * N)) (b : ℤ) := by
    have : Nat.Coprime (p ^ (2 * N)) b :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb)
    have := Nat.isCoprime_iff_coprime.2 this
    push_cast at this
    exact this
  have hdv : (p : ℤ) ^ (2 * N) ∣ (N : ℤ) := hcop.dvd_of_dvd_mul_right ⟨a * q.den, by rw [e]; ring⟩
  have hle : ((p : ℤ) ^ (2 * N)) ≤ (N : ℤ) := Int.le_of_dvd (by omega) hdv
  have hle' : p ^ (2 * N) ≤ N := by exact_mod_cast hle
  have h2 : N < 2 ^ N := Nat.lt_two_pow_self
  have h3 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left (by have := hp.out.two_le; omega) N
  have h4 : p ^ N ≤ p ^ (2 * N) := Nat.pow_le_pow_right hp.out.pos (by omega)
  omega

end padic

theorem int_of_isIntegral (D : D7) (r : ℚ) (h : IsIntegral ℤ ((r : D.host.E))) : ∃ z : ℤ, r = z := by
  have hinj : Function.Injective ((Algebra.ofId ℚ D.host.E).restrictScalars ℤ) := (algebraMap ℚ D.host.E).injective
  have h' : IsIntegral ℤ r := by
    rw [← isIntegral_algHom_iff _ hinj]
    convert h using 1
    simp
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  exact ⟨z, by rw [← hz]; simp⟩

theorem bE_isIntegral (D : D7) : IsIntegral ℤ (D.host.sqd) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, CS.s_sq]
  simp

theorem coord_of_OK (D : D7) (w : 𝓞 D.host.K) (a b' : ℚ)
    (hw : (((w : D.host.K)) : D.host.E) = (a : D.host.E) + (b' : D.host.E) * D.host.sqd) :
    (∃ z : ℤ, 2 * a = z) ∧ (∃ z : ℤ, 2 * D.host.d * b' = z) := by
  have hI : IsIntegral ℤ (((w : D.host.K)) : D.host.E) := by
    have h0 : IsIntegral ℤ (w : D.host.K) := w.2
    exact h0.map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  have hc : IsIntegral ℤ (D.host.conj (((w : D.host.K)) : D.host.E)) :=
    hI.map ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)
  have hb := bE_isIntegral D
  have hcw : D.host.conj (((w : D.host.K)) : D.host.E) =
      (a : D.host.E) - (b' : D.host.E) * D.host.sqd := by
    rw [hw, map_add, map_mul, map_ratCast, map_ratCast, G0.conj_b]; ring
  constructor
  · apply int_of_isIntegral D
    have e : ((2 * a : ℚ) : D.host.E) = (((w : D.host.K)) : D.host.E) + D.host.conj (((w : D.host.K)) : D.host.E) := by
      rw [hcw, hw]; push_cast; ring
    rw [e]; exact hI.add hc
  · apply int_of_isIntegral D
    have e : ((2 * D.host.d * b' : ℚ) : D.host.E) =
        -(D.host.sqd * (((w : D.host.K)) : D.host.E) +
          (-D.host.sqd) * D.host.conj (((w : D.host.K)) : D.host.E)) := by
      rw [hcw, hw]; push_cast
      linear_combination (2 * (b' : D.host.E)) * CS.s_sq D
    rw [e]; exact ((hb.mul hI).add (hb.neg.mul hc)).neg

theorem okK_of_int (D : D7) (m1 m2 : ℤ) : ∃ w : 𝓞 D.host.K,
    (((w : D.host.K)) : D.host.E) = (m1 : D.host.E) + (m2 : D.host.E) * D.host.sqd := by
  let bK : D.host.K := ⟨D.host.sqd, FL.bE_mem D⟩
  have hbK : IsIntegral ℤ bK := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) := (algebraMap D.host.K D.host.E).injective
    rw [← isIntegral_algHom_iff _ hinj]
    exact bE_isIntegral D
  let bO : 𝓞 D.host.K := ⟨bK, hbK⟩
  refine ⟨(m1 : 𝓞 D.host.K) + (m2 : 𝓞 D.host.K) * bO, ?_⟩
  have e : ((((m1 : 𝓞 D.host.K) + (m2 : 𝓞 D.host.K) * bO : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K ((m1 : 𝓞 D.host.K) + (m2 : 𝓞 D.host.K) * bO)) := rfl
  rw [e]
  simp only [map_add, map_mul, map_intCast]
  rfl

theorem okK_mul_mem (D : D7) (κ : 𝓞 D.host.K) {z : D.host.E} (hz : z ∈ AAs D) :
    (((κ : D.host.K)) : D.host.E) * z ∈ AAs D := by
  have hI : IsIntegral ℤ (((κ : D.host.K)) : D.host.E) := by
    have h0 : IsIntegral ℤ (κ : D.host.K) := κ.2
    exact h0.map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  have := Submodule.smul_mem (AAs D) (⟨(((κ : D.host.K)) : D.host.E), hI⟩ : 𝓞 D.host.E) hz
  exact this

theorem nat_mul_mem (D : D7) (n : ℕ) {z : D.host.E} (hz : z ∈ AAs D) : (n : D.host.E) * z ∈ AAs D := by
  have := nsmul_mem hz n
  rwa [nsmul_eq_mul] at this

theorem trace_K_mul (D : D7) (κ : D.host.K) (z : D.host.E) :
    Algebra.trace D.host.K D.host.E ((κ : D.host.E) * z) = κ * Algebra.trace D.host.K D.host.E z := by
  rw [show (κ : D.host.E) = algebraMap D.host.K D.host.E κ from rfl, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem trace_rat_mul (D : D7) (r : ℚ) (z : D.host.E) :
    Algebra.trace D.host.K D.host.E ((r : D.host.E) * z) = (r : D.host.K) * Algebra.trace D.host.K D.host.E z := by
  rw [← map_ratCast (algebraMap D.host.K D.host.E) r, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem tr_pos (D : D7) (x : D.host.E) (hx : x ≠ 0) :
    ∃ q : ℚ, 0 < q ∧ Algebra.trace D.host.K D.host.E (x * D.host.conj x) = ((q : ℚ) : D.host.K) := by
  have hφ : D.host.φ₀ ((G0.hK D x x : D.host.K) : D.host.E)
      = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
    rw [← FL.sum_tau_trace]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, CU.emb_conj, Complex.mul_conj]
  have hpos : 0 < ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) := by
    haveI := G0.tau_nonempty D
    exact Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ((map_ne_zero _).2 hx)) Finset.univ_nonempty
  obtain ⟨p, q, e⟩ := CS.K_repr D _ (G0.hK D x x).2
  have hs := IO.sqrt_d_pos D
  rw [e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
  have him := congrArg Complex.im hφ
  have hre := congrArg Complex.re hφ
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
  have hq : (q : ℝ) = 0 := by
    have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hs.ne'
  have hq' : q = 0 := by exact_mod_cast hq
  have hp : (0 : ℝ) < (p : ℝ) := by rw [hq] at hre; linarith
  have hp' : 0 < p := by exact_mod_cast hp
  have hKp : G0.hK D x x = ((p : ℚ) : D.host.K) := by
    apply Subtype.ext
    rw [e, hq']
    show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
    rw [map_ratCast]; simp
  exact ⟨p, hp', hKp⟩

section tE
variable (D : D7)

theorem tE_add_l (y y' z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E ((y + y') * D.host.conj z) : D.host.K) : D.host.E) =
      (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) +
        (Algebra.trace D.host.K D.host.E (y' * D.host.conj z) : D.host.E) := by
  rw [add_mul, map_add, IntermediateField.coe_add]

theorem tE_add_r (y z z' : D.host.E) :
    ((Algebra.trace D.host.K D.host.E (y * D.host.conj (z + z')) : D.host.K) : D.host.E) =
      (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) +
        (Algebra.trace D.host.K D.host.E (y * D.host.conj z') : D.host.E) := by
  rw [map_add, mul_add, map_add, IntermediateField.coe_add]

theorem tE_mul_l (κ : D.host.K) (y z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E ((κ : D.host.E) * y * D.host.conj z) : D.host.K) : D.host.E) =
      (κ : D.host.E) * (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) := by
  rw [mul_assoc, trace_K_mul, IntermediateField.coe_mul]

theorem tE_mul_r (κ : D.host.K) (y z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E (y * D.host.conj ((κ : D.host.E) * z)) : D.host.K) : D.host.E) =
      D.host.conj (κ : D.host.E) * (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) := by
  have e : y * D.host.conj ((κ : D.host.E) * z) = ((G0.cK D κ : D.host.K) : D.host.E) * (y * D.host.conj z) := by
    rw [map_mul]; show _ = D.host.conj (κ : D.host.E) * _; ring
  rw [e, trace_K_mul, IntermediateField.coe_mul]
  rfl

theorem tE_swap (y z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E (z * D.host.conj y) : D.host.K) : D.host.E) =
      D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.K) : D.host.E) := by
  have := (G0.herm D).symm y z
  simp only [G0.hK] at this
  rw [this]
  rfl

end tE

def InC (D : D7) (p : ℕ) {k : ℕ} (e : Fin k → D.host.E) (z : D.host.E) : Prop :=
  (∃ t : ℕ, Nat.Coprime t p ∧ (t : D.host.E) * z ∈ AAs D) ∧
    ∀ i, Algebra.trace D.host.K D.host.E (z * D.host.conj (e i)) = 0

section compl

variable (D : D7) (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (e : Fin k → D.host.E)

theorem InC_add {x y : D.host.E} (hx : InC D p e x) (hy : InC D p e y) : InC D p e (x + y) := by
  obtain ⟨⟨t, ht, htx⟩, hxo⟩ := hx
  obtain ⟨⟨t', ht', hty⟩, hyo⟩ := hy
  refine ⟨⟨t * t', Nat.Coprime.mul ht ht', ?_⟩, fun i => ?_⟩
  · have e1 : ((t * t' : ℕ) : D.host.E) * (x + y) = (t' : D.host.E) * ((t : D.host.E) * x) + (t : D.host.E) * ((t' : D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (nat_mul_mem D t' htx) (nat_mul_mem D t hty)
  · rw [add_mul, map_add, hxo i, hyo i, add_zero]

theorem InC_bE {v : D.host.E} (hv : InC D p e v) : InC D p e (D.host.sqd * v) := by
  obtain ⟨⟨t, ht, htv⟩, hvo⟩ := hv
  refine ⟨⟨t, ht, ?_⟩, fun i => ?_⟩
  · have e1 : (t : D.host.E) * (D.host.sqd * v) = D.host.sqd * ((t : D.host.E) * v) := by ring
    rw [e1]
    have := Submodule.smul_mem (AAs D) (⟨D.host.sqd, bE_isIntegral D⟩ : 𝓞 D.host.E) htv
    exact this
  · have e1 : D.host.sqd * v * D.host.conj (e i) =
        (((⟨D.host.sqd, FL.bE_mem D⟩ : D.host.K)) : D.host.E) * (v * D.host.conj (e i)) := by
      show _ = D.host.sqd * _
      ring
    rw [e1, trace_K_mul, hvo i, mul_zero]

variable (u : Fin k → ℚ)

def cf (w : D.host.E) (i : Fin k) : D.host.K := Algebra.trace D.host.K D.host.E (w * D.host.conj (e i)) / (u i : D.host.K)

def oprj (w : D.host.E) : D.host.E := w - ∑ i, ((cf D e u w i : D.host.K) : D.host.E) * e i

variable {D e u}

theorem oprj_orth (h2 : ∀ i j, i ≠ j → Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) = 0)
    (hu : ∀ i, 0 < u i ∧ Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u i : ℚ) : D.host.K))
    (w : D.host.E) (j : Fin k) : Algebra.trace D.host.K D.host.E (oprj D e u w * D.host.conj (e j)) = 0 := by
  unfold oprj
  rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  have h1 : ∀ i, Algebra.trace D.host.K D.host.E ((cf D e u w i : D.host.E) * e i * D.host.conj (e j)) =
      cf D e u w i * Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) := by
    intro i; rw [mul_assoc, trace_K_mul]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_eq_single j]
  · rw [(hu j).2, cf, div_mul_cancel₀ _ (Rat.cast_ne_zero.2 (hu j).1.ne'), sub_self]
  · intro i _ hij; rw [h2 i j hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem oprj_pair {x : D.host.E} (hxo : ∀ i, Algebra.trace D.host.K D.host.E (x * D.host.conj (e i)) = 0) (w : D.host.E) :
    Algebra.trace D.host.K D.host.E (x * D.host.conj w) = Algebra.trace D.host.K D.host.E (x * D.host.conj (oprj D e u w)) := by
  unfold oprj
  rw [map_sub, mul_sub, map_sub, map_sum, Finset.mul_sum, map_sum]
  have h1 : ∀ i, Algebra.trace D.host.K D.host.E (x * D.host.conj ((cf D e u w i : D.host.E) * e i)) = 0 := by
    intro i
    have e1 : x * D.host.conj ((cf D e u w i : D.host.E) * e i) =
        ((G0.cK D (cf D e u w i) : D.host.K) : D.host.E) * (x * D.host.conj (e i)) := by
      rw [map_mul]; show _ = D.host.conj ((cf D e u w i : D.host.E)) * _; ring
    rw [e1, trace_K_mul, hxo i, mul_zero]
  rw [Finset.sum_eq_zero (fun i _ => h1 i), sub_zero]

theorem oprj_mp (s : Fin k → ℕ) (hs : ∀ i, Nat.Coprime (s i) p) (hsm : ∀ i, (s i : D.host.E) * e i ∈ AAs D)
    (hu : ∀ i, 0 < u i ∧ ¬ (p : ℤ) ∣ (u i).num ∧ ¬ p ∣ (u i).den ∧
      Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u i : ℚ) : D.host.K))
    (w : D.host.E) (hw : w ∈ AAs D) : ∃ t : ℕ, Nat.Coprime t p ∧ (t : D.host.E) * oprj D e u w ∈ AAs D := by
  have hpp : p.Prime := hp.out
  have hint : ∀ j, ∃ ω : 𝓞 D.host.K, (ω : D.host.K) =
      (s j : D.host.K) * Algebra.trace D.host.K D.host.E (w * D.host.conj (e j)) := by
    intro j
    obtain ⟨ω, hω⟩ := (factMMUnimodular D.R D.host w).1 hw _ (hsm j)
    refine ⟨ω, ?_⟩
    have e1 : ((ω : D.host.K)) = algebraMap (𝓞 D.host.K) D.host.K ω := rfl
    have e2 : D.host.conj ((s j : D.host.E) * e j) = (s j : D.host.E) * D.host.conj (e j) := by
      rw [map_mul, map_natCast]
    rw [e1, hω, e2, mul_left_comm, trace_natCast_mul]
  choose ω hω using hint
  let n : Fin k → ℕ := fun i => (u i).num.toNat
  have hnZ : ∀ i, ((n i : ℕ) : ℤ) = (u i).num := fun i => Int.toNat_of_nonneg (Rat.num_pos.2 (hu i).1).le
  have hn0 : ∀ i, n i ≠ 0 := by
    intro i h0
    have h1 := hnZ i
    rw [h0, Nat.cast_zero] at h1
    exact (Rat.num_pos.2 (hu i).1).ne h1
  have hncop : ∀ i, Nat.Coprime (n i) p := by
    intro i
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro hd
    apply (hu i).2.1
    rw [← hnZ i]
    exact Int.natCast_dvd_natCast.2 hd
  have hu' : ∀ i, (u i : D.host.K) = (n i : D.host.K) / ((u i).den : D.host.K) := by
    intro i
    have h1 : ((n i : ℚ)) = ((u i).num : ℚ) := by exact_mod_cast hnZ i
    have h2 : (n i : ℚ) / ((u i).den : ℚ) = u i := by rw [h1]; exact Rat.num_div_den (u i)
    conv_lhs => rw [← h2]
    push_cast
    ring
  set t := ∏ j, (s j * s j * n j) with htdef
  have hdv : ∀ j, s j * s j * n j ∣ t := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨t, Nat.Coprime.prod_left (fun j _ => Nat.Coprime.mul (Nat.Coprime.mul (hs j) (hs j)) (hncop j)), ?_⟩
  let κ : Fin k → 𝓞 D.host.K := fun j => ω j * (((u j).den : ℕ) : 𝓞 D.host.K) * ((t / (s j * s j * n j) : ℕ) : 𝓞 D.host.K)
  have hterm : ∀ j, (t : D.host.E) * (((cf D e u w j : D.host.K) : D.host.E) * e j) =
      (((κ j : D.host.K)) : D.host.E) * ((s j : D.host.E) * e j) := by
    intro j
    have hs0 : (s j : D.host.K) ≠ 0 := by
      have : s j ≠ 0 := by
        intro h0; have := hs j; rw [h0, Nat.coprime_zero_left] at this; exact hpp.one_lt.ne' this
      exact_mod_cast this
    have hn0' : (n j : D.host.K) ≠ 0 := by exact_mod_cast hn0 j
    have hd0 : (((u j).den : ℕ) : D.host.K) ≠ 0 := by exact_mod_cast (u j).den_nz
    have hκ : (κ j : D.host.K) = (ω j : D.host.K) * ((u j).den : D.host.K) * ((t / (s j * s j * n j) : ℕ) : D.host.K) := by
      show algebraMap (𝓞 D.host.K) D.host.K _ = _
      rw [map_mul, map_mul, map_natCast, map_natCast]
    have hsn : ((t / (s j * s j * n j) : ℕ) : D.host.K) * ((s j : D.host.K) * (s j : D.host.K) * (n j : D.host.K)) = (t : D.host.K) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, Nat.div_mul_cancel (hdv j)]
    have hK : (t : D.host.K) * cf D e u w j = (κ j : D.host.K) * (s j : D.host.K) := by
      rw [hκ, cf, hu' j, ← hsn]
      have hw' : Algebra.trace D.host.K D.host.E (w * D.host.conj (e j)) = (ω j : D.host.K) / (s j : D.host.K) := by
        rw [hω j]; field_simp
      rw [hw']
      field_simp
    have hKE := congrArg (fun z : D.host.K => (z : D.host.E)) hK
    have hnat : ∀ m : ℕ, (((m : D.host.K)) : D.host.E) = (m : D.host.E) :=
      fun m => map_natCast (algebraMap D.host.K D.host.E) m
    simp only [IntermediateField.coe_mul, hnat] at hKE
    rw [← mul_assoc, hKE, mul_assoc]
  have e1 : (t : D.host.E) * oprj D e u w = (t : D.host.E) * w - ∑ j, (((κ j : D.host.K)) : D.host.E) * ((s j : D.host.E) * e j) := by
    unfold oprj
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  rw [e1]
  exact sub_mem (nat_mul_mem D t hw) (Submodule.sum_mem _ (fun j _ => okK_mul_mem D (κ j) (hsm j)))

end compl

theorem coeK_nat (D : D7) (m : ℕ) : (((m : D.host.K)) : D.host.E) = (m : D.host.E) :=
  map_natCast (algebraMap D.host.K D.host.E) m

theorem coeK_rat (D : D7) (r : ℚ) : (((r : D.host.K)) : D.host.E) = (r : D.host.E) :=
  map_ratCast (algebraMap D.host.K D.host.E) r

theorem tE_bmul_l (D : D7) (y z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E (D.host.sqd * y * D.host.conj z) : D.host.K) : D.host.E) =
      D.host.sqd * (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) :=
  tE_mul_l D ⟨D.host.sqd, FL.bE_mem D⟩ y z

theorem tE_bmul_r (D : D7) (y z : D.host.E) :
    ((Algebra.trace D.host.K D.host.E (y * D.host.conj (D.host.sqd * z)) : D.host.K) : D.host.E) =
      D.host.conj (D.host.sqd) * (Algebra.trace D.host.K D.host.E (y * D.host.conj z) : D.host.E) :=
  tE_mul_r D ⟨D.host.sqd, FL.bE_mem D⟩ y z

theorem div_mem (D : D7) (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (e : Fin k → D.host.E) (u : Fin k → ℚ)
    (hpd : Nat.Coprime (2 * D.host.d) p)
    (s : Fin k → ℕ) (hs : ∀ i, Nat.Coprime (s i) p) (hsm : ∀ i, (s i : D.host.E) * e i ∈ AAs D)
    (h2 : ∀ i j, i ≠ j → Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) = 0)
    (hu : ∀ i, 0 < u i ∧ ¬ (p : ℤ) ∣ (u i).num ∧ ¬ p ∣ (u i).den ∧
      Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u i : ℚ) : D.host.K))
    (hPZ : ∀ z, InC D p e z → ∃ q : ℚ, Algebra.trace D.host.K D.host.E (z * D.host.conj z) = ((q : ℚ) : D.host.K) ∧ PZ p q)
    {x : D.host.E} (hx : InC D p e x) : InC D p e (x * (p : D.host.E)⁻¹) := by
  obtain ⟨⟨s0, hs0, hx0⟩, hxo⟩ := hx
  have hxC : InC D p e x := ⟨⟨s0, hs0, hx0⟩, hxo⟩
  have hpinv : x * (p : D.host.E)⁻¹ = (((p : ℚ)⁻¹ : ℚ) : D.host.E) * x := by push_cast; ring
  refine ⟨⟨2 * D.host.d * s0, Nat.Coprime.mul hpd hs0, ?_⟩, fun i => ?_⟩
  swap
  · rw [hpinv, mul_assoc, trace_rat_mul, hxo i, mul_zero]
  apply (factMMUnimodular D.R D.host _).2
  intro w hw
  have hvC : InC D p e (oprj D e u w) :=
    ⟨oprj_mp p s hs hsm hu w hw, oprj_orth h2 (fun i => ⟨(hu i).1, (hu i).2.2.2⟩) w⟩
  have hT : Algebra.trace D.host.K D.host.E (x * D.host.conj w) =
      Algebra.trace D.host.K D.host.E (x * D.host.conj (oprj D e u w)) := oprj_pair hxo w
  obtain ⟨α, β, hαβ⟩ := CS.K_repr D
    ((Algebra.trace D.host.K D.host.E (x * D.host.conj (oprj D e u w)) : D.host.K) : D.host.E)
    (Algebra.trace D.host.K D.host.E (x * D.host.conj (oprj D e u w))).2
  obtain ⟨qx, hqx, px⟩ := hPZ x hxC
  obtain ⟨qv, hqv, pv⟩ := hPZ _ hvC
  obtain ⟨q1, hq1, p1⟩ := hPZ _ (InC_add D p e hxC hvC)
  obtain ⟨q2, hq2, p2⟩ := hPZ _ (InC_add D p e hxC (InC_bE D p e hvC))
  have hcT : D.host.conj ((Algebra.trace D.host.K D.host.E (x * D.host.conj (oprj D e u w)) : D.host.K) : D.host.E) =
      (α : D.host.E) - (β : D.host.E) * D.host.sqd := by
    rw [hαβ, map_add, map_mul, map_ratCast, map_ratCast, G0.conj_b]; ring
  have hcb : D.host.conj (D.host.sqd) = -D.host.sqd := G0.conj_b D
  have hsq : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) := CS.s_sq D

  have ex1 : ((q1 : ℚ) : D.host.E) = (qx : D.host.E) + (qv : D.host.E) + 2 * (α : D.host.E) := by
    have h := congrArg (fun z : D.host.K => (z : D.host.E)) hq1
    rw [tE_add_l, tE_add_r, tE_add_r, tE_swap D x (oprj D e u w), hqx, hqv, coeK_rat, coeK_rat, coeK_rat, hcT, hαβ] at h
    linear_combination -h
  have ex2 : ((q2 : ℚ) : D.host.E) = (qx : D.host.E) + (D.host.d : D.host.E) * (qv : D.host.E) +
      2 * (D.host.d : D.host.E) * (β : D.host.E) := by
    have h := congrArg (fun z : D.host.K => (z : D.host.E)) hq2
    rw [tE_add_l, tE_add_r, tE_add_r, tE_bmul_r, tE_bmul_l, tE_bmul_l, tE_bmul_r, tE_swap D x (oprj D e u w), hqx, hqv,
      coeK_rat, coeK_rat, coeK_rat, hcT, hαβ, hcb] at h
    linear_combination -h - (2 * (β : D.host.E) + (qv : D.host.E)) * hsq
  have r1 : 2 * α = q1 - qx - qv := by
    apply Rat.cast_injective (α := D.host.E)
    push_cast
    linear_combination -ex1
  have r2 : 2 * (D.host.d : ℚ) * β = q2 - qx - (D.host.d : ℤ) * qv := by
    apply Rat.cast_injective (α := D.host.E)
    push_cast
    linear_combination -ex2
  have pA : PZ p (2 * α) := by rw [r1]; exact PZ_sub p (PZ_sub p p1 px) pv
  have pB : PZ p (2 * (D.host.d : ℚ) * β) := by rw [r2]; exact PZ_sub p (PZ_sub p p2 px) (PZ_zmul p _ pv)

  obtain ⟨ω, hω⟩ := (factMMUnimodular D.R D.host _).1 hx0 w hw
  have e3 : (((ω : D.host.K)) : D.host.E) = ((s0 * α : ℚ) : D.host.E) + ((s0 * β : ℚ) : D.host.E) * D.host.sqd := by
    have h := congrArg (fun z : D.host.K => (z : D.host.E)) hω
    rw [show (((ω : D.host.K)) : D.host.E) = ((algebraMap (𝓞 D.host.K) D.host.K ω : D.host.K) : D.host.E) from rfl, h,
      mul_assoc, trace_natCast_mul, hT, IntermediateField.coe_mul, coeK_nat, hαβ]
    push_cast
    ring
  obtain ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ := coord_of_OK D ω (s0 * α) (s0 * β) e3
  have pm1 : (p : ℤ) ∣ m1 := by
    apply PZ_int p
    rw [← hm1]
    have := PZ_zmul p (s0 : ℤ) pA
    convert this using 1
    push_cast; ring
  have pm2 : (p : ℤ) ∣ m2 := by
    apply PZ_int p
    rw [← hm2]
    have := PZ_zmul p (s0 : ℤ) pB
    convert this using 1
    push_cast; ring
  obtain ⟨a1, ha1⟩ := pm1
  obtain ⟨a2, ha2⟩ := pm2
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have ea1 : (a1 : ℚ) = 2 * (s0 * α) / p := by
    have h' : (m1 : ℚ) = (p : ℚ) * a1 := by exact_mod_cast ha1
    rw [hm1, h']; field_simp
  have ea2 : (a2 : ℚ) = 2 * D.host.d * (s0 * β) / p := by
    have h' : (m2 : ℚ) = (p : ℚ) * a2 := by exact_mod_cast ha2
    rw [hm2, h']; field_simp
  obtain ⟨ω', hω'⟩ := okK_of_int D (D.host.d * a1) a2
  refine ⟨ω', ?_⟩
  apply Subtype.ext
  show (((ω' : D.host.K)) : D.host.E) = _
  rw [hω']
  have eq1 : ((2 * D.host.d * s0 : ℕ) : D.host.E) * (x * (p : D.host.E)⁻¹) * D.host.conj w =
      ((2 * D.host.d * s0 / p : ℚ) : D.host.E) * (x * D.host.conj w) := by
    push_cast; ring
  rw [eq1, trace_rat_mul, IntermediateField.coe_mul, coeK_rat, hT, hαβ]
  have ha1E : ((a1 : ℤ) : D.host.E) = ((2 * (s0 * α) / p : ℚ) : D.host.E) := by
    rw [← ea1]; push_cast; rfl
  have ha2E : ((a2 : ℤ) : D.host.E) = ((2 * D.host.d * (s0 * β) / p : ℚ) : D.host.E) := by
    rw [← ea2]; push_cast; rfl
  push_cast
  rw [ha1E, ha2E]
  push_cast
  ring

theorem gram_schmidt_unit_vector : UnitVec := by
  intro D p _ hp5 hin k e h1 h2 h3 hk
  have hpp : p.Prime := Fact.out
  have hpd : Nat.Coprime (2 * D.host.d) p := by
    have hd : ¬ p ∣ D.host.d := by
      intro hd
      have h0 : (-(D.host.d : ℤ)) % (p : ℤ) = 0 :=
        Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.2 hd).neg_right
      rw [jacobiSym.mod_left, h0, jacobiSym.zero_left hpp.one_lt] at hin
      norm_num at hin
    have h2' : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    rcases hpp.dvd_mul.1 h with h | h
    · exact h2' h
    · exact hd h
  choose u hu using h3
  choose s hs hsm using h1
  by_contra hcon

  have hval : ∀ z, InC D p e z → z ≠ 0 → ∃ q : ℚ, 0 < q ∧
      Algebra.trace D.host.K D.host.E (z * D.host.conj z) = ((q : ℚ) : D.host.K) ∧ Zp p q := by
    intro z hzC hz
    obtain ⟨⟨t, ht, htz⟩, -⟩ := hzC
    obtain ⟨q, hq, hqe⟩ := tr_pos D z hz
    refine ⟨q, hq, hqe, ?_⟩
    obtain ⟨ω, hω⟩ := (factMMUnimodular D.R D.host _).1 htz _ htz
    have e1 : (((ω : D.host.K)) : D.host.E) = ((t * t * q : ℚ) : D.host.E) := by
      have h := congrArg (fun y : D.host.K => (y : D.host.E)) hω
      rw [show (((ω : D.host.K)) : D.host.E) = ((algebraMap (𝓞 D.host.K) D.host.K ω : D.host.K) : D.host.E) from rfl, h,
        show D.host.conj ((t : D.host.E) * z) = (t : D.host.E) * D.host.conj z by rw [map_mul, map_natCast],
        show (t : D.host.E) * z * ((t : D.host.E) * D.host.conj z) = (t : D.host.E) * ((t : D.host.E) * (z * D.host.conj z)) by ring,
        trace_natCast_mul, trace_natCast_mul, hqe, IntermediateField.coe_mul, IntermediateField.coe_mul, coeK_nat, coeK_rat]
      push_cast
      ring
    have hI : IsIntegral ℤ (((ω : D.host.K)) : D.host.E) := by
      have h0 : IsIntegral ℤ (ω : D.host.K) := ω.2
      exact h0.map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    obtain ⟨m, hm⟩ := int_of_isIntegral D (t * t * q) (by rw [← e1]; exact hI)
    have ht0 : t ≠ 0 := by
      intro h0; have := ht; rw [h0, Nat.coprime_zero_left] at this; exact hpp.one_lt.ne' this
    have ht0' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0
    refine ⟨m, t * t, fun h => (hpp.dvd_mul.1 h).elim (fun h' => ?_) (fun h' => ?_), ?_⟩
    · exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.1 ht) h')
    · exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.1 ht) h')
    · rw [← hm]; push_cast; field_simp

  have hPZ : ∀ z, InC D p e z → ∃ q : ℚ,
      Algebra.trace D.host.K D.host.E (z * D.host.conj z) = ((q : ℚ) : D.host.K) ∧ PZ p q := by
    intro z hzC
    by_cases hz : z = 0
    · exact ⟨0, by simp [hz], PZ_zero p⟩
    · obtain ⟨q, hq, hqe, hZ⟩ := hval z hzC hz
      rcases unit_or_PZ p hZ with h | h
      · exact absurd ⟨z, hzC.1, hzC.2, q, hq, h.1, h.2, hqe⟩ hcon
      · exact ⟨q, hqe, h⟩
  have hdiv : ∀ x, InC D p e x → InC D p e (x * (p : D.host.E)⁻¹) :=
    fun x hx => div_mem D p e u hpd s hs hsm h2 hu hPZ hx

  have hne : ∃ x0, InC D p e x0 ∧ x0 ≠ 0 := by
    by_contra hno
    push Not at hno
    have hall : ∀ y ∈ AAs D, oprj D e u y = 0 := fun y hy =>
      hno _ ⟨oprj_mp p s hs hsm hu y hy, oprj_orth h2 (fun i => ⟨(hu i).1, (hu i).2.2.2⟩) y⟩
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ AAs D, a ≠ 0 := by
      by_contra hz
      push Not at hz
      have h1mem : (1 : D.host.E) ∈ AAs D := (factMMUnimodular D.R D.host 1).2 (fun y hy => by
        rw [hz y hy, map_zero, mul_zero, map_zero]
        exact ⟨0, map_zero _⟩)
      exact one_ne_zero (hz 1 h1mem)
    have hW : ∀ y ∈ AAs D, y ∈ Submodule.span D.host.K (Set.range e) := by
      intro y hy
      have h0 := hall y hy
      unfold oprj at h0
      rw [sub_eq_zero] at h0
      rw [h0]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      have : ((cf D e u y i : D.host.K) : D.host.E) * e i = cf D e u y i • e i := by
        rw [Algebra.smul_def]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have htop : Submodule.span D.host.K (Set.range e) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      have hz : z = ∑ i, (integralBasis D.host.E).repr (a⁻¹ * z) i • (a * integralBasis D.host.E i) := by
        conv_lhs => rw [← mul_inv_cancel_left₀ ha0 z, ← (integralBasis D.host.E).sum_repr (a⁻¹ * z)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_smul_comm]
      rw [hz]
      refine Submodule.sum_mem _ (fun i _ => Submodule.smul_of_tower_mem _ _ (hW _ ?_))
      rw [integralBasis_apply, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha
    have h1 := finrank_range_le_card (R := D.host.K) e
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨x0, hx0C, hx0⟩ := hne
  have hallC : ∀ j : ℕ, InC D p e (x0 * ((p : D.host.E) ^ j)⁻¹) := by
    intro j
    induction j with
    | zero => simpa using hx0C
    | succ j ih =>
      have := hdiv _ ih
      rwa [mul_assoc, ← mul_inv, ← pow_succ] at this
  obtain ⟨q0, hq0, hq0e, -⟩ := hval x0 hx0C hx0
  apply Zp_div_pow p hq0
  intro j
  have hp0 : (p : D.host.E) ≠ 0 := by exact_mod_cast hpp.ne_zero
  obtain ⟨qj, -, hqje, hZ⟩ := hval _ (hallC j) (mul_ne_zero hx0 (inv_ne_zero (pow_ne_zero _ hp0)))
  have hq : qj = q0 / (p : ℚ) ^ (2 * j) := by
    apply Rat.cast_injective (α := D.host.K)
    rw [← hqje]
    have e1 : x0 * ((p : D.host.E) ^ j)⁻¹ * D.host.conj (x0 * ((p : D.host.E) ^ j)⁻¹) =
        ((((p : ℚ) ^ (2 * j))⁻¹ : ℚ) : D.host.E) * (x0 * D.host.conj x0) := by
      rw [map_mul, map_inv₀, map_pow, map_natCast]
      push_cast
      ring
    rw [e1, trace_rat_mul, hq0e]
    push_cast
    ring
  rw [hq] at hZ
  exact hZ

end unit

end Formalism.L2.KerInert.MMOnb

namespace Formalism.L2.KerInert

theorem one_theta_orthonormal : OneCopyOrth := MMOnb.oneCopyOrth_of MMOnb.gram_schmidt_unit_vector

theorem global_orthonormal_basis_four : GlobONB := MMOnb.globONB_of one_theta_orthonormal

end Formalism.L2.KerInert
