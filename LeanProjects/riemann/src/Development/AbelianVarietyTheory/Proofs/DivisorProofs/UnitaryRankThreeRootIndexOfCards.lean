import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Heis

theorem index_eq_map_mul_ker {A B : Type} [Group A] [Group B] (φ : A →* B) (V : Subgroup A) :
    V.index = (V.map φ).relIndex φ.range * V.relIndex φ.ker := by
  have h1 : (V.map φ).relIndex φ.range = (V ⊔ φ.ker).index := by
    rw [← Subgroup.index_comap, Subgroup.comap_map_eq]
  have h2 : V.relIndex φ.ker = V.relIndex (V ⊔ φ.ker) := by
    refine Nat.card_congr (Equiv.ofBijective
      (Subgroup.quotientSubgroupOfEmbeddingOfLE V (le_sup_right : φ.ker ≤ V ⊔ φ.ker))
      ⟨Function.Embedding.injective _, ?_⟩)
    intro y
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective y
    have hg' : g ∈ ((φ.ker ⊔ V : Subgroup A) : Set A) := by rw [sup_comm]; exact hg
    rw [Subgroup.normal_mul] at hg'
    obtain ⟨a, ha, v, hv, rfl⟩ := hg'
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hv
  rw [h1, h2, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def Heisenberg₂ (σ : L →+* L) (x y : L) : Matrix (Fin 3) (Fin 3) L := !![1, x, y; 0, 1, -σ x; 0, 0, 1]

theorem mem_root_iff (hσ : ∀ x, σ (σ x) = x) (g : GU σ 3) :
    g ∈ rootU σ ![0, 0, 0] ↔ ∃ x y, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y := by
  constructor
  · rintro ⟨hg, -⟩
    have hg : ∀ i j : Fin 3, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 3) (Fin 3) L) i j := hg
    have h1 : cT σ (mat g) * antiJ L 3 * mat g = antiJ L 3 := g.2
    have e00 : mat g 0 0 = 1 := by simpa using hg 0 0 (by decide)
    have e10 : mat g 1 0 = 0 := by simpa using hg 1 0 (by decide)
    have e11 : mat g 1 1 = 1 := by simpa using hg 1 1 (by decide)
    have e20 : mat g 2 0 = 0 := by simpa using hg 2 0 (by decide)
    have e21 : mat g 2 1 = 0 := by simpa using hg 2 1 (by decide)
    have e22 : mat g 2 2 = 1 := by simpa using hg 2 2 (by decide)
    have r0 : (0 : Fin 3).rev = 2 := rfl
    have r1 : (1 : Fin 3).rev = 1 := rfl
    have r2 : (2 : Fin 3).rev = 0 := rfl
    have a := congrFun (congrFun h1 1) 2
    have b := congrFun (congrFun h1 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three] at a b
    simp only [P.fSatake_cTJ, r0, r1, r2, e11, e21, e22, map_one, map_zero] at a b
    have a' : mat g 1 2 = -σ (mat g 0 1) := by
      have : antiJ L 3 1 2 = 0 := by simp [antiJ]
      linear_combination a + this
    have : antiJ L 3 2 2 = 0 := by simp [antiJ]
    rw [a', map_neg, hσ] at b
    refine ⟨mat g 0 1, mat g 0 2, by linear_combination b + this, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, e00, e10, e11, e20, e21, e22, a']
  · rintro ⟨x, y, -, e⟩
    refine ⟨fun i j h => ?_, fun i j h => ?_⟩
    · rw [e]
      fin_cases i <;> fin_cases j <;> simp [Heisenberg₂] at h ⊢
    · fin_cases i <;> fin_cases j <;> simp at h

theorem exists_heis (hσ : ∀ x, σ (σ x) = x) {x y : L} (h : y + σ y + x * σ x = 0) :
    ∃ g : GU σ 3, mat g = Heisenberg₂ σ x y := by
  apply exists_mat
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  simp only [P.fSatake_cTJ, r0, r1, r2]
  fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, antiJ, hσ]
  linear_combination h

theorem mem_int_iff (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ 3) :
    g ∈ KU σ 3 ⊓ rootU σ ![0, 0, 0] ↔
      ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y := by
  rw [Subgroup.mem_inf, mem_root_iff hσ, mem_KU_iff hv]
  constructor
  · rintro ⟨h, x, y, hr, e⟩
    refine ⟨x, ?_, y, ?_, hr, e⟩
    · simpa [e, Heisenberg₂] using h 0 1
    · simpa [e, Heisenberg₂] using h 0 2
  · rintro ⟨x, hx, y, hy, hr, e⟩
    refine ⟨fun i j => ?_, x, y, hr, e⟩
    have hx' : σ x ∈ intL L := by
      show Valued.v (σ x) ≤ 1
      rw [hv]; exact hx
    rw [e]
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, hx, hy, hx', one_mem, zero_mem]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem conj_iff {ϖ : L} (h0 : ϖ ≠ 0) (hϖ : σ ϖ = ϖ) {s : GU σ 3}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, 0, -1] : Fin 3 → ℤ) i)) (g : GU σ 3) (x y : L)
    (e : mat g = Heisenberg₂ σ x y) : mat (s * g * s⁻¹) = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) := by
  have : mat s * mat g = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) * mat s := by
    rw [e, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, hϖ] <;> field_simp
  rw [mat_mul, mat_mul, this, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem heis_mul (x y x' y' : L) :
    Heisenberg₂ σ x y * Heisenberg₂ σ x' y' = Heisenberg₂ σ (x + x') (y + y' - x * σ x') := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [Heisenberg₂] <;> ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem heis_01 (x y : L) : Heisenberg₂ σ x y 0 1 = x := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem heis_02 (x y : L) : Heisenberg₂ σ x y 0 2 = y := rfl

theorem mem_tz (y : L) : y ∈ (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔
    y ∈ intL L ∧ σ y + y = 0 := Iff.rfl

theorem exists_snd {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {x : L} (hx : x ∈ intL L) :
    ∃ y ∈ intL L, y + σ y + x * σ x = 0 := by
  obtain ⟨hσ, hv, -, -, ⟨a, ha, ha1⟩, -⟩ := hU
  have h0 : σ a - a ≠ 0 := by
    intro h; rw [h, map_zero] at ha1; exact zero_ne_one ha1
  have h0' : a - σ a ≠ 0 := fun h => h0 (by linear_combination -h)
  refine ⟨-(σ a / (σ a - a)) * (x * σ x), ?_, ?_⟩
  · show Valued.v (-(σ a / (σ a - a)) * (x * σ x)) ≤ 1
    have hx' : Valued.v x ≤ 1 := hx
    have ha' : Valued.v a ≤ 1 := ha
    rw [map_mul, Valuation.map_neg, map_div₀, ha1, div_one, map_mul, hv, hv]
    exact mul_le_one' ha' (mul_le_one' hx' hx')
  · simp only [map_mul, map_neg, map_div₀, map_sub, hσ]
    field_simp
    ring

theorem indexThree : IntIndex → TraceZeroIndex → IndexThree := by
  intro hI hT L _ _ ϖ σ q hU s hs
  have hI := hI L ϖ σ q hU
  have hT := hT L ϖ σ q hU
  have hsnd := fun x => exists_snd hU (x := x)
  obtain ⟨hσ, hv, hϖ, hvϖ, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    decide
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hTdef
  have mT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  set U := KU σ 3 ⊓ rootU σ ![0, 0, 0] with hUdef
  have mU : ∀ g, g ∈ U ↔ ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y :=
    mem_int_iff hσ hv
  set V := U.map (MulAut.conj s).toMonoidHom with hVdef
  have mV : ∀ g, g ∈ V ↔ ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧
      mat g = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) := by
    intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, y, hy, hr, e⟩ := (mU u).1 hu
      exact ⟨x, hx, y, hy, hr, conj_iff h0 hϖ hs u x y e⟩
    · rintro ⟨x, hx, y, hy, hr, e⟩
      obtain ⟨u, hu⟩ := exists_heis hσ hr
      exact ⟨u, (mU u).2 ⟨x, hx, y, hy, hr, hu⟩, mat_injective ((conj_iff h0 hϖ hs u x y hu).trans e.symm)⟩
  have VU : V ≤ U := by
    intro g hg
    obtain ⟨x, hx, y, hy, hr, e⟩ := (mV g).1 hg
    refine (mU g).2 ⟨_, mul_mem hϖO hx, _, mul_mem hϖO (mul_mem hϖO hy), ?_, e⟩
    simp only [map_mul, hϖ]
    linear_combination ϖ * ϖ * hr
  let φ : U →* Multiplicative L := MonoidHom.mk' (fun g => Multiplicative.ofAdd (mat g.1 0 1)) (by
    intro a b
    obtain ⟨x, -, y, -, -, e⟩ := (mU a).1 a.2
    obtain ⟨x', -, y', -, -, e'⟩ := (mU b).1 b.2
    rw [← ofAdd_add, Subgroup.coe_mul, mat_mul, e, e', heis_mul]
    rfl)
  have hφ : ∀ g, φ g = Multiplicative.ofAdd (mat g.1 0 1) := fun _ => rfl
  have hker : ∀ g : φ.ker, ∃ y ∈ T, mat g.1.1 = Heisenberg₂ σ 0 y := by
    intro g
    obtain ⟨x, -, y, hy, hr, e⟩ := (mU g.1).1 g.1.2
    have : mat g.1.1 0 1 = 0 := g.2
    rw [e, heis_01] at this
    subst this
    exact ⟨y, (mT y).2 ⟨hy, by linear_combination hr⟩, e⟩
  let χ : φ.ker →* Multiplicative L := MonoidHom.mk' (fun g => Multiplicative.ofAdd (mat g.1.1 0 2)) (by
    intro a b
    obtain ⟨y, -, e⟩ := hker a
    obtain ⟨y', -, e'⟩ := hker b
    rw [← ofAdd_add, Subgroup.coe_mul, Subgroup.coe_mul, mat_mul, e, e', heis_mul, heis_02, heis_02, heis_02,
      zero_mul, sub_zero])
  have r1 : φ.range = AddSubgroup.toSubgroup (intL L).toAddSubgroup := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨x, hx, y, -, -, e⟩ := (mU g).1 g.2
      show mat g.1 0 1 ∈ intL L
      rw [e]; exact hx
    · intro hz
      obtain ⟨y, hy, hr⟩ := hsnd z.toAdd hz
      obtain ⟨u, hu⟩ := exists_heis hσ hr
      refine ⟨⟨u, (mU u).2 ⟨_, hz, y, hy, hr, hu⟩⟩, ?_⟩
      rw [hφ, hu]; rfl
  have r2 : (V.subgroupOf U).map φ =
      AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, y, -, -, e⟩ := (mV g).1 hg
      refine ⟨x, hx, ?_⟩
      show ϖ * x = mat g.1 0 1
      rw [e]; rfl
    · rintro ⟨x, hx, hz⟩
      have hz : ϖ * x = z.toAdd := hz
      obtain ⟨y, hy, hr⟩ := hsnd x hx
      have hr' : ϖ * (ϖ * y) + σ (ϖ * (ϖ * y)) + ϖ * x * σ (ϖ * x) = 0 := by
        simp only [map_mul, hϖ]
        linear_combination ϖ * ϖ * hr
      obtain ⟨u, hu⟩ := exists_heis hσ hr'
      have huV : u ∈ V := (mV u).2 ⟨x, hx, y, hy, hr, hu⟩
      refine ⟨⟨u, VU huV⟩, huV, ?_⟩
      rw [hφ, hu, heis_01, hz]; rfl
  have r3 : χ.range = AddSubgroup.toSubgroup T := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, hy, e⟩ := hker g
      show mat g.1.1 0 2 ∈ T
      rw [e]; exact hy
    · intro hz
      obtain ⟨hy, hr⟩ := (mT z.toAdd).1 hz
      have hr' : z.toAdd + σ z.toAdd + 0 * σ 0 = 0 := by linear_combination hr
      obtain ⟨u, hu⟩ := exists_heis hσ hr'
      refine ⟨⟨⟨u, (mU u).2 ⟨_, zero_mem _, _, hy, hr', hu⟩⟩, ?_⟩, ?_⟩
      · show mat u 0 1 = 0
        rw [hu]; rfl
      · show Multiplicative.ofAdd (mat u 0 2) = z
        rw [hu]; rfl
  have r4 : (V.subgroupOf U).subgroupOf φ.ker = (AddSubgroup.toSubgroup
      ((T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft ϖ))).comap χ := by
    ext g
    obtain ⟨w, -, e⟩ := hker g
    constructor
    · intro hg
      obtain ⟨x, hx, y, hy, hr, e'⟩ := (mV g.1.1).1 hg
      have hx0 : ϖ * x = 0 := by rw [← heis_01 (σ := σ) (ϖ * x), ← e', e]; rfl
      have hx0 : x = 0 := (mul_eq_zero.1 hx0).resolve_left h0
      subst hx0
      refine ⟨ϖ * y, ⟨y, (mT y).2 ⟨hy, by linear_combination hr⟩, rfl⟩, ?_⟩
      show ϖ * (ϖ * y) = mat g.1.1 0 2
      rw [e']; rfl
    · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
      have hz : ϖ * (ϖ * y) = mat g.1.1 0 2 := hz
      rw [e, heis_02] at hz
      obtain ⟨hy, hr⟩ := (mT y).1 hy
      exact (mV g.1.1).2 ⟨0, zero_mem _, y, hy, by linear_combination hr, by rw [e, mul_zero, hz]⟩
  have TT : T.map (AddMonoidHom.mulLeft ϖ) ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hy, hr⟩ := (mT y).1 hy
    refine (mT (ϖ * y)).2 ⟨mul_mem hϖO hy, ?_⟩
    rw [map_mul, hϖ]
    linear_combination ϖ * hr
  have r5 : ((T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft ϖ)).relIndex T = q * q := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono TT) TT,
      AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ h0), hT]
  have r6 : (V.subgroupOf U).relIndex φ.ker = q * q := by
    rw [Subgroup.relIndex, r4, Subgroup.index_comap, r3, AddSubgroup.relIndex_toSubgroup, r5]
  rw [Subgroup.relIndex, index_eq_map_mul_ker φ, r6, r1, r2, AddSubgroup.relIndex_toSubgroup, hI]
  ring

end GlobalTheory.SatakeWeyl.Heis

end
