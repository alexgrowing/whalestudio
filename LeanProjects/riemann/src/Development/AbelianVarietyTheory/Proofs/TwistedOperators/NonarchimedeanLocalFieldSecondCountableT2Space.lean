import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise

namespace GlobalTheory.RootExchangeFixed

section alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem lowU_neg_mul (C : Matrix (Fin c) n k) : lowU (-C) * lowU C = 1 := by
  ext1
  simp [lowU, fromBlocks_multiply]

theorem conj_val (C : Matrix (Fin c) n k) (B : Matrix n (Fin c) k) (h : B * C = 0) :
    (lowU C * upU B * lowU (-C)).val = fromBlocks 1 B 0 (C * B + 1) := by
  simp [lowU, upU, fromBlocks_multiply, h, Matrix.add_mul, Matrix.mul_assoc]

theorem exists_conj (h1 : 1 ≤ p) (hc : p < c) (u β : n → k) :
    ∃ g ∈ N k n c p, simpleSum g = ∑ r, u r * β r ∧
      rowE c p u * colE c (p + 1) β = g * rowE c p u := by
  set C : Matrix (Fin c) n k := Matrix.of fun l s => if l.val + 1 = p then u s else 0 with hC
  set B : Matrix n (Fin c) k := Matrix.of fun r i => if i.val + 1 = p + 1 then β r else 0 with hB
  have hBC : B * C = 0 := by
    ext r s
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with a b
    · omega
    all_goals simp
  have hCB : ∀ l i, (C * B) l i = if l.val + 1 = p ∧ i.val = p then ∑ r, u r * β r else 0 := by
    intro l i
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply]
    by_cases a : l.val + 1 = p <;> by_cases b : i.val = p <;> simp [a, b]
  have hv := conj_val C B hBC
  refine ⟨lowU C * upU B * lowU (-C), Subgroup.subset_closure ?_, ?_, ?_⟩
  · intro r s hrs
    rw [hv]
    rcases r with r | r <;> rcases s with s | s
    · simp [Matrix.one_apply]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₁₂, hB, Matrix.of_apply]
      rw [if_neg (by omega)]; simp
    · simp
    · simp only [lev, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
      rw [if_neg (by omega)]; simp [Matrix.one_apply]
  · unfold simpleSum
    rw [hv]
    simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
    rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), Finset.sum_eq_single (⟨p, hc⟩ : Fin c)]
    · rw [if_pos (by simp; omega), if_pos (by simp; omega), Matrix.one_apply_ne, add_zero]
      intro h
      have := congrArg Fin.val h
      simp at this; omega
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      ext
      simp at h ⊢; omega
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with a b
      · exfalso
        apply hi
        ext
        simp; omega
      · rw [Matrix.one_apply_ne, add_zero]
        intro h
        have := congrArg Fin.val h
        omega
      · rfl
    · simp
  · show lowU C * upU B = _ * lowU C
    rw [mul_assoc, lowU_neg_mul, mul_one]

end alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lowU_mem_KO {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix (Fin c) n k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : lowU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix (Fin c) n 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 0 C' 1, fromBlocks 1 0 (-C') 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [lowU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)

theorem upU_mem_KO {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix n (Fin c) k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : upU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix n (Fin c) 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 C' 0 1, fromBlocks 1 (-C') 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [upU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)

theorem nonarchimedeanLocalField_secondCountable_t2Space : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem vanish {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (u : n → k) (r : n) (hr : ¬ valuation k (u r) ≤ valuation k (s : k)) :
    l (σ (rowE c p u) v) = 0 := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  have hu : 0 < valuation k (u r) := hs.trans (not_le.1 hr)
  have hu0 : u r ≠ 0 := by rintro h; simp [h] at hu
  have hx : ¬ valuation k (u r / s) ≤ valuation k ((1 : kˣ) : k) := by
    rw [map_div₀, div_le_iff₀ hs]; simpa using hr
  rw [← hψ] at hx
  push Not at hx
  obtain ⟨y, hy, hy1⟩ := hx
  obtain ⟨g, hg, hsum, hmul⟩ := exists_conj h1 hc u (Pi.single r (y / u r))
  have hfix := hβ (Pi.single r (y / u r)) (by
    intro t
    by_cases ht : t = r
    · subst ht
      rw [map_div₀, le_div_iff₀ hs] at hy
      rw [Pi.single_eq_same, map_mul, map_div₀, div_mul_eq_mul_div, div_le_iff₀ hu, one_mul]
      exact hy
    · simp [Pi.single_eq_of_ne ht])
  have hy' : simpleSum g = y := by
    rw [hsum, Finset.sum_eq_single r]
    · simp only [Pi.single_eq_same]; field_simp
    · intro t _ ht; simp [Pi.single_eq_of_ne ht]
    · simp
  have key : l (σ (rowE c p u) v) = (ψ y : ℂ) * l (σ (rowE c p u) v) := by
    conv_lhs => rw [← hfix]
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply, hl g hg, hy']
  by_contra hne
  apply hy1
  have : (ψ y : ℂ) = 1 := by
    have h2 : (ψ y : ℂ) * l (σ (rowE c p u) v) = 1 * l (σ (rowE c p u) v) := by
      rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hne h2
  exact Circle.ext (by simpa using this)

variable [MeasurableSpace k] [BorelSpace k]

theorem ball_eq (s : kˣ) : {x : k | valuation k x ≤ valuation k (s : k)} = s • (𝒪[k] : Set k) := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show _ ↔ valuation k (((s⁻¹ : kˣ) : k) * x) ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hs, mul_one]
  rfl

theorem meas_ball (s : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (s : k)} := by
  rw [ball_eq]
  refine (IsOpen.smul ?_ s).measurableSet
  exact Valuation.isOpen_integer

theorem vol_ball (ν : Measure k) (hν : IsUnitVol ν) (s : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (s : k)} = ENNReal.ofReal (nabs k s) := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  rw [ball_eq, ← distribHaarChar_mul ν s, hν.2, nabs]
  simp

theorem exUp_of_fixed {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) (hν : IsUnitVol ν)
    {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (hu : ∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) :
    exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  let S : Set (n → k) := Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k (s : k)}
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => meas_ball s
  have hf : (fun u : n → k => l (σ (rowE c p u) v)) = S.indicator fun _ => l v := by
    funext u
    by_cases h : u ∈ S
    · rw [Set.indicator_of_mem h, hu u fun r => h r trivial]
    · rw [Set.indicator_of_notMem h]
      simp only [S, Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
      obtain ⟨r, hr⟩ := h
      exact vanish h1 hc hψ σ l hl v s hβ u r hr
  have hn : 0 ≤ nabs k s := NNReal.coe_nonneg _
  unfold exUp
  rw [hf, integral_indicator_const _ hS, Measure.real, Measure.pi_pi]
  simp [vol_ball ν hν s, hn]

theorem exUp_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ p σ l) (v : A), (∀ s : kˣ, (∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v) → (∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) → exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v) ∧ ((∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → exUp ν p σ l v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hc ψ hψ ν hν A _ _ σ l hl v
  refine ⟨fun s hβ hu => exUp_of_fixed h1 hc hψ ν hν σ l hl v s hβ hu, fun hK => ?_⟩
  rw [exUp_of_fixed h1 hc hψ ν hν σ l hl v 1]
  · simp [nabs]
  · intro β h
    refine hK _ (upU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h r
    · simp
  · intro u h
    refine hK _ (lowU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h i
    · simp

end GlobalTheory.RootExchangeFixed
