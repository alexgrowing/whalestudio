import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinTypCount

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem countable_field : Countable L :=
  (Module.finBasis ℚ L).equivFun.toEquiv.injective.countable

theorem tmul_mem_ALint (o : 𝓞 L) {a : AFplus L} (ha : ∀ v, a v ∈ v.adicCompletionIntegers L⁺) :
    ((o : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L := by
  have h1 : ((o : L) ⊗ₜ[L⁺] (1 : AFplus L) : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inl ⟨o, rfl⟩)
  have h2 : ((1 : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩)
  have := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

theorem exists_nat_smul_int (e : L) : ∃ D : ℕ, 0 < D ∧ ∃ o : 𝓞 L, (o : L) = D • e := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := L) ({e} : Finset L)
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • e) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h e (Finset.mem_singleton_self e)).smul y
  exact ⟨⟨_, hi⟩, rfl⟩

theorem exists_approx (M : ℕ) (hM : 0 < M) (x : AL L) :
    ∃ c : L, ∃ y ∈ ALint L, x = c ⊗ₜ[L⁺] (1 : AFplus L) + M • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x x' hx hx' =>
    obtain ⟨c, y, hy, rfl⟩ := hx
    obtain ⟨c', y', hy', rfl⟩ := hx'
    exact ⟨c + c', y + y', add_mem hy hy', by rw [TensorProduct.add_tmul, smul_add]; abel⟩
  | tmul e a =>
    obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int e
    obtain ⟨k, a', ha', rfl⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat L⁺ (D * M) (Nat.mul_pos hD hM)).1 a
    refine ⟨algebraMap L⁺ L k * e, _, tmul_mem_ALint o ha', ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one k, ← TensorProduct.smul_tmul,
      ← Algebra.smul_def, ho, TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_comm, mul_smul]
    simp only [TensorProduct.smul_tmul']

theorem exists_denom (x : AL L) : ∃ m : ℕ, 0 < m ∧ (m : AL L) * x ∈ ALint L := by
  obtain ⟨c, y, hy, rfl⟩ := exists_approx 1 one_pos x
  obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int c
  refine ⟨D, hD, ?_⟩
  have e1 : (D : AL L) * (c ⊗ₜ[L⁺] (1 : AFplus L)) = (o : L) ⊗ₜ[L⁺] (1 : AFplus L) := by
    rw [ho, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  rw [mul_add, e1, one_smul]
  exact add_mem (tmul_mem_ALint o (fun v => one_mem _)) (Subring.mul_mem _ (natCast_mem _ _) hy)

variable {n : ℕ}

theorem exists_denom_matrix (G : Matrix (Fin n) (Fin n) (AL L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, (m : AL L) * G i j ∈ ALint L := by
  classical
  choose m hm h using fun p : Fin n × Fin n => exists_denom (G p.1 p.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (h (i, j))

theorem exists_code (N : ℕ) (hN : 0 < N) (g : GAf L n) :
    ∃ p : ℕ × (Fin n → Fin n → L), 0 < p.1 ∧
      (∀ i j, (p.1 : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) ∧
      ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        p.2 i j ⊗ₜ[L⁺] (1 : AFplus L) + (p.1 * N) • y := by
  obtain ⟨m, hm, h⟩ := exists_denom_matrix (g.1 : Matrix (Fin n) (Fin n) (AL L))
  choose c y hy e using fun i j =>
    exists_approx (m * N) (Nat.mul_pos hm hN) ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  exact ⟨(m, c), hm, h, fun i j => ⟨y i j, hy i j, e i j⟩⟩

theorem inv_val (g : GAf L n) :
    (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (g.1 : Matrix (Fin n) (Fin n) (AL L)) := by
  have hm := g.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  exact Units.inv_eq_of_mul_eq_one_right hm

theorem cong_of_code {N m : ℕ} {c : Fin n → Fin n → L} {g g' : GAf L n}
    (hg : ∀ i j, (m : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L)
    (e : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y)
    (e' : ∀ i j, ∃ y ∈ ALint L, (g'.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y) :
    Cong L n N (g⁻¹ * g') := by
  choose y hy ey using e
  choose y' hy' ey' using e'
  set A : Matrix (Fin n) (Fin n) (AL L) := (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hAdef
  have hAint : ∀ i j, (m : AL L) * A i j ∈ ALint L := by
    intro i j
    rw [hAdef, inv_val]
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]
    have := conjAL_mem_ALint L (hg j i)
    rwa [map_mul, map_natCast] at this
  have hAG : A * (g.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul g.1
  set Y : Matrix (Fin n) (Fin n) (AL L) := Matrix.of fun i j => y' i j - y i j
  have hG' : (g'.1 : Matrix (Fin n) (Fin n) (AL L)) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (N : AL L) • ((m : AL L) • Y) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul, ey, ey',
      nsmul_eq_mul]
    push_cast
    ring
  have hk : (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + (N : AL L) • (((m : AL L) • A) * Y) := by
    change A * (g'.1 : Matrix (Fin n) (Fin n) (AL L)) = _
    rw [hG', Matrix.mul_add, hAG, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j, (((m : AL L) • A) * Y) i j ∈ ALint L := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (hAint i k) (Subring.sub_mem _ (hy' k j) (hy k j))
  refine ⟨fun i j => ?_, fun i j => ⟨_, hz i j, ?_⟩⟩
  · show (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hz i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem rt_mul (h h' : GAf L n) (f : GAf L n → ℂ) : rt L n (h * h') f = rt L n h (rt L n h' f) := by
  funext x
  simp [rt, mul_assoc]

theorem countable_range_rt {f : GAf L n → ℂ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, Cong L n N κ → rt L n κ f = f) :
    (Set.range fun h : GAf L n => rt L n h f).Countable := by
  classical
  haveI := countable_field (L := L)
  choose p _ hp2 hp3 using exists_code (L := L) (n := n) N hN
  let Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → ℂ) := fun q =>
    if hq : ∃ g, p g = q then rt L n hq.choose f else 0
  have key : ∀ g, rt L n g f = Ψ (p g) := by
    intro g
    have hq : ∃ g', p g' = p g := ⟨g, rfl⟩
    simp only [Ψ, dif_pos hq]
    have e := hq.choose_spec
    have h3 := hp3 hq.choose
    rw [e] at h3
    have hc : Cong L n N (g⁻¹ * hq.choose) := cong_of_code (hp2 g) (hp3 g) h3
    calc rt L n g f = rt L n g (rt L n (g⁻¹ * hq.choose) f) := by rw [hf _ hc]
      _ = rt L n hq.choose f := by rw [← rt_mul, mul_inv_cancel_left]
  refine (Set.countable_range Ψ).mono ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨p g, (key g).symm⟩

end GlobalTheory.FinTypCount

namespace GlobalTheory

open GlobalTheory.FinTypCount in

theorem FinTyp.rank_le_aleph0 : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  intro L _ _ _ n π
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hfix⟩ := π.smooth f hfS
  let T := Submodule.span ℂ (Set.range fun h : GAf L n => rt L n h f)
  have hle : T ≤ π.S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact π.stable h f hfS
  have hst : ∀ h, ∀ u ∈ T, rt L n h u ∈ T := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', rt_mul h h' f⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hfT : f ∈ T := Submodule.subset_span ⟨1, by funext x; simp [rt]⟩
  have hT : T = π.S := by
    rcases π.irr T hle hst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0
    · exact h
  rw [← hT]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))

end GlobalTheory
