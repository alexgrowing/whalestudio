import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000

namespace GlobalTheory.NL.ExtLattice

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γ_smul (g : W.Gam) (a : LetA O n) (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem φ_smul (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem Q_def : ((letφ (n := n) W.φ₀ ^ (W.s - 1)) (fun _ => W.q₀)) = W.Q := rfl

theorem sum_smul_sum {r : ℕ} (b : Fin r → W.DD T) (x : Fin r → LetA O n) (Mt : Fin r → Fin r → LetA O n) :
    ∑ j, x j • ∑ i, Mt i j • b i = ∑ i, (∑ j, Mt i j * x j) • b i := by
  simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem X_smul_injective (a : ℕ) {x y : W.DD T} (h : W.X ^ a • x = W.X ^ a • y) : x = y := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (W.X ^ a)) := by
    rw [map_pow]; exact (GlobalTheory.NL.IoXQ.isUnit_X W).pow a
  rw [← algebraMap_smul W.EE (W.X ^ a) x, ← algebraMap_smul W.EE (W.X ^ a) y] at h
  exact hu.smul_left_cancel.mp h

theorem mem_N_of_div {r : ℕ} (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (hspan : ∀ x ∈ W.N T, ∃ u : Fin r → LetA O n, x = ∑ i, u i • b i)
    (hli : ∀ u u' : Fin r → LetA O n, ∑ i, u i • b i = ∑ i, u' i • b i → u = u')
    (a : ℕ)
    (hdiv : ∀ (mm mm' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) (LetA O n)),
      (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) →
      (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) →
      (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) →
      P₁ * P₁' = (W.Q ^ mm') • (1 : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) (LetA O n)) →
      Pm * B.map W.φA = (W.Q ^ mm) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j)
    (M : ℕ) (m : W.DD T) (hφ : W.Q ^ M • (W.φD T m - m) ∈ W.N T)
    (hγ : ∃ y ∈ W.N T, W.γD T W.gam m - m = (letπ : LetA O n) • y)
    (hX : W.X ^ a • m ∈ W.N T) : m ∈ W.N T := by

  have hΓ : ∀ j, ∃ u : Fin r → LetA O n, W.γD T W.gam (b j) = ∑ i, u i • b i ∧
      ∀ i, u i - (if i = j then 1 else 0) ∈ Ideal.span {(letπ : LetA O n)} := by
    intro j
    obtain ⟨y, hy, hyeq⟩ := W.N_π T W.gam (b j) (hbN j)
    obtain ⟨w, rfl⟩ := hspan y hy
    refine ⟨fun i => (if i = j then 1 else 0) + letπ * w i, ?_, fun i => ?_⟩
    · rw [sub_eq_iff_eq_add'.1 hyeq]
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Finset.smul_sum, smul_smul]
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  choose Γc hΓeq hΓmem using hΓ
  have hcomm : ∀ (e : LetA O n) (x : LetA O n) (z : W.DD T), e • (x • z) = x • (e • z) :=
    fun e x z => smul_comm _ _ _

  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ j, W.Q ^ K • W.φD T (b j) ∈ W.N T := by
    choose k hk using fun j => W.N_φ T (b j) (hbN j)
    refine ⟨∑ j, k j, fun j => ?_⟩
    have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ j)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact (W.N T).smul_mem _ (by rw [← Q_def]; exact hk j)
  choose Φc hΦc using fun j => hspan _ (hK j)

  have hspanφ : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
      Submodule.span (LetA O n) (Set.range fun i => W.φD T (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, rfl⟩ := hspan x hx
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [φ_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, ∀ j, W.Q ^ k' • b j ∈
      Submodule.span (LetA O n) (Set.range fun i => W.φD T (b i)) := by
    choose k hk using fun j => W.N_φinv T (b j) (hbN j)
    refine ⟨∑ j, k j, fun j => ?_⟩
    have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ j)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hspanφ (by rw [← Q_def]; exact hk j))
  choose Ψc hΨc using fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (hk' j)

  obtain ⟨c, hc⟩ := hspan _ hX
  obtain ⟨υ, hυ⟩ := hspan _ hφ
  obtain ⟨y, hy, hym⟩ := hγ
  obtain ⟨ω, rfl⟩ := hspan y hy

  have E1 : ∀ i, W.X ^ a * ∑ k, Γc k i * W.γA W.gam (c k) =
      W.γA W.gam W.X ^ a * (c i + letπ * W.X ^ a * ω i) := by
    have h1 : W.X ^ a • W.γD T W.gam (W.X ^ a • m) =
        ∑ i, (W.X ^ a * ∑ k, Γc k i * W.γA W.gam (c k)) • b i := by
      rw [hc, map_sum]
      simp_rw [γ_smul, hΓeq]
      rw [sum_smul_sum W T b _ (fun i k => Γc k i), Finset.smul_sum]
      simp_rw [smul_smul]
    have h2 : W.X ^ a • W.γD T W.gam (W.X ^ a • m) =
        ∑ i, (W.γA W.gam W.X ^ a * (c i + letπ * W.X ^ a * ω i)) • b i := by
      calc W.X ^ a • W.γD T W.gam (W.X ^ a • m)
          = W.γA W.gam W.X ^ a • (W.X ^ a • m) + (W.γA W.gam W.X ^ a * letπ * W.X ^ a) •
              ∑ i, ω i • b i := by
            rw [γ_smul, map_pow, sub_eq_iff_eq_add'.1 hym]
            have hA : W.X ^ a * W.γA W.gam W.X ^ a = W.γA W.gam W.X ^ a * W.X ^ a := mul_comm _ _
            have hB : W.X ^ a * (W.γA W.gam W.X ^ a * letπ) = W.γA W.gam W.X ^ a * letπ * W.X ^ a := by ring
            simp only [smul_add, smul_smul, hA, hB]
        _ = _ := by
            rw [hc, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, smul_smul, ← add_smul]; congr 1; ring
    exact congrFun (hli _ _ (h1.symm.trans h2))
  have E2 : ∀ i, W.Q ^ M * ∑ k, Φc k i * W.φA (c k) =
      W.Q ^ K * W.Q ^ a * W.Q ^ M * c i + W.Q ^ K * W.X ^ a * W.Q ^ a * υ i := by
    have h1 : W.Q ^ M • W.Q ^ K • W.φD T (W.X ^ a • m) =
        ∑ i, (W.Q ^ M * ∑ k, Φc k i * W.φA (c k)) • b i := by
      rw [hc, map_sum, Finset.smul_sum]
      simp_rw [φ_smul, hcomm (W.Q ^ K), hΦc]
      rw [sum_smul_sum W T b _ (fun i k => Φc k i), Finset.smul_sum]
      simp_rw [smul_smul]
    have h2 : W.Q ^ M • W.Q ^ K • W.φD T (W.X ^ a • m) =
        ∑ i, (W.Q ^ K * W.Q ^ a * W.Q ^ M * c i + W.Q ^ K * W.X ^ a * W.Q ^ a * υ i) • b i := by
      calc W.Q ^ M • W.Q ^ K • W.φD T (W.X ^ a • m)
          = (W.Q ^ K * W.Q ^ a * W.Q ^ M) • (W.X ^ a • m) + (W.Q ^ K * W.X ^ a * W.Q ^ a) •
              (W.Q ^ M • (W.φD T m - m)) := by
            rw [φ_smul, map_pow, W.φA_X, mul_pow]
            have hA : W.Q ^ K * W.Q ^ a * W.Q ^ M * W.X ^ a = W.Q ^ K * W.X ^ a * W.Q ^ a * W.Q ^ M := by ring
            have hB : W.Q ^ M * (W.Q ^ K * (W.X ^ a * W.Q ^ a)) = W.Q ^ K * W.X ^ a * W.Q ^ a * W.Q ^ M := by ring
            simp only [smul_sub, smul_smul, hA, hB]
            abel
        _ = _ := by
            rw [hc, hυ, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, smul_smul, ← add_smul]
    exact congrFun (hli _ _ (h1.symm.trans h2))
  have E3 : ∀ j l, ∑ i, Φc i l * Ψc j i = if l = j then W.Q ^ K * W.Q ^ k' else 0 := by
    intro j
    have h1 : W.Q ^ K • W.Q ^ k' • b j = ∑ l, (∑ i, Φc i l * Ψc j i) • b l := by
      rw [← hΨc j, Finset.smul_sum]
      simp_rw [hcomm (W.Q ^ K), hΦc]
      exact sum_smul_sum W T b _ (fun l i => Φc i l)
    have h2 : W.Q ^ K • W.Q ^ k' • b j = ∑ l, (if l = j then W.Q ^ K * W.Q ^ k' else 0) • b l := by
      simp [ite_smul, smul_smul]
    exact congrFun (hli _ _ (h1.symm.trans h2))

  have key := hdiv (M + a) (K + k')
    (Matrix.fromBlocks (W.X ^ a • (1 : Matrix (Fin r) (Fin r) (LetA O n))) (Matrix.of fun i _ => -c i) 0
      (W.X ^ a • (1 : Matrix Unit Unit (LetA O n))))
    (Matrix.fromBlocks (Matrix.of fun i j => Γc j i) (Matrix.of fun i _ => letπ * ω i) 0 1)
    (Matrix.fromBlocks (Matrix.of fun i j => Γc j i) 0 0 1)
    (Matrix.fromBlocks (W.Q ^ M • Matrix.of fun i j => Φc j i) (Matrix.of fun i _ => W.Q ^ K * υ i) 0
      (W.Q ^ (K + M) • (1 : Matrix Unit Unit (LetA O n))))
    (Matrix.fromBlocks (Matrix.of fun i j => Φc j i) 0 0 (W.Q ^ K • (1 : Matrix Unit Unit (LetA O n))))
    (Matrix.fromBlocks (Matrix.of fun i j => Ψc j i) 0 0 (W.Q ^ k' • (1 : Matrix Unit Unit (LetA O n))))
    ?_ ?_ ?_ ?_ ?_
  · have hd : ∀ i, ∃ d, c i = W.X ^ a * d := fun i => by
      have := key (Sum.inl i) (Sum.inr ())
      exact (by simpa [dvd_neg] using this : W.X ^ a ∣ c i)
    choose d hd using hd
    have e : W.X ^ a • m = W.X ^ a • ∑ i, d i • b i := by
      rw [hc, Finset.smul_sum]
      simp_rw [hd, smul_smul]
    rw [X_smul_injective W T a e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbN i)
  · rintro (i | i) (j | j)
    · simpa [Matrix.one_apply] using hΓmem j i
    · simpa using Ideal.mul_mem_right (ω i) (Ideal.span {(letπ : LetA O n)}) (Ideal.mem_span_singleton_self _)
    · simp
    · simp
  · rintro (i | i) (j | j)
    · simpa [Matrix.one_apply] using hΓmem j i
    · simp
    · simp
    · simp
  · refine Matrix.ext fun p q => ?_
    rcases p with i | i <;> rcases q with j | j
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite (W.γA W.gam)]
      ring
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite (W.γA W.gam)]
      linear_combination (-1 : LetA O n) * E1 i
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite (W.γA W.gam)]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite (W.γA W.gam)]
      ring
  · refine Matrix.ext fun p q => ?_
    rcases p with i | i <;> rcases q with j | j
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
      rw [E3 j i, pow_add]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
      ring
  · refine Matrix.ext fun p q => ?_
    rcases p with i | i <;> rcases q with j | j
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite W.φA]
      rw [W.φA_X]; ring
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite W.φA]
      rw [W.φA_X]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      linear_combination (-1 : LetA O n) * E2 i
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite W.φA]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, apply_ite W.φA]
      rw [W.φA_X]; ring

end Generic

section Concrete

set_option maxHeartbeats 1600000 in

theorem X_pow_dvd_entry_of_fintype (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) {ι : Type} [Fintype ι] [DecidableEq ι] (a m m' : ℕ)
    (B G G₁ Pm P₁ P₁' : Matrix ι ι (AA K LL))
    (hG : ∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)})
    (hG₁ : ∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : AA K LL)})
    (hγ : ((HW l).W K s LL h).X ^ a • (G * B.map (((HW l).W K s LL h).γA ((HW l).W K s LL h).gam)) =
      (((HW l).W K s LL h).γA ((HW l).W K s LL h).gam ((HW l).W K s LL h).X ^ a) • (B * G₁))
    (hP : P₁ * P₁' = (((HW l).W K s LL h).Q ^ m') • (1 : Matrix ι ι (AA K LL)))
    (hφ : Pm * B.map ((HW l).W K s LL h).φA = (((HW l).W K s LL h).Q ^ m) • (B * P₁)) :
    ∀ i j, ((HW l).W K s LL h).X ^ a ∣ B i j := by
  set e := Fintype.equivFin ι
  set f := Matrix.reindexAlgEquiv (AA K LL) (AA K LL) e
  have hf : ∀ (Z : Matrix ι ι (AA K LL)) i j, f Z i j = Z (e.symm i) (e.symm j) := fun Z i j => rfl
  have hmap : ∀ (g : AA K LL → AA K LL) (Z : Matrix ι ι (AA K LL)), (f Z).map g = f (Z.map g) :=
    fun g Z => rfl
  have key := GlobalTheory.NL.WachMat.X_pow_dvd_entry D HW l K s LL h (Fintype.card ι) a m m'
    (f B) (f G) (f G₁) (f Pm) (f P₁) (f P₁') ?_ ?_ ?_ ?_ ?_
  · intro i j
    have := key (e i) (e j)
    rwa [hf, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro i j
    rw [← map_one f, ← map_sub, hf]
    exact hG _ _
  · intro i j
    rw [← map_one f, ← map_sub, hf]
    exact hG₁ _ _
  · rw [hmap, ← map_mul, ← map_smul, hγ, map_smul, map_mul]
  · rw [← map_mul, hP, map_smul, map_one]
  · rw [hmap, ← map_mul, hφ, map_smul, map_mul]

set_option maxHeartbeats 1600000 in

theorem mem_N : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M a : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → W.X ^ a • m ∈ W.N T → m ∈ W.N T := by
  intro D HW F l _ K s LL h W T hT M a m hφ hγ hX
  obtain ⟨bN⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_of_div W T (fun i => (bN i : W.DD T)) (fun i => (bN i).2) ?_ ?_ a ?_ M m ?_ ?_ hX
  · intro x hx
    refine ⟨fun i => bN.repr ⟨x, hx⟩ i, ?_⟩
    have h2 := congrArg Subtype.val (bN.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  · intro u u' huu
    have e : ∑ i, u i • bN i = ∑ i, u' i • bN i := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using huu
    have := congrArg (fun x => ⇑(bN.repr x)) e
    simpa only [Module.Basis.repr_sum_self] using this
  · intro mm mm' B G G₁ Pm P₁ P₁' h1 h2 h3 h4 h5
    exact X_pow_dvd_entry_of_fintype D HW l K s LL h a mm mm' B G G₁ Pm P₁ P₁' h1 h2 h3 h4 h5
  · exact hφ
  · obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hγ
    exact ⟨y, hy, hyx.symm⟩

end Concrete

end GlobalTheory.NL.ExtLattice
