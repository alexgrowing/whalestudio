import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFix

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramGen

theorem exists_normalised {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Subgroup G) (F : G)
    (hF : (Subgroup.zpowers F ⊔ I).topologicalClosure = ⊤) (z : G → ℤ_[l]) (hc : Continuous z)
    (hadd : ∀ σ τ, z (σ * τ) = z σ + z τ) (hI : ∀ σ ∈ I, z σ = 0) (h0 : ∃ σ, z σ ≠ 0) :
    ∃ ν : G →* Multiplicative ℤ_[l], Continuous ν ∧ (∀ σ ∈ I, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 := by
  have h1 : z 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ σ, z σ⁻¹ = - z σ := by
    intro σ
    have h := hadd σ σ⁻¹
    rw [mul_inv_cancel, h1] at h
    linear_combination -h

  let H : Subgroup G :=
    { carrier := {σ | ‖z σ‖ ≤ ‖z F‖}
      mul_mem' := fun {a b} ha hb => by
        show ‖z (a * b)‖ ≤ ‖z F‖
        rw [hadd]
        exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
      one_mem' := by
        show ‖z 1‖ ≤ ‖z F‖
        rw [h1, norm_zero]
        exact norm_nonneg _
      inv_mem' := fun {a} ha => by
        show ‖z a⁻¹‖ ≤ ‖z F‖
        rw [hinv, norm_neg]
        exact ha }
  have hHc : IsClosed (H : Set G) := isClosed_le (continuous_norm.comp hc) continuous_const
  have hsup : Subgroup.zpowers F ⊔ I ≤ H := by
    refine sup_le ((Subgroup.zpowers_le (H := H)).2 (show ‖z F‖ ≤ ‖z F‖ from le_rfl)) ?_
    intro σ hσ
    show ‖z σ‖ ≤ ‖z F‖
    rw [hI σ hσ, norm_zero]
    exact norm_nonneg _
  have hbound : ∀ σ, ‖z σ‖ ≤ ‖z F‖ := by
    intro σ
    have hle := Subgroup.topologicalClosure_minimal _ hsup hHc
    rw [hF] at hle
    exact hle (Subgroup.mem_top σ)
  have hF0 : z F ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := h0
    apply hσ
    have := hbound σ
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hF0' : (z F : ℚ_[l]) ≠ 0 := fun h => hF0 (Subtype.ext (h.trans PadicInt.coe_zero.symm))

  let w : G → ℤ_[l] := fun σ => ⟨(z σ : ℚ_[l]) / (z F : ℚ_[l]), by
    rw [norm_div, PadicInt.padic_norm_e_of_padicInt, PadicInt.padic_norm_e_of_padicInt,
      div_le_one (norm_pos_iff.mpr hF0)]
    exact hbound σ⟩
  have hw : ∀ σ, (w σ : ℚ_[l]) = (z σ : ℚ_[l]) / (z F : ℚ_[l]) := fun _ => rfl
  have hwadd : ∀ σ τ, w (σ * τ) = w σ + w τ := by
    intro σ τ
    apply Subtype.ext
    show (w (σ * τ) : ℚ_[l]) = ((w σ + w τ : ℤ_[l]) : ℚ_[l])
    rw [PadicInt.coe_add, hw, hw, hw, hadd, PadicInt.coe_add, add_div]
  have hwc : Continuous w :=
    Continuous.subtype_mk ((continuous_subtype_val.comp hc).div_const _) _
  let ν : G →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (w σ)) (fun σ τ => by
      rw [hwadd]
      rfl)
  refine ⟨ν, continuous_ofAdd.comp hwc, ?_, ?_⟩
  · intro σ hσ
    show Multiplicative.ofAdd (w σ) = 1
    rw [ofAdd_eq_one]
    apply Subtype.ext
    show (w σ : ℚ_[l]) = ((0 : ℤ_[l]) : ℚ_[l])
    rw [hw, hI σ hσ]
    simp
  · show Multiplicative.ofAdd (w F) = Multiplicative.ofAdd 1
    congr 1
    apply Subtype.ext
    show (w F : ℚ_[l]) = ((1 : ℤ_[l]) : ℚ_[l])
    rw [hw, div_self hF0', PadicInt.coe_one]

private theorem norm_prime_lt_one_algClosure {l : ℕ} [Fact l.Prime] : ‖(l : Om l)‖ < 1 := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem norm_pow_sub_pow_le_norm_sub {E : Type} [NormedField E] [IsUltrametricDist E] {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ ‖y - x‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro j _
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

private theorem fixes_root_of_unity_of_inertia_like {l : ℕ} [Fact l.Prime] (σ : GQ l)
    (hσ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) (n : ℕ) (hn : 0 < n) (x : Om l)
    (hx : x ^ l ^ n = x) : σ x = x := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl1
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hxq : x ^ (l ^ n - 1) = 1 := by
    have h : x ^ (l ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 h
  have hnx : ‖x‖ = 1 := by
    have h := congrArg norm hxq
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by omega)).mp h
  have hy : σ x ^ l ^ n = σ x := by rw [← map_pow, hx]
  have hε : ‖σ x - x‖ < 1 := hσ x hnx.le
  have hny : ‖σ x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (σ x - x) x
    rw [sub_add_cancel, hnx] at h
    exact h.trans (max_le hε.le le_rfl)
  by_contra hne
  have hne' : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range (l ^ n), σ x ^ i * x ^ (l ^ n - 1 - i) with hSdef

  have hS : S = 1 := by
    have h := geom_sum₂_mul (σ x) x (l ^ n)
    rw [hy, hx] at h
    exact mul_right_cancel₀ hne' (h.trans (one_mul _).symm)

  have hterm : ∀ i ∈ Finset.range (l ^ n),
      ‖σ x ^ i * x ^ (l ^ n - 1 - i) - 1‖ ≤ ‖σ x - x‖ := by
    intro i hi
    have hi' : i ≤ l ^ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (1 : Om l) = x ^ i * x ^ (l ^ n - 1 - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi', hxq]
    rw [h1, ← sub_mul, norm_mul, norm_pow, hnx, one_pow, mul_one]
    exact norm_pow_sub_pow_le_norm_sub hnx.le hny i
  have hsum : ‖S - ((l ^ n : ℕ) : Om l)‖ ≤ ‖σ x - x‖ := by
    have h : ((l ^ n : ℕ) : Om l) = ∑ i ∈ Finset.range (l ^ n), (1 : Om l) := by simp
    rw [h, hSdef, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
  have hlq : ‖((l ^ n : ℕ) : Om l)‖ < 1 := by
    rw [Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_prime_lt_one_algClosure hn.ne'
  have hq1 : ‖((l ^ n : ℕ) : Om l) - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlq.ne), norm_neg, norm_one]
    exact max_eq_right hlq.le
  have key : ‖S - 1‖ = 1 := by
    have e : S - 1 = (((l ^ n : ℕ) : Om l) - 1) + (S - ((l ^ n : ℕ) : Om l)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hq1]; exact (hsum.trans_lt hε).ne'), hq1]
    exact max_eq_left (hsum.trans hε.le)
  rw [hS, sub_self, norm_zero] at key
  exact zero_ne_one key

theorem exists_gen_degree : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l),
    ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 ∧
      (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  intro l _ K

  obtain ⟨φ, hφ⟩ := (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).1
  obtain ⟨z, hzc, hzadd, hzval⟩ := GlobalTheory.UnramifiedDegree.exists_degree l
    (fun n hn σ => GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l n hn σ)
    (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).2
  have hz1 : z 1 = 0 := by simpa using hzadd 1 1
  have hzφ : z φ = 1 := by
    have h := hzval φ 1 (fun n hn x hx => by rw [pow_one]; exact hφ n hn x hx)
    simpa using h
  have hzpow : ∀ m : ℕ, z (φ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hz1]
    | succ m ih =>
      rw [pow_succ, hzadd, ih, hzφ]
      push_cast
      ring

  have hfix : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0 := by
    intro σ hσ
    have h := hzval σ 0 (fun n hn x hx => by
      rw [pow_zero, pow_one]
      exact fixes_root_of_unity_of_inertia_like σ hσ n hn x hx)
    simpa using h

  obtain ⟨N, hN, hmem⟩ : ∃ N : ℕ, 0 < N ∧ φ ^ N ∈ GK K := by
    have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
    let g : ℕ → ((K : IntermediateField ℚ_[l] (Om l)) →ₐ[ℚ_[l]] Om l) := fun m =>
      ((φ ^ m : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (K : IntermediateField ℚ_[l] (Om l)).val
    have claim : ∀ i j, i < j → g i = g j → φ ^ (j - i) ∈ GK K := by
      intro i j hij hg
      show φ ^ (j - i) ∈ (K : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (φ ^ i) x = (φ ^ j) x := DFunLike.congr_fun hg ⟨x, hx⟩
      have h2 : φ ^ j = φ ^ i * φ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hij.le]
      rw [h2, AlgEquiv.mul_apply] at h1
      exact ((φ ^ i).injective h1).symm
    obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, claim i j h hg⟩
    · exact ⟨i - j, by omega, claim j i h hg.symm⟩

  let z' : ↥(GK K) → ℤ_[l] := fun σ => z σ
  have hz'c : Continuous z' := hzc.comp continuous_subtype_val
  have hz'add : ∀ σ τ, z' (σ * τ) = z' σ + z' τ := fun σ τ => hzadd σ τ
  let f : ↥(GK K) →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (z' σ)) (fun σ τ => by rw [hz'add]; rfl)
  have hIK : IK K ≤ f.ker := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z σ) = 1
    rw [hfix σ hσ, ofAdd_zero]
  have hz'I : ∀ σ ∈ IK K, z' σ = 0 := by
    intro σ hσ
    have h := hIK hσ
    rw [MonoidHom.mem_ker] at h
    change Multiplicative.ofAdd (z' σ) = 1 at h
    exact ofAdd_eq_one.mp h
  have h0 : ∃ σ, z' σ ≠ 0 := ⟨⟨φ ^ N, hmem⟩, by
    show z (φ ^ N) ≠ 0
    rw [hzpow]
    exact Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨F, hF⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨ν, hνc, hνI, hνF⟩ := exists_normalised (IK K) F hF z' hz'c hz'add hz'I h0
  refine ⟨F, ν, hνc, hνI, hνF, ?_⟩
  rw [eq_top_iff, ← hF]
  refine Subgroup.topologicalClosure_mono (sup_le ?_ ?_)
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert F _))
  · intro σ hσ
    exact Subgroup.subset_closure (Set.mem_insert_of_mem F hσ)

end GlobalTheory.UnramGen
