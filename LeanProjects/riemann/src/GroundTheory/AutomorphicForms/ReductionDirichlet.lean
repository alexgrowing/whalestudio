import Mathlib
import GroundTheory.AutomorphicForms.ReductionHeight
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.IntegersLattice
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex

open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in

theorem norm_apply_le_norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖GroundTheory.Global.homeomorphMixedSpace K x‖ := by
  rw [GroundTheory.Global.homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : w.IsReal
  · calc ‖x w‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ :=
          ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖fun v : {w : InfinitePlace K // w.IsReal} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)‖ :=
          norm_le_pi_norm (fun v : {w : InfinitePlace K // w.IsReal} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)) ⟨w, hw⟩
      _ ≤ _ := by rw [Prod.norm_def]; exact le_max_left _ _
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
    calc ‖x w‖ = ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ :=
          ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖fun v : {w : InfinitePlace K // w.IsComplex} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v)‖ :=
          norm_le_pi_norm (fun v : {w : InfinitePlace K // w.IsComplex} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v)) ⟨w, hc⟩
      _ ≤ _ := by rw [Prod.norm_def]; exact le_max_right _ _

theorem abs_sub_lt_one_of_floor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ⌊x⌋₊ = ⌊y⌋₊) :
    |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]
  constructor <;> linarith

theorem norm_le_one_of_mem_integralFiniteAdeles {a : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖a v‖ ≤ 1 :=
  norm_le_one_of_mem v (ha v)

open scoped Classical in

theorem exists_dirichlet_box : ∃ B : ℝ, 0 < B ∧ ∀ (a : 𝔸[K]) (N : ℕ), 0 < N →
    ∃ l : 𝓞 K, l ≠ 0 ∧
      (∀ w : InfinitePlace K, ‖(algebraMap K 𝔸[K] (l : K)).1 w‖ ≤ (N + 1) * B) ∧
      ∃ c : K, (∀ v : HeightOneSpectrum (𝓞 K),
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).2 v‖ ≤ 1) ∧
        ∀ w : InfinitePlace K,
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).1 w‖ ≤ B / N := by
  set bZ := RingOfIntegers.basis K
  set b := mixedEmbedding.latticeBasis K
  set B₁ : ℝ := ∑ i, ‖b i‖ with hB₁
  set B₂ : ℝ := ∑ w : InfinitePlace K, ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖ with hB₂
  have hB₁0 : 0 ≤ B₁ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB₂0 : 0 ≤ B₂ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨B₁ + B₂ + 1, by positivity, fun a N hN => ?_⟩

  let lam : (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin (N + 1)) → 𝓞 K :=
    fun m => bZ.equivFun.symm fun i => ((m i : ℕ) : ℤ)
  have hlam_inj : Function.Injective lam := by
    intro m m' h
    have h' := bZ.equivFun.symm.injective h
    funext i
    exact Fin.ext (by exact_mod_cast congrFun h' i)

  have hk : ∀ l : 𝓞 K, ∃ k : K, (algebraMap K 𝔸[K] (l : K) * a).2 -
      algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    fun l => GroundTheory.Global.exists_sub_mem_integralFiniteAdeles _
  choose k hk using hk
  let e : 𝓞 K → 𝔸[K] := fun l => algebraMap K 𝔸[K] (l : K) * a - algebraMap K 𝔸[K] (k l)
  let s : 𝓞 K → Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ :=
    fun l i => b.repr (GroundTheory.Global.homeomorphMixedSpace K (e l).1) i
  have hbox : ∀ (l : 𝓞 K) i, ⌊(N : ℝ) * Int.fract (s l i)⌋₊ < N := fun l i => by
    refine (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _))).2 ?_
    exact mul_lt_of_lt_one_right (by exact_mod_cast hN) (Int.fract_lt_one _)
  let box : 𝓞 K → Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin N :=
    fun l i => ⟨⌊(N : ℝ) * Int.fract (s l i)⌋₊, hbox l i⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin N) <
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin (N + 1)) := by
    have : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := bZ.index_nonempty
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self N) Fintype.card_ne_zero
  obtain ⟨m, m', hne, hmm⟩ := Fintype.exists_ne_map_eq_of_card_lt (box ∘ lam) hcard
  have hlamK : ∀ p, ((lam p : 𝓞 K) : K) = ∑ i, (((p i : ℕ) : ℤ) • ((bZ i : 𝓞 K) : K)) := by
    intro p
    change algebraMap (𝓞 K) K (bZ.equivFun.symm _) = _
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp
  refine ⟨lam m - lam m', sub_ne_zero.2 (hlam_inj.ne hne), ?_, ?_⟩
  · intro w
    let φ : K →+* w.Completion := (infEval w).comp (algebraMap K 𝔸[K])
    have hφ : ∀ x : K, (algebraMap K 𝔸[K] x).1 w = φ x := fun _ => rfl
    have hcast : ((lam m - lam m' : 𝓞 K) : K) =
        ∑ i, ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K)) := by
      rw [show ((lam m - lam m' : 𝓞 K) : K) = (lam m : K) - (lam m' : K) from
        map_sub (algebraMap (𝓞 K) K) _ _, hlamK, hlamK, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hz : ∀ i, ‖((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) : ℤ)‖ ≤ N := fun i => by
      have h1 := (m i).2
      have h2 := (m' i).2
      rw [Int.norm_eq_abs]
      have : |(((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ))| ≤ (N : ℤ) := by
        rw [abs_le]; constructor <;> omega
      exact_mod_cast this
    rw [hφ, hcast, map_sum]
    calc ‖∑ i, φ ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K))‖
        ≤ ∑ i, ‖φ ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K))‖ := norm_sum_le _ _
      _ ≤ ∑ i, (N : ℝ) * ‖φ ((bZ i : 𝓞 K) : K)‖ := Finset.sum_le_sum fun i _ => by
          rw [map_zsmul]
          exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_right (hz i) (norm_nonneg _))
      _ = N * ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖ := by rw [Finset.mul_sum]; rfl
      _ ≤ N * B₂ := mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun w : InfinitePlace K =>
            ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
          (Nat.cast_nonneg _)
      _ ≤ (N + 1) * (B₁ + B₂ + 1) := by
          have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          nlinarith
  · set sm := s (lam m) with hsm
    set sm' := s (lam m') with hsm'
    let F : 𝓞 K := ∑ i, (⌊sm i⌋ - ⌊sm' i⌋) • bZ i
    have hE : algebraMap K 𝔸[K] ((lam m - lam m' : 𝓞 K) : K) * a +
        algebraMap K 𝔸[K] (-(k (lam m) - k (lam m')) - (F : K)) =
        e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K) := by
      rw [show ((lam m - lam m' : 𝓞 K) : K) = (lam m : K) - (lam m' : K) from
        map_sub (algebraMap (𝓞 K) K) _ _]
      simp only [e, map_sub, map_neg, sub_mul]
      ring
    refine ⟨-(k (lam m) - k (lam m')) - (F : K), ?_, ?_⟩
    · intro v
      rw [hE]
      have hmem : (e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K)).2 ∈
          GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
        Subring.sub_mem _ (Subring.sub_mem _ (hk (lam m)) (hk (lam m')))
          (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K F)
      exact norm_le_one_of_mem_integralFiniteAdeles hmem v
    · intro w
      rw [hE]
      refine (norm_apply_le_norm_homeomorphMixedSpace _ w).trans ?_
      have hb : ∀ i, mixedEmbedding K ((bZ i : 𝓞 K) : K) = b i := fun i => by
        rw [mixedEmbedding.latticeBasis_apply, integralBasis_apply]
      have hF : GroundTheory.Global.homeomorphMixedSpace K (algebraMap K 𝔸[K] (F : K)).1 =
          ∑ i, ((⌊sm i⌋ - ⌊sm' i⌋ : ℤ) : ℝ) • b i := by
        change GroundTheory.Global.homeomorphMixedSpace K (algebraMap K (InfiniteAdeleRing K) (F : K)) = _
        rw [GroundTheory.Global.homeomorphMixedSpace_algebraMap]
        change mixedEmbedding K (algebraMap (𝓞 K) K F) = _
        simp only [F, map_sum, map_zsmul, hb, Int.cast_smul_eq_zsmul]
      have hhom : GroundTheory.Global.homeomorphMixedSpace K
          (e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K)).1 =
          ∑ i, (Int.fract (sm i) - Int.fract (sm' i)) • b i := by
        change GroundTheory.Global.homeomorphMixedSpace K ((e (lam m)).1 - (e (lam m')).1 -
          (algebraMap K 𝔸[K] (F : K)).1) = _
        rw [GroundTheory.Global.homeomorphMixedSpace_sub,
          GroundTheory.Global.homeomorphMixedSpace_sub, hF,
          ← b.sum_repr (GroundTheory.Global.homeomorphMixedSpace K (e (lam m)).1),
          ← b.sum_repr (GroundTheory.Global.homeomorphMixedSpace K (e (lam m')).1),
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, ← sub_smul]
        congr 1
        simp only [hsm, hsm', s, Int.fract]
        push_cast
        ring
      rw [hhom]
      have hclose : ∀ i, |Int.fract (sm i) - Int.fract (sm' i)| ≤ 1 / N := fun i => by
        have h := congrArg (fun f => ((f i : Fin N) : ℕ)) hmm
        simp only [Function.comp_apply, box] at h
        have h1 := abs_sub_lt_one_of_floor_eq
          (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg (sm i)))
          (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg (sm' i))) h
        rw [← mul_sub, abs_mul, Nat.abs_cast] at h1
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        rw [le_div_iff₀ hN']
        linarith
      calc ‖∑ i, (Int.fract (sm i) - Int.fract (sm' i)) • b i‖
          ≤ ∑ i, ‖(Int.fract (sm i) - Int.fract (sm' i)) • b i‖ := norm_sum_le _ _
        _ ≤ ∑ i, 1 / (N : ℝ) * ‖b i‖ := Finset.sum_le_sum fun i _ => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hclose i) (norm_nonneg _)
        _ = B₁ / N := by rw [← Finset.mul_sum]; ring
        _ ≤ (B₁ + B₂ + 1) / N := by
            have hN' : (0 : ℝ) < N := by exact_mod_cast hN
            gcongr
            linarith

theorem continuous_infiniteComponent (w : InfinitePlace K) :
    Continuous fun s : IdeleGroup K => (s : 𝔸[K]).1 w :=
  (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)

theorem exists_bound_infinite_of_isCompact {S : Set (IdeleGroup K)} (hS : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ S, ∀ w : InfinitePlace K, ‖(s : 𝔸[K]).1 w‖ ≤ M := by
  have hc : Continuous fun s : IdeleGroup K => ∑ w : InfinitePlace K, ‖(s : 𝔸[K]).1 w‖ :=
    continuous_finsetSum _ fun w _ => (continuous_infiniteComponent w).norm
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s hs w => ?_⟩
  have h := (Real.le_norm_self _).trans (hM s hs)
  exact ((Finset.single_le_sum (f := fun w : InfinitePlace K => ‖(s : 𝔸[K]).1 w‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ w)).trans h).trans (le_max_left _ _)

theorem finite_mulSupport_max_one_norm (s : IdeleGroup K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => max 1 ‖(s : 𝔸[K]).2 v‖).Finite := by
  refine (finite_mulSupport_norm s).subset fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv ⊢
  intro h
  exact hv (by rw [h, max_self])

theorem norm_mul_standardOpenSubgroup (s : IdeleGroup K) {u : IdeleGroup K}
    (hu : u ∈ standardOpenSubgroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖((s * u : IdeleGroup K) : 𝔸[K]).2 v‖ = ‖(s : 𝔸[K]).2 v‖ := by
  rw [Units.val_mul, adele_snd_mul_apply, norm_mul,
    norm_eq_one_of_mul_eq_one (finite_mul_inv u v) ((mem_standardOpenSubgroup K).1 hu v).1
      ((mem_standardOpenSubgroup K).1 hu v).2, mul_one]

theorem exists_bound_finite_of_isCompact {S : Set (IdeleGroup K)} (hS : IsCompact S) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ s ∈ S,
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), max 1 ‖(s : 𝔸[K]).2 v‖ ≤ P := by
  set f : IdeleGroup K → ℝ := fun s => ∏ᶠ v : HeightOneSpectrum (𝓞 K), max 1 ‖(s : 𝔸[K]).2 v‖
  have hinv : ∀ s, ∀ u ∈ standardOpenSubgroup K, f (s * u) = f s := fun s u hu => by
    simp only [f, norm_mul_standardOpenSubgroup s hu]
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    refine continuousAt_const.congr (f := fun _ => f s) ?_
    have hopen : IsOpen {y : IdeleGroup K | s⁻¹ * y ∈ standardOpenSubgroup K} :=
      (isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds (by simp [one_mem])] with y hy
    have := hinv s _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  obtain ⟨P, hP⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max P 1, le_max_right _ _, fun s hs => ?_⟩
  have h := hP s hs
  exact ((Real.le_norm_self _).trans h).trans (le_max_left _ _)

def posIdele (ρ : ℝ) (hρ : 0 < ρ) : IdeleGroup K :=
  ∏ w : InfinitePlace K, moduleSection w ⟨ρ ^ w.mult, pow_pos hρ _⟩

theorem infiniteProj_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    infiniteProj w (posIdele ρ hρ) = posRealToUnits w ⟨ρ ^ w.mult, pow_pos hρ _⟩ := by
  classical
  rw [posIdele, map_prod, Finset.prod_eq_single w]
  · exact infiniteProj_infiniteEmbedding w _
  · intro w' _ hw'
    exact infiniteProj_infiniteEmbedding_of_ne (Ne.symm hw') _
  · simp

theorem norm_posIdele_infinite (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ‖((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w‖ = ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  have h := norm_posRealElem_pow w (pow_pos hρ w.mult).le
  have hm : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_left_inj₀ (norm_nonneg _) hρ.le hm).1 h

theorem posIdele_finite (ρ : ℝ) (hρ : 0 < ρ) (v : HeightOneSpectrum (𝓞 K)) :
    ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).2 v = 1 := by
  rw [← coe_finiteProj, posIdele, map_prod]
  simp [moduleSection, finiteProj_infiniteEmbedding]

theorem ideleModule_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    (ideleModule K (posIdele ρ hρ) : ℝ) = ρ ^ Module.finrank ℚ K := by
  rw [ideleModule_eq]
  simp only [norm_posIdele_infinite, posIdele_finite, norm_one, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

private theorem finprod_le_finprod_of_nonneg' {ι : Type*} {f g : ι → ℝ} (hf : (Function.mulSupport f).Finite)
    (hg : (Function.mulSupport g).Finite) (h0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏ᶠ i, f i ≤ ∏ᶠ i, g i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      (fun i hi => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 hi))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      (fun i hi => Finset.mem_coe.2 (Finset.mem_union_right _ (hg.mem_toFinset.2 hi)))]
  exact Finset.prod_le_prod (fun i _ => h0 i) fun i _ => hfg i

theorem euclidNorm_two_le {E : Type*} [NormedField E] (y : Fin 2 → E) :
    euclidNorm y ≤ ‖y 0‖ + ‖y 1‖ := by
  rw [euclidNorm, Fin.sum_univ_two]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (y 0), norm_nonneg (y 1)]

theorem norm_pi_single_one {E : Type*} [NormedField E] {n : ℕ} (j : Fin n) :
    ‖(Pi.single j (1 : E) : Fin n → E)‖ = 1 := by
  classical
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · simpa using norm_le_pi_norm (Pi.single j (1 : E) : Fin n → E) j

theorem euclidNorm_pi_single_one {E : Type*} [NormedField E] {n : ℕ} (j : Fin n) :
    euclidNorm (Pi.single j (1 : E) : Fin n → E) = 1 := by
  classical
  rw [euclidNorm, Finset.sum_eq_single j (fun i _ h => by simp [h]) (by simp)]
  simp

theorem adelicNorm_ratVec_single {n : ℕ} (j : Fin n) :
    adelicNorm (ratVec (Pi.single j (1 : K))) = 1 := by
  classical
  have hinf : ∀ w : InfinitePlace K, infComp w (ratVec (Pi.single j (1 : K))) = Pi.single j 1 :=
    fun w => by
      funext i
      change ((infEval w).comp (algebraMap K 𝔸[K])) ((Pi.single j (1 : K) : Fin n → K) i) = _
      by_cases h : i = j
      · subst h; simp
      · rw [Pi.single_eq_of_ne h, map_zero, Pi.single_eq_of_ne h]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      finComp v (ratVec (Pi.single j (1 : K))) = Pi.single j 1 := fun v => by
    funext i
    change ((finEval v).comp (algebraMap K 𝔸[K])) ((Pi.single j (1 : K) : Fin n → K) i) = _
    by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, map_zero, Pi.single_eq_of_ne h]
  simp only [adelicNorm, hinf, hfin, euclidNorm_pi_single_one, norm_pi_single_one, one_pow,
    Finset.prod_const_one, finprod_one, mul_one]

theorem exists_adelicNorm_vecMul_le : ∃ C : ℝ, 0 < C ∧ ∀ (α δ : IdeleGroup K) (u : 𝔸[K]),
    ∃ x : Fin 2 → K, x ≠ 0 ∧ adelicNorm (ratVec x ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])]) ≤
      C * Real.sqrt (ideleModule K (α * δ) : ℝ) := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨M, hM0, hM⟩ := exists_bound_infinite_of_isCompact hD
  obtain ⟨P, hP1, hP⟩ := exists_bound_finite_of_isCompact hD
  obtain ⟨B, hB, hbox⟩ := exists_dirichlet_box (K := K)
  set d := Module.finrank ℚ K with hd
  set A : ℝ := 3 * B * M + B with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 (A ^ d * P), lt_of_lt_of_le one_pos (le_max_left _ _), fun α δ u => ?_⟩
  set r : IdeleGroup K := α * δ⁻¹ with hr
  have hr0 : 0 < (ideleModule K r : ℝ) := (ideleModule K r).2
  have hδ0 : 0 < (ideleModule K δ : ℝ) := (ideleModule K δ).2
  have hmod : (ideleModule K (α * δ) : ℝ) =
      (ideleModule K r : ℝ) * (ideleModule K δ : ℝ) ^ 2 := by
    have : α * δ = r * δ * δ := by rw [hr]; group
    rw [this, map_mul, map_mul]
    simp only [Positive.val_mul]
    ring
  by_cases hr1 : 1 ≤ (ideleModule K r : ℝ)
  · refine ⟨Pi.single 1 1, by simp, ?_⟩
    have hy : ratVec (Pi.single 1 1 : Fin 2 → K) ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])] =
        (δ : 𝔸[K]) • ratVec (Pi.single 1 1) := by
      ext i
      fin_cases i <;> simp [ratVec, vecMul, dotProduct, Fin.sum_univ_two]
    rw [hy, adelicNorm_smul (hasFiniteContent_ratVec (by simp)) δ, adelicNorm_ratVec_single,
      mul_one, hmod, Real.sqrt_mul hr0.le, Real.sqrt_sq hδ0.le]
    have h1 : 1 ≤ Real.sqrt (ideleModule K r : ℝ) := Real.one_le_sqrt.2 hr1
    calc (ideleModule K δ : ℝ) ≤ 1 * (Real.sqrt (ideleModule K r : ℝ) * ideleModule K δ) := by
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · rw [not_le] at hr1
    have hd0 : 0 < d := Module.finrank_pos
    set s : ℝ := (ideleModule K r : ℝ) ^ ((1 : ℝ) / (2 * d)) with hs
    have hs0 : 0 < s := Real.rpow_pos_of_pos hr0 _
    have hs1 : s < 1 := Real.rpow_lt_one hr0.le hr1 (by positivity)
    have hspow : s ^ (2 * d) = (ideleModule K r : ℝ) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]
    set t : IdeleGroup K := posIdele (s ^ 2) (by positivity) with ht
    have htmod : (ideleModule K t : ℝ) = (ideleModule K r : ℝ) := by
      rw [ht, ideleModule_posIdele, ← pow_mul, hspow]
    have hnorm1 : r * t⁻¹ ∈ normOneSubgroup K := by
      change r * t⁻¹ ∈ (ideleModule K).ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      exact Subtype.ext htmod.symm
    obtain ⟨μ, hμ⟩ := hxD _ hnorm1
    set σ : IdeleGroup K := diagonal K μ * (r * t⁻¹) with hσ
    set w' : 𝔸[K] := algebraMap K 𝔸[K] (μ : K) * u * ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) with hw'
    set N : ℕ := ⌈1 / s⌉₊ with hN
    have hN0 : 0 < N := Nat.ceil_pos.2 (by positivity)
    obtain ⟨l, hl0, hlw, c, hcv, hcw⟩ := hbox w' N hN0
    have hlK : (l : K) ≠ 0 := (RingOfIntegers.coe_ne_zero_iff).2 hl0
    set L : 𝔸[K] := algebraMap K 𝔸[K] (l : K) with hL
    set z : Fin 2 → 𝔸[K] := ![L * (σ : 𝔸[K]) * (t : 𝔸[K]), L * w' + algebraMap K 𝔸[K] c] with hz
    refine ⟨![(μ : K) * l, c], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
      exact mul_ne_zero μ.ne_zero hlK h0
    have h1 : (δ : 𝔸[K]) * ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) = 1 := Units.mul_inv δ
    have h2 : ((t⁻¹ : IdeleGroup K) : 𝔸[K]) * (t : 𝔸[K]) = 1 := Units.inv_mul t
    have hσ' : (σ : 𝔸[K]) = algebraMap K 𝔸[K] (μ : K) * (α : 𝔸[K]) *
        ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) * ((t⁻¹ : IdeleGroup K) : 𝔸[K]) := by
      rw [hσ, hr, Units.val_mul, Units.val_mul, Units.val_mul, coe_diagonal]
      ring
    have hy : ratVec ![(μ : K) * l, c] ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])] = (δ : 𝔸[K]) • z := by
      funext i
      fin_cases i
      · simp only [ratVec, vecMul, dotProduct, Fin.sum_univ_two, hz, hσ', hL,
          Pi.smul_apply, smul_eq_mul]
        simp
        linear_combination (-(algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * (α : 𝔸[K]) *
          (((t⁻¹ : IdeleGroup K) : 𝔸[K]) * (t : 𝔸[K])))) * h1 -
          (algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * (α : 𝔸[K])) * h2
      · simp only [ratVec, vecMul, dotProduct, Fin.sum_univ_two, hz, hw', hL,
          Pi.smul_apply, smul_eq_mul]
        simp
        linear_combination (-(algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * u)) * h1

    have hLv : ∀ v : HeightOneSpectrum (𝓞 K), ‖L.2 v‖ ≤ 1 := fun v =>
      norm_le_one_of_mem v (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K l v)
    have hz0v : ∀ v : HeightOneSpectrum (𝓞 K),
        ‖finComp v z 0‖ = ‖L.2 v‖ * ‖(σ : 𝔸[K]).2 v‖ := fun v => by
      simp only [finComp, hz, Matrix.cons_val_zero, adele_snd_mul_apply, norm_mul, ht,
        posIdele_finite, mul_one]
    have hz1v : ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v z 1‖ ≤ 1 := fun v => by
      simpa only [finComp, hz, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using hcv v
    have hzc : HasFiniteContent z := by
      filter_upwards [GroundTheory.Global.IdeleGroup.eventually_norm_eq_one σ,
        Reduction.eventually_norm_eq_one hlK] with v hv1 hv2
      have h0 : ‖finComp v z 0‖ = 1 := by
        rw [hz0v, hv1, mul_one]
        exact hv2
      refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)
        (h0 ▸ norm_le_pi_norm _ 0)
      fin_cases i
      · exact h0.le
      · exact hz1v v
    have hfinv : ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v z‖ ≤ max 1 ‖(σ : 𝔸[K]).2 v‖ := by
      intro v
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      fin_cases i
      · change ‖finComp v z 0‖ ≤ _
        rw [hz0v]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hLv v)).trans (le_max_right _ _)
      · exact (hz1v v).trans (le_max_left _ _)
    have hNl : 1 / s ≤ N := Nat.le_ceil _
    have hNu : (N : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
    have hinf : ∀ w : InfinitePlace K, euclidNorm (infComp w z) ≤ A * s := by
      intro w
      refine (euclidNorm_two_le _).trans ?_
      have e0 : ‖infComp w z 0‖ = ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 := by
        simp only [infComp, hz, Matrix.cons_val_zero, adele_fst_mul_apply, norm_mul, ht,
          norm_posIdele_infinite]
      have e1 : ‖infComp w z 1‖ ≤ B / N := by
        simpa only [infComp, hz, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using hcw w
      have hLw : ‖L.1 w‖ ≤ (N + 1) * B := hlw w
      have hσw : ‖(σ : 𝔸[K]).1 w‖ ≤ M := hM σ hμ w
      have hN1 : ((N : ℝ) + 1) * s ^ 2 ≤ 3 * s := by
        have : ((N : ℝ) + 1) * s ^ 2 ≤ (1 / s + 2) * s ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        calc ((N : ℝ) + 1) * s ^ 2 ≤ (1 / s + 2) * s ^ 2 := this
          _ = s + 2 * s ^ 2 := by field_simp
          _ ≤ 3 * s := by nlinarith
      have hBN : B / N ≤ B * s := by
        calc B / N ≤ B / (1 / s) := div_le_div_of_nonneg_left hB.le (by positivity) hNl
          _ = B * s := by field_simp
      have hprod : ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 ≤ 3 * B * M * s := by
        calc ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 ≤ ((N + 1) * B) * M * s ^ 2 := by
              gcongr
          _ = B * M * (((N : ℝ) + 1) * s ^ 2) := by ring
          _ ≤ B * M * (3 * s) := mul_le_mul_of_nonneg_left hN1 (by positivity)
          _ = 3 * B * M * s := by ring
      rw [e0]
      calc ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 + ‖infComp w z 1‖ ≤ 3 * B * M * s + B * s :=
            add_le_add hprod (e1.trans hBN)
        _ = A * s := by rw [hA]; ring
    have hzbound : adelicNorm z ≤ (A * s) ^ d * P := by
      rw [adelicNorm]
      refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
      · calc ∏ w : InfinitePlace K, euclidNorm (infComp w z) ^ w.mult
            ≤ ∏ w : InfinitePlace K, (A * s) ^ w.mult :=
              Finset.prod_le_prod (fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ =>
                pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _
          _ = (A * s) ^ d := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
      · calc ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖finComp v z‖
            ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), max 1 ‖(σ : 𝔸[K]).2 v‖ :=
              finprod_le_finprod_of_nonneg' hzc.finite_mulSupport (finite_mulSupport_max_one_norm σ)
                (fun _ => norm_nonneg _) hfinv
          _ ≤ P := hP σ hμ
    have hsq : Real.sqrt (ideleModule K r : ℝ) = s ^ d := by
      rw [← hspow, show s ^ (2 * d) = (s ^ d) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hy, adelicNorm_smul hzc δ, hmod, Real.sqrt_mul hr0.le, Real.sqrt_sq hδ0.le, hsq]
    calc (ideleModule K δ : ℝ) * adelicNorm z ≤ (ideleModule K δ : ℝ) * ((A * s) ^ d * P) :=
          mul_le_mul_of_nonneg_left hzbound hδ0.le
      _ = (A ^ d * P) * (s ^ d * (ideleModule K δ : ℝ)) := by rw [mul_pow]; ring
      _ ≤ max 1 (A ^ d * P) * (s ^ d * (ideleModule K δ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Reduction

end

end GroundTheory.Automorphic
