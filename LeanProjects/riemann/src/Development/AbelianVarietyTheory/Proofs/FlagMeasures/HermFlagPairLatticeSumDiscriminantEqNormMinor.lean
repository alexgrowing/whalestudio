import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSmulMemOfMemSpanLattice
import ReciprocityTheory.SemistableReduction.SemiDegCA

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.FlagDisc

open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb

theorem idx_sum {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A A' B B' : Submodule R W}
    (h : B ≤ A) (h' : B' ≤ A') (hd : A ⊓ A' = ⊥) : idx (A ⊔ A') (B ⊔ B') = idx A B * idx A' B' := by
  have e1 : idx (A ⊔ A') (B ⊔ A') = idx A B := by
    rw [idx_sup le_sup_right, ← idx_inf_left, inf_comm, sup_inf_assoc_of_le _ h, inf_comm, hd, sup_bot_eq]
  have hd' : B ⊓ A' = ⊥ := le_bot_iff.1 (hd ▸ inf_le_inf_right _ h)
  have e2 : idx (B ⊔ A') (B ⊔ B') = idx A' B' := by
    rw [sup_comm B A', idx_sup le_sup_left, ← idx_inf_left, inf_comm, sup_comm B, sup_inf_assoc_of_le _ h', hd',
      sup_bot_eq]
  rw [← idx_mul (sup_le_sup_left h' B) (sup_le_sup_right h A'), e1, e2, mul_comm]

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [StarRing K] in

theorem idx_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (hn : 0 ≤ n) :
    (1 : K) ∈ ipow 𝔡 (-n) ∧ (idx (ipow 𝔡 (-n)) 1 : ℝ) = (Ideal.absNorm 𝔡 : ℝ) ^ n := by
  lift n to ℕ using hn
  have h1 : (1 : K) ∈ ipow 𝔡 (-n) := by
    rw [mem_ipow_iff h, neg_neg]
    intro u hu
    obtain ⟨d, -, rfl⟩ := (mem_ipow_nat 𝔡 n u).1 hu
    exact Submodule.mem_one.2 ⟨d, (one_mul _).symm⟩
  refine ⟨h1, ?_⟩
  have hfg : (ipow 𝔡 (-n)).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one (ipow 𝔡 (-n)) hfg (Submodule.one_le.2 h1)
  have e : (⟨ipow 𝔡 (-n), FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (𝓞 K)⁰ K) =
      (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n : ℤ)) := rfl
  rw [e, map_zpow₀, FractionalIdeal.coeIdeal_absNorm, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _
    (by exact_mod_cast fun e => h (Ideal.absNorm_eq_zero_iff.1 e)))] at this
  have := congrArg (fun q : ℚ => (q : ℝ)) this
  simpa [idx] using this.symm

omit [NumberField K] in

theorem norm_star [NumberField K] (x : K) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x :=
  Algebra.norm_eq_of_algEquiv ((starRingAut : K ≃+* K).toRatAlgEquiv) x

theorem idx_free {ι : Type} [Fintype ι] [DecidableEq ι] (x x' : ι → V) (hx : Set.range x' = Set.range x)
    (hi : ∀ p q, H.B (x p) (x' q) ∈ (1 : Submodule (𝓞 K) K))
    (hd : (Matrix.of fun p q => H.B (x p) (x' q)).det ≠ 0) :
    (∀ v ∈ Submodule.span K (Set.range x), (∀ q, H.B v (x' q) = 0) → v = 0) ∧
    (idx (dual H (Submodule.span (𝓞 K) (Set.range x))) (Submodule.span (𝓞 K) (Set.range x)) : ℝ) =
      |((Algebra.norm ℚ (Matrix.of fun p q => H.B (x p) (x' q)).det : ℚ) : ℝ)| := by
  set G : Matrix ι ι K := Matrix.of fun p q => H.B (x p) (x' q) with hG
  have hu : IsUnit G.det := hd.isUnit
  choose g hg using fun p q => Submodule.mem_one.1 (hi p q)
  have eg : (algebraMap (𝓞 K) K).mapMatrix (Matrix.of g) = G := by
    ext p q; simp [hg, hG]
  have ed : algebraMap (𝓞 K) K (Matrix.of g).det = G.det := by rw [RingHom.map_det, eg]
  set u : ι → V := fun p => ∑ q, G⁻¹ p q • x q with hu'
  have pair : ∀ (c : ι → K) q, H.B (∑ p, c p • x p) (x' q) = Matrix.vecMul c G q := by
    intro c q
    simp [Matrix.vecMul, dotProduct, hG, LinearMap.sum_apply]
  have comb : ∀ c : ι → K, ∑ p, c p • u p = ∑ p, Matrix.vecMul c G⁻¹ p • x p := by
    intro c
    simp only [hu', Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have pu : ∀ (c : ι → K) q, H.B (∑ p, c p • u p) (x' q) = c q := by
    intro c q
    rw [comb, pair, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have rep : ∀ v ∈ Submodule.span K (Set.range x), v = ∑ p, H.B v (x' p) • u p := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
    rw [comb]
    simp only [pair]
    rw [show (fun p => Matrix.vecMul c G p) = Matrix.vecMul c G from rfl, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
  have li : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    rw [← pu c q, hc]; simp
  refine ⟨fun v hv h0 => by rw [rep v hv]; simp [h0], ?_⟩
  have hdual : dual H (Submodule.span (𝓞 K) (Set.range x)) = Submodule.span (𝓞 K) (Set.range u) := by
    ext v
    rw [mem_dual_iff, Submodule.span_span_of_tower]
    constructor
    · rintro ⟨h1, h2⟩
      rw [rep v h1]
      refine Submodule.sum_mem _ fun p _ => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h2 (x' p) (Submodule.subset_span (hx ▸ ⟨p, rfl⟩)))
      rw [← ha, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
    · intro hv
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
      have e : ∑ p, c p • u p = ∑ p, (fun p => algebraMap (𝓞 K) K (c p)) p • u p := by
        simp only [algebraMap_smul]
      rw [e]
      refine ⟨?_, fun w hw => ?_⟩
      · rw [comb]
        exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
      · rw [← hx] at hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨q, rfl⟩ := hw
          rw [pu]
          exact Submodule.mem_one.2 ⟨_, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul a b _ hb =>
          rw [← algebraMap_smul K a b, LinearMap.map_smulₛₗ]
          exact Submodule.smul_mem _ (sig K a) hb
  rw [hdual, idx, GlobalTheory.relIndex_span_eq_natAbs_norm_det li (g := Matrix.of g) (fun e => hd (by rw [← ed, e, map_zero]))
    (fun p => ?_), ← ed]
  · have := Algebra.coe_norm_int (Matrix.of g).det
    rw [RingOfIntegers.coe_eq_algebraMap] at this
    rw [← this, Nat.cast_natAbs]
    simp
  · rw [rep (x p) (Submodule.subset_span ⟨p, rfl⟩)]
    simp only [← hg, algebraMap_smul, Matrix.of_apply]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem Xa_succ (F : FlagD H r) (a : Fin r) :
    F.Xa (a.val + 1) = F.Xa a.val ⊔ Submodule.span K {F.e a.castSucc} := by
  unfold FlagD.Xa
  rw [← Submodule.span_union, ← Set.image_singleton (f := fun b : Fin r => F.e b.castSucc), ← Set.image_union]
  congr 2
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem eq_zero_of_smul_mem (F : FlagD H r) (a : Fin r) {t : K} (h : t • F.e a.castSucc ∈ F.Xa a.val) : t = 0 := by
  by_contra ht
  have := (F.Xa a.val).smul_mem t⁻¹ h
  rw [inv_smul_smul₀ ht] at this
  exact F.indep.notMem_span_image (s := {b | b.val < a.val}) (x := a) (lt_irrefl a.val) this

omit [NumberField K] in

theorem idx_flag (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (y : Fin r → V) (hy : ∀ a, y a ∈ Λ)
    (he : ∀ a, F.e a.castSucc - y a ∈ F.Xa a.val) (n : ℕ → ℝ)
    (hn : ∀ a : Fin r, (idx (lead F Λ a.castSucc) 1 : ℝ) = n a.val) : ∀ l ≤ r,
    Submodule.span K (y '' {a | a.val < l}) = F.Xa l ∧
      Submodule.span (𝓞 K) (y '' {a | a.val < l}) ≤ latF F Λ l ∧
      (idx (latF F Λ l) (Submodule.span (𝓞 K) (y '' {a | a.val < l})) : ℝ) = ∏ a ∈ Finset.range l, n a := by
  intro l
  induction l with
  | zero => intro _; simp [FlagD.Xa, latF, idx]
  | succ l ih =>
    intro hl
    obtain ⟨h1, h2, h3⟩ := ih (Nat.le_of_succ_le hl)
    set a : Fin r := ⟨l, hl⟩ with ha
    have es : y '' {b | b.val < l + 1} = y '' {b | b.val < l} ∪ {y a} := by
      rw [← Set.image_singleton, ← Set.image_union]
      congr 1
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff, ha]
      omega
    have hX : F.Xa (l + 1) = F.Xa l ⊔ Submodule.span K {F.e a.castSucc} := Xa_succ F a
    have hea : F.e a.castSucc - y a ∈ F.Xa l := he a
    have hz : ∀ t : K, t • F.e a.castSucc ∈ F.Xa l → t = 0 := fun t => eq_zero_of_smul_mem F a
    have hle : F.Xa l ≤ F.Xa (l + 1) := hX ▸ le_sup_left
    have hya : y a ∈ F.Xa (l + 1) := by
      have : F.e a.castSucc ∈ F.Xa (l + 1) := hX ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      simpa using sub_mem this (hle hea)
    have hA : latF F Λ l ≤ latF F Λ (l + 1) := inf_le_inf_left _ hle
    have hY : Submodule.span (𝓞 K) {y a} ≤ latF F Λ (l + 1) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 ⟨hy a, hya⟩
    rw [es, Submodule.span_union, Submodule.span_union, h1]
    refine ⟨le_antisymm (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hya)) ?_,
      sup_le (h2.trans hA) hY, ?_⟩
    · rw [hX]
      refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
      simpa using Submodule.add_mem_sup hea (Submodule.mem_span_singleton_self (R := K) (y a))
    have hd : latF F Λ l ⊓ Submodule.span (𝓞 K) {y a} = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨⟨-, hv⟩, hv'⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv'
      have hv : c • y a ∈ F.Xa l := hv
      rw [← algebraMap_smul K c] at hv ⊢
      have := add_mem ((F.Xa l).smul_mem (algebraMap (𝓞 K) K c) hea) hv
      rw [smul_sub, sub_add_cancel] at this
      rw [hz _ this, zero_smul]
      exact zero_mem _
    rw [← idx_mul (sup_le_sup_right h2 _) (sup_le hA hY), idx_sum h2 le_rfl hd, Finset.prod_range_succ, ← h3,
      ← show _ = n l from hn a]
    have e0 : idx (Submodule.span (𝓞 K) {y a}) (Submodule.span (𝓞 K) {y a}) = 1 := by simp [idx]
    rw [e0, mul_one, Nat.cast_mul]
    congr 2
    set T : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {y a} ⊔ rs (𝓞 K) (F.Xa l) with hT
    set f : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V (F.e a.castSucc)).restrictScalars (𝓞 K) with hf
    have e1 : T ⊓ latF F Λ (l + 1) = Submodule.span (𝓞 K) {y a} ⊔ latF F Λ l := by
      rw [hT, sup_inf_assoc_of_le _ hY]
      congr 1
      exact le_antisymm (fun v hv => ⟨hv.2.1, hv.1⟩) fun v hv => ⟨hv.2, hA hv⟩
    have e2 : T.comap f = 1 := by
      ext t
      change t • F.e a.castSucc ∈ T ↔ _
      constructor
      · intro h
        obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 h
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
        refine Submodule.mem_one.2 ⟨c, (sub_eq_zero.1 (hz _ ?_)).symm⟩
        have := sub_mem (show w ∈ F.Xa l from hw) ((F.Xa l).smul_mem (algebraMap (𝓞 K) K c) hea)
        convert this using 1
        rw [sub_smul, ← e, smul_sub, algebraMap_smul, algebraMap_smul]
        abel
      · intro h
        obtain ⟨c, rfl⟩ := Submodule.mem_one.1 h
        rw [algebraMap_smul]
        refine T.smul_mem c ?_
        simpa using Submodule.add_mem_sup (Submodule.mem_span_singleton_self (R := 𝓞 K) (y a))
          (show _ ∈ rs (𝓞 K) (F.Xa l) from hea)
    have e3 : (lead F Λ a.castSucc).map f ⊔ rs (𝓞 K) (F.Xa l) = latF F Λ (l + 1) ⊔ rs (𝓞 K) (F.Xa l) := by
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · rintro _ ⟨t, ht, rfl⟩
        have ht' : t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa l) := ht
        obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 ht'
        refine Submodule.mem_sup.2 ⟨v, ⟨hv, ?_⟩, w, hw, e⟩
        rw [eq_sub_of_add_eq e]
        refine sub_mem (show _ ∈ F.Xa (l + 1) from ?_) (hle hw)
        rw [hX]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · rintro v ⟨hv, hv'⟩
        have hv' : v ∈ F.Xa (l + 1) := hv'
        rw [hX] at hv'
        obtain ⟨w, hw, u, hu, e⟩ := Submodule.mem_sup.1 hv'
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
        refine Submodule.mem_sup.2 ⟨_, ⟨t, ?_, rfl⟩, w, hw, (add_comm _ _).trans e⟩
        change t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa l)
        rw [eq_sub_of_add_eq' e]
        exact sub_mem (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hw)
    rw [sup_comm, ← e1, inf_comm, idx_inf_left, ← idx_sup (I := rs (𝓞 K) (F.Xa l)) le_sup_right, ← e3,
      idx_sup le_sup_right, ← e2]
    exact (AddSubgroup.relIndex_comap T.toAddSubgroup f.toAddMonoidHom (lead F Λ a.castSucc).toAddSubgroup).symm

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem exists_unitri (F : FlagD H r) (y : Fin r → V) (he : ∀ a, F.e a.castSucc - y a ∈ F.Xa a.val) {l : ℕ}
    (hr : l ≤ r) (hl : l ≤ r + 1) : ∃ M : Matrix (Fin l) (Fin l) K, M.det = 1 ∧
      ∀ a, y (Fin.castLE hr a) = ∑ b, M a b • F.e (Fin.castLE hl b) := by
  choose m h1 h2 using fun a : Fin l => exists_coord F hl a (he (Fin.castLE hr a))
  refine ⟨1 - Matrix.of m, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular (1 - Matrix.of m) (fun a b hab => ?_)]
    · simp [fun a => h1 a a le_rfl]
    · have hab : a < b := hab
      simp [h1 a b hab.le, Matrix.one_apply_ne hab.ne]
  · simp only [Matrix.sub_apply, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, ← h2 a, Matrix.one_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (sub_sub_cancel _ _).symm

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem iso_Xa (F : FlagD H r) (l : ℕ) {v w : V} (hv : v ∈ F.Xa l) (hw : w ∈ F.Xa l) : H.B v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨b, -, rfl⟩ := hx; exact F.iso a b
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [LinearMap.map_smulₛₗ, hb, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul a b _ hb => rw [map_smul, LinearMap.smul_apply, hb, smul_zero]

theorem exists_vectors (N : NF H r) (F : FlagD H r) {Λ : Submodule (𝓞 K) V} (h : IsFrame F Λ N.aa) {l : ℕ}
    (hr : l ≤ r) (hl : l ≤ r + 1) : ∃ (y : Fin l → V) (M : Matrix (Fin l) (Fin l) K), M.det = 1 ∧
      (∀ a, y a = ∑ b, M a b • F.e (Fin.castLE hl b)) ∧ Submodule.span K (Set.range y) = F.Xa l ∧
      Submodule.span (𝓞 K) (Set.range y) ≤ latF F Λ l ∧
      (idx (latF F Λ l) (Submodule.span (𝓞 K) (Set.range y)) : ℝ) =
        (Ideal.absNorm N.𝔡 : ℝ) ^ (∑ a ∈ Finset.range l, ((r : ℤ) - a)) := by
  have hp : ∀ a : Fin r, (0 : ℤ) ≤ (r : ℤ) - a.val := fun a => by have := a.2; omega
  have h1 : ∀ a : Fin r, ∃ y ∈ Λ, F.e a.castSucc - y ∈ F.Xa a.val := by
    intro a
    have : (1 : K) ∈ lead F Λ a.castSucc := h.1 a ▸ (idx_ipow N.𝔡_ne _ (hp a)).1
    have : (1 : K) • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val) := this
    obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 this
    rw [one_smul] at e
    exact ⟨v, hv, by rw [← e, add_sub_cancel_left]; exact hw⟩
  choose y hy he using h1
  obtain ⟨M, hM, hM'⟩ := exists_unitri F y he hr hl
  have := idx_flag F Λ y hy he (fun a => (Ideal.absNorm N.𝔡 : ℝ) ^ ((r : ℤ) - a))
    (fun a => h.1 a ▸ (idx_ipow N.𝔡_ne _ (hp a)).2) l hr
  have es : Set.range (fun a : Fin l => y (Fin.castLE hr a)) = y '' {a | a.val < l} := by
    rw [← Fin.range_castLE hr, ← Set.range_comp]; rfl
  refine ⟨fun a => y (Fin.castLE hr a), M, hM, hM', ?_⟩
  rw [es]
  refine ⟨this.1, this.2.1, this.2.2.trans ?_⟩
  have h0 : (Ideal.absNorm N.𝔡 : ℝ) ≠ 0 := by exact_mod_cast fun e => N.𝔡_ne (Ideal.absNorm_eq_zero_iff.1 e)
  clear this es hM' hM M hr hl
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, ih, zpow_add₀ h0]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ l ≤ N.j, N.nD l ≠ 0 → normD N.F N.F' Λ l = N.nD l ∧ 1 ≤ N.nD l := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ l hj hne
  have hr := hj.trans N.j_le
  have hl : l ≤ r + 1 := hr.trans (Nat.le_succ r)
  have hD : Dl N.F N.F' l hl ≠ 0 := fun e => hne (by rw [NF.nD, dif_pos hl, e]; simp)
  refine ⟨?_, ?_⟩
  swap
  · obtain ⟨A, hA0, hA⟩ := exists_ideal N hΛ.1 l
    rw [← (hA hl hj hD).1]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun e => hA0 (Ideal.absNorm_eq_zero_iff.1 e)
  obtain ⟨hU, hF, hF'⟩ := hΛ.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hU.2] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2
  have hfg : Λ.FG := ((isUnimod_iff H Λ).1 hU).1.fg
  obtain ⟨y, M, d1, c1, s1, l1, i1⟩ := exists_vectors N N.F hF hr hl
  obtain ⟨y', M', d2, c2, s2, l2, i2⟩ := exists_vectors N N.F' hF' hr hl
  have m1 : ∀ a, y a ∈ latF N.F Λ l := fun a => l1 (Submodule.subset_span ⟨a, rfl⟩)
  have m2 : ∀ a, y' a ∈ latF N.F' Λ l := fun a => l2 (Submodule.subset_span ⟨a, rfl⟩)
  set P : Matrix (Fin l) (Fin l) K := Matrix.of fun a b => H.B (y a) (y' b) with hP
  have dP : P.det = Dl N.F N.F' l hl := by
    have e : P = M * (Zhat N.F N.F').submatrix (Fin.castLE hl) (Fin.castLE hl) * M'.conjTranspose := by
      ext a b
      simp only [hP, c1, c2, Matrix.of_apply, Matrix.mul_apply, Zhat,
        Matrix.submatrix_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply, map_smul,
        LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, d1, d2, star_one, one_mul, mul_one, Dl]
  have eG : (Matrix.of fun p q => H.B (Sum.elim y y' p) (Sum.elim y' y q)) =
      Matrix.fromBlocks P 0 0 P.conjTranspose := by
    ext p q
    rcases p with p | p <;> rcases q with q | q
    · rfl
    · exact iso_Xa N.F l (m1 p).2 (m1 q).2
    · exact iso_Xa N.F' l (m2 p).2 (m2 q).2
    · exact (H.herm _ _).symm
  have dG : (Matrix.of fun p q => H.B (Sum.elim y y' p) (Sum.elim y' y q)).det =
      Dl N.F N.F' l hl * star (Dl N.F N.F' l hl) := by
    rw [eG, Matrix.det_fromBlocks_zero₂₁, Matrix.det_conjTranspose, dP]
  have hrg : Set.range (Sum.elim y' y) = Set.range (Sum.elim y y') := by
    rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]
  have mm : ∀ p, Sum.elim y y' p ∈ Λ := by rintro (p | p); exacts [(m1 p).1, (m2 p).1]
  have mm' : ∀ p, Sum.elim y' y p ∈ Λ := by rintro (p | p); exacts [(m2 p).1, (m1 p).1]
  obtain ⟨nd, hi⟩ := idx_free (H := H) (Sum.elim y y') (Sum.elim y' y) hrg (fun p q => hint _ (mm p) _ (mm' q))
    (dG ▸ mul_ne_zero hD (star_ne_zero.2 hD))
  rw [dG, map_mul, norm_star] at hi
  set S := Submodule.span K (Set.range (Sum.elim y y')) with hS
  set L := Submodule.span (𝓞 K) (Set.range (Sum.elim y y')) with hL
  have eS : S = N.F.Xa l ⊔ N.F'.Xa l := by rw [hS, Set.Sum.elim_range, Submodule.span_union, s1, s2]
  have eL : L = Submodule.span (𝓞 K) (Set.range y) ⊔ Submodule.span (𝓞 K) (Set.range y') := by
    rw [hL, Set.Sum.elim_range, Submodule.span_union]
  have rad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ (⊥ : Submodule K V) := fun x hx =>
    ⟨fun h => nd x hx fun q => h _ (Submodule.subset_span (hrg ▸ ⟨q, rfl⟩)), fun h y _ => by
      rw [(Submodule.mem_bot K).1 h]; simp⟩
  set T := latF N.F Λ l ⊔ latF N.F' Λ l with hT
  have hLT : L ≤ T := eL ▸ sup_le_sup l1 l2
  have hTΛ : T ≤ Λ := sup_le inf_le_left inf_le_left
  have sL : Submodule.span K (L : Set V) = S := Submodule.span_span_of_tower _ _ _
  have sT : Submodule.span K (T : Set V) = S := by
    refine le_antisymm (Submodule.span_le.2 ?_) (sL ▸ Submodule.span_mono hLT)
    change T ≤ rs (𝓞 K) S
    rw [eS]
    exact sup_le (fun v hv => Submodule.mem_sup_left hv.2) fun v hv => Submodule.mem_sup_right hv.2
  have LL : IsLatMod L S ⊥ := ⟨⟨L, hfg.of_le (hLT.trans hTΛ), by simp⟩, sL⟩
  have LT : IsLatMod T S ⊥ := ⟨⟨T, hfg.of_le hTΛ, by simp⟩, sT⟩
  obtain ⟨-, -, k1, -⟩ := DelScale.main K V H hK T L S ⊥ bot_le rad LT LL
  obtain ⟨k0, -, -, k2⟩ := DelScale.main K V H hK L L S ⊥ bot_le rad LL LL
  have k3 := (k2 ((isIntegralLat_iff H L).2 fun a ha b hb => hint a (hTΛ (hLT ha)) b (hTΛ (hLT hb)))).2
  rw [hi, Rat.cast_mul, abs_mul, ← sq, sq_eq_sq₀ k0.le (abs_nonneg _)] at k3
  have hd : latF N.F Λ l ⊓ latF N.F' Λ l = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨h1, h2⟩
    refine nd v (eS ▸ Submodule.mem_sup_left h1.2) ?_
    rintro (q | q)
    exacts [iso_Xa N.F' l h2.2 (m2 q).2, iso_Xa N.F l h1.2 (m1 q).2]
  have k4 : gidx T L = (Ideal.absNorm N.𝔡 : ℝ) ^ (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)) := by
    rw [gidx, idx_eq L, GlobalTheory.Mass.DiscOrder.idxN_eq_one.2 hLT, eL, idx_sum l1 l2 hd, Nat.cast_one, div_one,
      Nat.cast_mul, i1, i2, mul_comm (2 : ℤ), zpow_mul, zpow_two]
  have h0 : (Ideal.absNorm N.𝔡 : ℝ) ≠ 0 := by exact_mod_cast fun e => N.𝔡_ne (Ideal.absNorm_eq_zero_iff.1 e)
  rw [normD, NF.nD, dif_pos hl, ← k3, k1, k4, zpow_neg, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ h0), one_mul]

end GlobalTheory.DegCnt.FlagDisc
