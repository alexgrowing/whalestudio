import Mathlib
open NumberField

namespace GlobalTheory

theorem exists_mem_span_pow_sup_pow_succ (F : Type) [Field F] [NumberField F] (w0 : Ideal (𝓞 F))
    (hmax : w0.IsMaximal) (hne : w0 ≠ ⊥) :
    ∃ π ∈ w0, ∀ j : ℕ, Ideal.span {π ^ j} ⊔ w0 ^ (j + 1) = w0 ^ j := by
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ w0 hne hmax.ne_top 1
  rw [pow_one] at hπ1
  have h1 : Ideal.span {π} ⊔ w0 ^ 2 = w0 := by
    have hle : Ideal.span {π} ⊔ w0 ^ 2 ≤ w0 :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).2 hπ1) (Ideal.pow_le_self two_ne_zero)
    obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.2 hle
    have hK' : w0 ≤ K := by
      have h2 : w0 * w0 ≤ w0 * K := by rw [← hK, ← pow_two]; exact le_sup_right
      rw [← Ideal.dvd_iff_le] at h2 ⊢
      exact (mul_dvd_mul_iff_left hne).1 h2
    by_cases hKt : K = ⊤
    · rw [hK, hKt, Ideal.mul_top]
    · exfalso
      have hKe : w0 = K := hmax.eq_of_le hKt hK'
      apply hπ2
      have : π ∈ Ideal.span {π} ⊔ w0 ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
      rw [hK, ← hKe, ← pow_two] at this
      simpa using this
  have hge : ∀ j : ℕ, w0 ^ j ≤ Ideal.span {π ^ j} ⊔ w0 ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc w0 ^ (j + 1) = w0 ^ j * w0 := pow_succ _ _
        _ ≤ (Ideal.span {π ^ j} ⊔ w0 ^ (j + 1)) * (Ideal.span {π} ⊔ w0 ^ 2) :=
            Ideal.mul_mono ih h1.ge
        _ ≤ Ideal.span {π ^ (j + 1)} ⊔ w0 ^ (j + 1 + 1) := by
            rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
            refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
            · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]; exact le_sup_left
            · refine le_trans ?_ le_sup_right
              calc Ideal.span {π ^ j} * w0 ^ 2 ≤ w0 ^ j * w0 ^ 2 :=
                    Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hπ1 j))
                _ = w0 ^ (j + 1 + 1) := by rw [← pow_add]
            · refine le_trans ?_ le_sup_right
              calc w0 ^ (j + 1) * Ideal.span {π} ≤ w0 ^ (j + 1) * w0 :=
                    Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hπ1)
                _ = w0 ^ (j + 1 + 1) := (pow_succ _ _).symm
            · refine le_trans ?_ le_sup_right
              calc w0 ^ (j + 1) * w0 ^ 2 = w0 * w0 ^ (j + 1 + 1) := by ring
                _ ≤ w0 ^ (j + 1 + 1) := Ideal.mul_le_right
  refine ⟨π, hπ1, fun j => le_antisymm (sup_le ?_ (Ideal.pow_le_pow_right (Nat.le_succ j))) (hge j)⟩
  exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hπ1 j)

theorem natCard_quotient_pow_eq (F : Type) [Field F] [NumberField F] (w0 : Ideal (𝓞 F)) (r : ℕ) :
    Nat.card (𝓞 F ⧸ w0 ^ r) = Nat.card (𝓞 F ⧸ w0) ^ r := by
  have := map_pow Ideal.absNorm w0 r
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using this

theorem exists_span_torsionBySet_maximal (F : Type) [Field F] [NumberField F] (M : Type)
    [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ) (hmax : w0.IsMaximal)
    (hne : w0 ≠ ⊥)
    (hc : Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h) :
    ∃ e : Fin h → M, (∀ i, ∀ c ∈ w0, c • e i = 0) ∧
      ∀ g : M, (∀ c ∈ w0, c • g = 0) → ∃ u : Fin h → 𝓞 F, g = ∑ i, u i • e i := by
  set T := Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F)) with hT
  haveI : Finite (𝓞 F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  haveI : Nontrivial (𝓞 F ⧸ w0) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  have hq : 2 ≤ Nat.card (𝓞 F ⧸ w0) := Finite.one_lt_card
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  letI : Field (𝓞 F ⧸ w0) := Ideal.Quotient.field w0
  haveI : Module.Finite (𝓞 F ⧸ w0) T := Module.Finite.of_finite
  letI := Fintype.ofFinite (𝓞 F ⧸ w0)
  letI := Fintype.ofFinite T
  have hrank : Module.finrank (𝓞 F ⧸ w0) T = h := by
    have := Module.card_eq_pow_finrank (K := 𝓞 F ⧸ w0) (V := T)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc] at this
    exact (Nat.pow_right_injective hq this).symm
  let b := Module.finBasisOfFinrankEq (𝓞 F ⧸ w0) T hrank
  have mem : ∀ g : M, g ∈ T ↔ ∀ c ∈ w0, c • g = 0 := by
    intro g; simp only [hT, Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]
  refine ⟨fun i => (b i : M), fun i => (mem _).1 (b i).2, fun g hg => ?_⟩
  choose u hu using fun i => Ideal.Quotient.mk_surjective (b.repr ⟨g, (mem g).2 hg⟩ i)
  refine ⟨u, ?_⟩
  have hsum := b.sum_repr ⟨g, (mem g).2 hg⟩
  have := congrArg (fun x : T => (x : M)) hsum
  simp only [Submodule.coe_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hu i]
  first
    | (rw [Submodule.torsionBySet.mk_smul]; rfl)
    | (rw [Module.IsTorsionBySet.mk_smul]; rfl)
    | rfl

theorem torsionBySet_pow_free_of_natCard : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h r : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h)) → ∃ f : (Fin h → 𝓞 F ⧸ w0 ^ r) →+ M, (∀ (c : 𝓞 F) (a : Fin h → 𝓞 F ⧸ w0 ^ r), f (Ideal.Quotient.mk (w0 ^ r) c • a) = c • f a) ∧ Function.Injective f ∧ ∀ g : M, (∀ c ∈ w0 ^ r, c • g = 0) → ∃ a, f a = g := by
  intro F _ _ M _ _ w0 h r hmax hne hcard
  set T : ℕ → Submodule (𝓞 F) M :=
    fun j => Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F)) with hT
  have memT : ∀ j (g : M), g ∈ T j ↔ ∀ c ∈ w0 ^ j, c • g = 0 := by
    intro j g
    simp only [hT, Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]
  haveI : Finite (𝓞 F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  haveI : Nontrivial (𝓞 F ⧸ w0) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  have hq : 2 ≤ Nat.card (𝓞 F ⧸ w0) := Finite.one_lt_card
  have hqpos : 0 < Nat.card (𝓞 F ⧸ w0) := by omega
  have hfin : ∀ j, Finite (T j) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hcard j]; positivity)
  rcases r with _ | n
  · haveI : Subsingleton (𝓞 F ⧸ w0 ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    refine ⟨0, fun c a => by simp, fun a b _ => Subsingleton.elim a b, fun g hg => ⟨0, ?_⟩⟩
    have h1 := hg 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    rw [one_smul] at h1
    rw [h1]; rfl
  · obtain ⟨π, hπ, hspan⟩ := exists_mem_span_pow_sup_pow_succ F w0 hmax hne
    have key : ∀ j (g : M), g ∈ T (j + 1) → π ^ j • g = 0 → g ∈ T j := by
      intro j g hg h0
      rw [memT] at hg ⊢
      intro c hc
      rw [← hspan j, Submodule.mem_sup] at hc
      obtain ⟨a, ha, b, hb, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [add_smul, mul_smul, h0, smul_zero, zero_add, hg b hb]
    obtain ⟨eb, heb, hspanb⟩ := exists_span_torsionBySet_maximal F M w0 h hmax hne
      (by simpa using hcard 1)
    have hebT : ∀ i, eb i ∈ T 1 := fun i =>
      (memT 1 _).2 fun c hc => heb i c (by rwa [pow_one] at hc)
    have hTle : T n ≤ T (n + 1) := fun x hx => by
      rw [memT] at hx ⊢
      exact fun c hc => hx c (Ideal.pow_le_pow_right (Nat.le_succ n) hc)

    have hlift : ∀ y ∈ T 1, ∃ x ∈ T (n + 1), π ^ n • x = y := by
      let φ : T (n + 1) →ₗ[𝓞 F] M := π ^ n • (T (n + 1)).subtype
      have φ_apply : ∀ x, φ x = π ^ n • (x : M) := fun x => rfl
      have hker : LinearMap.ker φ = (T n).comap (T (n + 1)).subtype := by
        ext x
        rw [LinearMap.mem_ker, Submodule.mem_comap, φ_apply, Submodule.coe_subtype]
        constructor
        · intro hx; exact key n x x.2 hx
        · intro hx; exact (memT _ _).1 hx _ (Ideal.pow_mem_pow hπ n)
      have hcardker : Nat.card (LinearMap.ker φ) = Nat.card (T n) := by
        rw [hker]; exact Nat.card_congr (Submodule.comapSubtypeEquivOfLe hTle).toEquiv
      have hcardrange : Nat.card (LinearMap.range φ) = Nat.card (T 1) := by
        have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
        rw [Nat.card_congr (φ.quotKerEquivRange).toEquiv, hcardker, hcard, hcard] at h1
        rw [hcard, one_mul]
        have e1 : (n + 1) * h = h + n * h := by ring
        rw [e1, pow_add] at h1
        exact (Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (mul_comm _ _))).symm
      have hrange_le : LinearMap.range φ ≤ T 1 := by
        rintro _ ⟨x, rfl⟩
        rw [memT, φ_apply]
        intro c hc
        rw [smul_smul]
        apply (memT _ _).1 x.2
        rw [pow_one] at hc
        rw [pow_succ']
        exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hπ n)
      have hbij := (Submodule.inclusion_injective hrange_le).bijective_of_nat_card_le
        (le_of_eq hcardrange.symm)
      intro y hy
      obtain ⟨⟨_, ⟨x, rfl⟩⟩, hx⟩ := hbij.2 ⟨y, hy⟩
      refine ⟨x, x.2, ?_⟩
      have := congrArg Subtype.val hx
      simpa [φ_apply] using this
    choose e he1 he2 using fun i => hlift (eb i) (hebT i)
    have hker_e : ∀ i, w0 ^ (n + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M (e i)) := by
      intro i c hc
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact (memT _ _).1 (he1 i) c hc
    let φi : Fin h → (𝓞 F ⧸ w0 ^ (n + 1)) →ₗ[𝓞 F] M := fun i =>
      (w0 ^ (n + 1)).liftQ (LinearMap.toSpanSingleton (𝓞 F) M (e i)) (hker_e i)
    have φi_mk : ∀ i c, φi i (Ideal.Quotient.mk _ c) = c • e i := fun i c => rfl
    let fL : (Fin h → 𝓞 F ⧸ w0 ^ (n + 1)) →ₗ[𝓞 F] M := ∑ i, (φi i).comp (LinearMap.proj i)
    have fL_apply : ∀ a, fL a = ∑ i, φi i (a i) := by
      intro a; simp [fL]
    have hce : ∀ i (c : 𝓞 F), c • e i ∈ LinearMap.range fL := by
      intro i c
      refine ⟨Pi.single i (Ideal.Quotient.mk _ c), ?_⟩
      rw [fL_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, φi_mk]
      · intro k _ hk; rw [Pi.single_eq_of_ne hk, map_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hrange : ∀ a, fL a ∈ T (n + 1) := by
      intro a
      rw [fL_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (a i)
      rw [← hc, φi_mk]
      exact Submodule.smul_mem _ c (he1 i)
    have hsurj : ∀ j, j ≤ n + 1 → ∀ g ∈ T j, g ∈ LinearMap.range fL := by
      intro j
      induction j with
      | zero =>
        intro _ g hg
        have h1 := (memT 0 g).1 hg 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
        rw [one_smul] at h1
        rw [h1]; exact Submodule.zero_mem _
      | succ j ih =>
        intro hj g hg
        have hgT1 : ∀ c ∈ w0, c • π ^ j • g = 0 := by
          intro c hc
          rw [smul_smul]
          apply (memT _ _).1 hg
          rw [pow_succ']
          exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hπ j)
        obtain ⟨u, hu⟩ := hspanb _ hgT1
        set w := ∑ i, (u i * π ^ (n - j)) • e i with hw_def
        have hw : w ∈ LinearMap.range fL := Submodule.sum_mem _ fun i _ => hce i _
        have hgw : g - w ∈ T j := by
          apply key j
          · refine Submodule.sub_mem _ hg (Submodule.sum_mem _ fun i _ => ?_)
            rw [memT]
            intro c hc
            rw [smul_smul]
            apply (memT _ _).1 (he1 i)
            have e1 : n + 1 = (j + 1) + (n - j) := by omega
            rw [e1, pow_add, mul_left_comm]
            exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hπ _))
          · rw [smul_sub, hu, Finset.smul_sum, sub_eq_zero]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← he2 i, smul_smul, smul_smul]
            congr 1
            rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
        have hgw' := ih (by omega) _ hgw
        have hsplit : g = (g - w) + w := by abel
        rw [hsplit]
        exact Submodule.add_mem _ hgw' hw
    refine ⟨fL.toAddMonoidHom, ?_, ?_, ?_⟩
    · intro c a
      have : (Ideal.Quotient.mk (w0 ^ (n + 1)) c • a) = c • a := by
        funext i
        simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      simp only [LinearMap.toAddMonoidHom_coe]
      rw [this, map_smul]
    · haveI : Finite (𝓞 F ⧸ w0 ^ (n + 1)) :=
        Nat.finite_of_card_ne_zero (by rw [natCard_quotient_pow_eq]; positivity)
      let f' : (Fin h → 𝓞 F ⧸ w0 ^ (n + 1)) → T (n + 1) := fun a => ⟨fL a, hrange a⟩
      have hs : Function.Surjective f' := by
        intro g
        obtain ⟨a, ha⟩ := hsurj (n + 1) le_rfl g g.2
        exact ⟨a, Subtype.ext ha⟩
      have hcardeq : Nat.card (Fin h → 𝓞 F ⧸ w0 ^ (n + 1)) ≤ Nat.card (T (n + 1)) := by
        rw [hcard, Nat.card_fun, natCard_quotient_pow_eq, Nat.card_eq_fintype_card (α := Fin h),
          Fintype.card_fin, ← pow_mul]
      have hb := hs.bijective_of_nat_card_le hcardeq
      intro a b hab
      exact hb.1 (Subtype.ext hab)
    · intro g hg
      obtain ⟨a, ha⟩ := hsurj (n + 1) le_rfl g ((memT _ _).2 hg)
      exact ⟨a, ha⟩

end GlobalTheory
