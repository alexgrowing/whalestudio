import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]

private theorem rk_fin [IsNoetherianRing O] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (j : ℤ)
    (hx : ∀ f ∈ 𝒜 j, x f = 0) (hfg : (oz 𝒜 j).FG) : Module.Finite O (cotLat x 𝒜 j) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  rw [Module.Finite.iff_fg]
  refine ⟨S.image (satSq x).mkQ, ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsA : s ∈ 𝒜 j := by
      have : s ∈ oz 𝒜 j := hS ▸ Submodule.subset_span hs
      exact this
    exact ⟨s, ⟨hsA, hx s hsA⟩, rfl⟩
  · rintro _ ⟨f, ⟨hf, -⟩, rfl⟩
    have hf' : f ∈ Submodule.span (𝒜 0) (S : Set A) := by
      rw [hS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul a b hb ih =>
      have hbA : b ∈ 𝒜 j := by
        have : b ∈ oz 𝒜 j := hS ▸ hb
        exact this
      have hxb : x b = 0 := hx b hbA
      have e : (satSq x).mkQ (a • b) = (satSq x).mkQ (x (a : A) • b) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        refine ⟨1, one_ne_zero, ?_⟩
        rw [one_smul, pow_two]
        have h1 : ((a : A) - algebraMap O A (x (a : A))) ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          simp
        have h2 : b ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          exact hxb
        have e2 : a • b - x (a : A) • b = ((a : A) - algebraMap O A (x (a : A))) * b := by
          rw [sub_mul, ← Algebra.smul_def]
          rfl
        rw [e2]
        exact Ideal.mul_mem_mul h1 h2
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ ih

private noncomputable def linPart {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem linPart_apply {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    linPart φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem linPart_sat {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) :
    ∀ f ∈ satSq x, linPart φ i f = 0 := by
  intro f hf
  obtain ⟨c, hc, hcf⟩ := hf
  have hker : ∀ g ∈ RingHom.ker x ^ 2, linPart φ i g = 0 := by
    intro g hg
    rw [pow_two] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      rw [linPart_apply, map_mul]
      apply MvPowerSeries.coeff_of_lt_order
      have ha0 : MvPowerSeries.constantCoeff (φ a) = 0 := by
        rw [h.const, RingHom.mem_ker.mp ha, map_zero]
      have hb0 : MvPowerSeries.constantCoeff (φ b) = 0 := by
        rw [h.const, RingHom.mem_ker.mp hb, map_zero]
      have hA := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr ha0
      have hB := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr hb0
      calc (((Finsupp.single i 1).degree : ℕ) : ℕ∞) = 1 := by simp
        _ < 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add hA hB
        _ ≤ ((φ a) * (φ b)).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  have h0 := hker _ hcf
  rw [map_smul, Algebra.smul_def, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd ((IsFractionRing.injective O (FractionRing O)) (h0.trans (map_zero _).symm)) hc
  · exact h0

private theorem linPart_wt {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : linPart φ i f = 0 := by
  rw [linPart_apply]
  apply h.graded j f hf
  simpa [Finsupp.weight_apply, Finsupp.sum_single_index] using hij

private theorem linPart_proj {τ : Type} {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i = j) (f : A) :
    linPart φ i (DirectSum.decompose 𝒜 f j) = linPart φ i f := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  rw [map_sum]
  by_cases hj : j ∈ (DirectSum.decompose 𝒜 f).support
  · rw [Finset.sum_eq_single j]
    · intro k _ hk
      exact linPart_wt h i (by rw [hij]; exact fun e => hk e.symm) (DirectSum.decompose 𝒜 f k).2
    · intro hn
      exact absurd hj hn
  · rw [DFinsupp.notMem_support_iff] at hj
    rw [hj]
    simp only [ZeroMemClass.coe_zero, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≠ j := by
      rintro rfl
      exact (DFinsupp.mem_support_iff.mp hk) hj
    exact linPart_wt h i (by rw [hij]; exact fun e => hk' e.symm) (DirectSum.decompose 𝒜 f k).2

end

theorem UpperTheory.V.Alg.M.rk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℤ → ℕ, SmoothPt 𝒜 x n → Module.Finite O (cotLat x 𝒜 (-1)) ∧ Module.finrank O (cotLat x 𝒜 (-1)) = n (-1) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW n hS
  obtain ⟨τ, _, wt, φ, hc, hn⟩ := hS
  classical
  have hfin : Module.Finite O (cotLat x 𝒜 (-1)) :=
    rk_fin 𝒜 x (-1) (hW.fixed (-1) (by norm_num)) (fg_holds O A 𝒜 x hW (-1))
  refine ⟨hfin, ?_⟩
  let Lq : (A ⧸ satSq x) →ₗ[O] ({i // wt i = -1} → FractionRing O) :=
    (satSq x).liftQ (LinearMap.pi fun i : {i // wt i = -1} => linPart φ i.1) (by
      intro f hf
      rw [LinearMap.mem_ker]
      funext i
      exact linPart_sat hc i.1 f hf)
  let L : cotLat x 𝒜 (-1) →ₗ[O] ({i // wt i = -1} → FractionRing O) := Lq ∘ₗ (cotLat x 𝒜 (-1)).subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨q, hq⟩ hLq
    obtain ⟨f, ⟨hf1, hf2⟩, rfl⟩ := hq
    have hx0 : x f = 0 := RingHom.mem_ker.mp hf2
    have hall : ∀ i : τ, MvPowerSeries.coeff (Finsupp.single i 1) (φ f) = 0 := by
      intro i
      rw [← linPart_apply]
      by_cases hi : wt i = -1
      · exact congrFun hLq ⟨i, hi⟩
      · exact linPart_wt hc i hi hf1
    have hs := hc.inj f hx0 hall
    apply Subtype.ext
    show (satSq x).mkQ f = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hs
  haveI : Module.IsTorsionFree O (FractionRing O) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O _)
  haveI : Module.IsTorsionFree O (cotLat x 𝒜 (-1)) :=
    Function.Injective.moduleIsTorsionFree (⇑L) hinj (fun r m => L.map_smul r m)
  have hup : Module.finrank O (cotLat x 𝒜 (-1)) ≤ Fintype.card {i // wt i = -1} := by
    let B := Module.Free.chooseBasis O (cotLat x 𝒜 (-1))
    have hli : LinearIndependent O (L ∘ B) := B.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hinj)
    have hli' := (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hli
    have h1 := hli'.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact h1
  choose F hF0 hF1 using fun i : {i // wt i = -1} => hc.onto i.1
  have hmem : ∀ k : {i // wt i = -1},
      (satSq x).mkQ (DirectSum.decompose 𝒜 (F k) (-1) : A) ∈ cotLat x 𝒜 (-1) := fun k =>
    ⟨_, ⟨(DirectSum.decompose 𝒜 (F k) (-1)).2,
      RingHom.mem_ker.mpr (hW.fixed (-1) (by norm_num) _ (DirectSum.decompose 𝒜 (F k) (-1)).2)⟩, rfl⟩
  let g : {i // wt i = -1} → cotLat x 𝒜 (-1) := fun k => ⟨_, hmem k⟩
  have hgv : ∀ k i : {i // wt i = -1}, L (g k) i = linPart φ i.1 (F k) := by
    intro k i
    show linPart φ i.1 (DirectSum.decompose 𝒜 (F k) (-1) : A) = _
    exact linPart_proj hc i.1 i.2 (F k)
  have hli : LinearIndependent O g := by
    apply LinearIndependent.of_comp L
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h1 := congrFun ha i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, hgv, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [linPart_apply, Algebra.smul_def, mul_eq_zero] at h1
      rcases h1 with h2 | h2
      · exact (IsFractionRing.injective O (FractionRing O)) (h2.trans (map_zero _).symm)
      · exact absurd h2 (hF0 i)
    · intro k _ hk
      rw [linPart_apply, hF1 k i.1 (fun e => hk (Subtype.ext e.symm)), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hlow : Fintype.card {i // wt i = -1} ≤ Module.finrank O (cotLat x 𝒜 (-1)) :=
    hli.fintype_card_le_finrank
  rw [← hn (-1), Nat.card_eq_fintype_card]
  exact le_antisymm hup hlow
