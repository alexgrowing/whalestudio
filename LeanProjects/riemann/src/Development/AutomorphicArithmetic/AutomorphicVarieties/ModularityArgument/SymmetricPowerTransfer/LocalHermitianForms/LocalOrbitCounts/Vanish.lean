import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

private theorem vanish_det {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (B : Matrix (Fin 3) (Fin 3) K) (hB : B.det ≠ 0) (S : Submodule O (Fin 3 → K)) (hfg : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, x ⬝ᵥ B *ᵥ y ∈ (algebraMap O K).range) :
    ∃ (u : Oˣ) (s : K), s ≠ 0 ∧ B.det = algebraMap O K u * s ^ 2 := by
  classical
  have finj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have lin : ∀ (z : Fin 3 → K) (T : Set (Fin 3 → K)),
      (∀ x ∈ T, x ⬝ᵥ B *ᵥ z ∈ (algebraMap O K).range) →
      ∀ x ∈ Submodule.span O T, x ⬝ᵥ B *ᵥ z ∈ (algebraMap O K).range := by
    intro z T hT x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hT x hx
    | zero => simp
    | add x y _ _ h1 h2 => rw [add_dotProduct]; exact add_mem h1 h2
    | smul r x _ h =>
      rw [smul_dotProduct, Algebra.smul_def]
      exact mul_mem ⟨r, rfl⟩ h
  haveI : Module.Finite O S := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O S := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O S
  let b : Module.Basis ι O S := Module.Free.chooseBasis O S
  let v : ι → (Fin 3 → K) := fun i => (b i : Fin 3 → K)
  have hSv : Submodule.span O (Set.range v) = S := by
    have h1 : Set.range v = S.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hvS : ∀ i, v i ∈ S := fun i => (b i).2
  have den : ∀ y : Fin 3 → K, ∃ a : O, a ≠ 0 ∧ a • y ∈ S := by
    intro y
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
      (Finset.univ.image fun i => v i ⬝ᵥ B *ᵥ y)
    refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
    rw [hd]
    intro x hx
    rw [← hSv] at hx
    refine lin _ _ ?_ x hx
    rintro _ ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    refine ⟨r, ?_⟩
    rw [hr, Matrix.mulVec_smul, dotProduct_smul]
  have hliO : LinearIndependent O v := b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).1 hliO
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro y _
    obtain ⟨a, ha, hay⟩ := den y
    have ha' : algebraMap O K a ≠ 0 := by
      intro h; exact ha (finj (by rw [h, map_zero]))
    have h1 : a • y ∈ Submodule.span K (Set.range v) := by
      rw [← hSv] at hay
      exact Submodule.span_le_restrictScalars O K _ hay
    have h2 : y = (algebraMap O K a)⁻¹ • (a • y) := by
      rw [← algebraMap_smul K a y, smul_smul, inv_mul_cancel₀ ha', one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  let bK := Module.Basis.mk hliK hspK
  have hcard : Fintype.card ι = 3 := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : Fin 3 ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let V : Matrix (Fin 3) (Fin 3) K := Matrix.of fun r j => v (e j) r
  have hVu : IsUnit V := by
    rw [← linearIndependent_cols_iff_isUnit]
    have : V.col = v ∘ e := by
      funext j r
      rfl
    rw [this]
    exact hliK.comp e e.injective
  have hVd : V.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det V).1 hVu).ne_zero
  have Gent : ∀ i j, (V.transpose * B * V) i j = v (e i) ⬝ᵥ B *ᵥ v (e j) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
      Finset.mul_sum, V, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hG : ∀ i j, ∃ g : O, algebraMap O K g = (V.transpose * B * V) i j := by
    intro i j
    rw [Gent]
    exact (hd (v (e j))).1 (hvS _) _ (hvS _)
  choose g hg using hG
  let Gi : Matrix (Fin 3) (Fin 3) O := Matrix.of g
  have hGi : (algebraMap O K).mapMatrix Gi = V.transpose * B * V := by
    ext i j
    simp [Gi, hg]
  have hMd : (V.transpose * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hVd hB
  let Y := (V.transpose * B)⁻¹
  have hMY : V.transpose * B * Y = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hMd)
  have hyS : ∀ j, (fun r => Y r j) ∈ S := by
    intro j
    rw [hd]
    intro x hx
    rw [← hSv] at hx
    refine lin _ _ ?_ x hx
    rintro _ ⟨i, rfl⟩
    obtain ⟨i', rfl⟩ := e.surjective i
    have : v (e i') ⬝ᵥ B *ᵥ (fun r => Y r j) = (V.transpose * B * Y) i' j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
        Finset.mul_sum, V, Matrix.of_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hMY, Matrix.one_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  let C : Matrix (Fin 3) (Fin 3) O := Matrix.of fun k j => b.repr ⟨_, hyS j⟩ (e k)
  have hYC : Y = V * (algebraMap O K).mapMatrix C := by
    ext r j
    have h := congrArg (fun z : S => (z : Fin 3 → K) r) (b.sum_repr ⟨_, hyS j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at h
    rw [← h, ← e.sum_comp]
    simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, C, V, Matrix.of_apply,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have hGC : (algebraMap O K).mapMatrix Gi * (algebraMap O K).mapMatrix C = 1 := by
    rw [hGi, Matrix.mul_assoc (V.transpose * B), ← hYC, hMY]
  have hdet : algebraMap O K (Gi.det * C.det) = 1 := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, hGC, Matrix.det_one]
  have hGu : IsUnit Gi.det := isUnit_iff_exists_inv.2 ⟨C.det, finj (by rw [hdet, map_one])⟩
  refine ⟨hGu.unit, V.det⁻¹, inv_ne_zero hVd, ?_⟩
  have h1 : algebraMap O K (hGu.unit : O) = V.det * B.det * V.det := by
    rw [IsUnit.unit_spec, RingHom.map_det, hGi, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [h1]
  field_simp

private theorem vanish_unit {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ : K} (hl : IsLoc O Δ) (hΔ : ¬ IsSquare Δ) (l : Lsq K Δ) (hl0 : l ≠ 0) :
    ∃ (k : K) (u u' : Lsq K Δ), k ≠ 0 ∧ IsInt O u ∧ IsInt O u' ∧ u * u' = 1 ∧ l = algebraMap K _ k * u := by
  classical
  haveI := hl.frac
  obtain ⟨ε, s, hs0, hΔs⟩ := hl.even
  have hdesc : Δ * s⁻¹ ^ 2 = algebraMap O K ε := by
    rw [hΔs]; field_simp
  have D := fun x => (descent O K Δ hl s⁻¹ ε hdesc x).1
  have nosq : ∀ r : O, r ^ 2 = ε → False := by
    intro r hr
    apply hΔ
    refine ⟨algebraMap O K r * s, ?_⟩
    rw [hΔs, ← hr, map_pow]
    ring
  have unitN : ∀ A B : O, IsUnit A ∨ IsUnit B → IsUnit (A ^ 2 - (ε : O) * B ^ 2) := by
    intro A B hAB
    by_contra hn
    have hm : A ^ 2 - (ε : O) * B ^ 2 ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).2 ((mem_nonunits_iff).2 hn)
    have hAB' : IsUnit A ∧ IsUnit B := by
      rcases hAB with hA | hB
      · refine ⟨hA, ?_⟩
        by_contra hB
        have hBm : B ∈ IsLocalRing.maximalIdeal O :=
          (IsLocalRing.mem_maximalIdeal _).2 ((mem_nonunits_iff).2 hB)
        have h1 : (ε : O) * B ^ 2 ∈ IsLocalRing.maximalIdeal O :=
          Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hBm 2 (by norm_num))
        have h2 : A ^ 2 ∈ IsLocalRing.maximalIdeal O := by
          have := Ideal.add_mem _ hm h1
          rwa [sub_add_cancel] at this
        exact IsLocalRing.notMem_maximalIdeal.2 (hA.pow 2) h2
      · refine ⟨?_, hB⟩
        by_contra hA
        have hAm : A ∈ IsLocalRing.maximalIdeal O :=
          (IsLocalRing.mem_maximalIdeal _).2 ((mem_nonunits_iff).2 hA)
        have h1 : A ^ 2 ∈ IsLocalRing.maximalIdeal O := Ideal.pow_mem_of_mem _ hAm 2 (by norm_num)
        have h2 : (ε : O) * B ^ 2 ∈ IsLocalRing.maximalIdeal O := by
          have := Ideal.sub_mem _ h1 hm
          rwa [sub_sub_cancel] at this
        exact IsLocalRing.notMem_maximalIdeal.2 ((ε.isUnit).mul (hB.pow 2)) h2
    obtain ⟨hA, hB⟩ := hAB'
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ hl (ε : O) (A * ↑hB.unit⁻¹) (hA.mul (Units.isUnit _)) (by
      have hBi : B * ↑hB.unit⁻¹ = 1 := hB.mul_val_inv
      have : (ε : O) - (A * ↑hB.unit⁻¹) ^ 2 = -(↑hB.unit⁻¹ : O) ^ 2 * (A ^ 2 - (ε : O) * B ^ 2) := by
        linear_combination (-(ε : O) * (B * ↑hB.unit⁻¹ + 1)) * hBi
      rw [this]
      exact Ideal.mul_mem_left _ _ hm)
    exact nosq r hr
  have mk : ∀ A B : O, IsUnit A ∨ IsUnit B → ∀ k : K, k ≠ 0 → l.re = k * algebraMap O K A →
      l.im = k * (s⁻¹ * algebraMap O K B) →
      ∃ (k : K) (u u' : Lsq K Δ), k ≠ 0 ∧ IsInt O u ∧ IsInt O u' ∧ u * u' = 1 ∧
        l = algebraMap K _ k * u := by
    intro A B hAB k hk hre him
    obtain ⟨w, hw⟩ := unitN A B hAB
    refine ⟨k, ⟨algebraMap O K A, s⁻¹ * algebraMap O K B⟩,
      ⟨algebraMap O K (A * ↑w⁻¹), s⁻¹ * algebraMap O K (-B * ↑w⁻¹)⟩, hk, ?_, ?_, ?_, ?_⟩
    · exact (D _).2 ⟨⟨A, rfl⟩, B, rfl⟩
    · exact (D _).2 ⟨⟨_, rfl⟩, _, rfl⟩
    · have hwK : algebraMap O K (↑w) * algebraMap O K (↑w⁻¹ : O) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      have hwv : algebraMap O K ↑w
          = (algebraMap O K A) ^ 2 - Δ * (s⁻¹ * algebraMap O K B) ^ 2 := by
        rw [hw, map_sub, map_mul, map_pow, map_pow, ← hdesc]
        ring
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one, map_mul, map_neg]
        linear_combination (-(algebraMap O K (↑w⁻¹ : O))) * hwv + hwK
      · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_one, map_mul, map_neg]
        ring
    · apply QuadraticAlgebra.ext
      · simp [hre]
      · simp [him]
  have hne : l.re ≠ 0 ∨ l.im * s ≠ 0 := by
    by_contra h
    push_neg at h
    apply hl0
    apply QuadraticAlgebra.ext
    · simpa using h.1
    · simpa [hs0] using h.2
  by_cases hc : l.re ≠ 0 ∧ IsLocalization.IsInteger O (l.im * s / l.re)
  · obtain ⟨ha, B, hB⟩ := hc
    refine mk 1 B (Or.inl isUnit_one) l.re ha (by simp) ?_
    rw [hB]
    field_simp
  · have hβ : l.im * s ≠ 0 := by
      rcases hne with h | h
      · intro h0
        apply hc
        refine ⟨h, 0, ?_⟩
        simp [h0]
      · exact h
    have hint : IsLocalization.IsInteger O (l.re / (l.im * s)) := by
      by_cases ha : l.re = 0
      · exact ⟨0, by simp [ha]⟩
      · rcases ValuationRing.isInteger_or_isInteger O (l.im * s / l.re) with h | h
        · exact absurd ⟨ha, h⟩ hc
        · simpa [inv_div] using h
    obtain ⟨A, hA⟩ := hint
    refine mk A 1 (Or.inr isUnit_one) (l.im * s) hβ ?_ ?_
    · rw [hA]
      have him0 : l.im ≠ 0 := left_ne_zero_of_mul hβ
      field_simp
    · simp only [map_one, mul_one]
      field_simp

private theorem vanish_inert {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ : K} (hl : IsLoc O Δ) (hΔ : ¬ IsSquare Δ) (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (x : K) (hx : x ≠ 0) (t : Lsq K Δ)
    (ht : IsUnit t) (hB : B.det = algebraMap K _ x * t ^ 2) (S : Submodule O (Fin 3 → Lsq K Δ)) (hfg : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, IsInt O (x ⬝ᵥ B *ᵥ y)) : EvenVal O x := by
  haveI : IsFractionRing O K := hl.frac
  haveI : Fact (∀ r : K, r ^ 2 ≠ Δ + 0 * r) := ⟨fun r hr => hΔ ⟨r, by rw [← sq]; simpa using hr.symm⟩⟩
  letI : Field (Lsq K Δ) := inferInstanceAs (Field (QuadraticAlgebra K Δ 0))
  have memI : ∀ w : Lsq K Δ, IsInt O w → w ∈ integralClosure O (Lsq K Δ) := fun w hw => hw
  have hK : ∀ k : K, IsIntegral O (algebraMap K (Lsq K Δ) k) → ∃ a : O, algebraMap O K a = k := by
    intro k hk
    have h1 : IsIntegral O k := (isIntegral_algebraMap_iff (algebraMap K (Lsq K Δ)).injective).1 hk
    exact IsIntegrallyClosed.isIntegral_iff.1 h1
  haveI hfr : IsFractionRing (integralClosure O (Lsq K Δ)) (Lsq K Δ) :=
    integralClosure.isFractionRing_of_finite_extension K (Lsq K Δ)
  haveI hpid : IsPrincipalIdealRing (integralClosure O (Lsq K Δ)) := by
    constructor
    intro I
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (I.comap (algebraMap O (integralClosure O (Lsq K Δ))))).principal
    refine ⟨⟨algebraMap O (integralClosure O (Lsq K Δ)) g, ?_⟩⟩
    apply le_antisymm
    · intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Submodule.zero_mem _
      · have hz0' : (z : Lsq K Δ) ≠ 0 := fun h => hz0 (Subtype.ext h)
        obtain ⟨k, u, u', hk, hu, hu', huu, hzk⟩ := vanish_unit hl hΔ (z : Lsq K Δ) hz0'
        have hku : algebraMap K (Lsq K Δ) k = z * u' := by
          rw [hzk, mul_assoc, huu, mul_one]
        obtain ⟨a, ha⟩ := hK k (by rw [hku]; exact z.2.mul hu')
        have haI : a ∈ I.comap (algebraMap O (integralClosure O (Lsq K Δ))) := by
          rw [Ideal.mem_comap]
          have : algebraMap O (integralClosure O (Lsq K Δ)) a = z * ⟨u', memI u' hu'⟩ := by
            apply Subtype.ext
            show algebraMap O (Lsq K Δ) a = (z : Lsq K Δ) * u'
            rw [← hku, ← ha, IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
          rw [this]
          exact I.mul_mem_right _ hz
        rw [hg, Submodule.mem_span_singleton] at haI
        obtain ⟨r, hr⟩ := haI
        rw [Submodule.mem_span_singleton]
        refine ⟨algebraMap O (integralClosure O (Lsq K Δ)) r * ⟨u, memI u hu⟩, ?_⟩
        apply Subtype.ext
        show (algebraMap O (Lsq K Δ) r * u) * algebraMap O (Lsq K Δ) g = (z : Lsq K Δ)
        rw [hzk, ← ha, ← hr, smul_eq_mul]
        simp only [IsScalarTower.algebraMap_apply O K (Lsq K Δ), map_mul]
        ring
    · rw [Submodule.span_singleton_le_iff_mem]
      have : g ∈ I.comap (algebraMap O (integralClosure O (Lsq K Δ))) := by
        rw [hg]; exact Submodule.mem_span_singleton_self g
      exact this
  have hSL : ∀ (c : Lsq K Δ), IsInt O c → ∀ y ∈ S, c • y ∈ S := by
    intro c hc y hy
    rw [hd] at hy ⊢
    intro w hw
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    exact hc.mul (hy w hw)
  let S' : Submodule (integralClosure O (Lsq K Δ)) (Fin 3 → Lsq K Δ) :=
    { carrier := S, add_mem' := S.add_mem, zero_mem' := S.zero_mem,
      smul_mem' := fun c y hy => hSL c c.2 y hy }
  have hfg' : S'.FG := by
    obtain ⟨s, hs⟩ := hfg
    refine ⟨s, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      show y ∈ S
      rw [← hs]; exact Submodule.subset_span hy
    · intro y hy
      have hy' : y ∈ Submodule.span O (s : Set (Fin 3 → Lsq K Δ)) := by rw [hs]; exact hy
      exact Submodule.span_le_restrictScalars O (integralClosure O (Lsq K Δ)) _ hy'
  have hd' : ∀ y, y ∈ S' ↔ ∀ w ∈ S', w ⬝ᵥ B *ᵥ y ∈ (algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ)).range := by
    intro y
    show y ∈ S ↔ ∀ w ∈ S, _
    rw [hd]
    refine forall₂_congr fun w _ => ⟨fun h => ⟨⟨_, memI _ h⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    rw [← hz]
    exact z.2
  have hB0 : B.det ≠ 0 := by
    rw [hB]
    exact mul_ne_zero ((map_ne_zero _).2 hx) (pow_ne_zero _ ht.ne_zero)
  obtain ⟨u, s, hs, hdet⟩ := vanish_det B hB0 S' hfg' hd'
  have ht0 : t ≠ 0 := ht.ne_zero
  obtain ⟨k, v, v', hk, hv, hv', hvv, hqk⟩ := vanish_unit hl hΔ (s * t⁻¹) (mul_ne_zero hs (inv_ne_zero ht0))
  have hkL : algebraMap K (Lsq K Δ) k ≠ 0 := (map_ne_zero _).2 hk
  have h1 : algebraMap K (Lsq K Δ) x
      = algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) u * (s * t⁻¹) ^ 2 := by
    have e := hB.symm.trans hdet
    field_simp
    linear_combination e
  have e1 : algebraMap K (Lsq K Δ) (x / k ^ 2)
      = algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) u * v ^ 2 := by
    rw [map_div₀, map_pow, h1, hqk]
    field_simp
  have hUU : algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) u
      * algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have e2 : algebraMap K (Lsq K Δ) (k ^ 2 / x)
      = algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) ↑u⁻¹ * v' ^ 2 := by
    rw [show k ^ 2 / x = (x / k ^ 2)⁻¹ by rw [inv_div], map_inv₀, e1]
    apply inv_eq_of_mul_eq_one_right
    calc algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) u * v ^ 2
          * (algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) ↑u⁻¹ * v' ^ 2)
        = (algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) u
          * algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ) ↑u⁻¹) * (v * v') ^ 2 := by ring
      _ = 1 := by rw [hUU, hvv]; ring
  obtain ⟨a, ha⟩ := hK _ (by rw [e1]; exact (u : integralClosure O (Lsq K Δ)).2.mul (hv.pow 2))
  obtain ⟨b, hb⟩ := hK _ (by rw [e2]; exact ((u⁻¹ : (integralClosure O (Lsq K Δ))ˣ) : integralClosure O (Lsq K Δ)).2.mul (hv'.pow 2))
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, ha, hb, map_one]
    field_simp
  refine ⟨Units.mkOfMulEqOne a b hab, k, hk, ?_⟩
  show x = algebraMap O K a * k ^ 2
  rw [ha]
  field_simp

private theorem exists_algHom_lsq_of_sq_eq {K : Type} [Field K] {Δ : K} (r : K) (hr : Δ = r * r) :
    ∃ φ : Lsq K Δ →ₐ[K] K, ∀ z : Lsq K Δ, φ z = z.re + r * z.im := by
  refine ⟨QuadraticAlgebra.lift ⟨r, by simp [hr]⟩, fun z => ?_⟩
  simp [QuadraticAlgebra.lift]
  ring

private theorem vanish_split {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ : K} (hl : IsLoc O Δ) (hΔ : IsSquare Δ) (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (x : K) (hx : x ≠ 0) (t : Lsq K Δ)
    (ht : IsUnit t) (hB : B.det = algebraMap K _ x * t ^ 2) (S : Submodule O (Fin 3 → Lsq K Δ)) (hfg : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, IsInt O (x ⬝ᵥ B *ᵥ y)) : EvenVal O x := by
  haveI := hl.frac
  have h2 : (2 : K) ≠ 0 := by
    have := ((hl.two).map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hΔ0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, hus⟩ := hl.even
    rw [hus]
    exact mul_ne_zero ((u.isUnit.map (algebraMap O K)).ne_zero) (pow_ne_zero _ hs)
  obtain ⟨δ, hδ⟩ := hΔ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ0 (by simp [hδ])
  obtain ⟨φ₁, hφ₁⟩ := exists_algHom_lsq_of_sq_eq δ hδ
  obtain ⟨φ₂, hφ₂⟩ := exists_algHom_lsq_of_sq_eq (Δ := Δ) (-δ) (by rw [hδ]; ring)
  set e : Lsq K Δ := ⟨1 / 2, 1 / (2 * δ)⟩ with he
  have e1 : φ₁ e = 1 := by
    rw [hφ₁, he]
    field_simp
    try norm_num
  have e2 : φ₂ e = 0 := by
    rw [hφ₂, he]
    field_simp
    ring
  have hee : e * e = e := by
    apply QuadraticAlgebra.ext
    · simp only [he, QuadraticAlgebra.re_mul]
      rw [hδ]
      field_simp
      ring
    · simp only [he, QuadraticAlgebra.im_mul]
      field_simp
      ring
  have eint : IsIntegral O e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).sub_of_left (by
        rw [Polynomial.degree_X, Polynomial.degree_X_pow]
        norm_num)
    · simp [sq, hee]
  have decomp : ∀ z : Lsq K Δ,
      z = algebraMap K _ (φ₁ z) * e + algebraMap K _ (φ₂ z) * (1 - e) := by
    intro z
    rw [hφ₁, hφ₂]
    apply QuadraticAlgebra.ext
    · simp [he, QuadraticAlgebra.algebraMap_eq]
      field_simp
      ring
    · simp [he, QuadraticAlgebra.algebraMap_eq]
      field_simp
      ring
  have intcrit : ∀ z : Lsq K Δ, φ₁ z ∈ (algebraMap O K).range →
      φ₂ z ∈ (algebraMap O K).range → IsIntegral O z := by
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    rw [decomp z, ← ha, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (isIntegral_algebraMap.mul eint).add (isIntegral_algebraMap.mul (isIntegral_one.sub eint))
  have fwd : ∀ z : Lsq K Δ, IsIntegral O z → φ₁ z ∈ (algebraMap O K).range := by
    intro z hz
    exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (hz.map φ₁))
  have tr : ∀ (φ : Lsq K Δ →ₐ[K] K) (v w : Fin 3 → Lsq K Δ),
      φ (v ⬝ᵥ B *ᵥ w) = (φ ∘ v) ⬝ᵥ (B.map φ) *ᵥ (φ ∘ w) := by
    intro φ v w
    have h1 := RingHom.map_dotProduct (φ : Lsq K Δ →+* K) v (B *ᵥ w)
    rw [show ((φ : Lsq K Δ →+* K) ∘ (B *ᵥ w)) = (B.map φ) *ᵥ (φ ∘ w) from
      funext fun i => RingHom.map_mulVec (φ : Lsq K Δ →+* K) B w i] at h1
    exact h1
  have hφt : φ₁ t ≠ 0 := (ht.map φ₁).ne_zero
  have hdet : (B.map φ₁).det = x * (φ₁ t) ^ 2 := by
    have h1 := RingHom.map_det (φ₁ : Lsq K Δ →+* K) B
    rw [hB] at h1
    simp only [map_mul, map_pow, RingHom.coe_coe, AlgHom.commutes] at h1
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at h1
    exact h1.symm
  let F : (Fin 3 → Lsq K Δ) →ₗ[O] (Fin 3 → K) :=
    ((φ₁.restrictScalars O).toLinearMap).compLeft (Fin 3)
  have hF : ∀ v, F v = φ₁ ∘ v := fun v => rfl
  obtain ⟨u, s, hs, hus⟩ := vanish_det (O := O) (K := K) (B.map φ₁)
    (by rw [hdet]; exact mul_ne_zero hx (pow_ne_zero _ hφt)) (S.map F) (hfg.map F) (by
      intro y'
      constructor
      · rintro ⟨y, hy, rfl⟩ x' ⟨x₀, hx₀, rfl⟩
        have h1 := fwd _ ((hd y).1 hy x₀ hx₀)
        rw [tr] at h1
        simpa only [hF] using h1
      · intro h
        refine ⟨fun i => algebraMap K _ (y' i) * e, ?_, ?_⟩
        · rw [SetLike.mem_coe, hd]
          intro x₀ hx₀
          apply intcrit
          · rw [tr]
            have h3 : (φ₁ ∘ fun i => algebraMap K (Lsq K Δ) (y' i) * e) = y' := by
              funext i
              simp [e1]
            rw [h3]
            exact h _ ⟨x₀, hx₀, rfl⟩
          · rw [tr]
            have h3 : (φ₂ ∘ fun i => algebraMap K (Lsq K Δ) (y' i) * e) = 0 := by
              funext i
              simp [e2]
            rw [h3]
            simp
        · funext i
          simp [hF, e1])
  refine ⟨u, s / φ₁ t, div_ne_zero hs hφt, ?_⟩
  rw [hdet] at hus
  field_simp
  linear_combination hus

private theorem vanish_sigL_mul {K : Type} [Field K] {Δ τ : K} (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  have hτ : star ((algebraMap K (Lsq K Δ)) τ) = (algebraMap K (Lsq K Δ)) τ := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  apply QuadraticAlgebra.ext
  · simp [sigL, star_mul', star_add, star_neg, star_one]
  · simp [sigL, star_mul', star_add, hτ]

private theorem vanish_sigL_sigL {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

theorem UpperTheory.V.Z.Sym.Loc.vanish :
    UpperTheory.V.Z.Sym.Loc.Vanish := by
  intro O K _ _ _ _ _ Δ τ hL c d m hD hc
  obtain ⟨S, hS⟩ : ∃ S, IsFix O c d m S := by
    by_contra hno
    push_neg at hno
    apply hc
    unfold lcount wcount
    apply finsum_eq_zero_of_forall_eq_zero
    intro o
    simp [hno]
  have hsem : ∀ y : Sp Δ τ, semi d (semi d y) = (y.1, ofE Δ ω * y.2) := by
    intro y
    simp only [semi, star_star, vanish_sigL_mul, vanish_sigL_sigL, ← mul_assoc, hD.d_norm]
  have hτ2 : τ - 2 ≠ 0 := by
    intro h
    apply hD.reg
    rw [sub_eq_zero.1 h]
    norm_num
  haveI := hL.frac
  obtain ⟨s, hs⟩ := hS.fg
  have memS : ∀ y, y ∈ S ↔ y ∈ Submodule.span O (s : Set (Sp Δ τ)) := by
    intro y
    rw [hs]
    rfl
  have inS : ∀ y ∈ S, semi d y ∈ S := by
    intro y hy
    have := Set.mem_image_of_mem (semi d) hy
    rwa [hS.stab] at this
  have preS : ∀ y ∈ S, ∃ z ∈ S, semi d z = y := by
    intro y hy
    rw [← hS.stab] at hy
    exact hy
  have hω2 : ofE Δ ω * ofE Δ ω = algebraMap K (EL Δ τ) τ * ofE Δ ω - 1 := by
    have h1 : (ofE Δ ω : EL Δ τ) = ⟨0, 1⟩ := by
      ext <;> simp [ofE]
    have h2 : (algebraMap K (EL Δ τ) τ) = ⟨algebraMap K (Lsq K Δ) τ, 0⟩ := by
      rfl
    rw [h1, h2]
    ext <;> simp
  have hV : ∀ y ∈ S, ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * y.2) ∈ S := by
    intro y hy
    obtain ⟨z1, hz1, rfl⟩ := preS y hy
    obtain ⟨z, hz, rfl⟩ := preS z1 hz1
    have h1 : semi d (semi d (semi d (semi d z))) ∈ S := inS _ (inS _ hy)
    have key : ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * (semi d (semi d z)).2)
        = semi d (semi d (semi d (semi d z))) + z - (semi d (semi d z) + semi d (semi d z)) := by
      simp only [hsem]
      refine Prod.ext ?_ ?_
      · simp
      · simp only [Prod.snd_add, Prod.snd_sub, map_sub, map_ofNat]
        linear_combination (-z.2) * hω2
    rw [key, memS]
    rw [memS] at h1 hz hy
    exact Submodule.sub_mem _ (Submodule.add_mem _ h1 hz) (Submodule.add_mem _ hy hy)
  have hex : ∃ y ∈ S, y.2 ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h01 : ((0 : Lsq K Δ), (1 : EL Δ τ)) ∈ S := by
      rw [hS.dual]
      intro x hx
      have hx2 := hno x hx
      simp [herm, hx2]
      exact isIntegral_zero
    exact one_ne_zero (hno _ h01)
  have hint : IsIntegral O (τ - 2) := by
    obtain ⟨y, hy, hy2⟩ := hex
    refine isIntegral_of_smul_mem_submodule
      (Submodule.span O (s : Set (Sp Δ τ)) ⊓ LinearMap.ker (LinearMap.fst O (Lsq K Δ) (EL Δ τ))) ?_ ?_ (τ - 2) ?_
    · intro hbot
      have hmem : ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * y.2) ∈
          Submodule.span O (s : Set (Sp Δ τ)) ⊓ LinearMap.ker (LinearMap.fst O (Lsq K Δ) (EL Δ τ)) :=
        ⟨(memS _).1 (hV y hy), by simp⟩
      rw [hbot, Submodule.mem_bot] at hmem
      have h2 := congrArg Prod.snd hmem
      simp only [Prod.snd_zero] at h2
      exact hy2 (((isUnit_iff_ne_zero.2 hτ2).map (algebraMap K (EL Δ τ))).mul_right_eq_zero.1 h2)
    · exact Submodule.FG.of_le ⟨s, rfl⟩ inf_le_left
    · intro n hn
      obtain ⟨hn1, hn2⟩ := hn
      have hn0 : n.1 = 0 := by simpa using hn2
      refine ⟨?_, by simp [hn0]⟩
      have := (memS _).1 (hV n ((memS _).2 hn1))
      have e : (τ - 2) • n = ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * n.2) :=
        Prod.ext (by simp [hn0]) (by simp [Algebra.smul_def])
      rw [e]
      exact this
  have hτO : τ ∈ (algebraMap O K).range := by
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨o + 2, ?_⟩
    rw [map_add, ho, map_ofNat]
    ring
  have hω1 : (ofE Δ ω : EL Δ τ) = ⟨0, 1⟩ := by
    ext <;> simp [ofE]
  have hωs : ofE Δ ω * star (ofE Δ ω) = (1 : EL Δ τ) := by
    rw [hω1]
    ext <;> simp
  have hωu : IsUnit (ofE Δ ω : EL Δ τ) := ⟨⟨_, _, hωs, by rw [mul_comm]; exact hωs⟩, rfl⟩
  have hsm : sigL m = star m := by
    have := congrArg star hD.m_star
    rwa [star_star] at this
  set ν : EL Δ τ := m * star (sigL d) with hνdef
  have hνs : star ν = ν * ofE Δ ω := by
    rw [hνdef, star_mul', star_star, ← hsm, hD.m_sig, ← hD.d_norm]
    ring
  have hp : ν.re = -ν.im - algebraMap K (Lsq K Δ) τ * ν.im := by
    have := congrArg QuadraticAlgebra.re hνs
    rw [hω1] at this
    simp at this
    linear_combination this
  have hνu : IsUnit ν :=
    hD.m_unit.mul (isUnit_of_mul_isUnit_right (hD.d_norm ▸ hωu)).star
  have hN : QuadraticAlgebra.norm ν = ν.im ^ 2 * (2 + algebraMap K (Lsq K Δ) τ) := by
    rw [QuadraticAlgebra.norm_def, hp]
    ring
  have hNu : IsUnit (ν.im ^ 2 * (2 + algebraMap K (Lsq K Δ) τ)) := hN ▸ hνu.map QuadraticAlgebra.norm
  have htu : IsUnit ((2 + algebraMap K (Lsq K Δ) τ) * ν.im) :=
    (isUnit_of_mul_isUnit_right hNu).mul ((isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left hNu))
  let Φ : Sp Δ τ →ₗ[O] (Fin 3 → Lsq K Δ) :=
    { toFun := fun x => ![x.1, x.2.re, x.2.im]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro r x
        funext i
        fin_cases i <;> simp }
  let Ψ : (Fin 3 → Lsq K Δ) → Sp Δ τ := fun v => (v 0, ⟨v 1, v 2⟩)
  have hΦΨ : ∀ v, Φ (Ψ v) = v := by
    intro v
    funext i
    fin_cases i <;> rfl
  have hΨΦ : ∀ x, Ψ (Φ x) = x := fun x => rfl
  let B : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
    !![algebraMap K (Lsq K Δ) c, 0, 0;
      0, 2 * ν.re + algebraMap K (Lsq K Δ) τ * ν.im, algebraMap K (Lsq K Δ) τ * ν.re + 2 * ν.im;
      0, algebraMap K (Lsq K Δ) τ * ν.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * ν.im,
        2 * ν.re + algebraMap K (Lsq K Δ) τ * ν.im]
  have hid : ∀ x y : Sp Δ τ, Φ x ⬝ᵥ B *ᵥ Φ y = herm c m x (semi d y) := by
    intro x y
    have e1 : herm c m x (semi d y) = algebraMap K (Lsq K Δ) c * x.1 * y.1
        + QuadraticAlgebra.trace (ν * x.2 * star y.2) := by
      simp only [herm, semi, star_star, vanish_sigL_mul, vanish_sigL_sigL, star_mul', hνdef]
      congr 2
      ring
    rw [e1, QuadraticAlgebra.trace_def]
    simp [Φ, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hdet : B.det = algebraMap K (Lsq K Δ) (c * (2 - τ)) * ((2 + algebraMap K (Lsq K Δ) τ) * ν.im) ^ 2 := by
    rw [Matrix.det_fin_three]
    simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      Matrix.tail_cons, map_mul, map_sub, map_ofNat]
    rw [hp]
    ring
  have hsemiS : ∀ y, y ∈ S ↔ semi d y ∈ S := by
    intro y
    refine ⟨inS y, fun h => ?_⟩
    obtain ⟨z, hz, hzy⟩ := preS _ h
    have h2 := congrArg (semi d) hzy
    rw [hsem, hsem] at h2
    simp only [Prod.mk.injEq] at h2
    obtain ⟨e1, e2⟩ := h2
    have e3 : z.2 = y.2 := hωu.mul_left_cancel e2
    have : z = y := Prod.ext e1 e3
    rwa [← this]
  have memS' : ∀ v, v ∈ Submodule.map Φ (Submodule.span O (s : Set (Sp Δ τ))) ↔ Ψ v ∈ S := by
    intro v
    rw [memS, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hΨΦ]
    · intro h
      exact ⟨Ψ v, h, hΦΨ v⟩
  have hdual' : ∀ v, v ∈ Submodule.map Φ (Submodule.span O (s : Set (Sp Δ τ))) ↔
      ∀ x ∈ Submodule.map Φ (Submodule.span O (s : Set (Sp Δ τ))), IsInt O (x ⬝ᵥ B *ᵥ v) := by
    intro v
    rw [memS', hsemiS, hS.dual]
    constructor
    · intro h x hx
      rw [memS'] at hx
      have := h _ hx
      rwa [← hid, hΦΨ, hΦΨ] at this
    · intro h x hx
      have := h (Φ x) ((memS' _).2 (by rwa [hΨΦ]))
      rw [← hΦΨ v, hid] at this
      exact this
  have hfg : (Submodule.map Φ (Submodule.span O (s : Set (Sp Δ τ)))).FG :=
    Submodule.FG.map Φ ⟨s, rfl⟩
  have hx0 : c * (2 - τ) ≠ 0 := mul_ne_zero hD.c_ne (by
    intro h
    apply hτ2
    linear_combination -h)
  refine ⟨hτO, ?_⟩
  by_cases hsq : IsSquare Δ
  · exact vanish_split hL hsq B _ hx0 _ htu hdet _ hfg hdual'
  · exact vanish_inert hL hsq B _ hx0 _ htu hdet _ hfg hdual'
