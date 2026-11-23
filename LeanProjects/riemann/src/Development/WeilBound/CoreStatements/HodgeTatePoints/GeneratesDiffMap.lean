import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  {D : HTChart A K c p R N Ω}
  {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
  {φ : A →+* O} {P : HTPoint C O c κ' N V Ω'} {ι : D.om →ₛₗ[φ] Ω'}

theorem om'_le_om (D : HTChart A K c p R N Ω) : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem_om' (D : HTChart A K c p R N Ω) {x : Ω} (hx : x ∈ D.om) :
    (p : A) ^ R • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem span_om' (hred : D.ReducesTo φ P ι) (hκ : κ' ∣ (p : O) ^ R) :
    Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) = P.om' := by
  have hn : ∀ y : Ω', (p ^ R) • y = (p : O) ^ R • y := fun y => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hι : ∀ x : D.om, ι ((p : A) ^ R • x) = (p : O) ^ R • ι x := fun x => by
    rw [ι.map_smulₛₗ, map_pow, map_natCast]
  have a1 : ∀ y ∈ P.om, (p : O) ^ R • y ∈ P.om' := by
    intro y hy
    obtain ⟨w, hw⟩ := hκ
    obtain ⟨x, hx, e⟩ := P.κ_mem _ (P.om.smul_mem w hy)
    exact ⟨x, hx, by rw [hw, mul_smul]; exact e⟩
  have a2 : ∀ y ∈ P.om, (p : O) ^ R • y ∈
      Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
    intro y hy
    rw [← hred.span_eq] at hy
    have : Submodule.span O (Set.range ι) ≤ (Submodule.span O
        (ι '' {x : D.om | (x : Ω) ∈ D.om'})).comap ((p : O) ^ R • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨(p : A) ^ R • x, pow_smul_mem_om' D x.2, hι x⟩
    exact this hy
  have ht : ∀ x, P.tate x ∈ P.T := by
    intro x
    refine P.T.sum_mem fun i _ => ?_
    rw [← (RingOfIntegers.basis E).sum_repr (x i), map_sum, LinearMap.sum_apply]
    refine P.T.sum_mem fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  apply le_antisymm
  · have h : D.om' ≤ (P.om'.comap ι).map D.om.subtype := by
      refine sup_le (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨⟨D.h x, D.h_mem x⟩, ?_, rfl⟩
        obtain ⟨y, hy, e⟩ := hred.ht_eq x
        change ι _ ∈ P.om'
        rw [e, hn]
        exact P.om'.add_mem ⟨_, ht x, rfl⟩ (a1 y hy)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨(p : A) ^ R • ⟨x, hx⟩, ?_, rfl⟩
        change ι _ ∈ P.om'
        rw [hι]
        refine a1 _ ?_
        rw [← hred.span_eq]
        exact Submodule.subset_span ⟨_, rfl⟩
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', e⟩ := h hx
    rw [← (Subtype.ext e : x' = x)]
    exact hx'
  · rw [HTPoint.om', Submodule.map_le_iff_le_comap]
    conv_lhs => rw [P.free.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    have e0 : P.ρ (RingOfIntegers.basis E k) (P.t i) =
        P.tate (Pi.single i (RingOfIntegers.basis E k)) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    obtain ⟨y, hy, e⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ Submodule.span O _
    rw [e0, eq_sub_of_add_eq e.symm, hn]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, Submodule.mem_sup_left
      (Submodule.subset_span ⟨_, rfl⟩), rfl⟩) (a2 y hy)

omit [NumberField E] in
theorem transfer_mul [NumberField E] (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d a' : A} {e : E} (h : algebraMap A K a' = algebraMap A K d * σ e) :
    algebraMap O C (φ a') = algebraMap O C (φ d) * σ' e := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨α, hα⟩ := hσ a
  obtain ⟨β, hβ⟩ := hσ b
  have h1 : a' * β = d * α := hAK (by
    rw [map_mul, map_mul, h, hα, hβ, map_div₀, mul_assoc,
      div_mul_cancel₀ _ ((map_ne_zero σ).2 hb0)])
  have h2 := congrArg (fun t => algebraMap O C (φ t)) h1
  simp only [map_mul, hφ a α hα, hφ b β hβ] at h2
  rw [map_div₀, ← mul_div_assoc, eq_div_iff ((map_ne_zero σ').2 hb0)]
  exact h2

theorem generatesDiff_map (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d : A} (hd : GeneratesDiff σ d) : GeneratesDiff σ' (φ d) := by
  apply le_antisymm
  · have key : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        ∃ a', algebraMap A K a' = y ∧ algebraMap O C (φ a') ∈
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ' (x : E)} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨x, hx, rfl⟩ := h
        obtain ⟨a', ha'⟩ := hσ x
        exact ⟨a', ha', Submodule.subset_span ⟨x, hx, hφ x a' ha'⟩⟩
      | zero => exact ⟨0, map_zero _, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, ha'⟩ := hy
        obtain ⟨b, hb, hb'⟩ := hz
        exact ⟨a + b, by rw [map_add, ha, hb], by
          rw [map_add, map_add]; exact Submodule.add_mem _ ha' hb'⟩
      | smul r y _ hy =>
        obtain ⟨a, ha, ha'⟩ := hy
        exact ⟨r * a, by rw [map_mul, ha, Algebra.smul_def], by
          rw [map_mul, map_mul, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha'⟩
    obtain ⟨a', ha, ha'⟩ := key _ (hd.le (Submodule.mem_span_singleton_self _))
    rw [hAK ha] at ha'
    exact (Submodule.span_singleton_le_iff_mem _ _).2 ha'
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    refine Submodule.mem_span_singleton.2 ⟨φ a, ?_⟩
    rw [← hφ x (a * d) (by rw [map_mul, ← ha, Algebra.smul_def]), map_mul, map_mul,
      Algebra.smul_def]

theorem smul_eigProj_eq (ρ : 𝓞 E →+* Module.End K Ω) {σ : E →+* K} {d : A}
    {cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A}
    (h : ∀ k, algebraMap A K (cc k) = algebraMap A K d * σ (dualInt E k)) (x : Ω) :
    d • eigProj ρ σ x = ∑ k, cc k • ρ (RingOfIntegers.basis E k) x := by
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K (cc k), h, mul_smul, algebraMap_smul]

theorem span_eigQuot {σ : E →+* K} {σ' : E →+* C} {d : A}
    (h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om)
    (h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x))
    {X : Submodule A Ω} (hX : X ≤ D.om) {X' : Submodule O Ω'}
    (hs : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ X}) = X') :
    Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ X, (y : Ω) = d • z}) =
      (eigQuot P.ρΩ σ' X').map (φ d • LinearMap.id) := by
  rw [eigQuot, eigQuot, ← Submodule.map_comp, ← hs, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, e⟩, rfl⟩
    exact ⟨_, ⟨⟨x, hX hx⟩, hx, rfl⟩, (h2 ⟨x, hX hx⟩ y e).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨_, h1 x x.2⟩, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, h2 x _ rfl⟩

end

theorem red_proj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → GeneratesDiff σ' (φ d) ∧ (∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om) ∧ (∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x)) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z}) = (P.omHT σ').map (φ d • LinearMap.id) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ D.om, (y : Ω) = d • z}) = (P.omRec σ').map (φ d • LinearMap.id) := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv κ' V _ _ _ _ Ω' _ _ _ _
    φ P ι hred σ σ' d hσ hφ hd hκ
  obtain ⟨-, hcc, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose cc hcc using hcc
  have h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om := by
    intro x hx
    rw [smul_eigProj_eq _ hcc]
    exact D.om.sum_mem fun k _ => D.om.smul_mem _ (D.om_stable _ x hx)
  have h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x →
      ι y = φ d • eigProj P.ρΩ σ' (ι x) := by
    intro x y e
    have hy : y = ∑ k, cc k • (⟨D.ρΩ (RingOfIntegers.basis E k) x, D.om_stable _ x x.2⟩ : D.om) := by
      apply Subtype.ext
      rw [e, smul_eigProj_eq _ hcc]
      simp
    rw [hy, map_sum, smul_eigProj_eq (cc := fun k => φ (cc k)) _
      (fun k => transfer_mul hAK hσ hφ (hcc k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ι.map_smulₛₗ, hred.lin]
  refine ⟨generatesDiff_map hAK hσ hφ hd, h1, h2,
    span_eigQuot h1 h2 (om'_le_om D) (span_om' hred hκ), span_eigQuot h1 h2 le_rfl ?_⟩
  rw [← hred.span_eq]
  congr 1
  ext w
  simp

end PositivityTheory.HtPt.Gb
