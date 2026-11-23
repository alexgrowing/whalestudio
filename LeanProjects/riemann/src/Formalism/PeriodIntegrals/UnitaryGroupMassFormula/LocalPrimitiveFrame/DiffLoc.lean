import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop

noncomputable section

namespace PI.LocFramePrimWork

open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def DiffLoc_psi (S : Set E) : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (inclR (F := F) (Fv F v) '' S)

def DiffLoc_P : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  DiffLoc_psi (E := E) v (Set.range ((↑) : 𝓞 E → E))

theorem DiffLoc_OEv (p : Fv F v ⊗[F] E) : p ∈ OEv (E := E) v ↔ p ∈ DiffLoc_P (E := E) v := by
  have h : (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ =
      inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E) := by
    ext y; simp
  unfold OEv DiffLoc_P DiffLoc_psi
  rw [h]
  rfl

theorem DiffLoc_psi_mul_mem (S : Set E) (hS : ∀ (o : 𝓞 E) (s : E), s ∈ S → (o : E) * s ∈ S)
    {y : Fv F v ⊗[F] E} (hy : y ∈ DiffLoc_psi v S) (o : 𝓞 E) :
    inclR (F := F) (Fv F v) (o : E) * y ∈ DiffLoc_psi v S := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [← map_mul]
    exact Submodule.subset_span ⟨_, hS o s hs, rfl⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem DiffLoc_span_le (Q : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E))
    (hQ : ∀ (o : 𝓞 E) (y : Fv F v ⊗[F] E), y ∈ Q → inclR (F := F) (Fv F v) (o : E) * y ∈ Q)
    (T : Set E) (hT : ∀ t ∈ T, inclR (F := F) (Fv F v) t ∈ Q) :
    DiffLoc_psi v (Submodule.span (𝓞 E) T : Set E) ≤ Q := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hT x hx
  | zero => rw [SetLike.mem_coe, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [SetLike.mem_coe, map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [SetLike.mem_coe, Algebra.smul_def, map_mul]; exact hQ o _ hx

theorem DiffLoc_frac_closed (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∀ (o : 𝓞 E) (s : E), s ∈ (I : Set E) → (o : E) * s ∈ (I : Set E) := by
  intro o s hs
  have := (I : Submodule (𝓞 E) E).smul_mem o hs
  rwa [Algebra.smul_def] at this

theorem DiffLoc_range_closed :
    ∀ (o : 𝓞 E) (s : E), s ∈ Set.range ((↑) : 𝓞 E → E) → (o : E) * s ∈ Set.range ((↑) : 𝓞 E → E) := by
  rintro o _ ⟨t, rfl⟩
  exact ⟨o * t, by push_cast; rfl⟩

theorem DiffLoc_psi_mul (I J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    DiffLoc_psi v ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      DiffLoc_psi v (I : Set E) * DiffLoc_psi v (J : Set E) := by
  apply le_antisymm
  · have h : ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
        (Submodule.span (𝓞 E) ((I : Set E) * (J : Set E)) : Set E) := by
      show (((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) : Set E) = _
      rw [FractionalIdeal.coe_mul, Submodule.mul_eq_span_mul_set]
      rfl
    rw [h]
    apply DiffLoc_span_le
    · intro o y hy
      refine Submodule.mul_induction_on (C := fun y =>
        inclR (F := F) (Fv F v) (o : E) * y ∈ DiffLoc_psi v (I : Set E) * DiffLoc_psi v (J : Set E))
        hy (fun m hm n hn => ?_) (fun x y hx hy => ?_)
      · rw [← mul_assoc]
        exact Submodule.mul_mem_mul (DiffLoc_psi_mul_mem v _ (DiffLoc_frac_closed I) hm o) hn
      · rw [mul_add]; exact add_mem hx hy
    · rintro _ ⟨i, hi, j, hj, rfl⟩
      rw [map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, hi, rfl⟩) (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [DiffLoc_psi, DiffLoc_psi, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    show inclR (F := F) (Fv F v) i * inclR (F := F) (Fv F v) j ∈ _
    rw [← map_mul]
    exact Submodule.subset_span ⟨i * j, FractionalIdeal.mul_mem_mul hi hj, rfl⟩

theorem DiffLoc_psi_one :
    DiffLoc_psi v ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) = DiffLoc_P (E := E) v := by
  unfold DiffLoc_P
  congr 1
  ext x
  exact (FractionalIdeal.mem_one_iff _).trans Iff.rfl

theorem DiffLoc_PP : DiffLoc_P (E := E) v * DiffLoc_P (E := E) v = DiffLoc_P (E := E) v := by
  rw [← DiffLoc_psi_one, ← DiffLoc_psi_mul, mul_one]

theorem DiffLoc_exists : ∃ d, IsDiffVal v d := by
  classical
  have hD : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (differentIdeal ℤ (𝓞 F)) : (differentIdeal ℤ (𝓞 F)).FG)
  let val : 𝓞 F → _ := fun x => Valued.v (algebraMap F (Fv F v) (x : F))
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hD
    rw [← hs]
    simp
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image s val hsne
  have hle : ∀ x ∈ differentIdeal ℤ (𝓞 F), val x ≤ val g := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp [val]
    | add x y _ _ hx hy =>
      calc val (x + y) = Valued.v (algebraMap F (Fv F v) (x : F) + algebraMap F (Fv F v) (y : F)) := by
            simp [val]
        _ ≤ max (val x) (val y) := Valuation.map_add _ _ _
        _ ≤ val g := max_le hx hy
    | smul o x _ hx =>
      have ho : val o ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1
          (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v o)
      calc val (o • x) = val o * val x := by simp [val]
        _ ≤ 1 * val x := mul_le_mul_left ho _
        _ = val x := one_mul _
        _ ≤ val g := hx
  have hg0 : val g ≠ 0 := by
    intro h0
    apply hD
    rw [eq_bot_iff]
    intro x hx
    have h1 : val x = 0 := le_antisymm (h0 ▸ hle x hx) zero_le
    have h2 : (x : F) = 0 := (algebraMap F (Fv F v)).injective (by
      rw [map_zero]; exact (Valuation.zero_iff _).1 h1)
    rw [Submodule.mem_bot]
    exact_mod_cast h2
  refine ⟨algebraMap F (Fv F v) (g : F), ?_, ?_, ?_⟩
  · intro h; apply hg0; simp [val, h]
  · intro x hx; exact hle x hx
  · exact ⟨g, hs ▸ Submodule.subset_span hg, rfl⟩

theorem DiffLoc_isDiffVal : IsDiffVal v (dV v) := by
  have h := DiffLoc_exists v
  unfold dV
  rw [dif_pos h]
  exact h.choose_spec

theorem DiffLoc_sc_eq (x : Fv F v) : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := rfl

theorem DiffLoc_sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b :=
  map_mul (algebraMap (Fv F v) (Fv F v ⊗[F] E)) a b

theorem DiffLoc_inclR_alg (x : F) :
    inclR (F := F) (Fv F v) (algebraMap F E x) = sc (E := E) v (algebraMap F (Fv F v) x) := by
  show (1 : Fv F v) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Fv F v) x) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact (TensorProduct.smul_tmul x (1 : Fv F v) (1 : E)).symm

theorem DiffLoc_ddE_eq : ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
    (Submodule.span (𝓞 E) ((fun d : 𝓞 F => algebraMap F E (d : F)) ''
      (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) : Set E) := by
  show (((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) : Set E) = _
  unfold ddE
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule, Ideal.map, Ideal.span, Submodule.map_span,
    Set.image_image]
  rfl

theorem DiffLoc_psi_ddE :
    DiffLoc_psi v ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} * DiffLoc_P (E := E) v := by
  obtain ⟨hδ, hle, d0, hd0mem, heq⟩ := DiffLoc_isDiffVal v
  have hvδ : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 hδ
  apply le_antisymm
  · rw [DiffLoc_ddE_eq]
    apply DiffLoc_span_le
    · intro o y hy
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_span_singleton_mul.1 hy
      rw [mul_left_comm]
      exact Submodule.mem_span_singleton_mul.2 ⟨_, DiffLoc_psi_mul_mem v _ DiffLoc_range_closed hp o, rfl⟩
    · rintro _ ⟨d, hd, rfl⟩
      show inclR (F := F) (Fv F v) (algebraMap F E (d : F)) ∈ _
      set t := algebraMap F (Fv F v) (d : F) * (dV v)⁻¹ with ht_def
      have ht : t ∈ v.adicCompletionIntegers F := by
        show Valued.v t ≤ 1
        rw [ht_def, map_mul, map_inv₀]
        calc Valued.v (algebraMap F (Fv F v) (d : F)) * (Valued.v (dV v))⁻¹
            ≤ Valued.v (dV v) * (Valued.v (dV v))⁻¹ := mul_le_mul_left (hle d hd) _
          _ = 1 := mul_inv_cancel₀ hvδ
      have hsplit : algebraMap F (Fv F v) (d : F) = dV v * t := by
        rw [ht_def, mul_comm (algebraMap F (Fv F v) (d : F)), ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]
      have h1 : inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) = 1 := by simp
      have htP : sc (E := E) v t ∈ DiffLoc_P (E := E) v := by
        have : sc (E := E) v t =
            (⟨t, ht⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
          rw [h1]; exact Algebra.algebraMap_eq_smul_one t
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨1, rfl⟩, rfl⟩)
      rw [DiffLoc_inclR_alg, hsplit, DiffLoc_sc_mul]
      exact Submodule.mem_span_singleton_mul.2 ⟨_, htP, rfl⟩
  · refine Submodule.mul_le.2 (fun m hm p hp => ?_)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ a ?_
    have hd0v : Valued.v (algebraMap F (Fv F v) (d0 : F)) ≠ 0 := heq ▸ hvδ
    have hd0 : algebraMap F (Fv F v) (d0 : F) ≠ 0 := (Valuation.ne_zero_iff _).1 hd0v
    set u := dV v * (algebraMap F (Fv F v) (d0 : F))⁻¹ with hu_def
    have hu : u ∈ v.adicCompletionIntegers F := by
      show Valued.v u ≤ 1
      rw [hu_def, map_mul, map_inv₀, ← heq, mul_inv_cancel₀ hd0v]
    have hmemδ : sc (E := E) v (dV v) ∈
        DiffLoc_psi v ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
      have h1 : sc (E := E) v (dV v) =
          (⟨u, hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (algebraMap F E (d0 : F)) := by
        rw [DiffLoc_inclR_alg]
        show sc (E := E) v (dV v) = u • sc (E := E) v (algebraMap F (Fv F v) (d0 : F))
        rw [Algebra.smul_def, ← DiffLoc_sc_eq, ← DiffLoc_sc_mul, hu_def, mul_assoc, inv_mul_cancel₀ hd0,
          mul_one]
      rw [h1]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [DiffLoc_ddE_eq]
      exact Submodule.subset_span ⟨d0, hd0mem, rfl⟩
    unfold DiffLoc_P DiffLoc_psi at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨o, rfl⟩, rfl⟩ := hx
      rw [mul_comm]
      exact DiffLoc_psi_mul_mem v _ (DiffLoc_frac_closed (ddE F)) hmemδ o
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem DiffLoc_span_pow (c : Fv F v ⊗[F] E) (k : ℕ) :
    (Submodule.span (v.adicCompletionIntegers F) {c}) ^ k =
      Submodule.span (v.adicCompletionIntegers F) {c ^ k} := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ k ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]

theorem DiffLoc_pow_nat (k : ℕ) :
    DiffLoc_psi v (((ddE (E := E) F) ^ k : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v := by
  induction k with
  | zero => rw [pow_zero, DiffLoc_psi_one, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ, DiffLoc_psi_mul, ih, DiffLoc_psi_ddE, pow_succ]
    calc _ = Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k *
          Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} *
          (DiffLoc_P (E := E) v * DiffLoc_P (E := E) v) := by ring
      _ = _ := by rw [DiffLoc_PP]

theorem DiffLoc_ddE_ne : (ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
  unfold ddE
  rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem DiffLoc_neg (k : ℕ) :
    DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k * DiffLoc_P (E := E) v := by
  have h1 : DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) *
      (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v) =
      DiffLoc_P (E := E) v := by
    rw [← DiffLoc_pow_nat, ← DiffLoc_psi_mul, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ DiffLoc_ddE_ne), DiffLoc_psi_one]
  have h2 : DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) *
      DiffLoc_P (E := E) v =
      DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
    rw [← DiffLoc_psi_one, ← DiffLoc_psi_mul, mul_one]
  have h3 : Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k *
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k = 1 := by
    rw [← mul_pow, Submodule.span_mul_span, Set.singleton_mul_singleton, ← DiffLoc_sc_mul,
      inv_mul_cancel₀ (DiffLoc_isDiffVal v).1, DiffLoc_sc_eq, map_one, ← Submodule.one_eq_span, one_pow]
  generalize DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Set E) = Q at h1 h2 ⊢
  calc Q = Q * DiffLoc_P (E := E) v * (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k *
        Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k) := by rw [h3, mul_one, h2]
    _ = Q * (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v) *
        Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k := by ring
    _ = _ := by rw [h1, mul_comm]

end

theorem localDifferentPowerSpan : DiffLoc := by
  intro F E _ _ _ _ _ v k y
  change y ∈ DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Set E) ↔ _
  rw [DiffLoc_neg, DiffLoc_span_pow, Submodule.mem_span_singleton_mul]
  have hsc : sc (E := E) v ((dV v)⁻¹ ^ k) = sc (E := E) v (dV v)⁻¹ ^ k := by
    rw [DiffLoc_sc_eq, DiffLoc_sc_eq, map_pow]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (DiffLoc_OEv v p).2 hp, by rw [hsc]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (DiffLoc_OEv v p).1 hp, by rw [hsc]⟩

end PI.LocFramePrimWork
