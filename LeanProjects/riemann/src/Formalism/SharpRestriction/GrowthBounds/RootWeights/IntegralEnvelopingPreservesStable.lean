import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_charZero {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI hc := ringChar.charP O
  have hO : CharZero O := by
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      by_cases hpq : p = ringChar O
      · apply S.p_ne
        rw [hpq]
        exact CharP.cast_eq_zero O (ringChar O)
      · have hcop : Nat.Coprime p (ringChar O) := (Nat.coprime_primes hp hq).mpr hpq
        have h := Nat.gcd_eq_gcd_ab p (ringChar O)
        rw [hcop.gcd_eq_one] at h
        have h' := congrArg (Int.cast : ℤ → O) h
        push_cast at h'
        rw [CharP.cast_eq_zero O (ringChar O), zero_mul, add_zero] at h'
        exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem (IsUnit.of_mul_eq_one _ h'.symm)
    · rw [hq] at hc
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_preserves_stable (f : Module.End K V) (W : Submodule K V) (hf : ∀ x ∈ W, f x ∈ W) (k : ℕ) :
    ∀ x ∈ W, (f ^ k) x ∈ W := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ ih

theorem list_prod_preserves_stable (l : List (Module.End K V)) (W : Submodule K V) (hl : ∀ f ∈ l, ∀ x ∈ W, f x ∈ W) :
    ∀ x ∈ W, l.prod x ∈ W := by
  revert hl
  induction l with
  | nil =>
    intro _ x hx
    simpa using hx
  | cons f l ih =>
    intro hl x hx
    rw [List.prod_cons, Module.End.mul_apply]
    exact hl f (List.mem_cons.mpr (Or.inl rfl)) _
      (ih (fun g hg => hl g (List.mem_cons.mpr (Or.inr hg))) x hx)

theorem integral_enveloping_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    ∀ u ∈ UZmon E, ∀ x ∈ W, u x ∈ W := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · intro x hx
      simp only [divPowE, LinearMap.smul_apply]
      exact W.smul_mem _ (pow_preserves_stable _ W (hW a b) k x hx)
    · intro x hx
      simp only [binomE, LinearMap.smul_apply]
      refine W.smul_mem _ (list_prod_preserves_stable _ W ?_ x hx)
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, -, rfl⟩ := hf
      intro y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a a y hy) (W.smul_mem _ hy)
  | one =>
    intro x hx
    simpa using hx
  | mul u v _ _ hu hv =>
    intro x hx
    rw [Module.End.mul_apply]
    exact hu _ (hv _ hx)

theorem generated_subrep_operator_stable (E : GLOps n K V) (h : V) : ∀ a b, ∀ x ∈ generatedSubrep E h, E a b x ∈ generatedSubrep E h := by
  intro a b x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span
      ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem isHWV_mem_highestWeightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) : v ∈ highestWeightVectors E lam := by
  refine Submodule.mem_inf.mpr ⟨hv.2.1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun a b hab => hv.2.2 a b hab

theorem highestWeight_mem_weightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : v ∈ highestWeightVectors E lam) : v ∈ weightSp E lam :=
  (Submodule.mem_inf.mp hv).1

theorem weight_projection_generated_scalar (E : GLOps n K V) (lam : Fin n → ℤ) (π : Module.End K V) (hπ : IsWtProj E lam π) (h : V)
    (hh : h ∈ highestWeightVectors E lam)
    (hB : generatedSubrep E h ≤ Submodule.span K {h} ⊔
      ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h))
    (y : V) (hy : y ∈ generatedSubrep E h) : ∃ a : K, π y = a • h := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (hB hy)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π := by
    refine iSup₂_le fun mu hmu => ?_
    intro z hz
    exact hπ.2 mu hmu z (Submodule.mem_inf.mp hz).1
  refine ⟨a, ?_⟩
  rw [map_add, LinearMap.mem_ker.mp (hker ht), add_zero, map_smul, hπ.1 h (highestWeight_mem_weightSpace E lam h hh)]

theorem isotypic_sum_generated_subreps (E : GLOps n K V) (lam : Fin n → ℤ) {k : ℕ} (h : Fin k → V)
    (hspan : highestWeightVectors E lam ≤ Submodule.span K (Set.range h)) (Y : V) (hY : Y ∈ isoSub E lam) :
    ∃ y : Fin k → V, (∀ j, y j ∈ generatedSubrep E (h j)) ∧ Y = ∑ j, y j := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan (isHWV_mem_highestWeightSpace E lam v hv))
    refine ⟨fun j => c j • u (h j), fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, hu, rfl⟩), ?_⟩
    rw [← hc, map_sum]
    simp only [map_smul]
  | zero => exact ⟨0, fun j => Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hz
    exact ⟨y + y', fun j => Submodule.add_mem _ (hy j) (hy' j), by simp [Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨a • y, fun j => Submodule.smul_mem _ a (hy j), by simp [Finset.smul_sum]⟩

end

theorem isotypic_lattice_of_five_parts (D : Formalism.BasicNotions.D7) (hA : IsotypicProjectorFixedMem) (hB : GeneratedMultipleOfHWV) (hC1 : DualLatticeDivisibility) (hC2 : LatticeSubspaceBasis) (hD : GeneratedLatticeCorollary) :
    TranslateCorollaryField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ lam hlam e he π hπ c Y _ heY hyp
  have := dvr_fraction_field_charZero S hG.prime
  have hp0 : (p : KK O) ≠ 0 := by exact_mod_cast hG.prime.ne_zero
  have hpc : (p : KK O) ^ c ≠ 0 := zpow_ne_zero _ hp0
  have hYiso : Y ∈ isoSub E lam := hA (KK O) V n E hE lam e he Y heY
  obtain ⟨k, h, hh, hli, hspan, hint⟩ := hC2 O V M hM.2 hMQ (highestWeightVectors E lam)
  obtain ⟨y, hy, hYsum⟩ := isotypic_sum_generated_subreps E lam h hspan Y hYiso
  have hkey : ∀ j, ∀ u ∈ UZmon E, ∃ o : O, π (u (y j)) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h j := by
    intro j0 u hu
    have hex : ∀ j, ∃ a : KK O, π (u (y j)) = a • h j := fun j =>
      weight_projection_generated_scalar E lam π hπ (h j) (hh j).2 (hB (KK O) V n E hE lam (h j) (hh j).2) _
        (integral_enveloping_preserves_stable E _ (generated_subrep_operator_stable E (h j)) u hu _ (hy j))
    choose a ha using hex
    have hz : π (u Y) = ∑ j, a j • h j := by
      rw [hYsum, map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => ha j
    obtain ⟨m, hmM, hm⟩ := hC1 O V M hM.2 hMQ ((p : KK O) ^ c) (π (u Y)) (hyp u hu)
    have hzHW : π (u Y) ∈ highestWeightVectors E lam := by
      rw [hz]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hh j).2
    have hmHW : m ∈ highestWeightVectors E lam := by
      have : m = ((p : KK O) ^ c)⁻¹ • π (u Y) := by rw [hm, smul_smul, inv_mul_cancel₀ hpc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hzHW
    obtain ⟨o, ho⟩ := hint m hmM hmHW
    refine ⟨o j0, ?_⟩
    have hsum : ∑ j, (a j - (p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = 0 := by
      have h1 : ∑ j, ((p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = π (u Y) := by
        rw [hm, ho, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul, algebraMap_smul]
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [h1, hz, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ hsum j0
    rw [ha j0, sub_eq_zero.1 this]
  have hfin : ∀ j, ∃ m ∈ M, y j = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m := fun j =>
    hD p n' O S hG n V E hE M hM lam hlam π hπ (h j) (hh j).1 (hh j).2 (hli.ne_zero j) c (y j) (hy j) (hkey j)
  choose m hmM hm using hfin
  refine ⟨∑ j, m j, Submodule.sum_mem _ fun j _ => hmM j, ?_⟩
  rw [hYsum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => hm j

end Formalism.MainNotions.G.GLWeightTheory
