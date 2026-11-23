import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.OneSubEvTInvInt

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section TL

variable {F : Type} [Field F] [NumberField F]

theorem algebraMap_int_intAf (t : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F t) ∈ intAf F := by
  intro w
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F t)) w ∈ w.adicCompletionIntegers F
  rw [af_alg_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t) =
      ((algebraMap (𝓞 F) F t : F) : w.adicCompletion F) := rfl
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one w t

theorem finElt (m : 𝓞 F) (hm : m ≠ 0) : {w : HeightOneSpectrum (𝓞 F) | m ∈ w.asIdeal}.Finite := by
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  apply (Ideal.finite_factors hI).subset
  intro w hw
  show w.asIdeal ∣ Ideal.span {m}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

theorem evT_compl (X : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT Xᶜ = evT X := by
  apply af_ext
  intro u
  rw [af_sub_apply, af_one_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_neg (fun h' => h' h), if_pos h, sub_zero]
  · rw [if_pos (show u ∈ Xᶜ from h), if_neg h, sub_self]

theorem evT_inv_int (X : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F) (ht : ∀ u ∈ X, t ∉ u.asIdeal) :
    evT X * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  rw [← evT_compl]
  exact one_sub_evT_inv_int Xᶜ t (fun u hu => ht u (by simpa using hu))

theorem evT_mul_of_subset {X Y : Set (HeightOneSpectrum (𝓞 F))} (hXY : X ⊆ Y) : evT X * evT Y = evT X := by
  apply af_ext
  intro u
  rw [af_mul_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_pos h, if_pos (hXY h), mul_one]
  · rw [if_neg h, zero_mul]

theorem evT_split {B S : Set (HeightOneSpectrum (𝓞 F))} (hBS : B ⊆ S) : evT S = evT B + evT (S \ B) := by
  apply af_ext
  intro u
  rw [af_add_apply, evT_apply, evT_apply, evT_apply]
  by_cases h1 : u ∈ B
  · rw [if_pos (hBS h1), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
  · by_cases h2 : u ∈ S
    · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
    · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]

theorem t_lemma (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) (hm : m ≠ 0) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) ∈ intAf F := by
  classical
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ n : ℕ, m ∉ w.asIdeal ^ n := by
    intro w
    by_contra h
    push_neg at h
    have hmem : m ∈ ⨅ i, w.asIdeal ^ i := (Submodule.mem_iInf _).2 h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top, Ideal.mem_bot] at hmem
    exact hm hmem
  choose n hn using hn
  let s : Finset (HeightOneSpectrum (𝓞 F)) := insert v (finElt m hm).toFinset
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun w => w.asIdeal)
    (fun w => if w = v then 1 else n w) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  refine ⟨t, ?_, ?_⟩
  · intro htv
    have h1 : t - 1 ∈ v.asIdeal := by simpa using ht v (Finset.mem_insert_self _ _)
    have h2 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem htv h1
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · intro w
    show ((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m)) w ∈
      w.adicCompletionIntegers F
    rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
    split_ifs with hw
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) =
          ((algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m : F) : w.adicCompletion F) := rfl
      rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hw' : w ≠ v := fun h => hw (by rw [h]; exact Set.mem_singleton v)
      have hpos : 0 < w.intValuation m := zero_lt_iff.2 (HeightOneSpectrum.intValuation_ne_zero w m hm)
      by_cases hmw : m ∈ w.asIdeal
      · have hws : w ∈ s := Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hmw)
        have h1 := ht w hws
        simp only [if_neg hw', sub_zero] at h1
        have hle := (HeightOneSpectrum.intValuation_le_pow_iff_mem w t (n w)).2 h1
        have hnot : ¬ w.intValuation m ≤ WithZero.exp (-((n w : ℕ) : ℤ)) :=
          fun h => hn w ((HeightOneSpectrum.intValuation_le_pow_iff_mem w m (n w)).1 h)
        have hlt := lt_of_le_of_lt hle (not_le.1 hnot)
        exact (div_le_one₀ hpos).2 hlt.le
      · rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w m).2 hmw, div_one]
        exact HeightOneSpectrum.intValuation_le_one w t

end TL

section FL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem tmul_one_smul_Fsmul (a : Af F) (c : F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • (c • Y) = ((a * algebraMap F (Af F) c) ⊗ₜ[F] (1 : E)) • Y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_smul_comm, show a * algebraMap F (Af F) c = c • a by rw [Algebra.smul_def, mul_comm],
    ← TensorProduct.smul_tmul', smul_mul_assoc]

theorem tmul_one_smul_smul (a a' : Af F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • ((a' ⊗ₜ[F] (1 : E)) • Y) = ((a * a') ⊗ₜ[F] (1 : E)) • Y := by
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem crd_iff (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 F) (w : V) :
    algebraMap (𝓞 F) (𝓞 E) s • w ∈ L0 ↔ (algebraMap (𝓞 F) F s) • b.equivFun w ∈ crdOf b L0 := by
  rw [mem_iff_crdOf b L0, equivFun_osmul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F E, algebraMap_smul]

theorem flocHat [FiniteDimensional E V] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hL : Submodule.IsLattice E L0)
    (hsat : ∀ y : Fin M → E, vinc (F := F) y ∈ latHat F E (crdOf b L0) → y ∈ crdOf b L0)
    (S : Set (HeightOneSpectrum (𝓞 F))) (w : V) :
    (evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w) ∈ latHat F E (crdOf b L0) ↔
      ∀ v ∈ S, w ∈ Floc v L0 := by
  classical
  obtain ⟨m, hm0, hmL⟩ := cofin1 (Submodule.span (𝓞 E) {w}) L0 (Submodule.fg_span_singleton w) hL.span_eq_top
  set mF : 𝓞 F := (m : 𝓞 F) with hmF
  have hmF0 : mF ≠ 0 := intCast_ne_zero_OF m hm0
  have hmw : algebraMap (𝓞 F) (𝓞 E) mF • w ∈ L0 := by
    rw [hmF, map_intCast]
    exact hmL w (Submodule.mem_span_singleton_self w)
  have hmy := (crd_iff b L0 mF w).1 hmw
  have hne : ∀ t : 𝓞 F, t ≠ 0 → algebraMap (𝓞 F) F t ≠ 0 := fun t ht h =>
    ht (FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [h, map_zero]))
  constructor
  · intro hY v hv
    obtain ⟨t, htv, htint⟩ := t_lemma v mF hmF0
    have htF : algebraMap (𝓞 F) F t ≠ 0 := hne t (fun h => htv (by rw [h]; exact v.asIdeal.zero_mem))
    have key : vinc (F := F) ((algebraMap (𝓞 F) F t) • b.equivFun w) ∈ latHat F E (crdOf b L0) := by
      have hdec : vinc (F := F) ((algebraMap (𝓞 F) F t) • b.equivFun w) =
          (evT {v} ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) +
          ((1 - evT {v}) ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) := by
        rw [vinc_Fsmul, ← add_smul, ← TensorProduct.add_tmul, add_sub_cancel,
          ← Algebra.TensorProduct.one_def, one_smul]
      rw [hdec]
      apply add_mem
      · rw [tmul_one_smul_Fsmul]
        have e2 : ((evT {v} * algebraMap F (Af F) (algebraMap (𝓞 F) F t)) ⊗ₜ[F] (1 : E)) •
              vinc (F := F) (b.equivFun w) =
            ((evT {v} * algebraMap F (Af F) (algebraMap (𝓞 F) F t)) ⊗ₜ[F] (1 : E)) •
              ((evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w)) := by
          rw [tmul_one_smul_smul, mul_right_comm, evT_mul_of_subset (Set.singleton_subset_iff.2 hv)]
        rw [e2]
        exact latHat_smul _ (intAf_mul (evT_int _) (algebraMap_int_intAf t)) hY
      · have e3 : ((1 - evT {v}) ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) =
            (((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F mF)) ⊗ₜ[F] (1 : E)) •
              vinc (F := F) ((algebraMap (𝓞 F) F mF) • b.equivFun w) := by
          rw [vinc_Fsmul, tmul_one_smul_Fsmul, tmul_one_smul_Fsmul, mul_assoc, ← map_mul,
            div_mul_cancel₀ _ (hne mF hmF0)]
        rw [e3]
        exact latHat_smul _ htint (vinc_mem _ hmy)
    exact ⟨t, htv, (crd_iff b L0 t w).2 (hsat _ key)⟩
  · intro hS
    set B : Set (HeightOneSpectrum (𝓞 F)) := {u | u ∈ S ∧ mF ∈ u.asIdeal} with hB
    have hBfin : B.Finite := (finElt mF hmF0).subset (fun u hu => hu.2)
    have hBS : B ⊆ S := fun u hu => hu.1
    obtain ⟨t, htI, ht0, htB⟩ : ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t • w ∈ L0 ∧ t ≠ 0 ∧
        ∀ u ∈ B, t ∉ u.asIdeal := by
      by_cases hBe : hBfin.toFinset = ∅
      · refine ⟨mF, hmw, hmF0, fun u hu => ?_⟩
        have : u ∈ hBfin.toFinset := (Set.Finite.mem_toFinset _).2 hu
        rw [hBe] at this
        simp at this
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hBe
        let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V w) L0)
        have hnot : ¬ ((I : Set (𝓞 F)) ⊆ ⋃ i ∈ (↑hBfin.toFinset : Set (HeightOneSpectrum (𝓞 F))),
            (fun u : HeightOneSpectrum (𝓞 F) => u.asIdeal) i) := by
          rw [Ideal.subset_union_prime a a (fun i _ _ _ => i.isPrime)]
          rintro ⟨u, hu, hIu⟩
          obtain ⟨s, hs, hsw⟩ := hS u ((Set.Finite.mem_toFinset _).1 hu).1
          exact hs (hIu hsw)
        rw [Set.not_subset] at hnot
        obtain ⟨t, htI, htU⟩ := hnot
        have htB : ∀ u ∈ B, t ∉ u.asIdeal := fun u hu hut =>
          htU (Set.mem_biUnion (x := u) ((Set.Finite.mem_toFinset _).2 hu) hut)
        refine ⟨t, htI, fun h => htB a ((Set.Finite.mem_toFinset _).1 ha) (by rw [h]; exact a.asIdeal.zero_mem), htB⟩
    have hty := (crd_iff b L0 t w).1 htI
    have htF := hne t ht0
    rw [evT_split hBS, TensorProduct.add_tmul, add_smul]
    apply add_mem
    · have e1 : evT B = (evT B * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) *
          algebraMap F (Af F) (algebraMap (𝓞 F) F t) := by
        rw [mul_assoc, ← map_mul, inv_mul_cancel₀ htF, map_one, mul_one]
      rw [e1, ← tmul_one_smul_Fsmul, ← vinc_Fsmul]
      exact latHat_smul _ (evT_inv_int B t htB) (vinc_mem _ hty)
    · have e1 : evT (S \ B) = (evT (S \ B) * algebraMap F (Af F) ((algebraMap (𝓞 F) F mF)⁻¹)) *
          algebraMap F (Af F) (algebraMap (𝓞 F) F mF) := by
        rw [mul_assoc, ← map_mul, inv_mul_cancel₀ (hne mF hmF0), map_one, mul_one]
      rw [e1, ← tmul_one_smul_Fsmul, ← vinc_Fsmul]
      exact latHat_smul _ (evT_inv_int (S \ B) mF (fun u hu hmu => hu.2 ⟨hu.1, hmu⟩)) (vinc_mem _ hmy)

end FL

end PI.UnitaryGroupMassFormula.UJClassMass

end
