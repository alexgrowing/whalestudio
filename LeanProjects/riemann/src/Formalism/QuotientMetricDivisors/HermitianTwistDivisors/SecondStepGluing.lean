import Mathlib
import Formalism.QuotientMetricDivisors.LatticeGlueUnique
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace GluingInclusion

open Formalism.HermitianLatticesTheory

section General

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem lg (hR : ¬ IsField R) (A : Submodule R V) (x : V)
    (hx : ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal A) : x ∈ A := by
  let I : Ideal R :=
    { carrier := {r | r • x ∈ A}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_smul] at *
        exact A.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c r hr => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *
        exact A.smul_mem c hr }
  by_contra hxA
  have hI : I ≠ ⊤ := fun h => hxA (by
    have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using h1)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := fun h => hR (Ring.isField_iff_maximal_bot.2 (h ▸ hM))
  let w : HeightOneSpectrum R := ⟨M, hM.isPrime, hM0⟩
  obtain ⟨s, hs, hsx⟩ := hx w
  exact hs (hIM hsx)

theorem le_of_forall_localized_le_of_not_isField (hR : ¬ IsField R) (A B : Submodule R V)
    (h : ∀ w : HeightOneSpectrum R, localization₂ w.asIdeal A ≤ localization₂ w.asIdeal B) : A ≤ B :=
  fun x hx => lg hR B x fun w => h w ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩

theorem sep (w : HeightOneSpectrum R) (c : R) (hc : c ≠ 0) :
    ∃ s, s ∉ w.asIdeal ∧ ∀ w' : HeightOneSpectrum R, w' ≠ w → ∃ t, t ∉ w'.asIdeal ∧ c ∣ t * s := by
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {c}) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top)
      (by simpa using hc)
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJw : ¬ J ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsw⟩ := SetLike.not_le_iff_exists.mp hJw
  refine ⟨s, hsw, fun w' hw' => ?_⟩
  have hpow : ¬ w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {c}) ≤ w'.asIdeal := by
    intro h
    have h1 : w.asIdeal ≤ w'.asIdeal := w'.isPrime.le_of_pow_le h
    exact hw' (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htw⟩ := SetLike.not_le_iff_exists.mp hpow
  refine ⟨t, htw, ?_⟩
  have : t * s ∈ Ideal.span {c} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht hsJ
  exact Ideal.mem_span_singleton.mp this

theorem denom (A B : Submodule R V) (hA : A.FG) (hB : Submodule.span K (B : Set V) = ⊤) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ A, d • x ∈ B := by
  obtain ⟨d, hd, h⟩ := indexBasic_denom (nonZeroDivisors R) A B hA
    (by rw [indexBasic_locS_top (K := K) B hB]; exact le_top)
  exact ⟨d, nonZeroDivisors.ne_zero hd, h⟩

theorem glue_spec (hR : ¬ IsField R) (L0 : Submodule R V) (L : HeightOneSpectrum R → Submodule R V)
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum R | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) ∧
      ∀ w : HeightOneSpectrum R,
        localization₂ w.asIdeal (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) =
          localization₂ w.asIdeal (L w) := by
  classical
  set G : Submodule R V := ⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w) with hG
  have hGmem : ∀ x, x ∈ G ↔ ∀ w : HeightOneSpectrum R, x ∈ localization₂ w.asIdeal (L w) := by
    intro x
    rw [hG, Submodule.mem_iInf]

  have hA : ∃ a : R, a ≠ 0 ∧ ∀ x ∈ L0, a • x ∈ G := by
    choose a ha0 ha using fun w => denom (K := K) L0 (L w) (Submodule.IsLattice.fg (self := h0))
      (Submodule.IsLattice.span_eq_top (self := hL w))
    refine ⟨∏ w ∈ hfin.toFinset, a w, Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w), ?_⟩
    intro x hx
    rw [hGmem]
    intro w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a hw
      rw [hr, mul_comm, mul_smul]
      exact locBasic_le_locS _ _ ((L w).smul_mem r (ha w x hx))
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw']
      exact locBasic_le_locS _ _ (L0.smul_mem _ hx)

  have hB : ∃ b : R, b ≠ 0 ∧ ∀ x ∈ G, b • x ∈ L0 := by
    choose b hb0 hb using fun w => denom (K := K) (L w) L0 (Submodule.IsLattice.fg (self := hL w))
      (Submodule.IsLattice.span_eq_top (self := h0))
    refine ⟨∏ w ∈ hfin.toFinset, b w, Finset.prod_ne_zero_iff.mpr (fun w _ => hb0 w), ?_⟩
    intro x hx
    apply lg hR
    intro w
    have hxw := (hGmem x).mp hx w
    by_cases hw : w ∈ hfin.toFinset
    · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem b hw
      obtain ⟨s, hs, hsx⟩ := hxw
      refine ⟨s, hs, ?_⟩
      have e : s • (∏ w ∈ hfin.toFinset, b w) • x = r • (b w • (s • x)) := by
        rw [hr]
        module
      rw [e]
      exact L0.smul_mem r (hb w _ hsx)
    · have hw' : localization₂ w.asIdeal (L w) = localization₂ w.asIdeal L0 := by
        by_contra h
        exact hw (hfin.mem_toFinset.mpr h)
      rw [hw'] at hxw
      exact (localization₂ w.asIdeal L0).smul_mem _ hxw
  obtain ⟨a, ha0, ha⟩ := hA
  obtain ⟨b, hb0, hb⟩ := hB
  have hinvsmul : ∀ (r : R), r ≠ 0 → ∀ y : V, (algebraMap R K r)⁻¹ • (r • y) = y := by
    intro r hr y
    have : algebraMap R K r ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne hr
    rw [← algebraMap_smul K r y, smul_smul, inv_mul_cancel₀ this, one_smul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hN : IsNoetherian R L0 :=
      isNoetherian_of_fg_of_noetherian L0 (Submodule.IsLattice.fg (self := h0))
    have hle : G.map (LinearMap.lsmul R V b) ≤ L0 := by
      rintro _ ⟨x, hx, rfl⟩
      exact hb x hx
    have hfg : (G.map (LinearMap.lsmul R V b)).FG := isNoetherian_submodule.mp hN _ hle
    refine Submodule.fg_of_fg_map_injective (LinearMap.lsmul R V b) ?_ hfg
    intro x y hxy
    have hxy' : b • x = b • y := hxy
    rw [← hinvsmul b hb0 x, ← hinvsmul b hb0 y, hxy']
  ·
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (self := h0), Submodule.span_le]
    intro x hx
    rw [← hinvsmul a ha0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (ha x hx))
  · intro w
    apply le_antisymm
    · have h1 : G ≤ localization₂ w.asIdeal (L w) := iInf_le _ w
      calc localization₂ w.asIdeal G ≤ localization₂ w.asIdeal (localization₂ w.asIdeal (L w)) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal (L w) := locBasic_locS_idem _ _
    · have h1 : L w ≤ localization₂ w.asIdeal G := by
        intro x hx

        obtain ⟨c', hc', hc'x⟩ : ∃ c' ∈ nonZeroDivisors R, c' • x ∈ L0 := by
          have : x ∈ locS (nonZeroDivisors R) L0 := by
            rw [indexBasic_locS_top (K := K) L0 (Submodule.IsLattice.span_eq_top (self := h0))]
            exact Submodule.mem_top
          exact this
        have hc0 : a * c' ≠ 0 := mul_ne_zero ha0 (nonZeroDivisors.ne_zero hc')
        have hcx : (a * c') • x ∈ G := by
          rw [mul_smul]
          exact ha _ hc'x
        obtain ⟨s, hsw, hs⟩ := sep w (a * c') hc0
        refine ⟨s, hsw, ?_⟩
        rw [hGmem]
        intro w'
        by_cases hw' : w' = w
        · subst hw'
          exact locBasic_le_locS _ _ ((L w').smul_mem s hx)
        · obtain ⟨t, ht, u, hu⟩ := hs w' hw'
          have h2 : t • (s • x) ∈ localization₂ w'.asIdeal (L w') := by
            rw [smul_smul, hu, mul_comm, mul_smul]
            exact (localization₂ w'.asIdeal (L w')).smul_mem u ((hGmem _).mp hcx w')
          have h3 : s • x ∈ localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) := ⟨t, ht, h2⟩
          rwa [show localization₂ w'.asIdeal (localization₂ w'.asIdeal (L w')) = localization₂ w'.asIdeal (L w') from
            locBasic_locS_idem _ _] at h3
      calc localization₂ w.asIdeal (L w) ≤ localization₂ w.asIdeal (localization₂ w.asIdeal G) := locBasic_locS_mono _ h1
        _ = localization₂ w.asIdeal G := locBasic_locS_idem _ _

end General

section NF

variable {K : Type} [Field K] [NumberField K]

theorem glueLat_spec {D : ℕ} (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal (glueLat L) = localization₂ w.asIdeal (L w) :=
  glue_spec (NumberField.RingOfIntegers.not_isField K) L0 L h0 hL hfin

theorem eq_of_localization_eq {D : ℕ} (R R' : Submodule (𝓞 K) (Fin D → K))
    (h : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal R') : R = R' :=
  le_antisymm (le_of_forall_localized_le_of_not_isField (NumberField.RingOfIntegers.not_isField K) R R' fun w => (h w).le)
    (le_of_forall_localized_le_of_not_isField (NumberField.RingOfIntegers.not_isField K) R' R fun w => (h w).ge)

end NF

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjIdeal_eq (w : HeightOneSpectrum (𝓞 K)) :
    conjIdeal (K := K) w.asIdeal = (conjPl w).asIdeal := by
  show Ideal.span _ = Ideal.map (cO K) w.asIdeal
  unfold Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (RingOfIntegers.ext h).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

theorem loc_eq (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) :
    loc (K := K) w.asIdeal A = localization₂ w.asIdeal A ⊓ localization₂ (conjPl w).asIdeal A := by
  obtain ⟨hp, h⟩ := (locBasic (𝓞 K) K (Fin d → K) (IsFractionRing.injective (𝓞 K) K)).2.2.2.2
    (fun r => ⟨cO K r, rfl⟩) w.asIdeal
  rw [h A]
  congr 1
  ext x
  unfold localization₂
  simp only [locBasic_mem_locS, Ideal.mem_primeCompl_iff, conjIdeal_eq]

theorem matLat_lattice' {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K (matLat P M) := by
  refine ⟨(Submodule.IsLattice.fg (self := hM)).map _, ?_⟩
  have : ((matLat P M : Submodule (𝓞 K) (Fin D → K)) : Set (Fin D → K)) =
      (Matrix.mulVecLin P) '' (M : Set (Fin n → K)) := by
    rw [matLat, Submodule.map_coe]
    rfl
  rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hM), Submodule.map_top,
    LinearMap.range_eq_top]
  exact hP

theorem loc_glueLat {D : ℕ} (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (hc : ∀ w, L (conjPl w) = L w) (R : Submodule (𝓞 K) (Fin D → K))
    (hR : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal (L w))
    (w : HeightOneSpectrum (𝓞 K)) :
    loc (K := K) w.asIdeal R = loc (K := K) w.asIdeal (L w) := by
  rw [loc_eq, loc_eq, hR w, hR (conjPl w), hc w]

end Star

end GluingInclusion

open GluingInclusion Formalism.HermitianLatticesTheory

theorem lattice_gluing : LatticeGlue := by
  intro K _ _ D L0 L h0 hL hfin
  exact glueLat_spec L0 L h0 hL hfin

theorem lattice_gluing_unique : LatticeGlueUnique := by
  intro K _ _ D R R'
  have hR := NumberField.RingOfIntegers.not_isField K
  refine ⟨eq_of_localization_eq R R', le_of_forall_localized_le_of_not_isField hR R R', ?_⟩
  apply le_antisymm
  · intro x hx
    exact lg hR R x fun w => (Submodule.mem_iInf _).1 hx w
  · intro x hx
    exact (Submodule.mem_iInf _).2 fun w => ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩

theorem lattice_gluing_independent : LatticeGlueIndep := by
  classical
  intro K _ _ D L0 L1 h0 h1 S hS
  obtain ⟨hlat, hloc⟩ := glueLat_spec L0 (fun w => if w ∈ S then L1 else L0) h0
    (fun w => by by_cases hw : w ∈ S <;> simp only [hw, if_true, if_false] <;> assumption)
    (hS.subset (fun w hw => by
      by_contra hwS
      apply hw
      simp only [hwS, if_false]))
  refine ⟨_, ⟨hlat, fun w hw => ?_, fun w hw => ?_⟩, ?_⟩
  · rw [hloc w]
    simp only [hw, if_true]
  · rw [hloc w]
    simp only [hw, if_false]
  · rintro R ⟨-, hR1, hR0⟩
    apply eq_of_localization_eq
    intro w
    rw [hloc w]
    by_cases hw : w ∈ S
    · simp only [hw, if_true]
      exact hR1 w hw
    · simp only [hw, if_false]
      exact hR0 w hw

theorem lattice_gluing_semilocal : LatticeGlueSemi := by
  intro K _ _ _ D
  refine ⟨?_, ?_⟩
  · intro L0 L h0 hL hc hfin
    obtain ⟨hlat, hloc⟩ := glueLat_spec L0 L h0 hL (hfin.subset (fun w hw h => hw
      (StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq w _ _ h).1))
    refine ⟨hlat, loc_glueLat L hc _ hloc, ?_⟩
    apply le_antisymm
    · refine le_iInf (fun w => ?_)
      rw [loc_eq]
      refine le_inf (iInf_le _ w) ?_
      have h := iInf_le (fun w : HeightOneSpectrum (𝓞 K) => localization₂ w.asIdeal (L w)) (conjPl w)
      rw [hc w] at h
      exact h
    · refine le_iInf (fun w => le_trans (iInf_le _ w) ?_)
      rw [loc_eq]
      exact inf_le_left
  · intro R R' h
    exact eq_of_localization_eq R R' (fun w => (StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq w _ _ (h w)).1)

theorem second_step_gluing : StepBGlue := by
  intro K _ _ _ D Tup μ0 μ hμc hμ abelian₂ hLam ι hι
  have hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w))) ≠
      localization₂ w.asIdeal (matLat (ι μ0) (abelian₂ μ0))}.Finite :=
    hμ.subset (fun w hw h => hw (by rw [h]))
  obtain ⟨hlat, hloc⟩ := glueLat_spec (matLat (ι μ0) (abelian₂ μ0))
    (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) (StepBAux.matLat_lattice _ (hι _) _ (hLam _))
    (fun w => StepBAux.matLat_lattice _ (hι _) _ (hLam _)) hfin
  have huniq : ∀ R : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        localization₂ w.asIdeal R = localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      R = glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) :=
    fun R hR => eq_of_localization_eq _ _ (fun w => by rw [hR w, hloc w])
  refine ⟨⟨_, hloc, huniq⟩, ?_⟩
  intro R hR
  refine ⟨?_, huniq R hR, ?_, ?_⟩
  · rw [huniq R hR]
    exact hlat
  · exact loc_glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) (fun w => by simp only [hμc w]) R hR
  · refine hfin.subset (fun w hw => ?_)
    rw [Set.mem_ofPred_eq, hR w] at hw
    exact hw

theorem divisor_into_dual_gluing : DivIntoDualGlue := by
  intro K _ _ _ D Tup μ0 μ hμ n M hM π hπ ι hι
  have hl : ∀ t, Submodule.IsLattice K (matLat (ι t) (matLat (π t) (M t))) := fun t =>
    StepBAux.matLat_lattice _ (hι t) _ (matLat_lattice' _ (hπ t) _ (hM t))
  obtain ⟨hlat, hloc⟩ := glueLat_spec (matLat (ι μ0) (matLat (π μ0) (M μ0)))
    (fun w => matLat (ι (μ w)) (matLat (π (μ w)) (M (μ w)))) (hl μ0) (fun w => hl (μ w))
    (hμ.subset (fun w hw h => hw (by rw [h])))
  exact ⟨_, ⟨hlat, hloc⟩, fun R hR => eq_of_localization_eq _ _ (fun w => by rw [hR.2 w, hloc w])⟩

end Formalism.DivisionValues
