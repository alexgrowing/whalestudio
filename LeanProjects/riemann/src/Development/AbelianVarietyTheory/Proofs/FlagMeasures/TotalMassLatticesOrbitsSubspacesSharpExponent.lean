import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FewOrbitsSubspacesHermitianLatticeDiscriminant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLe
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.TotalMass

theorem count_sets (K : Type) [Field K] [NumberField K] (d : ℕ) : 1 ≤ d →
    ∃ T : Finset (Finset (Ideal (𝓞 K))), (T.card : ℝ) ≤ (d : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) ∧
      ∀ S : Finset (Ideal (𝓞 K)), (∀ P ∈ S, P.IsMaximal ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2) →
        ∏ P ∈ S, qIn P = d → S ∈ T := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd
  have hn : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL : 0 ≤ Real.logb 2 (Module.finrank ℚ K) := Real.logb_nonneg (by norm_num) hn
  rcases hd.eq_or_lt with rfl | hd
  · refine ⟨{∅}, by simp, fun S hS h1 => ?_⟩
    rw [Finset.mem_singleton, Finset.eq_empty_iff_forall_notMem]
    intro P hP
    have h2 := Finset.dvd_prod_of_mem (fun P => qIn P) hP
    rw [h1] at h2
    have := Nat.le_of_dvd one_pos h2
    have := (hS P hP).2.1
    omega
  · have hp : (Nat.minFac d).Prime := Nat.minFac_prime (by omega)
    obtain ⟨Ps, hcard, hPs⟩ := Formalism.SLP.P.CountO.primes_card K _ hp
    choose! T hT1 hT2 using ih
    have hlt : ∀ q : ℕ, 2 ≤ q → q ∣ d → d / q < d ∧ 1 ≤ d / q ∧ ((d / q : ℕ) : ℝ) ≤ d / 2 := by
      intro q h2 hq
      refine ⟨Nat.div_lt_self (by omega) h2, Nat.div_pos (Nat.le_of_dvd (by omega) hq) (by omega), ?_⟩
      refine Nat.cast_div_le.trans ?_
      gcongr
      exact_mod_cast h2
    refine ⟨(Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d).biUnion fun P => (T (d / qIn P)).image (insert P), ?_, ?_⟩
    · have h1 : (((Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d).biUnion
          fun P => (T (d / qIn P)).image (insert P)).card : ℝ) ≤
          ∑ P ∈ Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d, (((T (d / qIn P)).image (insert P)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      refine h1.trans ?_
      calc _ ≤ ∑ _P ∈ Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d,
            ((d : ℝ) / 2) ^ Real.logb 2 (Module.finrank ℚ K) := by
            refine Finset.sum_le_sum fun P hP => ?_
            obtain ⟨-, h2, hq⟩ := Finset.mem_filter.1 hP
            obtain ⟨a, b, c⟩ := hlt _ h2 hq
            refine le_trans ?_ ((hT1 _ a b).trans (Real.rpow_le_rpow (by positivity) c hL))
            exact_mod_cast Finset.card_image_le
        _ ≤ (Module.finrank ℚ K : ℝ) * ((d : ℝ) / 2) ^ Real.logb 2 (Module.finrank ℚ K) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact (Finset.card_filter_le _ _).trans hcard
        _ = _ := by
            rw [Real.div_rpow (by positivity) (by norm_num),
              Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
            field_simp
    · intro S hS hprod
      have hdvd : Nat.minFac d ∣ ∏ P ∈ S, qIn P := hprod ▸ Nat.minFac_dvd d
      obtain ⟨P, hP, hpP⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hdvd
      obtain ⟨hmax, h2, hN⟩ := hS P hP
      have hq : qIn P ∣ d := hprod ▸ Finset.dvd_prod_of_mem (fun P => qIn P) hP
      obtain ⟨a, b, -⟩ := hlt _ h2 hq
      have hmem : ((Nat.minFac d : ℕ) : 𝓞 K) ∈ P := by
        have hP0 : P ≠ ⊥ := by
          intro h0
          have : Ideal.absNorm P = 0 := by rw [h0, Ideal.absNorm_bot]
          rw [hN] at this
          have := pow_eq_zero_iff (two_ne_zero) |>.1 this
          omega
        have hdv : Nat.minFac d ∣ Ideal.absNorm P := hN ▸ hpP.trans (dvd_pow_self _ two_ne_zero)
        obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hdv
        rw [hmax.eq_of_le hQ.ne_top (Ideal.le_of_dvd hQP)]
        have : ((Nat.minFac d : ℕ) : ℤ) ∈ Q.under ℤ := hQu ▸ Ideal.mem_span_singleton_self _
        simpa using Ideal.mem_comap.1 this
      refine Finset.mem_biUnion.2 ⟨P, Finset.mem_filter.2 ⟨hPs P hmax hmem, h2, hq⟩,
        Finset.mem_image.2 ⟨S.erase P, ?_, Finset.insert_erase hP⟩⟩
      refine hT2 _ a b _ (fun Q hQ => hS Q (Finset.mem_of_mem_erase hQ)) ?_
      rw [← hprod, ← Finset.mul_prod_erase S _ hP, Nat.mul_div_cancel_left _ (by omega)]

theorem space_mass (hMM : MaxMass) (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (hj : 1 ≤ Module.finrank K V)
    (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (hs' : h'.IsSymm) (I : Submodule (𝓞 K) V')
    (hI : IsOrthoLattice h' I (Module.finrank K V)) (M₀ : Submodule (𝓞 K) V) (hM₀ : IsMaxLat h M₀)
    (n i : ℕ) (hi0 : i ≠ 0) (hnn : n = discN h M₀ * i ^ 2) :
    orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤
      ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) *
        (mass h' I * (discN h M₀ : ℝ) ^ ((Module.finrank K V : ℝ) / 2))) := by
  have hnd := SpaceMass.nondeg_of_PD h hp
  have hp' := SpaceMass.PD_of_ortho h' hK I _ hI
  have hnd' := SpaceMass.nondeg_of_PD h' hp'
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨c, hc⟩ := hMM K hK _ hj
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIl hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hcpos : 0 < c := hcI ▸ (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V' h' hK hs' hp' I hIl).2.1
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  have hn'0 := (hdisc M₀ hM₀.1).1
  set n' := discN h M₀ with hn'
  have hm₀ : mass h M₀ ≤ c * (n' : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
    rw [hc V h hs hp rfl M₀ hM₀]
    exact mul_le_mul_of_nonneg_left (GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le K V h hK hs hnd hj M₀ hM₀).2 hcpos.le
  have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
    intro g M hM
    have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (SpaceMass.mem_genus_self h M hM.1.1)
    have h2 := (hdisc M hM.1).2.2.2.1 _ h1
    exact ⟨h2.1, h2.2.trans hM.2⟩
  let X : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
    {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
  have hXst : Stable (isom h) X := by
    rintro g p ⟨h1, h2, h3⟩
    exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
  have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
    (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
  have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
    (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) X := by
    rw [f1]
    refine mono _ _ _ _ subset_rfl fun M hM => ?_
    obtain ⟨M', hM', hle⟩ := hex M hM.1
    have hne : (X ∩ Prod.fst ⁻¹' {M}).Nonempty :=
      ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
    have := Set.one_le_encard_iff_nonempty.2 hne
    exact_mod_cast this
  have s2 : orbMass (isom h) X ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) +
      Real.logb 2 (Module.finrank ℚ K))) * orbMass (isom h) (genus h M₀) := by
    rw [f2, ← hconst]
    refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
    refine le_trans ?_ (GlobalTheory.T.encard_sublattices_of_index_le K V h hK hs hnd M' hM'.1 i (Nat.one_le_iff_ne_zero.2 hi0))
    have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
    have : (X ∩ Prod.snd ⁻¹' {M'}).encard ≤
        {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N = i}.encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        refine ⟨h3, ?_⟩
        have h5 := ((hdisc N h1.1).2.2.1 N' hM''.1 h3).2
        rw [h1.2, hM''.2, hnn] at h5
        have h6 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn'0) h5
        exact ((Nat.pow_left_injective (by norm_num)) h6).symm
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine s1.trans (s2.trans ?_)
  rw [← hmass, ← ENNReal.ofReal_mul (by positivity), hcI]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm₀ (by positivity))

theorem real_eq (d i j : ℕ) (L c : ℝ) (hd : d ≠ 0) (hi : i ≠ 0) :
    (i : ℝ) ^ ((j : ℝ) + L) * (c * ((d ^ 2 : ℕ) : ℝ) ^ ((j : ℝ) / 2)) =
      c * ((d * i : ℕ) : ℝ) ^ j * ((d * i : ℕ) : ℝ) ^ L / (d : ℝ) ^ L := by
  have hd' : (0 : ℝ) < d := by positivity
  have hi' : (0 : ℝ) < i := by positivity
  have e : ((d ^ 2 : ℕ) : ℝ) ^ ((j : ℝ) / 2) = (d : ℝ) ^ j := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd'.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hdL : (0 : ℝ) < (d : ℝ) ^ L := by positivity
  rw [e, Real.rpow_add hi', Real.rpow_natCast]
  push_cast
  rw [Real.mul_rpow hd'.le hi'.le]
  field_simp
  ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ de : ℕ, 1 ≤ de → ∃ s : Finset (Submodule K V), (∀ U ∈ s, Module.finrank K U = j) ∧ (∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U) ∧ ∑ U ∈ s, orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) ≤ ENNReal.ofReal (mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hL j hj V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ de hde
  obtain ⟨witt, res⟩ := GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp
  choose! T hT1 hT2 using count_sets K
  have hc : 0 < mass h₁ I₁ := by
    have hp' := SpaceMass.PD_of_ortho h₁ hK I₁ _ hI₁
    obtain ⟨-, -, ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V₁ h₁ hK hs₁ (SpaceMass.nondeg_of_PD h₁ hp')
    exact (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V₁ h₁ hK hs₁ hp' I₁ (ho' I₁ _ hI₁).1).2.1
  set L : ℝ := Real.logb 2 (Module.finrank ℚ K) with hLdef
  have hLf : L = 1 + Real.logb 2 (fDeg K) := by
    have := hK.1
    have e : Module.finrank ℚ K = 2 * fDeg K := by
      rw [IsTotallyComplex.finrank, fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hf : (fDeg K : ℝ) ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := K)
      have : fDeg K ≠ 0 := by omega
      exact_mod_cast this
    rw [hLdef, e]
    push_cast
    rw [Real.logb_mul (by norm_num) hf, Real.logb_self_eq_one (by norm_num)]
  let Q : ℕ × Finset (Ideal (𝓞 K)) → Submodule K V → Prop := fun p U => Module.finrank K U = j ∧
    ∃ M : Submodule (𝓞 K) U, IsMaxLat (hRes h U) M ∧ badP (hRes h U) M = p.2 ∧
      discN (hRes h U) M = p.1 ^ 2 ∧ p.1 ∣ de
  let f : ℕ × Finset (Ideal (𝓞 K)) → Submodule K V := fun I => if hI : ∃ U, Q I U then hI.choose else ⊥
  have hf : ∀ I, (∃ U, Q I U) → Q I (f I) := fun I hI => by
    simp only [f, dif_pos hI]
    exact hI.choose_spec
  let A : Finset (ℕ × Finset (Ideal (𝓞 K))) :=
    ((Finset.Icc 1 de).sigma T).map ⟨fun x => (x.1, x.2), by
      rintro ⟨a, b⟩ ⟨c, d⟩ e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rfl⟩
  refine ⟨(A.filter fun I => ∃ U, Q I U).image f, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hU
    exact (hf I (Finset.mem_filter.1 hI).2).1
  · rintro U hU ⟨N, hN, hNn⟩
    obtain ⟨-, hsU, hpU, -⟩ := res U
    have hnU := FewOrbits.nondeg _ hpU
    obtain ⟨M, hM, hNM⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K U (hRes h U) hK hsU hnU).1 N hN
    obtain ⟨hbf, hdisc, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K U (hRes h U) hK hsU hnU M hM
    obtain ⟨hi0, hd⟩ := (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK hsU hnU N hN).2.2.1 M hM.1 hNM
    set S := hbf.toFinset with hS
    set d := ∏ P ∈ S, qIn P with hdd
    have hgood : ∀ P ∈ S, P.IsMaximal ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 := fun P hP =>
      have hP' := hbf.mem_toFinset.1 hP
      ⟨hP'.1, (hloc P hP').2.1, (hloc P hP').2.2.1⟩
    have hnorm : discN (hRes h U) M = d ^ 2 := by
      rw [hdisc, finprod_mem_eq_finite_toFinset_prod _ hbf, hdd, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun P hP => (hgood P hP).2.2
    have hdvd : d ∣ de := by
      rw [hNn, hnorm] at hd
      exact (Nat.pow_dvd_pow_iff two_ne_zero).1 (Dvd.intro _ hd.symm)
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hde
    have hQ : ∃ U, Q (d, S) U := ⟨U, hU, M, hM, by simp [hS], hnorm, hdvd⟩
    have hIS : (d, S) ∈ A.filter fun I => ∃ U, Q I U := by
      refine Finset.mem_filter.2 ⟨Finset.mem_map.2 ⟨⟨d, S⟩, Finset.mem_sigma.2
        ⟨Finset.mem_Icc.2 ⟨hd1, Nat.le_of_dvd hde hdvd⟩, hT2 d hd1 S hgood rfl⟩, rfl⟩, hQ⟩
    obtain ⟨hU0, M0, hM0, hI0, -⟩ := hf _ hQ
    refine ⟨f (d, S), Finset.mem_image_of_mem f hIS, ?_⟩
    generalize f (d, S) = U0 at hU0 M0 hM0 hI0
    obtain ⟨-, hsU0, hpU0, -⟩ := res U0
    have hbad : badP (hRes h U0) M0 = badP (hRes h U) M := by
      rw [hI0]; simp [hS]
    obtain ⟨e, he⟩ := GlobalTheory.T.definite_hermitian_isometric_of_same_bad_primes K U0 (hRes h U0) hK hsU0 hpU0 hL U (hRes h U) hsU hpU
      (hU0.trans hU.symm) M0 M hM0 hM hbad
    obtain ⟨g, hg, hge⟩ := witt U0 U e he
    refine ⟨⟨g, hg⟩, ?_⟩
    change gmap g U0 = U
    ext x
    simp only [gmap, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := hge ⟨y, hy⟩
      simp only at this
      change g y ∈ U
      rw [this]
      exact (e _).2
    · intro hx
      refine ⟨(e.symm ⟨x, hx⟩ : U0), (e.symm ⟨x, hx⟩).2, ?_⟩
      change g _ = x
      rw [hge]
      simp
  · set B : ℝ := mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ L with hB
    have hB0 : 0 ≤ B := by positivity
    have key : ∀ p ∈ A.filter fun I => ∃ U, Q I U,
        orbMass (isom (hRes h (f p))) (latsDisc (R := 𝓞 K) (hRes h (f p)) (de ^ 2)) ≤
          ENNReal.ofReal (B / (p.1 : ℝ) ^ L) := by
      intro p hp'
      obtain ⟨hU0, M0, hM0, -, hd, i, hi⟩ := hf _ (Finset.mem_filter.1 hp').2
      generalize f p = U0 at hU0 M0 hM0 hd
      obtain ⟨-, hsU0, hpU0, -⟩ := res U0
      have hi0 : i ≠ 0 := by rintro rfl; omega
      have hd0 : p.1 ≠ 0 := by intro h0; rw [h0] at hi; omega
      have := space_mass hMM K U0 (hRes h U0) hK hsU0 hpU0 (hU0 ▸ hj) V₁ h₁ hs₁ I₁ (hU0 ▸ hI₁) M0 hM0
        (de ^ 2) i hi0 (by rw [hd, hi]; ring)
      rw [hd, hU0, real_eq _ _ _ _ _ hd0 hi0, ← hi] at this
      exact this
    calc _ ≤ ∑ p ∈ A.filter fun I => ∃ U, Q I U,
          orbMass (isom (hRes h (f p))) (latsDisc (R := 𝓞 K) (hRes h (f p)) (de ^ 2)) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)
      _ ≤ ∑ p ∈ A.filter fun I => ∃ U, Q I U, ENNReal.ofReal (B / (p.1 : ℝ) ^ L) := Finset.sum_le_sum key
      _ ≤ ∑ p ∈ A, ENNReal.ofReal (B / (p.1 : ℝ) ^ L) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal (∑ p ∈ A, B / (p.1 : ℝ) ^ L) :=
          (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.sum_map, Finset.sum_sigma]
          calc _ ≤ ∑ _d ∈ Finset.Icc 1 de, B := by
                refine Finset.sum_le_sum fun d hd => ?_
                have hd1 := (Finset.mem_Icc.1 hd).1
                have hpos : (0 : ℝ) < (d : ℝ) ^ L := by
                  have : (0 : ℝ) < d := by exact_mod_cast hd1
                  positivity
                change ∑ _S ∈ T d, B / (d : ℝ) ^ L ≤ B
                rw [Finset.sum_const, nsmul_eq_mul]
                calc _ ≤ (d : ℝ) ^ L * (B / (d : ℝ) ^ L) :=
                      mul_le_mul_of_nonneg_right (hT1 d hd1) (by positivity)
                  _ = B := by field_simp
            _ = _ := by
                have : (0 : ℝ) < de := by exact_mod_cast hde
                rw [show 2 + Real.logb 2 (fDeg K) = 1 + L by rw [hLf]; ring, Real.rpow_add this,
                  Real.rpow_one, hB]
                simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
                ring

end GlobalTheory.Mass.TotalMass
