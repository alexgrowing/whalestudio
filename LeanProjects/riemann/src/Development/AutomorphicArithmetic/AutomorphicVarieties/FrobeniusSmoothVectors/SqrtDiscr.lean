import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.SubSmulMulSubSmulEqZeroOfQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hom_ext {l : ℕ} [Fact l.Prime] {k : Type} [CommRing k] [CharP k l] (f g : ℤ_[l] →+* k) : f = g := by
  ext x
  obtain ⟨y, hy⟩ : (l : ℤ_[l]) ∣ x - (x.zmodRepr : ℤ_[l]) := by
    have hm := PadicInt.sub_zmodRepr_mem x
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  have hx : x = (x.zmodRepr : ℤ_[l]) + l * y := by rw [← hy]; ring
  rw [hx]
  simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero k l, zero_mul]

private theorem sqrt_discr {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ δ : K, δ ^ 2 = (discr K : K) := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  set b := NumberField.integralBasis K with hb
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card Gal(K/ℚ) := by
    rw [← Module.finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank ℚ K).symm
  let e := Fintype.equivOfCardEq hcard
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) K :=
    fun i j => (e j) (b i)
  refine ⟨M.det, ?_⟩
  have h1 : (discr K : K) = algebraMap ℚ K (Algebra.discr ℚ b) := by
    rw [hb, ← NumberField.coe_discr]
    exact (map_intCast _ _).symm
  have h2 : (algebraMap ℚ K).mapMatrix (Algebra.traceMatrix ℚ b) = M * M.transpose := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      trace_eq_sum_automorphisms, Matrix.mul_apply]
    rw [← Fintype.sum_equiv e (fun j' => (e j') (b i) * (e j') (b j)) (fun σ => σ (b i * b j))
      (fun j' => by simp only [map_mul])]
    rfl
  rw [h1, Algebra.discr_def, RingHom.map_det, h2, Matrix.det_mul, Matrix.det_transpose, sq]

private theorem discr_neg {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (h : IsTotallyComplex K) :
    discr K < 0 := by
  haveI := h
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, hK] at h1
  have hc : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hs := NumberField.sign_discr K
  rw [hc, pow_one] at hs
  exact Int.sign_eq_neg_one_iff_neg.mp hs

private theorem quad_ex {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    (hK : Module.finrank ℚ K = 2) (h : IsTotallyComplex K) (η : G ℚ Ω →* ℤˣ) (hη : η.ker = galOf ℚ K Ω) (σ : G ℚ Ω)
    (φ : Ω →+* ℂ) (hφ : ∀ x, φ (σ x) = starRingEnd ℂ (φ x)) (hσ : η σ = -1) :
    ∃ δ : Ω, δ ^ 2 = -((discr K).natAbs : Ω) ∧ ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ := by
  obtain ⟨δ0, hδ0⟩ := sqrt_discr hK
  have hneg := discr_neg hK h
  have hnd : ((discr K).natAbs : ℤ) = -discr K := Int.ofNat_natAbs_of_nonpos hneg.le
  have hirr : ∀ r : ℚ, r • (1 : K) ≠ δ0 := by
    intro r hr
    rw [Rat.smul_def, mul_one] at hr
    have h2 : ((r ^ 2 : ℚ) : K) = ((discr K : ℚ) : K) := by
      rw [Rat.cast_pow, hr, hδ0, Rat.cast_intCast]
    have h3 := Rat.cast_injective h2
    have h4 : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
    rw [h3] at h4
    have h5 : (discr K : ℚ) < 0 := by exact_mod_cast hneg
    linarith
  have hli : LinearIndependent ℚ ![(1 : K), δ0] :=
    (LinearIndependent.pair_iff' one_ne_zero).mpr hirr
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hK]; rfl)
  have hspan : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * δ0 := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), δ0]) := by rw [hsp]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc, Fin.sum_univ_two]
    simp [Rat.smul_def]
  have hfix : ∀ s : G ℚ Ω, s (algebraMap K Ω δ0) = algebraMap K Ω δ0 → s ∈ galOf ℚ K Ω := by
    intro s hs x
    obtain ⟨a, b, rfl⟩ := hspan x
    rw [map_add, map_mul, map_ratCast, map_ratCast, map_add, map_mul, hs, map_ratCast, map_ratCast]
  have hsq : (algebraMap K Ω δ0) ^ 2 = -((discr K).natAbs : Ω) := by
    rw [← map_pow, hδ0, map_intCast]
    rw [← Int.cast_natCast, hnd, Int.cast_neg, neg_neg]
  refine ⟨algebraMap K Ω δ0, hsq, ?_⟩
  intro s
  have hs2 : (s (algebraMap K Ω δ0)) ^ 2 = (algebraMap K Ω δ0) ^ 2 := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases Int.units_eq_one_or (η s) with he | he
  · have hk : s ∈ η.ker := he
    rw [hη] at hk
    rw [he, Units.val_one, one_smul]
    exact hk δ0
  · rw [he, Units.val_neg, Units.val_one, neg_smul, one_smul]
    have hm : (s (algebraMap K Ω δ0) - algebraMap K Ω δ0) * (s (algebraMap K Ω δ0) + algebraMap K Ω δ0) = 0 := by
      linear_combination hs2
    rcases mul_eq_zero.mp hm with h1 | h1
    · exfalso
      have hk : s ∈ η.ker := by
        rw [hη]
        exact hfix s (sub_eq_zero.mp h1)
      have h1' : η s = 1 := hk
      rw [he] at h1'
      exact absurd h1' (by decide)
    · exact eq_neg_of_add_eq_zero_left h1

private theorem kills_mono {Ω C : Type} [Field Ω] [CharZero Ω] [Monoid C] {M M' : ℕ} (h : M ∣ M') {χ : G ℚ Ω →* C}
    (hχ : Af.KillsMu M χ) : Af.KillsMu M' χ := fun s hs => hχ s fun ζ hζ => hs ζ (by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hζ, one_pow])

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl1 : 1 ≤ A.valuation (l : Ω) := not_lt.mp hA
  have fix : ∀ (n : ℕ) (t : Ω), t ^ (l ^ n) = 1 → σ t = t := by
    intro n t ht
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hker : σ ∈ (UpperTheory.V.Chr.cls ℚ Ω (l ^ n)).ker := by
      apply (UpperTheory.V.Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A
      · rw [Nat.cast_pow, map_pow, not_lt]
        exact one_le_pow₀ hl1
      · exact hσ
    rw [MonoidHom.mem_ker] at hker
    rw [UpperTheory.V.Chr.cls_spec (l ^ n) σ t ht, hker]
    rcases n with _ | n
    · simp only [pow_zero, pow_one] at ht
      simp [ht]
    · have h1 : l ^ (n + 1) ≠ 1 := (Nat.one_lt_pow (Nat.succ_ne_zero n) (Fact.out : l.Prime).one_lt).ne'
      rw [Units.val_one, ZMod.val_one'' h1, pow_one]
  show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) = 1
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow, Units.val_one, map_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have htn : (t : Ω) ^ (l ^ n) = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  change σ (t : Ω) = (t : Ω) ^ (1 : ZMod (l ^ n)).val
  rw [fix n t htn]
  rcases n with _ | n
  · simp only [pow_zero, pow_one] at htn
    simp [htn]
  · have h1 : l ^ (n + 1) ≠ 1 := (Nat.one_lt_pow (Nat.succ_ne_zero n) (Fact.out : l.Prime).one_lt).ne'
    rw [ZMod.val_one'' h1, pow_one]

theorem UpperTheory.V.Fr.gen_gd :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 → Gen l D.η D.Ψ D.cc B (l * N * (discr K).natAbs) ⊤ := by
  intro Ω _ _ _ K _ _ _ _ l _ c _ N _ e ψ D B hB
  have gd := D.gd
  obtain ⟨hcc2, hηcc, hΨcc, -, -, -, -, -, -, -, hIneL⟩ := dat_facts D
  obtain ⟨hηd, hd1, hψN, -⟩ := eta_killsMu D
  obtain ⟨⟨w, hw, huniq⟩, hwF⟩ := omT Ω l c
  obtain ⟨hwker1, hwcls, -, -, -, -, -, -⟩ := hwF w hw
  obtain ⟨w', η', a, hlit⟩ := (gdIff Ω K l c e N ψ).1.mp gd
  have hrel := (gdIff Ω K l c e N ψ).2 w' η' a hlit
  have hww : w' = w := huniq w' hlit.om
  subst hww
  have hbar : ∀ s, Units.map (residue c.O : c.O →* ResidueField c.O) (chiO ℚ Ω l c.O s) = omO Ω l c.O s := by
    intro s
    apply Units.ext
    exact RingHom.congr_fun (hom_ext ((residue c.O).comp (algebraMap ℤ_[l] c.O))
      ((ZMod.castHom (dvd_pow_self l one_ne_zero) (ResidueField c.O)).comp (PadicInt.toZModPow 1))) _
  have hPsi : ∀ s, D.Ψ s = chiO ℚ Ω l c.O s ^ e * Chr.dirG ℚ Ω ψ s := fun s => rfl
  have hbarPsi : ∀ s, barChar c.O D.Ψ s = omO Ω l c.O s ^ e * Units.map (residue c.O : c.O →* ResidueField c.O) (Chr.dirG ℚ Ω ψ s) := by
    intro s
    show Units.map _ (D.Ψ s) = _
    rw [hPsi, map_mul, map_pow]
    congr 2
    exact hbar s
  have hbarw : ∀ s, Units.map (residue c.O : c.O →* ResidueField c.O) (w' s) = omO Ω l c.O s := by
    intro s
    rw [← hbar s]
    apply Units.ext
    change residue c.O (w' s : c.O) = residue c.O (chiO ℚ Ω l c.O s : c.O)
    exact Ideal.Quotient.eq.mpr (hw.2 s)
  have homO : ∀ s, s ∈ (cycMod ℚ Ω l 1).ker → omO Ω l c.O s = 1 := by
    intro s hs
    show Units.map _ (cycMod ℚ Ω l 1 s) = 1
    rw [hs, map_one]
  refine
    { odd := gd.l_odd
      fin := ?_
      M_ne := ?_
      l_dvd := ⟨N * (discr K).natAbs, by ring⟩
      two_dvd := ?_
      cc := D.conj
      over_l := hB
      quad := ?_
      cyc := ?_
      η_l := fun B' hB' => (hIneL B' hB').1
      even := ?_
      Ψ_l := ?_
      g4 := ?_
      g5 := ?_
      Hb_open := ?_
      Hb_ab := le_top
      Hb_idx := ⟨0, by simp⟩
      Hb_l := fun _ _ => le_top
      teich := ?_ }
  · haveI := c.dvr
    haveI := c.fin
    exact (abelian₂.dvr_finite l c.O).2.1
  · have hl := (Fact.out : l.Prime).ne_zero
    have hN := NeZero.ne N
    have hd : (discr K).natAbs ≠ 0 := by omega
    exact Nat.mul_ne_zero (Nat.mul_ne_zero hl hN) hd
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (even_iff_two_dvd.mp gd.N_even) l) _
  · obtain ⟨φ, hφ⟩ := D.conj
    obtain ⟨δ, hδ, hs⟩ := quad_ex gd.quad gd.imag D.η D.η_ker D.cc φ hφ hηcc
    exact ⟨_, δ, by omega, fun q _ hq => Dvd.dvd.mul_left hq _, hδ, hs⟩
  · refine ⟨1, ?_, ?_⟩
    · rw [pow_one]
      exact kills_mono (Dvd.intro_left _ rfl) hηd
    · rw [pow_one]
      intro s hs
      have hdiv : ∀ k, k ∣ l * N * (discr K).natAbs → ∀ ζ : Ω, ζ ^ k = 1 → s ζ = ζ := by
        intro k hk ζ hζ
        apply hs
        obtain ⟨m, hm⟩ := hk
        rw [hm, pow_mul, hζ, one_pow]
      have h1 : Chr.dirG ℚ Ω ψ s = 1 :=
        hψN s (hdiv N (Dvd.dvd.mul_right (Dvd.intro_left l rfl) _))
      haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
      haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
      have h2 : s ∈ (Chr.cls ℚ Ω l).ker := by
        rw [MonoidHom.mem_ker]
        apply (Chr.clsFacts ℚ Ω l).2.2.1
        intro ζ hζ
        rw [Units.val_one, ZMod.val_one, pow_one]
        exact hdiv l ⟨N * (discr K).natAbs, by ring⟩ ζ hζ
      rw [← hwcls, hwker1] at h2
      rw [hbarPsi, homO s h2, h1, one_pow, map_one, one_mul]
  · show Units.map _ (D.Ψ D.cc) = 1
    rw [hΨcc, map_one]
  · refine ⟨e + a, fun B' hB' s hs => ?_⟩
    rw [hbarPsi, hlit.ine B' hB' s hs, map_pow, hbarw s, pow_add]
  · intro hle
    apply gd.eta
    intro s hs
    obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.mp hs
    rw [← D.η_ker]
    apply hle
    have hw1 : w' s = 1 := by
      rw [← MonoidHom.mem_ker, hwker1]
      exact hs1
    have hψ1 : Chr.dirG ℚ Ω ψ s = 1 := by
      have h3 := hs2
      rw [MonoidHom.mem_ker, hrel] at h3
      simpa [hw1] using h3
    refine Subgroup.mem_inf.mpr ⟨homO s hs1, ?_⟩
    rw [MonoidHom.mem_ker, hbarPsi, homO s hs1, hψ1, one_pow, map_one, one_mul]
  · obtain ⟨s, hs, hu⟩ := (hIneL B hB).2
    refine ⟨s, hs.1, (hIneL B hB).1 hs, ?_⟩
    intro h
    have h' : residue c.O ((D.Ψ s : c.O) ^ 2) = residue c.O 1 := by
      have h4 := congrArg Units.val h
      simpa [barChar] using h4
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.Quotient.eq.mp h') hu
  · exact isOpen_univ
  · intro B' hB' s hs hb
    have hs' : s ∈ Ine B' := (Subgroup.mem_inf.mp hs).1
    have hz : cycZ ℚ Ω l s = 1 := cyc_ine Ω l B' hB' hs'
    have hc : chiO ℚ Ω l c.O s = 1 := by
      show Units.map _ (cycZ ℚ Ω l s) = 1
      rw [hz, map_one]
    have hx : Chr.dirG ℚ Ω ψ s = 1 := by
      have hm : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ) := hlit.ord
      have hpow : Chr.dirG ℚ Ω ψ s ^ orderOf (Chr.dirG ℚ Ω ψ) = 1 := by
        have h5 : (Chr.dirG ℚ Ω ψ ^ orderOf (Chr.dirG ℚ Ω ψ)) s = 1 := by
          rw [pow_orderOf_eq_one, MonoidHom.one_apply]
        rwa [MonoidHom.pow_apply] at h5
      apply (congrFacts Ω l c).2.2.2.1 _ 1 _ hm hpow (one_pow _)
      rw [hbarPsi, ← hbar, hc, map_one, one_pow, one_mul] at hb
      have hb' : residue c.O (Chr.dirG ℚ Ω ψ s : c.O) = residue c.O 1 := by
        have h6 := congrArg Units.val hb
        simpa using h6
      exact Ideal.Quotient.eq.mp hb'
    rw [hPsi, hc, hx, one_pow, one_mul]
