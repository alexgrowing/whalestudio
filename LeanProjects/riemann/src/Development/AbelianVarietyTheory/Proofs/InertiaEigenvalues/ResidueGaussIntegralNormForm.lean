import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

noncomputable section

namespace GlobalTheory.JR.ResidueGauss

theorem setIntegral_addChar_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (H : AddSubgroup G) (f : G → ℂ)
    (hf : ∀ x y, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ H) (hne : f s₀ ≠ 1) :
    ∫ x in (H : Set G), f x ∂μ = 0 := by
  have hmp : MeasurePreserving (fun x => s₀ + x) μ μ := measurePreserving_add_left μ s₀
  have hpre : (fun x => s₀ + x) ⁻¹' (H : Set G) = H := by
    ext x; simp [H.add_mem_cancel_left hs₀]
  have e := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft s₀) f H
  rw [hpre] at e
  simp_rw [hf s₀] at e
  rw [integral_const_mul] at e
  have h : (f s₀ - 1) * ∫ x in (H : Set G), f x ∂μ = 0 := by rw [sub_mul, e]; ring
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)

theorem setIntegral_comp_mul_unit {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (u v : R) (huv : u * v = 1) (h0 : μ S ≠ 0)
    (hT : μ S ≠ ⊤) (hu : ∀ y ∈ S, u * y ∈ S) (hv : ∀ y ∈ S, v * y ∈ S) (g : R → ℂ) :
    ∫ y in S, g (u * y) ∂μ = ∫ y in S, g y ∂μ := by
  have hU : IsUnit u := ⟨⟨u, v, huv, by rw [mul_comm]; exact huv⟩, rfl⟩
  set w : Rˣ := hU.unit with hw
  have hwv : (w : R) = u := IsUnit.unit_spec hU
  have hvu : v * u = 1 := by rw [mul_comm]; exact huv
  have hwS : w • S = S := by
    ext y
    simp only [Set.mem_smul_set, Units.smul_def, hwv, smul_eq_mul]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hu z hz
    · intro hy; exact ⟨v * y, hv y hy, by rw [← mul_assoc, huv, one_mul]⟩
  have hΔ : distribHaarChar R w = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul h0 hT
    rw [hwS]; simp
  let e : R ≃ₜ R :=
    { toFun := fun y => u * y
      invFun := fun y => v * y
      left_inv := fun y => by simp only; rw [← mul_assoc, hvu, one_mul]
      right_inv := fun y => by simp only; rw [← mul_assoc, huv, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hemb : MeasurableEmbedding (fun y => u * y) := e.toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun y => u * y) μ μ := by
    refine ⟨hemb.measurable, ?_⟩
    ext T hT'
    rw [Measure.map_apply hemb.measurable hT']
    have : (fun y => u * y) ⁻¹' T = w⁻¹ • T := by
      ext y
      rw [Set.mem_inv_smul_set_iff, Units.smul_def, hwv]
      rfl
    rw [this, ← distribHaarChar_mul, map_inv, hΔ]
    simp
  have hpre : (fun y => u * y) ⁻¹' S = S := by
    ext y
    constructor
    · intro hy
      have := hv _ hy
      simp only at this
      rwa [← mul_assoc, hvu, one_mul] at this
    · intro hy; exact hu y hy
  have := hmp.setIntegral_preimage_emb hemb g S
  rwa [hpre] at this

theorem setIntegral_swap_of_continuous {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (S : Set X) (T : Set Y) (hS : μ S ≠ ⊤) (hT : ν T ≠ ⊤) (g : X → Y → ℂ)
    (hg : Continuous (Function.uncurry g)) (hb : ∀ x y, ‖g x y‖ ≤ 1) :
    ∫ x in S, ∫ y in T, g x y ∂ν ∂μ = ∫ y in T, ∫ x in S, g x y ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict T) := ⟨by simpa using hT.lt_top⟩
  apply integral_integral_swap
  exact Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun q => hb q.1 q.2)

theorem algebraMap_continuous_isCompact_preimage {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [U : Unram F E] (A : Et F E) :
    Continuous (algebraMap A.K A.L) ∧
      ∀ O : Set A.L, IsCompact O → IsCompact (algebraMap A.K A.L ⁻¹' O) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  let ιF : A.K →ₗ[F] A.L := (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hιF : ∀ s, ιF s = algebraMap A.K A.L s := fun s => rfl
  have hc : Continuous (algebraMap A.K A.L) := by
    have := IsModuleTopology.continuous_of_linearMap ιF
    exact this
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.2 hinj)
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  refine ⟨hc, fun O hO => ?_⟩
  refine (hO.image hrc).of_isClosed_subset (hO.isClosed.preimage hc) ?_
  intro s hs
  exact ⟨algebraMap A.K A.L s, hs, LinearMap.congr_fun hr s⟩

theorem residue_algebra {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (hK : IsField K) (hinj : Function.Injective (algebraMap K L)) (N : L → K)
    (hN : ∀ y, algebraMap K L (N y) = y * star y) (O : Subring L) (ϖ : Kˣ)
    (hOs : ∀ y ∈ O, star y ∈ O) (hϖO : algebraMap K L (ϖ : K) ∈ O)
    (hϖnu : ¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hnorm : ∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, N w = s) :
    (∀ y ∈ O, (¬ ∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) →
      algebraMap K L (N y) ∈ O ∧ (¬ ∃ t, algebraMap K L t ∈ O ∧ N y = ϖ * t) ∧
        ∃ r, algebraMap K L r ∈ O ∧ N y * r = 1) ∧
    (∀ s, algebraMap K L s ∈ O → (¬ ∃ t, algebraMap K L t ∈ O ∧ s = ϖ * t) →
      (∃ r, algebraMap K L r ∈ O ∧ s * r = 1) ∧ ∃ w ∈ O, ∃ v ∈ O, w * v = 1 ∧ N w = s) := by
  set ι := algebraMap K L with hι
  have hNmul1 : ∀ y z, y * z = 1 → N y * N z = 1 := by
    intro y z h
    apply hinj
    rw [map_mul, hN, hN, map_one]
    calc y * star y * (z * star z) = (y * z) * star (y * z) := by rw [star_mul']; ring
      _ = 1 := by rw [h, star_one, one_mul]
  refine ⟨fun y hy hny => ?_, fun s hs hns => ?_⟩
  · have hNO : ι (N y) ∈ O := by rw [hN]; exact O.mul_mem hy (hOs y hy)
    obtain ⟨z, hz, hyz⟩ := (hdich y hy).resolve_left hny
    have h1 := hNmul1 y z hyz
    have hNz : ι (N z) ∈ O := by rw [hN]; exact O.mul_mem hz (hOs z hz)
    refine ⟨hNO, ?_, N z, hNz, h1⟩
    rintro ⟨t, ht, e⟩
    apply hϖnu
    refine ⟨ι t * ι (N z), O.mul_mem ht hNz, ?_⟩
    rw [← map_mul, ← map_mul, ← mul_assoc, ← e, h1, map_one]
  · have hsu : ∃ z ∈ O, ι s * z = 1 := by
      refine (hdich _ hs).resolve_left ?_
      rintro ⟨z, hz, e⟩
      apply hns
      refine ⟨((ϖ⁻¹ : Kˣ) : K) * s, ?_, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      have : ι (((ϖ⁻¹ : Kˣ) : K) * s) = z := by
        rw [map_mul, e, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [this]; exact hz
    obtain ⟨z, hz, hsz⟩ := hsu
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hsz
      have h10 : (1 : K) = 0 := hinj (by rw [map_one, map_zero]; exact hsz.symm)
      obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
      exact hxy (by rw [← one_mul x, ← one_mul y, h10, zero_mul, zero_mul])
    obtain ⟨r, hr⟩ := hK.mul_inv_cancel hs0
    have hzr : z = ι r := by
      calc z = ι (s * r) * z := by rw [hr, map_one, one_mul]
        _ = ι r := by rw [map_mul, mul_comm (ι s), mul_assoc, hsz, mul_one]
    have hrO : ι r ∈ O := hzr ▸ hz
    refine ⟨⟨r, hrO, hr⟩, ?_⟩
    obtain ⟨w, hw, hNw⟩ := hnorm s hs ⟨ι r, hrO, by rw [← map_mul, hr, map_one]⟩
    refine ⟨w, hw, star w * ι r, O.mul_mem (hOs w hw) hrO, ?_, hNw⟩
    rw [← mul_assoc, ← hN, hNw, ← map_mul, hr, map_one]

set_option maxHeartbeats 1000000 in
theorem residue_gauss_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ U A ψ μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖnu hdich hnorm hvol a ha hna
  classical
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨-, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hιc, hιK⟩ := algebraMap_continuous_isCompact_preimage A
  obtain ⟨hψlc, hψn, -⟩ := (GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ
  obtain ⟨alg1, alg2⟩ := residue_algebra hK hinj A.NL hN O ϖ hOs hϖO hϖnu hdich hnorm
  set ι := algebraMap A.K A.L with hι
  set p : A.K := (ϖ : A.K) with hp

  set f : A.K → ℂ := fun t => A.psiK ψ (a * t) with hfdef
  have hfadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hfdef, Et.psiK, mul_add, map_add, AddChar.map_add_eq_mul]
  have hfc : Continuous f := by
    have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψlc.continuous.comp (htr.comp (continuous_const.mul continuous_id))
  have hfn : ∀ t, ‖f t‖ = 1 := fun t => hψn _

  set OK : Subring A.K := O.comap ι with hOK
  have memOK : ∀ s, s ∈ OK ↔ ι s ∈ O := fun s => Iff.rfl
  set PK : Set A.K := ϖ • (OK : Set A.K) with hPK
  have memPK : ∀ s, s ∈ PK ↔ ∃ t, ι t ∈ O ∧ s = p * t := by
    intro s
    simp only [hPK, Set.mem_smul_set, SetLike.mem_coe, memOK, Units.smul_def, smul_eq_mul]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  set UK : Set A.K := (OK : Set A.K) \ PK with hUK
  set PL : Set A.L := {y | ∃ z ∈ O, y = ι p * z} with hPL
  set UL : Set A.L := (O : Set A.L) \ PL with hUL
  have hPKsub : PK ⊆ OK := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs
    exact (memOK _).2 (by rw [map_mul]; exact O.mul_mem hϖO ht)
  have hPLsub : PL ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    exact O.mul_mem hϖO hz
  have hPLeq : PL = (fun z => ι p * z) '' (O : Set A.L) := by
    ext y; simp only [hPL, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

  have hOKo : IsOpen (OK : Set A.K) := hOo.preimage hιc
  have hOKc : IsCompact (OK : Set A.K) := hιK _ hOc
  have hPKc : IsCompact PK := by
    rw [hPK]; exact hOKc.image (continuous_const_smul ϖ)
  have hPLc : IsCompact PL := by
    rw [hPLeq]; exact hOc.image (continuous_const.mul continuous_id)
  have hOKm : MeasurableSet (OK : Set A.K) := hOKc.isClosed.measurableSet
  have hPKm : MeasurableSet PK := hPKc.isClosed.measurableSet
  have hUKm : MeasurableSet UK := hOKm.diff hPKm
  have hOm : MeasurableSet (O : Set A.L) := hOc.isClosed.measurableSet
  have hPLm : MeasurableSet PL := hPLc.isClosed.measurableSet
  have hULm : MeasurableSet UL := hOm.diff hPLm
  have h1UK : (1 : A.K) ∈ UK := by
    refine ⟨(memOK 1).2 (by rw [map_one]; exact O.one_mem), fun h => hϖnu ?_⟩
    obtain ⟨t, ht, e⟩ := (memPK 1).1 h
    exact ⟨ι t, ht, by rw [← map_mul, ← e, map_one]⟩
  have hUKo : IsOpen UK := hOKo.sdiff hPKc.isClosed

  set μK : Measure A.K := Measure.addHaar with hμK
  set x : ℝ := A.absK p with hxdef
  have hx : x = (distribHaarChar A.K ϖ : ℝ) := EtMeas.absK_unit A ϖ
  have hx0 : 0 ≤ x := by rw [hx]; exact NNReal.coe_nonneg _
  have hOKT : μK OK ≠ ⊤ := hOKc.measure_lt_top.ne
  have hPKT : μK PK ≠ ⊤ := hPKc.measure_lt_top.ne
  have hUKT : μK UK ≠ ⊤ := (measure_mono Set.sdiff_subset).trans_lt hOKc.measure_lt_top |>.ne
  have hUK0 : μK UK ≠ 0 := hUKo.measure_ne_zero μK ⟨1, h1UK⟩
  have hOT : μ O ≠ ⊤ := hOc.measure_lt_top.ne
  have hO0 : μ O ≠ 0 := hOo.measure_ne_zero μ ⟨1, O.one_mem⟩
  set mK : ℝ := (μK OK).toReal with hmK
  set M : ℝ := (μ O).toReal with hM
  have hmPK : (μK PK).toReal = x * mK := by
    rw [hPK, ← distribHaarChar_mul, ENNReal.toReal_mul, hx]; rfl
  have hmUK : (μK UK).toReal = mK - x * mK := by
    rw [hUK, measure_sdiff hPKsub hPKm.nullMeasurableSet hPKT, ENNReal.toReal_sub_of_le (measure_mono hPKsub) hOKT,
      hmPK]
  have hmPL : (μ PL).toReal = x ^ 2 * M := by
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hmUL : (μ UL).toReal = M - x ^ 2 * M := by
    rw [hUL, measure_sdiff hPLsub hPLm.nullMeasurableSet (measure_ne_top_of_subset hPLsub hOT),
      ENNReal.toReal_sub_of_le (measure_mono hPLsub) hOT, hmPL]
  have hmUKpos : 0 < (μK UK).toReal := ENNReal.toReal_pos hUK0 hUKT

  have hf1 : ∀ m, ι m ∈ O → f (p * m) = 1 := by
    intro m hm
    simp only [hfdef]
    rw [← mul_assoc]; exact ha m hm
  have hNp : ∀ z, A.NL (ι p * z) = p * (p * A.NL z) := by
    intro z
    apply hinj
    rw [hN, map_mul, map_mul, hN, star_mul', A.star_K]
    ring

  set I : ℂ := ∫ y in (O : Set A.L), f (A.NL y) ∂μ with hIdef
  have hI1 : ∀ s ∈ UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ = I := by
    intro s hs
    obtain ⟨-, w, hw, v, hv, hwv, hNw⟩ :=
      alg2 s ((memOK s).1 hs.1) (fun ⟨t, ht, e⟩ => hs.2 ((memPK s).2 ⟨t, ht, e⟩))
    have key : ∀ y, A.NL (w * y) = s * A.NL y := by
      intro y
      apply hinj
      rw [hN, map_mul, hN, ← hNw, hN, star_mul']
      ring
    have := setIntegral_comp_mul_unit μ (O : Set A.L) w v hwv hO0 hOT (fun y hy => O.mul_mem hw hy)
      (fun y hy => O.mul_mem hv hy) (fun y => f (A.NL y))
    simp only [key] at this
    exact this

  have hIOK : IntegrableOn f OK μK := hfc.continuousOn.integrableOn_compact hOKc
  have hintOK : ∫ s in (OK : Set A.K), f s ∂μK = 0 := by
    obtain ⟨s₀, hs₀, hne⟩ := hna
    exact setIntegral_addChar_eq_zero μK OK.toAddSubgroup f hfadd s₀ hs₀ hne
  have hintPK : ∫ s in PK, f s ∂μK = (μK PK).toReal := by
    rw [setIntegral_congr_fun hPKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs; exact hf1 t ht)]
    simp [Measure.real]
  have hintUK : ∫ s in UK, f s ∂μK = -((μK PK).toReal : ℂ) := by
    rw [hUK, setIntegral_sdiff hPKm hIOK hPKsub, hintOK, hintPK, zero_sub]
  have hUKmul : ∀ t ∈ UK, ∫ s in UK, f (s * t) ∂μK = -((μK PK).toReal : ℂ) := by
    intro t ht
    obtain ⟨⟨r, hr, htr⟩, -⟩ :=
      alg2 t ((memOK t).1 ht.1) (fun ⟨m, hm, e⟩ => ht.2 ((memPK t).2 ⟨m, hm, e⟩))
    have hcl : ∀ u v : A.K, u * v = 1 → ι u ∈ O → ι v ∈ O → ∀ s ∈ UK, u * s ∈ UK := by
      intro u v huv hu hv s hs
      refine ⟨(memOK _).2 (by rw [map_mul]; exact O.mul_mem hu hs.1), fun h => hs.2 ?_⟩
      obtain ⟨m, hm, e⟩ := (memPK _).1 h
      refine (memPK s).2 ⟨v * m, by rw [map_mul]; exact O.mul_mem hv hm, ?_⟩
      calc s = v * (u * s) := by rw [← mul_assoc, mul_comm v u, huv, one_mul]
        _ = p * (v * m) := by rw [e]; ring
    have := setIntegral_comp_mul_unit μK UK t r htr hUK0 hUKT (hcl t r htr ht.1 hr)
      (hcl r t (by rw [mul_comm]; exact htr) hr ht.1) f
    simp only [mul_comm _ t]
    rw [this, hintUK]
  have hJP : ∀ y ∈ PL, ∫ s in UK, f (s * A.NL y) ∂μK = (μK UK).toReal := by
    rintro y ⟨z, hz, rfl⟩
    rw [setIntegral_congr_fun hUKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      simp only [hNp]
      rw [show s * (p * (p * A.NL z)) = p * (s * p * A.NL z) by ring]
      refine hf1 _ ?_
      rw [map_mul, map_mul, hN]
      exact O.mul_mem (O.mul_mem hs.1 hϖO) (O.mul_mem hz (hOs z hz)))]
    simp [Measure.real]
  have hJU : ∀ y ∈ UL, ∫ s in UK, f (s * A.NL y) ∂μK = -((μK PK).toReal : ℂ) := by
    intro y hy
    obtain ⟨h1, h2, -⟩ := alg1 y hy.1 hy.2
    exact hUKmul _ ⟨(memOK _).2 h1, fun h => h2 ((memPK _).1 h)⟩

  have hswap := setIntegral_swap_of_continuous μK μ UK (O : Set A.L) hUKT hOT (fun s y => f (s * A.NL y))
    (hfc.comp (continuous_fst.mul ((EtMeas.continuous_NL A).comp continuous_snd))) (fun s y => (hfn _).le)
  have hLHS : ∫ s in UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ ∂μK = (μK UK).toReal * I := by
    rw [setIntegral_congr_fun hUKm (g := fun _ => I) hI1]
    simp [Measure.real]
  have hOsplit : (O : Set A.L) = PL ∪ UL := (Set.union_sdiff_cancel hPLsub).symm
  have hRHS : ∫ y in (O : Set A.L), ∫ s in UK, f (s * A.NL y) ∂μK ∂μ =
      (μ PL).toReal * (μK UK).toReal + (μ UL).toReal * (-((μK PK).toReal : ℂ)) := by
    have hPLT : μ PL ≠ ⊤ := measure_ne_top_of_subset hPLsub hOT
    have hULT : μ UL ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hOT
    have i1 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) PL μ :=
      (integrableOn_const hPLT).congr_fun (fun y hy => (hJP y hy).symm) hPLm
    have i2 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) UL μ :=
      (integrableOn_const hULT).congr_fun (fun y hy => (hJU y hy).symm) hULm
    rw [hOsplit, setIntegral_union Set.disjoint_sdiff_right hULm i1 i2,
      setIntegral_congr_fun hPLm hJP, setIntegral_congr_fun hULm hJU]
    simp [Measure.real]
  rw [hLHS, hRHS] at hswap
  have hne : ((μK UK).toReal : ℂ) ≠ 0 := by exact_mod_cast hmUKpos.ne'
  apply mul_left_cancel₀ hne
  rw [hswap, hmUK, hmPL, hmUL, hmPK]
  push_cast
  ring

end GlobalTheory.JR.ResidueGauss
