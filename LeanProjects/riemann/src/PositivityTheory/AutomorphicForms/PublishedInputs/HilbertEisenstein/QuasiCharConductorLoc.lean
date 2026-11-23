import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

section Abstract

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem shell_vanish (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) {n j k : ℤ} (hψ : IsTrivialOn ψ n) {v : Kˣ}
    (hv0 : ord (v : K) = 0) (hv1 : χ v ≠ 1) (hvj : (v : K) - 1 ∈ valBall K j) (hjk : n ≤ j + k) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ) ∂multHaar K = 0 := by
  refine setIntegral_ordShell_eq_zero _ hv0 (a := ((χ v : ℂˣ) : ℂ)) (fun h => hv1 (Units.val_eq_one.mp h)) k
    fun u hu => ?_
  have hmem : ((v : K) - 1) * (u : K) ∈ valBall K n := by
    have h := mul_mem_valBall hvj ((mem_valBall_iff_le_ord u.ne_zero).mpr (le_of_eq (mem_ordShell.mp hu).symm))
    exact valBall_antitone hjk h
  have hψ' : (ψ ((v * u : Kˣ) : K) : ℂ) = (ψ (u : K) : ℂ) := by
    rw [show ((v * u : Kˣ) : K) = (u : K) + ((v : K) - 1) * (u : K) by push_cast; ring,
      AddChar.map_add_eq_mul, hψ _ hmem, mul_one]
  rw [hψ', map_mul, Units.val_mul]
  ring

theorem shell_ne_zero (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hχ : Continuous χ) (hr : ¬ IsUnramifiedChar χ) :
    ∫ u in ordShell K (addCharConductor ψ - quasiCharConductor χ), ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ)
      ∂multHaar K ≠ 0 := by
  have hχ' : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := continuous_quasiChar_inv hχ
  have hr' : ¬ IsUnramifiedChar χ⁻¹ := by rwa [isUnramifiedChar_inv_iff]
  obtain ⟨a, ha, k, hk⟩ := exists_localEpsilon_eq_monomial (χ := χ⁻¹) hψ hψ1 hχ'
  have h0 := hk 0
  rw [localEpsilon_of_not_isUnramified_eq hr', quasiCharConductor_inv, inv_inv] at h0
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ
  have hadd : ∫ x in (valBall K m : Set K) \ valBall K (m + 1), quasiCharExt χ x * (ψ x : ℂ) ∂haarIntegers K ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h0
    simp only [neg_zero, Complex.cpow_zero, one_zpow, mul_one] at h0
    exact ha h0.symm
  have hsh := setIntegral_ordShell_eq_haarIntegers (fun x => quasiCharExt χ x * (ψ x : ℂ)) m
  simp only [quasiCharExt_units] at hsh
  rw [hsh]
  refine mul_ne_zero ?_ hadd
  have h1 : (multHaarConst K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have h2 : (residueCard K : ℝ) ^ m ≠ 0 := zpow_ne_zero _ residueCard_pos_real.ne'
  exact_mod_cast mul_ne_zero h1 h2

end Abstract

section Bridge

variable {F : Type} [Field F] [NumberField F]

theorem dd_eq (w : HeightOneSpectrum (𝓞 F)) : dd w = differentExp w := by
  unfold dd differentExp ordI
  rw [FractionalIdeal.count_coe]
  exact _root_.differentIdeal_ne_bot

theorem continuous_loc (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) : Continuous (ω.loc w) :=
  ω.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele w)

theorem mem_U_iff (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : (w.adicCompletion F)ˣ) :
    x ∈ unitFiltrationUnits (w.adicCompletion F) n ↔
      IsUnitAt w x ∧ Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : x ∈ unitFiltrationUnits (w.adicCompletion F) 0 ↔ IsUnitAt w x := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, IsUnitAt, valued_eq_one_iff_ord x.ne_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [h0]
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have hx : (x : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord x.ne_zero]
      exact le_of_eq ((valued_eq_one_iff_ord x.ne_zero).mp h).symm
    have h1 : (1 : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord one_ne_zero]
      have := (valued_eq_one_iff_ord (one_ne_zero (α := w.adicCompletion F))).mp (map_one _)
      omega
    have := (mem_valBall_iff_valued).mp (sub_mem hx h1)
    simpa using this
  · rw [mem_unitFiltrationUnits_iff_valBall hn, mem_valBall_iff_valued]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have hU := unitFiltrationUnits_antitone (Nat.zero_le n) ((mem_unitFiltrationUnits_iff_valBall hn).mpr
        ((mem_valBall_iff_valued).mpr h))
      exact h0.mp hU
    · exact fun h => h.2

theorem quasiCharConductor_loc {ω : HChar F} {c : ℕ} {w : HeightOneSpectrum (𝓞 F)} (h : IsCondAt w ω c) :
    quasiCharConductor (ω.loc w) = c := by
  have hset : {n : ℕ | unitFiltrationUnits (w.adicCompletion F) n ≤ (ω.loc w).ker} =
      {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hle x hx hv
      exact MonoidHom.mem_ker.mp (hle ((mem_U_iff w n x).mpr ⟨hx, hv⟩))
    · intro hP x hx
      obtain ⟨h1, h2⟩ := (mem_U_iff w n x).mp hx
      exact MonoidHom.mem_ker.mpr (hP x h1 h2)
  unfold quasiCharConductor
  rw [hset]
  exact h.csInf_eq

end Bridge

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open LocalShellIntegral

theorem local_ramified_holds : LocRam := by
  intro F _ _ _ ω c H w hcw
  set χ := ω.loc w
  set ψ := localAdelicChar F w
  have hcond : quasiCharConductor χ = c w := quasiCharConductor_loc (H.cond w)
  have hn : addCharConductor ψ = -dd w := by rw [addCharConductor_localAdelicChar, dd_eq]
  have hχ : Continuous χ := continuous_loc ω w
  have hr : ¬ IsUnramifiedChar χ := by
    rw [← quasiCharConductor_eq_zero_iff, hcond]
    all_goals first | exact hcw | exact hχ
  refine ⟨fun k hk => ?_, ?_⟩
  · set j : ℕ := (-dd w - k).toNat with hj
    have hjc : j < c w := by
      have : (j : ℤ) < c w := by
        rcases le_or_gt (-dd w - k) 0 with h | h
        · rw [hj, Int.toNat_of_nonpos h]; exact_mod_cast Nat.pos_of_ne_zero hcw
        · rw [hj, Int.toNat_of_nonneg h.le]; omega
      exact_mod_cast this
    have hnot : j ∉ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
      fun hm => absurd ((H.cond w).2 hm) (not_le.mpr hjc)
    simp only [Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨x, hx1, hx2, hx3⟩ := hnot
    have hψt : IsTrivialOn ψ (-dd w) := (isTrivialOn_localAdelicChar_iff w _).2 (by rw [dd_eq])
    refine shell_vanish χ ψ (n := -dd w) (j := j) hψt ((valued_eq_one_iff_ord x.ne_zero).mp hx1) hx3
      ((mem_valBall_iff_valued).mpr hx2) ?_
    have : (-dd w - k) ≤ (j : ℤ) := by rw [hj]; exact Int.self_le_toNat _
    omega
  · have h := shell_ne_zero χ ψ (continuous_localAdelicChar w) (localAdelicChar_ne_one w) hχ hr
    rw [hn, hcond] at h
    have e : -((c w : ℤ) + dd w) = -dd w - (c w : ℤ) := by ring
    rw [e]
    exact h

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
