import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlaceStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

include hp hPv in

theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega

include hp hPv in

theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => GlobalTheory.T.singleBlock_doublingIntegral_value D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

@[simp] theorem reQ_geo (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).geo = Z₀.geo := rfl

@[simp] theorem reQ_Lev (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Lev = Z₀.Lev := rfl

@[simp] theorem reQ_levPr (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).levPr = Z₀.levPr := rfl

@[simp] theorem reQ_shv (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv = Z₀.shv := rfl

@[simp] theorem reQ_shv_N (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv_N = Z₀.shv_N := rfl

@[simp] theorem reQ_shv_lev (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv_lev = Z₀.shv_lev := rfl

@[simp] theorem reQ_PlP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).PlP = Z₀.PlP := rfl

@[simp] theorem reQ_plpNe (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plpNe = Z₀.plpNe := rfl

@[simp] theorem reQ_wtP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).wtP = Z₀.wtP := rfl

@[simp] theorem reQ_wtP_nonneg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_nonneg = Z₀.divisorWeight_nonneg := rfl

@[simp] theorem reQ_wtP_sum (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_sum = Z₀.divisorWeight_sum := rfl

@[simp] theorem reQ_plP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plP = Z₀.plP := rfl

@[simp] theorem reQ_wtP_def (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_def = Z₀.divisorWeight_def := rfl

@[simp] theorem reQ_jC (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jC = Z₀.jC := rfl

@[simp] theorem reQ_Mp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Mp = Z₀.Mp := rfl

@[simp] theorem reQ_vdd (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd = Z₀.vdd := rfl

@[simp] theorem reQ_vdd_unram (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd_unram = Z₀.vdd_unram := rfl

@[simp] theorem reQ_phiFr_unram (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).phiFr_unram = Z₀.phiFr_unram := rfl

@[simp] theorem reQ_vdd_nonneg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd_nonneg = Z₀.vdd_nonneg := rfl

@[simp] theorem reQ_CurveM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).CurveM = Z₀.CurveM := rfl

@[simp] theorem reQ_degM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).degM = Z₀.degM := rfl

@[simp] theorem reQ_htMdl (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htMdl = Z₀.htMdl := rfl

@[simp] theorem reQ_htCurve (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htCurve = Z₀.htCurve := rfl

@[simp] theorem reQ_htCurve_deg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htCurve_deg = Z₀.htCurve_deg := rfl

@[simp] theorem reQ_MjH (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjH = Z₀.MjH := rfl

@[simp] theorem reQ_MjH_good (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjH_good = Z₀.MjH_good := rfl

@[simp] theorem reQ_jM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM = Z₀.jM := rfl

@[simp] theorem reQ_jM_basis (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_basis = Z₀.jM_basis := rfl

@[simp] theorem reQ_jM_lat (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_lat = Z₀.jM_lat := rfl

@[simp] theorem reQ_MjLat_sub (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjLat_sub = Z₀.MjLat_sub := rfl

@[simp] theorem reQ_jM_metric (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_metric = Z₀.jM_metric := rfl

@[simp] theorem reQ_Comp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Comp = Z₀.Comp := rfl

@[simp] theorem reQ_degHH (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).degHH = Z₀.degHH := rfl

@[simp] theorem reQ_Yv (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Yv = Z₀.Yv := rfl

@[simp] theorem reQ_Ybd (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Ybd = Z₀.Ybd := rfl

@[simp] theorem reQ_Lw (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Lw = Z₀.Lw := rfl

@[simp] theorem reQ_iMj (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).iMj = Z₀.iMj := rfl

@[simp] theorem reQ_iMj_mem (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).iMj_mem = Z₀.iMj_mem := rfl

@[simp] theorem reQ_logLam (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).logLam = Z₀.logLam := rfl

@[simp] theorem reQ_logLam_base (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).logLam_base = Z₀.logLam_base := rfl

@[simp] theorem reQ_kapR (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR = Z₀.kapR := rfl

@[simp] theorem reQ_kapR_pos (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR_pos = Z₀.kapR_pos := rfl

@[simp] theorem reQ_kapR_conj (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR_conj = Z₀.kapR_conj := rfl

@[simp] theorem reQ_Surf (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Surf = Z₀.Surf := rfl

@[simp] theorem reQ_surfCh2 (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfCh2 = Z₀.surfCh2 := rfl

@[simp] theorem reQ_surfDegOm (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfDegOm = Z₀.surfDegOm := rfl

@[simp] theorem reQ_SurfFp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).SurfFp = Z₀.SurfFp := rfl

@[simp] theorem reQ_surfFpCh2 (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfFpCh2 = Z₀.surfFpCh2 := rfl

@[simp] theorem reQ_plpFin (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plpFin = Z₀.plpFin := rfl

@[simp] theorem reQ_compFin (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).compFin = Z₀.compFin := rfl

@[simp] theorem reQ_Qp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Qp = qpSet Tp := rfl

@[simp] theorem reQ_QPl (Z₀ : DivX D) (μ : D.what₂.Tup) :
    (reQ Tp hp Pv hPv Z₀).QPl μ = {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
