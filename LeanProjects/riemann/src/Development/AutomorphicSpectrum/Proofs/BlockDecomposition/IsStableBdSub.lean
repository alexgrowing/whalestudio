import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.CompanionTheory.CTSmooth
open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace GlobalTheory.CompanionTheory.HullExp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def trans (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trans_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) :
    (trans r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    change f (aT E N r s * (aT E N r (s * i) * g)) = _
    rw [← mul_assoc, ← aT_add]
    congr 3
    push_cast
    ring

theorem kl_iff {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} :
    Kl r s p F ↔ aeval (trans (E := E) (N := N) r s) p F = 0 := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, trans_pow]
  constructor
  · intro h
    funext g
    simpa [Finset.sum_apply] using h g
  · intro h g
    simpa [Finset.sum_apply] using congrFun h g

theorem kl_mul_left {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (q : ℂ[X]) :
    Kl r s (q * p) F := by
  rw [kl_iff] at h ⊢
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem lo_fin {φ : Sm E N} (h : LO φ) (k : GL (Fin N) (Af E)) : LO (act (.fin k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ ?_⟩
  · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h.1]
  · have hc : Continuous fun u : GL (Fin N) (Af E) => k⁻¹ * u * k := by fun_prop
    have hm : {u | finRep E N u φ = φ} ∈ nhds (k⁻¹ * 1 * k) := by
      have : k⁻¹ * 1 * k = 1 := by group
      rw [this]
      exact h.2.mem_nhds (by simp)
    refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hm) fun u hu => ?_
    have hu' : finRep E N (k⁻¹ * u * k) φ = φ := hu
    change finRep E N u (finRep E N k φ) = finRep E N k φ
    conv_rhs => rw [← hu']
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

theorem lo_cpt {φ : Sm E N} (h : LO φ) (k : Kinf E N) : LO (act (.cpt k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun u hu => ?_)⟩
  · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h.1]
  · have hu' : finRep E N u φ = φ := hu
    apply Subtype.ext
    funext g
    change φ.1 (g * finGL E N u * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    have e : φ.1 (g * infGL E N (Unitary.toUnits k) * finGL E N u) = φ.1 (g * infGL E N (Unitary.toUnits k)) :=
      congrArg (fun ψ : Sm E N => ψ.1 (g * infGL E N (Unitary.toUnits k))) hu'
    rw [← e, mul_assoc, mul_assoc, infGL_comm]

theorem lo_act {φ : Sm E N} (h : LO φ) (o : Op E N) : LO (act o φ) := by
  cases o with
  | fin k => exact lo_fin h k
  | cpt k => exact lo_cpt h k
  | lie X => exact lo_lie h X

theorem lo_add {φ ψ : Sm E N} (h : LO φ) (h' : LO ψ) : LO (φ + ψ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((h.2.inter h'.2).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)⟩
  · change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.1, h'.1]
  · have h1 : finRep E N k φ = φ := hk.1
    have h2 : finRep E N k ψ = ψ := hk.2
    change finRep E N k (φ + ψ) = φ + ψ
    rw [map_add, h1, h2]

theorem lo_smul {φ : Sm E N} (h : LO φ) (c : ℂ) : LO (c • φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · change c * φ.1 _ = c * φ.1 _
    rw [h.1]
  · have h1 : finRep E N k φ = φ := hk
    change finRep E N k (c • φ) = c • φ
    rw [map_smul, h1]

theorem lo_zero : LO (0 : Sm E N) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  have : {k | finRep E N k (0 : Sm E N) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
  rw [this]
  exact isOpen_univ

section CT

variable {r : ℕ} [MeasurableSpace (BlockIx N r → Ad E)] [BorelSpace (BlockIx N r → Ad E)]
  (μ : Measure (BlockIx N r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx N r → Ad E))

theorem ct_add_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {φ ψ : Sm E N} (hφ : LO φ) (hψ : LO ψ) :
    PositivityTheory.Affgl.CT.ct μ 𝓕 (φ + ψ).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 + PositivityTheory.Affgl.CT.ct μ 𝓕 ψ.1 := by
  funext g
  exact integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.1 hφ.2 g)
    (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.1 hψ.2 g)

theorem kl_act_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {s : ℝ} {p : ℂ[X]} {φ : Sm E N}
    (hφ : LO φ) (h : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)) (o : Op E N) :
    Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 (act o φ).1) := by
  cases o with
  | fin k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | cpt k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 =
        fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | lie X =>
    obtain ⟨F, hF1, hF2⟩ := ct_smooth E N r φ hφ.1 hφ.2 μ 𝓕 inferInstance h𝓕
    have e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := funext hF1
    have e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1 := funext (hF2 X)
    rw [← e2]
    exact kl_lie (e1 ▸ h) X

end CT

def bdSub (r : ℕ) (ρ : ℝ) : Submodule ℂ (Sm E N) where
  carrier := {φ | LO φ ∧ ∃ p : ℂ[X], p.Monic ∧ (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp ρ) ∧ ∀ F, IsCT r φ.1 F → Kl r 1 p F}
  add_mem' := by
    rintro φ ψ ⟨hφ, p, hp, hpz, hpk⟩ ⟨hψ, q, hq, hqz, hqk⟩
    refine ⟨lo_add hφ hψ, p * q, hp.mul hq, fun z hz => ?_, ?_⟩
    · exact (Polynomial.root_mul.1 hz).elim (hpz z) (hqz z)
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      have _ := hμ
      rw [ct_add_lo μ 𝓕 h𝓕 hφ hψ]
      refine (klSub r 1 (p * q)).add_mem ?_ ?_
      · rw [mul_comm]
        exact kl_mul_left (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) q
      · exact kl_mul_left (hqk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) p
  zero_mem' := by
    refine ⟨lo_zero, 1, monic_one, fun z hz => ?_, ?_⟩
    · simp [Polynomial.IsRoot] at hz
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have : PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0 := by
        funext g
        simp [PositivityTheory.Affgl.CT.ct]
      rw [this]
      exact (klSub r 1 1).zero_mem
  smul_mem' := by
    rintro c φ ⟨hφ, p, hp, hpz, hpk⟩
    refine ⟨lo_smul hφ c, p, hp, hpz, ?_⟩
    rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
    let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
    rw [ct_smul]
    exact (klSub r 1 p).smul_mem c (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)

theorem isStable_bdSub (r : ℕ) (ρ : ℝ) : IsStable (bdSub (E := E) (N := N) r ρ) := by
  rintro o φ ⟨hφ, p, hp, hpz, hpk⟩
  refine ⟨lo_act hφ o, p, hp, hpz, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  have _ := hμ
  exact kl_act_lo μ 𝓕 h𝓕 hφ (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) o

theorem re_le_of_mem {r : ℕ} {ρ : ℝ} {φ : Sm E N} (hφ : φ ∈ bdSub (E := E) (N := N) r ρ) {c : ℂ}
    (hc : c ∈ Exp r φ.1) : c.re ≤ ρ := by
  obtain ⟨-, p, -, hpz, hpk⟩ := hφ
  obtain ⟨F₀, hCT, F, hF, hF0, hFe⟩ := hc
  have hroot := kl_eigen (kl_span (hpk _ hCT) hF) hF0 hFe
  have := hpz _ hroot
  simpa [Complex.norm_exp] using this

theorem mem_bdSub {r : ℕ} (hr : 0 < r) (hrN : r < N) {ρ : ℝ} {φ : Sm E N} (hφ : IsAutForm φ)
    (hρ : ∀ c ∈ Exp r φ.1, c.re ≤ ρ) : φ ∈ bdSub (E := E) (N := N) r ρ := by
  obtain ⟨-, -, -, hDct⟩ := dict_holds E N
  obtain ⟨hct, huniq⟩ := hDct φ hφ r hr hrN
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
    have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
    obtain ⟨F, hF, -⟩ := ct_smooth E N r φ hφ.left hφ.level μ 𝓕 hμ h𝓕
    have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
    intro g
    rw [e2]
    exact PDich.continuous_aT F r g
  obtain ⟨p, hp, hk, hroot⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
    (finTr_holds E N φ hφ r hr hrN _ hct)
  have hk' : Kl r 1 p (An.ctn r φ.1) := fun g => by
    simpa only [one_mul] using hk g
  refine ⟨⟨hφ.left, hφ.level⟩, p, hp, fun z hz => ?_, fun F hF => ?_⟩
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroot z hz
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hρ c ⟨_, hct, F, hF, hF0, hFe⟩)
  · obtain ⟨a, -, rfl⟩ := huniq F hF
    exact (klSub r 1 p).smul_mem a hk'

end GlobalTheory.CompanionTheory.HullExp

open GlobalTheory.CompanionTheory.HullExp in

theorem GlobalTheory.CompanionTheory.HullExp.hullNonPos : PositivityTheory.Rg.BcB.E.E3.HullNonPos := by
  intro E _ _ _ N S hS φ hφ r hr hrN c hc
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have key : ∀ ψ ∈ S, ψ ∈ bdSub (E := E) (N := N) r (An.rho E N r) := fun ψ hψ =>
    mem_bdSub hr hrN (hS ψ hψ).1 fun c' hc' => by
      have := (hS ψ hψ).2 r hr hrN c' hc'
      rw [pE, sub_nonpos, div_le_iff₀ hd] at this
      rw [An.rho]
      linarith
  have hmem : φ ∈ bdSub (E := E) (N := N) r (An.rho E N r) :=
    (Submodule.mem_sInf.1 hφ) _ ⟨key, isStable_bdSub r _⟩
  have := re_le_of_mem hmem hc
  rw [pE, sub_nonpos, div_le_iff₀ hd]
  rw [An.rho] at this
  linarith

end
