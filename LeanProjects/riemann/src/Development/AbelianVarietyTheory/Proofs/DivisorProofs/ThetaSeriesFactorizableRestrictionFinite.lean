import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.SplitSvN
open MeasureTheory Matrix ComplexConjugate

theorem exists_haar_factor {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (p : G →+ G) (hp : Continuous p) (hpp : ∀ x, p (p x) = p x) :
    ∃ μ : Measure G, μ.IsAddHaarMeasure ∧ ∃ I J : (G → ℂ) → ℂ,
      ∀ a b : G → ℂ, ∫ x, a (p x) * b (x - p x) ∂μ = I a * J b := by
  let H₁ : AddSubgroup G := (AddMonoidHom.id G - p).ker
  let H₂ : AddSubgroup G := p.ker
  have m₁ : ∀ x, x ∈ H₁ ↔ x - p x = 0 := fun x => Iff.rfl
  have m₂ : ∀ x, x ∈ H₂ ↔ p x = 0 := fun x => Iff.rfl
  have c₁ : IsClosed (H₁ : Set G) := isClosed_eq (continuous_id.sub hp) continuous_const
  have c₂ : IsClosed (H₂ : Set G) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace H₁ := c₁.locallyCompactSpace
  haveI : LocallyCompactSpace H₂ := c₂.locallyCompactSpace
  haveI : SecondCountableTopology H₁ := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology H₂ := TopologicalSpace.Subtype.secondCountableTopology _
  have k₁ : ∀ z : H₁ × H₂, p ((z.1 : G) + z.2) = z.1 := fun z => by
    rw [map_add, (m₂ _).1 z.2.2, add_zero]
    exact (sub_eq_zero.1 ((m₁ _).1 z.1.2)).symm
  let e : (H₁ × H₂) ≃ₜ+ G :=
    { toFun := fun z => (z.1 : G) + z.2
      invFun := fun x => (⟨p x, (m₁ _).2 (by rw [hpp, sub_self])⟩, ⟨x - p x, (m₂ _).2 (by rw [map_sub, hpp, sub_self])⟩)
      left_inv := fun z => Prod.ext (Subtype.ext (k₁ z)) (Subtype.ext (by
        show (z.1 : G) + z.2 - p ((z.1 : G) + z.2) = z.2
        rw [k₁, add_sub_cancel_left]))
      right_inv := fun x => add_sub_cancel _ _
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]
        abel
      continuous_toFun := by fun_prop
      continuous_invFun := (hp.subtype_mk _).prodMk ((continuous_id.sub hp).subtype_mk _) }
  let ν : Measure (H₁ × H₂) := (Measure.addHaar : Measure H₁).prod (Measure.addHaar : Measure H₂)
  haveI : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨ν.map e, e.isAddHaarMeasure_map ν, fun a => ∫ x : H₁, a x ∂Measure.addHaar,
    fun b => ∫ x : H₂, b x ∂Measure.addHaar, fun a b => ?_⟩
  have := integral_map_equiv (μ := ν) e.toHomeomorph.toMeasurableEquiv (fun x => a (p x) * b (x - p x))
  refine this.trans ?_
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show a (p ((z.1 : G) + z.2)) * b ((z.1 : G) + z.2 - p ((z.1 : G) + z.2)) = _
  rw [k₁, add_sub_cancel_left]

theorem proportional {G : Type} [AddCommGroup G] (p : G →+ G) (hpp : ∀ x, p (p x) = p x) (a b v Φ Ψ : G → ℂ)
    (hΦ : ∀ x, Φ x = a (p x) * v (x - p x)) (hΨ : ∀ x, Ψ x = b (p x) * v (x - p x))
    (h : ∀ x x₁, p x₁ = x₁ → Ψ x * conj (Ψ (x + x₁)) = Φ x * conj (Φ (x + x₁))) : ∃ c : ℂ, Ψ = c • Φ := by
  have h0 : ∀ x, Ψ x * conj (Ψ x) = Φ x * conj (Φ x) := fun x => by simpa using h x 0 (map_zero p)
  by_cases hz : Ψ = 0
  · exact ⟨0, by rw [hz, zero_smul]⟩
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hz
  have hx₀' : Ψ x₀ ≠ 0 := hx₀
  have hv : v (x₀ - p x₀) ≠ 0 := fun hv => hx₀' (by rw [hΨ, hv, mul_zero])
  refine ⟨conj (Φ x₀) / conj (Ψ x₀), funext fun x => ?_⟩
  have h1 := h x₀ (p x - p x₀) (by rw [map_sub, hpp, hpp])
  have e1 : p (x₀ + (p x - p x₀)) = p x := by rw [map_add, map_sub, hpp, hpp, add_sub_cancel]
  have e2 : x₀ + (p x - p x₀) - p x = x₀ - p x₀ := by abel
  rw [hΨ (x₀ + _), hΦ (x₀ + _), e1, e2] at h1
  have h2 := congrArg conj h1
  simp only [map_mul, Complex.conj_conj] at h2
  have h3 : conj (Ψ x₀) * b (p x) = conj (Φ x₀) * a (p x) :=
    mul_right_cancel₀ hv (by linear_combination h2)
  have hc : conj (Ψ x₀) ≠ 0 := by simpa using hx₀'
  rw [Pi.smul_apply, smul_eq_mul, hΨ x, hΦ x]
  field_simp
  linear_combination v (x - p x) * h3

theorem proportional_of_coeff {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (ψ : AddChar R ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1)
    (hψs : ∀ x, (∀ y, ψ (x * y) = 1) → x = 0) (e : R) (he : e * e = e) (a b v Φ Ψ : (κ → R) → ℂ)
    (hΦ : ∀ x, Φ x = a (e • x) * v (x - e • x)) (hΨ : ∀ x, Ψ x = b (e • x) * v (x - e • x))
    (cΦ : Continuous Φ) (cΨ : Continuous Ψ) (bΦ : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (bΨ : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (iΦ : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → Integrable Φ μ)
    (iΨ : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → Integrable Ψ μ)
    (h : ∀ x₁ y₁ : κ → R, e • x₁ = x₁ → e • y₁ = y₁ → ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      ∫ x, Ψ x * conj (schr ψ (x₁, y₁) Ψ x) ∂μ = ∫ x, Φ x * conj (schr ψ (x₁, y₁) Φ x) ∂μ) :
    ∃ c : ℂ, Ψ = c • Φ := by
  classical
  let p : (κ → R) →+ (κ → R) := DistribSMul.toAddMonoidHom (κ → R) e
  have hp : ∀ x, p x = e • x := fun x => rfl
  have hee : ∀ x : κ → R, e • e • x = e • x := fun x => by rw [smul_smul, he]
  obtain ⟨μ, hμ, I, J, hIJ⟩ := exists_haar_factor p (continuous_const_smul e) hee
  simp only [hp] at hIJ
  have hψ0 : ∀ x, ψ x ≠ 0 := fun x hx => by simpa [hx] using hψn x

  have hint : ∀ Θ : (κ → R) → ℂ, Continuous Θ → (∃ C, ∀ x, ‖Θ x‖ ≤ C) → Integrable Θ μ → ∀ x₁,
      Continuous (fun x => Θ x * conj (Θ (x + x₁))) ∧ Integrable (fun x => Θ x * conj (Θ (x + x₁))) μ := by
    intro Θ hc ⟨C, hC⟩ hi x₁
    have hc' : Continuous fun x => conj (Θ (x + x₁)) :=
      Complex.continuous_conj.comp (hc.comp (continuous_id.add continuous_const))
    exact ⟨hc.mul hc', hi.mul_bdd hc'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [RCLike.norm_conj]; exact hC _)⟩

  have hfac : ∀ (c Θ : (κ → R) → ℂ), (∀ x, Θ x = c (e • x) * v (x - e • x)) → ∀ x₁ y : κ → R, e • x₁ = x₁ →
      (∫ x, conj (ψ (x ⬝ᵥ y)) * (Θ x * conj (Θ (x + x₁))) ∂μ =
        I (fun z => conj (ψ (z ⬝ᵥ (e • y))) * (c z * conj (c (z + x₁)))) *
          J (fun z => conj (ψ (z ⬝ᵥ y)) * (v z * conj (v z)))) ∧
      (∫ x, Θ x * conj (schr ψ (x₁, e • y) Θ x) ∂μ = conj (ψ (⅟(2 : R) * x₁ ⬝ᵥ (e • y))) *
        (I (fun z => conj (ψ (z ⬝ᵥ (e • y))) * (c z * conj (c (z + x₁)))) * J (fun z => v z * conj (v z)))) := by
    intro c Θ hΘ x₁ y hx₁
    have e1 : ∀ x, Θ (x + x₁) = c (e • x + x₁) * v (x - e • x) := fun x => by
      rw [hΘ, smul_add, hx₁, add_sub_add_right_eq_sub]
    have e2 : ∀ x : κ → R, (e • x) ⬝ᵥ (e • y) = x ⬝ᵥ (e • y) := fun x => by
      rw [smul_dotProduct, ← dotProduct_smul, hee]
    have e3 : ∀ x : κ → R, x ⬝ᵥ y = x ⬝ᵥ (e • y) + (x - e • x) ⬝ᵥ y := fun x => by
      rw [sub_dotProduct, smul_dotProduct, dotProduct_smul, add_sub_cancel]
    constructor
    · rw [← hIJ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [e1, hΘ x, e2, e3 x, AddChar.map_add_eq_mul]
      simp only [map_mul]
      ring
    · rw [← hIJ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [schr]
      rw [e1, hΘ x, e2, AddChar.map_add_eq_mul]
      simp only [map_mul]
      ring
  by_cases hJ : J (fun z => v z * conj (v z)) = 0
  ·
    have h1 := (hfac b Ψ hΨ 0 0 (smul_zero e)).2
    rw [hJ, mul_zero, mul_zero] at h1
    simp only [schr, smul_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul,
      Complex.mul_conj] at h1
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
    have hi : Integrable (fun x => Complex.normSq (Ψ x)) μ := by
      have := (hint Ψ cΨ bΨ (iΨ μ hμ) 0).2.re
      simpa [Complex.mul_conj] using this
    have h2 := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (Ψ x)) hi).1 h1
    have h3 := (Continuous.ae_eq_iff_eq μ (Complex.continuous_normSq.comp cΨ) continuous_const).1 h2
    refine ⟨0, funext fun x => ?_⟩
    rw [zero_smul]
    exact Complex.normSq_eq_zero.1 (congrFun h3 x)
  refine proportional p hee a b v Φ Ψ hΦ hΨ fun x x₁ hx₁ => ?_
  have hx₁' : e • x₁ = x₁ := hx₁
  obtain ⟨c1, i1⟩ := hint Φ cΦ bΦ (iΦ μ hμ) x₁
  obtain ⟨c2, i2⟩ := hint Ψ cΨ bΨ (iΨ μ hμ) x₁
  have hχc : ∀ y : κ → R, Continuous fun x : κ → R => conj (ψ (x ⬝ᵥ y)) := fun y =>
    Complex.continuous_conj.comp (hψc.comp (continuous_id.dotProduct continuous_const))
  have hχn : ∀ y x : κ → R, ‖conj (ψ (x ⬝ᵥ y))‖ = 1 := fun y x => by rw [RCLike.norm_conj, hψn]
  have key := GlobalTheory.CharFourierInj.eq_zero (fun (y x : κ → R) => conj (ψ (x ⬝ᵥ y))) hχc
    (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul, map_mul])
    (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul, map_mul])
    (fun x => by simp) hχn
    (fun x hx => funext fun i => hψs _ fun t => by
      have := congrArg conj (hx (Pi.single i t))
      simpa using this)
    μ (fun x => Ψ x * conj (Ψ (x + x₁)) - Φ x * conj (Φ (x + x₁))) (c2.sub c1) (i2.sub i1) (fun y => by
      simp only [mul_sub]
      rw [integral_sub (i2.bdd_mul (hχc y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hχn y x).le))
        (i1.bdd_mul (hχc y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hχn y x).le)),
        (hfac a Φ hΦ x₁ y hx₁').1, (hfac b Ψ hΨ x₁ y hx₁').1]
      have h1 := h x₁ (e • y) hx₁' (hee y) μ hμ
      rw [(hfac a Φ hΦ x₁ y hx₁').2, (hfac b Ψ hΨ x₁ y hx₁').2] at h1
      rw [mul_right_cancel₀ hJ (mul_left_cancel₀ (by simpa using hψ0 _) h1), sub_self])
  exact sub_eq_zero.1 (congrFun key x)

variable {F : Type} [Field F] [NumberField F]

theorem schA_facts (hF : IsTotallyReal F) {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ ∧ (∃ C, ∀ x, ‖Φ x‖ ≤ C) ∧
      ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → Integrable Φ μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : (κ → AF F) ≃ₜ+ (Fin (Fintype.card κ) → AF F) :=
    { toFun := fun x => x ∘ j
      invFun := fun y => y ∘ j.symm
      left_inv := fun x => funext fun i => by simp
      right_inv := fun y => funext fun i => by simp
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_apply _
      continuous_invFun := continuous_pi fun i => continuous_apply _ }
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  set Φ' := fun y : Fin (Fintype.card κ) → AF F => Φ (Function.extend j y 0) with hΦ'
  have e : Φ = Φ' ∘ r := funext fun x => by
    show Φ x = Φ (Function.extend j (x ∘ j) 0)
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  refine ⟨e ▸ hd.1.comp r.continuous, ?_, fun μ hμ => ?_⟩
  · obtain ⟨C, hC⟩ := hd.2.2 0
    exact ⟨C, fun x => by rw [e]; simpa using hC (r x)⟩
  · have hi := (GlobalTheory.decay_integrable_periodise F _ hF Φ' hd).1 (μ.map r) (r.isAddHaarMeasure_map μ)
    rw [e]
    exact hi.comp_measurable r.continuous.measurable

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def idem (S : Finset (Pl F)) : AF F :=
  infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1

theorem fstA_idem (S : Finset (Pl F)) : fstA F (idem S) = 1 := by
  have h0 : fstA F (infOne (F := F)) = 1 := rfl
  have hl : ∀ w : Pl F, fstA F (GlobalTheory.LatVac.liftV w 1) = 0 := fun w => rfl
  rw [idem, map_add, map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero]

open Classical in
theorem evFin_idem (S : Finset (Pl F)) (w : Pl F) : evFin F w (idem S) = if w ∈ S then 1 else 0 := by
  have h0 : evFin F w (infOne (F := F)) = 0 :=
    map_zero (evalV F w)
  have hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : w = x
    · subst hx; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
    · rw [if_neg hx]; exact evalV_singleFin_ne hx _
  rw [idem, map_add, map_sum, h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), zero_add]

theorem evI_idem_mul (S : Finset (Pl F)) (t : AF F) : evI F (idem S * t) = evI F t := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (idem S * t)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F t)
  rw [map_mul (fstA F), fstA_idem, one_mul]

theorem mul_idem_eq_zero (S : Finset (Pl F)) (t : AF F) (h1 : evI F t = 0) (h2 : ∀ w ∈ S, evFin F w t = 0) :
    t * idem S = 0 := by
  classical
  have h3 : fstA F t = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact h1)
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun w => ?_)
  · change fstA F (t * idem S) = 0
    rw [map_mul, h3, zero_mul]
  · change evFin F w (t * idem S) = 0
    rw [map_mul, evFin_idem]
    split_ifs with hw
    · rw [h2 w hw, zero_mul]
    · rw [mul_zero]

theorem idem_mul_idem (S : Finset (Pl F)) : idem S * idem S = idem S := by
  classical
  have := mul_idem_eq_zero S (1 - idem S) (by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - idem S)) = 0
    rw [map_sub (fstA F), map_one, fstA_idem, sub_self, map_zero]) (fun w hw => by
    rw [map_sub, map_one, evFin_idem, if_pos hw, sub_self])
  rw [sub_mul, one_mul, sub_eq_zero] at this
  exact this.symm

open Classical in

theorem pure_split {κ : Type} [Fintype κ] (S : Finset (Pl F)) (f : SInf F κ) (φ ω : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hω : ∀ᶠ w in Filter.cofinite, ω w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    (hφ : ∀ w, w ∉ S → φ w = ω w) (x : κ → AF F) :
    pure f φ x = (fun z : κ → AF F => f (fun i => evI F (z i)) * ∏ w ∈ S, φ w fun i => evFin F w (z i)) (idem S • x) *
      (fun z : κ → AF F => ∏ᶠ w, if w ∈ S then (1 : ℂ) else ω w fun i => evFin F w (z i)) (x - idem S • x) := by
  have e1 : ∏ w ∈ S, φ w (fun i => evFin F w ((idem S • x) i)) =
      ∏ᶠ w, if w ∈ S then φ w (fun i => evFin F w (x i)) else 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun w hw => by
      by_contra h
      exact hw (if_neg h))]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [if_pos hw]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem, if_pos hw, one_mul]
  have e2 : (∏ᶠ w, if w ∈ S then (1 : ℂ) else ω w fun i => evFin F w ((x - idem S • x) i)) =
      ∏ᶠ w, if w ∈ S then (1 : ℂ) else ω w fun i => evFin F w (x i) := by
    refine finprod_congr fun w => ?_
    split_ifs with hw
    · rfl
    · congr 1
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, evFin_idem, if_neg hw, zero_mul, sub_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [e1, e2, mul_assoc, ← finprod_mul_distrib]
  · congr 1
    · simp only [Pi.smul_apply, smul_eq_mul, evI_idem_mul]
    · refine finprod_congr fun w => ?_
      split_ifs with hw
      · rw [mul_one]
      · rw [one_mul, hφ w hw]
  · exact S.finite_toSet.subset fun w hw => by
      by_contra h
      exact hw (if_neg h)
  · exact (GlobalTheory.PureFactor.mulSupport_finite ω hω x).subset fun w hw => by
      intro h
      apply hw
      beta_reduce at h ⊢
      rw [h, ite_self]

theorem scalar_of_coeff : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ i w, w ∉ S → φ' i w = G.M'.vac w) →
    (∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
            (∑ i, pure (f' i) (φ' i)) x * starRingEnd ℂ (G.M'.co.rho B.ψ u (∑ i, pure (f' i) (φ' i)) x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => pure f φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (pure f φ) x)) →
    ∃ c : ℂ, ∑ i, pure (f' i) (φ' i) = c • pure f φ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT S f φ hSB hvac m f' φ' hSB' hvac' h
  classical
  letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hF : IsTotallyReal F := hT.base.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hT.base.std
  have hω := hT.geo.hM'.std
  have hmem : ∀ (g : SInf F (Fin a' × Fin (a + a'))) (χ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, χ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → χ w = G.M'.vac w) →
      pure g χ ∈ schA F (Fin a' × Fin (a + a')) := fun g χ h1 h2 =>
    GlobalTheory.TensUniq.pure_mem_schA g χ h1 (by
      filter_upwards [hω, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [h2 v hvS, hv])
  obtain ⟨c1, b1, i1⟩ := schA_facts hF (hmem f φ hSB hvac)
  obtain ⟨c2, b2, i2⟩ := schA_facts hF
    (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) => hmem (f' i) (φ' i) (hSB' i) (hvac' i))
  refine proportional_of_coeff B.ψ hψ.1 hψ.2.1 (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 (idem S)
    (idem_mul_idem S)
    (fun z => f (fun i => evI F (z i)) * ∏ w ∈ S, φ w fun i => evFin F w (z i))
    (fun z => ∑ k, f' k (fun i => evI F (z i)) * ∏ w ∈ S, φ' k w fun i => evFin F w (z i))
    (fun z => ∏ᶠ w, if w ∈ S then (1 : ℂ) else G.M'.vac w fun i => evFin F w (z i)) _ _
    (pure_split S f φ G.M'.vac hω hvac) (fun x => ?_) c1 c2 b1 b2 i1 i2 fun x₁ y₁ hx hy μ hμ => ?_
  · rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => pure_split S (f' k) (φ' k) G.M'.vac hω (hvac' k) x
  · have := h (G.M'.co.e.symm (x₁, y₁)) (fun t h1 h2 => by
      rw [← hx, ← hy, ← Prod.smul_mk, ← map_smul, smul_smul, mul_idem_eq_zero S t h1 h2, zero_smul, map_zero]) μ hμ
    simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using this

end GlobalTheory.SplitSvN

end
