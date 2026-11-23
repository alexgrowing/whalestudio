import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing in
theorem sq_ne (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ : (κ → AF F) → ℂ}
    (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) : ∫ u, Φ u * star (Φ u) ∂ν ≠ 0 := fun z => by
  obtain ⟨c, -, hc⟩ := lD_haar ν hν
  have e := hc Φ h Φ h
  have i := (sl_int (box_mem h h) 0).norm
  have ct := GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi h
  have : ∀ u, boxFun Φ (star Φ) (Sum.elim u u) = ((‖Φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by simp [boxFun, Complex.mul_conj']
  rw [z, mul_zero, lD_int (box_mem h h)] at e
  simp only [sl, add_zero, this, Complex.norm_real, norm_pow, norm_norm] at e i
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) i,
    Continuous.ae_eq_iff_eq _ (show Continuous fun x => ‖Φ x‖ ^ 2 from ct.norm.pow 2) continuous_zero] at e
  exact h0 (funext fun u => by simpa using congrFun e u)

theorem norm_eig {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) {g : G} {Φ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {c : ℂ} (hc : om g Φ = c • Φ) :
    ‖c‖ = 1 := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨a, a0, ha⟩ := lD_haar (F := F) (κ := κ) Measure.addHaar inferInstance
  have e := lD_unit hu hp g h h
  rw [hc, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, smul_smul, map_smul, smul_eq_mul,
    mul_eq_right₀ (ha Φ h Φ h ▸ mul_ne_zero (Complex.ofReal_ne_zero.2 a0.ne') (sq_ne _ inferInstance h h0)), Complex.star_def,
    Complex.mul_conj'] at e
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by exact_mod_cast e)

theorem schr_unit {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (ν : @Measure (κ → AF F) (borel _))
    (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) (w) (A C : (κ → AF F) → ℂ) :
    ∫ u, schr ψ w A u * star (schr ψ w C u) ∂ν = ∫ u, A u * star (C u) ∂ν := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  rw [← integral_add_right_eq_self (fun u => A u * star (C u)) w.1]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [schr, star_mul']
  rw [mul_mul_mul_comm, Complex.star_def, Complex.mul_conj', GlobalTheory.StdCharFromIsStd.norm_psi hψ]
  simp

open scoped Classical in
theorem ev_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => mul_comm _ _⟩

variable {f : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hS : ∀ v, φ v ∈ SB _)
  (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hS hs

theorem rest_ex (v : Pl F) : ∃ r, Rest (evFin F v) (φ v) r ∧ tens (evFin F v) (φ v) r = pure f φ := by
  classical
  obtain ⟨r, h1, h2⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
  have e := h2 (φ v)
  rw [Function.update_eq_self] at e
  exact ⟨r, ⟨h1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩, e⟩

theorem eig {v : Pl F} {S} {c : ℂ} (h : Acts (evFin F v) S (φ v) (c • φ v)) : S (pure f φ) = c • pure f φ := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  rw [← h2, h r h1]
  exact funext fun x => mul_assoc _ _ _

theorem fix_real {S} (h : Acts (evI F) S f f) : S (pure f φ) = pure f φ := by
  refine h (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩
  refine finprod_congr fun v => congrArg _ (funext fun i => ?_)
  have := congrArg (evFin F v) (congrFun (hz (idem F v) (evI_idem v)) i)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul, Pi.zero_apply, map_zero] at this
  rw [Pi.add_apply, map_add, this, add_zero]

theorem fix_box {v : Pl F} {S} (h : Acts (evFin F v) S (boxFun (φ v) (star (φ v))) (boxFun (φ v) (star (φ v)))) :
    S (boxFun (pure f φ) (star (pure f φ))) = boxFun (pure f φ) (star (pure f φ)) := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  have e : tens (evFin F v) (boxFun (φ v) (star (φ v))) (boxFun r (star r)) = boxFun (pure f φ) (star (pure f φ)) := by
    rw [← h2]
    funext x
    simp only [tens, boxFun, Pi.star_apply, star_mul', Function.comp_def]
    ring
  have m := GlobalTheory.TensUniq.pure_mem_schA f φ hS hs
  rw [← e]
  refine h _ ⟨fun x z hz => ?_, e ▸ box_mem m m⟩
  exact congrArg₂ (fun a b => a * star b) (h1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => congrArg (· ∘ Sum.inl) (hz u hu))
    (h1.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => congrArg (· ∘ Sum.inr) (hz u hu))

end GlobalTheory.ThK.Dbl.Bad

end
