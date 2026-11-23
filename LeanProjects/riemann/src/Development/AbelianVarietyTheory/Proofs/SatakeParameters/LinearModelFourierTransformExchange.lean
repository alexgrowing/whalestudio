import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LinearModelFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flat (n r : ℕ) : Matrix (Fin n) (Fin r) k ≃ₜ (Fin n × Fin r → k) where
  toFun z p := z p.1 p.2
  invFun y := Matrix.of (Function.curry y)
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

def flatT (n r : ℕ) : Matrix (Fin r) (Fin n) k ≃ₜ (Fin n × Fin r → k) where
  toFun x p := x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun j => continuous_pi fun i => continuous_apply (i, j)

theorem trace_mul_eq_dotProduct {n r : ℕ} (x : Matrix (Fin r) (Fin n) k) (y : Matrix (Fin n) (Fin r) k) :
    trace (x * y) = flat n r y ⬝ᵥ flatT n r x := by
  simp only [trace, diag, mul_apply, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show x j i * y i j = y i j * x j i
  ring

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.SplitWeil.SB X) : (f ∘ e) ∈ GlobalTheory.SplitWeil.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

variable [MeasurableSpace k]

def fou (ψ : AddChar k Circle) (ν : Measure k) (n r : ℕ) (Φ : Matrix (Fin n) (Fin r) k → ℂ)
    (x : Matrix (Fin r) (Fin n) k) : ℂ :=
  ∫ y, Φ y * (ψ (trace (x * y)) : ℂ) ∂(volM ν (Fin n) (Fin r))

variable [BorelSpace k] {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure] {n r : ℕ}

theorem fou_eq_pi (Φ : Matrix (Fin n) (Fin r) k → ℂ) (x : Matrix (Fin r) (Fin n) k) :
    fou ψ ν n r Φ x = ∫ z, (Φ ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ flatT n r x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [fou, integral_volM_eq_pi]
  congr 1
  funext z
  rw [trace_mul_eq_dotProduct]
  rfl

theorem integrable_fou (hψ : Continuous ψ) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) (x : Matrix (Fin r) (Fin n) k) :
    Integrable (fun y => f y * (ψ (trace (x * y)) : ℂ)) (volM ν (Fin n) (Fin r)) := by
  haveI := secondCountable k
  letI : MeasurableSpace (Matrix (Fin n) (Fin r) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))
  haveI : (volM ν (Fin n) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : IsFiniteMeasureOnCompacts (volM ν (Fin n) (Fin r)) := inferInstance
  have hc : Continuous fun y : Matrix (Fin n) (Fin r) k => f y * (ψ (trace (x * y)) : ℂ) :=
    hf.1.continuous.mul (continuous_subtype_val.comp
      (hψ.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)))
  exact hc.integrable_of_hasCompactSupport (μ := volM ν (Fin n) (Fin r)) hf.2.mul_right

theorem fou_mem (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) : fou ψ ν n r f ∈ SB (Matrix (Fin r) (Fin n) k) := by
  haveI := secondCountable k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ h1
  have h2 := FourierPi.fourier_mem_SB (Measure.pi fun _ : Fin n × Fin r => ν) hc
    (comp_mem_SB (flat n r).symm hf)
  have h3 : fou ψ ν n r f = (fun y => ∫ z, (f ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∘ flatT n r := funext fun x => fou_eq_pi ν f x
  rw [h3]
  exact comp_mem_SB _ h2

theorem nabs_det_inv {m : ℕ} (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det g⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  simp [nabs, map_inv]

theorem fou_om (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ) :
    fou ψ ν n r (om μ hk gk Φ) = om μ⁻¹ gk hk (fou ψ ν n r Φ) := by
  funext x
  set F : Matrix (Fin n) (Fin r) k → ℂ :=
    fun z => Φ z * (ψ (trace (((hk⁻¹ : GL (Fin r) k).val * x * gk.val) * z)) : ℂ) with hF
  have key := integral_comp_mul_mul_volM ν hk gk⁻¹ F
  have htr : ∀ y : Matrix (Fin n) (Fin r) k,
      trace ((hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val)) =
        trace (x * y) := by
    intro y
    have e : (hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) =
        (hk⁻¹ : GL (Fin r) k).val * (x * y * hk.val) := by
      calc _ = (hk⁻¹ : GL (Fin r) k).val * (x * (gk.val * (gk⁻¹ : GL (Fin n) k).val) * y * hk.val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv, Matrix.mul_one]
    rw [e, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  set A : ℂ := (μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card (Fin r) : ℝ) / 2) : ℝ) : ℂ) with hA
  have lhs : fou ψ ν n r (om μ hk gk Φ) x =
      A * ∫ y, F ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) ∂(volM ν (Fin n) (Fin r)) := by
    rw [fou, ← integral_const_mul]
    congr 1
    funext y
    simp only [om, hF, htr, hA]
    ring
  have hFint : ∫ z, F z ∂(volM ν (Fin n) (Fin r)) =
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val) := rfl
  rw [lhs, key, hFint, nabs_det_inv]
  simp only [om, hA, MonoidHom.inv_apply, inv_inv, Complex.real_smul, Fintype.card_fin]
  set a := nabs k (Matrix.GeneralLinearGroup.det gk) with ha
  set b := nabs k (Matrix.GeneralLinearGroup.det hk) with hb
  have ha0 : 0 < a := nabs_pos' _
  have hb0 : 0 < b := nabs_pos' _
  have h1 : ((b ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((b ^ (-(n : ℝ)) : ℝ) : ℂ) = ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb0]
    ring_nf
  have h2 : ((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) = ((a ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le, neg_neg, ← Complex.ofReal_mul, ← Real.rpow_add ha0]
    ring_nf
  rw [Complex.ofReal_mul]
  linear_combination
    ((μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val)) *
    (((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) * h1 + ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * h2)

def fouL (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] SB (Matrix (Fin r) (Fin n) k) where
  toFun Φ := ⟨fou ψ ν n r Φ.1, fou_mem ν hψ h1 Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (Φ.1 + Ψ.1) x = fou ψ ν n r Φ.1 x + fou ψ ν n r Ψ.1 x
    simp only [fou, Pi.add_apply, add_mul]
    exact integral_add (integrable_fou ν hψ Φ.2 x) (integrable_fou ν hψ Ψ.2 x)
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (c • Φ.1) x = c * fou ψ ν n r Φ.1 x
    simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem fouL_surjective (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hν : IsSelfDual ψ ν) :
    Function.Surjective (fouL (n := n) (r := r) ν hψ h1) := by
  intro G
  obtain ⟨Φ₀, hΦ₀⟩ := (FourierSurj.hat_surjective k (Fin n × Fin r) ψ hψ h1 ν hν).2
    ⟨_, comp_mem_SB (flatT n r).symm G.2⟩
  refine ⟨⟨Φ₀.1 ∘ flat n r, comp_mem_SB _ Φ₀.2⟩, Subtype.ext (funext fun x => ?_)⟩
  show fou ψ ν n r (Φ₀.1 ∘ flat n r) x = G.1 x
  have h2 := congrFun hΦ₀ (flatT n r x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, Function.comp_apply, Homeomorph.symm_apply_apply] at h2
  rw [fou_eq_pi, ← h2]
  congr 1
  funext z
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, dotProduct_comm z]

end GlobalTheory.LinearModelFourier

theorem GlobalTheory.linearModel_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  intro k _ _ _ _ n r
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ, h1, -⟩ := (conductor_exists k).2.1
  obtain ⟨ν, hν⟩ := (selfDual_measure k ψ hψ h1).1
  haveI := hν.1
  refine ⟨GlobalTheory.LinearModelFourier.fouL ν hψ h1, GlobalTheory.LinearModelFourier.fouL_surjective ν hψ h1 hν,
    fun μ gk hk Φ Φ' hΦ => ?_⟩
  show GlobalTheory.LinearModelFourier.fou ψ ν n r Φ'.1 = om μ⁻¹ gk hk (GlobalTheory.LinearModelFourier.fou ψ ν n r Φ.1)
  rw [hΦ]
  exact GlobalTheory.LinearModelFourier.fou_om ν μ gk hk Φ.1
