import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrForm

variable {F : Type} [Field F] [NumberField F]

theorem exists_weighted_clm {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace D] [BorelSpace D]
    [SecondCountableTopology D] (μ : Measure D) [hμ : μ.HasTemperateGrowth] (ph : D → ℂ)
    (hph : AEStronglyMeasurable ph μ) (hb : ∀ y, ‖ph y‖ ≤ 1) :
    ∃ Λ : SchwartzMap D ℂ →L[ℂ] ℂ, ∀ h : SchwartzMap D ℂ, Λ h = ∫ y, ph y * h y ∂μ := by
  have hint : ∀ h : SchwartzMap D ℂ, Integrable (fun y => ph y * h y) μ := fun h =>
    h.integrable.bdd_mul hph (Eventually.of_forall hb)
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun h => ∫ y, ph y * h y ∂μ) (fun h h' => ?_)
    (fun a h => ?_) ?_, fun h => rfl⟩
  · simp only [SchwartzMap.add_apply, mul_add]; exact integral_add (hint h) (hint h')
  · simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]; congr 1; funext y; ring
  · rcases hμ.exists_integrable with ⟨n, hn⟩
    let m := (n, 0)
    refine ⟨Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : ℝ)) ∂μ, by positivity, fun f => ?_⟩
    refine (norm_integral_le_integral_norm _).trans ?_
    have h' : ∀ x, ‖ph x * f x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
        (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) f)) := by
      intro x
      refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hb x)).trans ?_)
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity), Real.rpow_natCast]
      simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := m) (k := n) (n := 0) le_rfl le_rfl f x
    refine (integral_mono (hint f).norm (hn.mul_const _) h').trans (le_of_eq ?_)
    unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]

variable (F) in

def iotaI : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (algebraMap F (InfiniteAdeleRing F))

def linI {r : ℕ} {κ : Type} [Fintype κ] (c : Fin r → κ → mixedEmbedding.mixedSpace F) :
    (Fin r → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y k := ∑ j, y j * c j k
  map_add' y y' := by funext k; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a y := by funext k; simp [Finset.smul_sum, smul_mul_assoc]

def linP {r : ℕ} {κ : Type} [Fintype κ] (a : Fin r → κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin r → mixedEmbedding.mixedSpace F) where
  toFun v i := ∑ k, a i k * v k
  map_add' y y' := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by funext k; simp [Finset.smul_sum, mul_smul_comm]

theorem exists_leftInv {r : ℕ} {κ : Type} [Fintype κ] (w : Fin r → κ → F) (hw : LinearIndependent F w) :
    ∃ A : Matrix (Fin r) κ F, ∀ i j, ∑ k, A i k * w j k = if i = j then 1 else 0 := by
  let V : (Fin r → F) →ₗ[F] (κ → F) :=
    { toFun := fun c => ∑ j, c j • w j
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hker : LinearMap.ker V = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    exact Fintype.linearIndependent_iff.1 hw c hc i
  obtain ⟨Q, hQ⟩ := V.exists_leftInverse_of_injective hker
  refine ⟨LinearMap.toMatrix' Q, fun i j => ?_⟩
  have h1 : Q (w j) = Pi.single j 1 := by
    have := congrArg (fun φ => φ (Pi.single j 1)) hQ
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← this]
    congr 1
    simp [V, Pi.single_apply, ite_smul]
  have h2 := congrFun (LinearMap.toMatrix'_mulVec Q (w j)) i
  rw [h1] at h2
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using h2

end GlobalTheory.LagrForm

noncomputable section
namespace GlobalTheory.LagrForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ}

def Xv (u : Fin r → (κ → F) × (κ → F)) (x : Fin r → AF F) : (κ → AF F) × (κ → AF F) :=
  ∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))

def sc (u : Fin r → (κ → F) × (κ → F)) (x : Fin r → AF F) : AF F :=
  ⅟(2 : AF F) * ((Xv u x).1 ⬝ᵥ (Xv u x).2)

variable (F) in

def fstH : AF F →+* InfiniteAdeleRing F := RingHom.fst _ _

variable (F) in

def sndH : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

theorem fstH_apply (a : AF F) : fstH F a = a.1 := rfl
theorem sndH_apply (a : AF F) : sndH F a = a.2 := rfl

theorem Xv_fst_fst (u : Fin r → (κ → F) × (κ → F)) (x : Fin r → AF F) (k : κ) :
    ((Xv u x).1 k).1 = ∑ j, (x j).1 * algebraMap F (InfiniteAdeleRing F) ((u j).1 k) := by
  simp only [Xv, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← fstH_apply, map_sum]; simp only [map_mul, fstH_apply]; rfl

theorem Xv_fst_snd (u : Fin r → (κ → F) × (κ → F)) (x : Fin r → AF F) (k : κ) :
    ((Xv u x).1 k).2 = ∑ j, (x j).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((u j).1 k) := by
  simp only [Xv, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← sndH_apply, map_sum]; simp only [map_mul, sndH_apply]; rfl

theorem sc_fst_congr (u : Fin r → (κ → F) × (κ → F)) (x x' : Fin r → AF F) (h : ∀ j, (x j).1 = (x' j).1) :
    (sc u x).1 = (sc u x').1 := by
  simp only [sc, Xv, dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← fstH_apply, ← fstH_apply]; simp only [map_mul, map_sum, fstH_apply, h]

theorem sc_snd_congr (u : Fin r → (κ → F) × (κ → F)) (x x' : Fin r → AF F) (h : ∀ j, (x j).2 = (x' j).2) :
    (sc u x).2 = (sc u x').2 := by
  simp only [sc, Xv, dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← sndH_apply, ← sndH_apply]; simp only [map_mul, map_sum, sndH_apply, h]

theorem continuous_sc (u : Fin r → (κ → F) × (κ → F)) : Continuous (sc u) := by
  unfold sc Xv
  fun_prop

end GlobalTheory.LagrForm

noncomputable section
namespace GlobalTheory.LagrForm

open GlobalTheory.WeilAdm.HaarSplit in

theorem lagr_form_admitted : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (pureA F (⇑f) g) 0 ∂μ = T f := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ g hg
  letI mA : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := volume_isAddHaar F (Fin r)
  haveI : BorelSpace (Fin r → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (Fin r → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (Fin r → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (Fin r → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (Fin r → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : MeasurableAdd (Fin r → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (Fin r → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI := Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin r → mixedEmbedding.mixedSpace F)) ν
  haveI hρ : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F (Fin r))) :=
    (splitE F (Fin r)).isAddHaarMeasure_map _ (continuous_splitE F (Fin r)) (continuous_splitE_symm F (Fin r))
  let em : ((Fin r → mixedEmbedding.mixedSpace F) × (Fin r → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (Fin r → AF F) :=
    (Homeomorph.mk (splitE F (Fin r)).toEquiv (continuous_splitE F (Fin r))
      (continuous_splitE_symm F (Fin r))).toMeasurableEquiv
  haveI : (volume : Measure (Fin r → mixedEmbedding.mixedSpace F)).HasTemperateGrowth :=
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth

  obtain ⟨A, hA⟩ := exists_leftInv (fun j => (u j).1) hu
  let c : Fin r → κ → mixedEmbedding.mixedSpace F := fun j k => iotaI F ((u j).1 k)
  let a : Fin r → κ → mixedEmbedding.mixedSpace F := fun i k => iotaI F (A i k)
  let L := LinearMap.toContinuousLinearMap (linI c)
  let P := LinearMap.toContinuousLinearMap (linP a)
  have hPL : ∀ y, P (L y) = y := by
    intro y
    funext i
    show ∑ k, a i k * (∑ j, y j * c j k) = y i
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ k, a i k * (y j * c j k) = y j * iotaI F (∑ k, A i k * (u j).1 k) := by
      intro j
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, a, c]
      ring
    simp only [h1, hA]
    simp [apply_ite (iotaI F)]
  have hup : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖L y‖) ^ k := by
    refine ⟨1, ‖P‖, fun y => ?_⟩
    calc ‖y‖ = ‖P (L y)‖ := by rw [hPL]
      _ ≤ ‖P‖ * ‖L y‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (1 + ‖L y‖) ^ 1 := by
        rw [pow_one]; gcongr; linarith
  let Cm := SchwartzMap.compCLM ℂ (F := ℂ) (g := ⇑L) L.hasTemperateGrowth hup

  let ph : (Fin r → mixedEmbedding.mixedSpace F) → ℂ := fun y => ψ (pairA F (sc u (splitE F (Fin r) (y, 0))).1 0)
  have hphc : Continuous ph := by
    refine hψ.1.comp ?_
    have h0 : Continuous fun y : Fin r → mixedEmbedding.mixedSpace F => (sc u (splitE F (Fin r) (y, 0))).1 :=
      continuous_fst.comp ((continuous_sc u).comp ((continuous_splitE F (Fin r)).comp (continuous_id.prodMk continuous_const)))
    exact h0.prodMk continuous_const
  obtain ⟨Λ, hΛ⟩ := exists_weighted_clm volume ph hphc.aestronglyMeasurable (fun y => (GlobalTheory.StdCharFromIsStd.norm_psi hψ _).le)

  let B : (Fin r → FiniteAdeleRing (𝓞 F) F) → ℂ := fun z =>
    ψ (pairA F 0 (sc u (splitE F (Fin r) (0, z))).2) * g (fun k => ((Xv u (splitE F (Fin r) (0, z))).1 k).2)
  set ρ := (volume.prod ν).map (splitE F (Fin r)) with hρdef
  set s := Measure.addHaarScalarFactor μ ρ with hs
  refine ⟨(((s : ℝ) : ℂ) * ∫ z, B z ∂ν) • Λ.comp Cm, fun f => ?_⟩
  change ∫ x, schr ψ (Xv u x) (pureA F (⇑f) g) 0 ∂μ = _
  have hsplit : ∀ y z, schr ψ (Xv u (splitE F (Fin r) (y, z))) (pureA F (⇑f) g) 0 = (ph y * f (L y)) * B z := by
    intro y z
    have h1 : ψ (sc u (splitE F (Fin r) (y, z))) = ψ (pairA F (sc u (splitE F (Fin r) (y, z))).1 0) *
        ψ (pairA F 0 (sc u (splitE F (Fin r) (y, z))).2) := by
      conv_lhs => rw [GlobalTheory.StdCharFromIsStd.pairA_split (sc u (splitE F (Fin r) (y, z)))]
      exact AddChar.map_add_eq_mul ψ _ _
    have h2 : (sc u (splitE F (Fin r) (y, z))).1 = (sc u (splitE F (Fin r) (y, 0))).1 := sc_fst_congr u _ _ (fun j => rfl)
    have h3 : (sc u (splitE F (Fin r) (y, z))).2 = (sc u (splitE F (Fin r) (0, z))).2 := sc_snd_congr u _ _ (fun j => rfl)
    have h4 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Xv u (splitE F (Fin r) (y, z))).1 k).1) = L y := by
      funext k
      rw [Xv_fst_fst]
      show _ = ∑ j, y j * c j k
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      simp only [splitE_apply, RingEquiv.apply_symm_apply, c]
      rfl
    have h5 : (fun k => ((Xv u (splitE F (Fin r) (y, z))).1 k).2) = (fun k => ((Xv u (splitE F (Fin r) (0, z))).1 k).2) := by
      funext k; rw [Xv_fst_snd, Xv_fst_snd]; rfl
    simp only [schr, zero_dotProduct, zero_add, pureA]
    change ψ (sc u (splitE F (Fin r) (y, z))) * (f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Xv u (splitE F (Fin r) (y, z))).1 i).1) *
      g (fun i => ((Xv u (splitE F (Fin r) (y, z))).1 i).2)) = _
    rw [h1, h2, h3, h4, h5]
    simp only [ph, B]
    ring
  rw [Measure.isAddLeftInvariant_eq_smul μ ρ, integral_smul_nnreal_measure]
  have hmap : ρ = (volume.prod ν).map em := rfl
  have hint : ∫ x, schr ψ (Xv u x) (pureA F (⇑f) g) 0 ∂ρ = ∫ p, schr ψ (Xv u (em p)) (pureA F (⇑f) g) 0 ∂(volume.prod ν) := by
    rw [hmap, integral_map_equiv em]
  rw [hint]
  have hI : (fun p => schr ψ (Xv u (em p)) (pureA F (⇑f) g) 0) = fun p => (ph p.1 * f (L p.1)) * B p.2 := by
    funext p
    exact hsplit p.1 p.2
  rw [hI, integral_prod_mul (fun y => ph y * f (L y)) B]
  try rw [← hs]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hΛ]
  have hC : ∀ y, (Cm f) y = f (L y) := fun y => rfl
  simp only [hC]
  rw [NNReal.smul_def, Complex.real_smul, smul_eq_mul]
  ring

end GlobalTheory.LagrForm
