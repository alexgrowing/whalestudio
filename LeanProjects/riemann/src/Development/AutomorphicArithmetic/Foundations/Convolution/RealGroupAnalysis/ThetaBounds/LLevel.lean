import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFinGLLeInvAbsDet
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Tube

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

private theorem tube {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
    (T : G → X → X) (hT : Continuous fun p : G × X => T p.1 p.2) (h1 : ∀ w, T 1 w = w)
    (hinv : ∀ k w, T k⁻¹ (T k w) = w) {g : X → ℂ} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∀ᶠ k in 𝓝 (1 : G), ∀ w, g (T k w) = g w :=
  _root_.UpperTheory.Reformulated.B.Qi19.tube T hT h1 hinv hg hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def eI (K : Type) [Field K] [NumberField K] : A K := (1, 0)

private theorem am_eI : am E (eI F) = eI E :=
  Prod.ext (map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)))
    (map_zero (AdeleBaseChange.finiteAdeleMap F E))

private theorem eI_fst (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).1 = x.1 :=
  one_mul x.1

private theorem eI_snd (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).2 = 0 :=
  zero_mul x.2

private theorem fin_fst (k : GL (Fin 2) (Af E)) (a b : Fin 2) :
    ((finGL E 2 k).val a b).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) a b).1 := by
  have := GlobalTheory.HenQ.finGL_apply k a b
  rw [this]
  simp [GlobalTheory.HenQ.sFin_fst]

private theorem eI_mul (x y : A E) (h : x.1 = y.1) : eI E * x = eI E * y :=
  Prod.ext (by rw [eI_fst, eI_fst, h]) (by rw [eI_snd, eI_snd])

private theorem eI_fin (k : GL (Fin 2) (Af E)) :
    eI E • (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  ext a b
  exact eI_mul _ _ (fin_fst k a b)

private theorem eI_star (D : Dat F E) (k : GL (Fin 2) (Af E)) :
    eI E • D.star2 (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  have hb : D.bar (eI E) = eI E := by rw [← am_eI (F := F), D.bar_am]
  have h1 := eI_fin k
  ext a b
  have h2 := congrFun (congrFun h1 b) a
  simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
  rw [D.conjTransposeGal_apply]
  have h3 := congrArg D.bar h2
  rw [map_mul, map_mul, hb] at h3
  rw [h3]
  have : D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) b a) = (1 : Matrix (Fin 2) (Fin 2) (A E)) a b := by
    by_cases hab : a = b
    · subst hab; simp
    · have hba : b ≠ a := fun h => hab h.symm
      simp [Matrix.one_apply, hab, hba]
  rw [this]

private theorem act_eI (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    D.act (finGL E 2 k) (eI F • v) = eI F • v := by
  apply D.herm_injective
  rw [D.herm_act, D.herm_smul, am_eI]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, eI_fin, Matrix.smul_mul, one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, eI_star, Matrix.mul_smul, mul_one]

private theorem act_fst (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) (i : Fin 4) :
    (D.act (finGL E 2 k) v i).1 = (v i).1 := by
  have h := congrFun (act_eI D k v) i
  rw [D.act_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have := congrArg Prod.fst h
  rwa [eI_fst, eI_fst] at this

private def io (w : Fin 4 → Af F) : V4 F := fun i => (0, w i)

private theorem continuous_io : Continuous (io (F := F)) :=
  continuous_pi fun i => continuous_const.prodMk (continuous_apply i)

private theorem finPart_io (w : Fin 4 → Af F) : finPartPi (io w) = w := rfl

private theorem split (v : V4 F) : v = eI F • v + io (finPartPi v) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (v i).1 = (eI F * v i).1 + 0
    rw [eI_fst, add_zero]
  · show (v i).2 = (eI F * v i).2 + (v i).2
    rw [eI_snd, zero_add]

private def TT (D : Dat F E) (k : GL (Fin 2) (Af E)) (w : Fin 4 → Af F) : Fin 4 → Af F :=
  finPartPi (D.act (finGL E 2 k) (io w))

private theorem finPart_act (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    finPartPi (D.act (finGL E 2 k) v) = TT D k (finPartPi v) := by
  conv_lhs => rw [split v]
  rw [D.act_add, act_eI]
  funext i
  show (eI F * v i).2 + _ = _
  rw [eI_snd, zero_add]
  rfl

end UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

end

open UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice in
theorem UpperTheory.ConvolutionTheory.R2.Ff.lLevel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), LLevel W := by
  intro F E _ _ _ _ _ _ _ D W φ
  obtain ⟨ρ, -, -, -, -, hfin⟩ := actCont F E D
  have hT : Continuous fun p : GL (Fin 2) (Af E) × (Fin 4 → Af F) => TT D p.1 p.2 :=
    continuous_finPartPi.comp (D.continuous_act' (hfin.comp continuous_fst) (continuous_io.comp continuous_snd))
  have h1 : ∀ w, TT D 1 w = w := fun w => by
    simp only [TT, map_one, D.act_one, finPart_io]
  have hinv : ∀ k w, TT D k⁻¹ (TT D k w) = w := fun k w => by
    have e := finPart_act D k⁻¹ (D.act (finGL E 2 k) (io w))
    rw [map_inv, D.act_inv_act, finPart_io] at e
    exact e.symm
  have key : ∀ f ∈ schwartzBruhatPi F (Fin 4), ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)),
      ∀ v, f (D.act (finGL E 2 k)⁻¹ v) = f v := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ₀, g, hg, rfl⟩ := hG
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
      have ht : Tendsto (fun k : GL (Fin 2) (Af E) => k⁻¹) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_inv (G := GL (Fin 2) (Af E))).tendsto 1
      filter_upwards [ht.eventually (tube (TT D) hT h1 hinv hlc hcs)] with k hk v
      have e1 : infPartPi (D.act (finGL E 2 k)⁻¹ v) = infPartPi v := by
        funext i
        simp only [infPartPi, ← map_inv, act_fst]
      have e2 : finPartPi (D.act (finGL E 2 k)⁻¹ v) = TT D k⁻¹ (finPartPi v) := by
        rw [← map_inv, finPart_act]
      simp only [schwartzBruhatTensorPi, e1, e2, hk]
    | zero => exact Eventually.of_forall fun _ _ => rfl
    | add G H _ _ hG hH =>
      filter_upwards [hG, hH] with k h h' v
      simp only [Pi.add_apply, h, h']
    | smul c G _ hG =>
      filter_upwards [hG] with k h v
      simp only [Pi.smul_apply, h]
  have hab : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), ab (nu F (finGL E 2 k)) = 1 := by
    have hU : (KLev E 2 1 : Set (GL (Fin 2) (Af E))) ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
      (isOpen_KLev le_rfl).mem_nhds (one_mem _)
    filter_upwards [hU] with k hk
    let f : GL (Fin 2) (Af E) →* {r : ℝ // 0 < r} :=
      (IdeleGroup.ideleModule F).comp ((ideleNorm F E).comp
        ((Matrix.GeneralLinearGroup.det).comp (finGL E 2)))
    have := GroundTheory.Automorphic.Reduction.eq_one_of_isCompact (isCompact_KLev le_rfl) f
      (continuous_ab.comp (continuous_nu.comp hfin)) hk
    exact congrArg Subtype.val this
  filter_upwards [key φ.1 φ.2, hab] with k h₁ h₂
  refine Subtype.ext (funext fun v => ?_)
  rw [W.L_apply, h₁, h₂]
  simp
