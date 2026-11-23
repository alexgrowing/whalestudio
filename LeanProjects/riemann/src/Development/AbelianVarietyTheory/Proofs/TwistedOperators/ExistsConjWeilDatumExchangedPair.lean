import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.WeilConj

variable {D : D7}

theorem dag_dag {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ T S) (f : WO T S → ℂ) :
    dag S T (dag T S f) = f := by
  funext y
  simp only [dag, Complex.conj_conj, h.invol y]

theorem dag_add (S T : HSp D) (f f' : WO S T → ℂ) : dag S T (f + f') = dag S T f + dag S T f' := by
  funext y; simp [dag]

theorem dag_smul (S T : HSp D) (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext y; simp [dag]

def conjE (S T : HSp D) (A : Module.End ℂ (WO S T → ℂ)) : Module.End ℂ (WO T S → ℂ) where
  toFun f := dag S T (A (dag T S f))
  map_add' f f' := by simp only [dag_add, map_add]
  map_smul' c f := by simp only [dag_smul, map_smul, Complex.conj_conj, RingHom.id_apply]

def conjRep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) (ω : WRep S T) :
    WRep T S where
  toFun p := conjE S T (ω (p.2, p.1))
  map_one' := by
    apply LinearMap.ext; intro f
    show dag S T (ω 1 (dag T S f)) = f
    rw [map_one, Module.End.one_apply, dag_dag hTS]
  map_mul' p q := by
    apply LinearMap.ext; intro f
    show dag S T (ω ((p * q).2, (p * q).1) (dag T S f)) = dag S T (ω (p.2, p.1) (dag T S (dag S T (ω (q.2, q.1) (dag T S f)))))
    rw [dag_dag hST]
    have : ((p * q).2, (p * q).1) = (p.2, p.1) * (q.2, q.1) := rfl
    rw [this, map_mul, Module.End.mul_apply]

theorem conjRep_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (ω : WRep S T) (h : GA D T) (g : GA D S) (f : WO T S → ℂ) :
    conjRep hST hTS ω (h, g) f = dag S T (ω (g, h) (dag T S f)) := rfl

theorem adjO_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ S T) : adjO S T 0 = 0 := by
  have := h.add 0 0
  rw [add_zero] at this
  simpa using this

theorem unit_transport {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (μ : Measure (WO T S)) (𝓕 : Set (WO T S)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL S T) 𝓕 μ) :
    ∃ (μ' : Measure (WO S T)) (𝓕' : Set (WO S T)), μ'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕' μ' ∧
      ∀ G : WO S T → ENNReal, ∫⁻ w in 𝓕, G (adjO S T w) ∂μ = ∫⁻ v in 𝓕', G v ∂μ' := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (WO T S) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, hHaar, hF, fun G => ?_⟩
  symm
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  rfl

theorem enorm_dag (S T : HSp D) (f : WO S T → ℂ) (y : WO T S) : ‖dag S T f y‖ₑ = ‖f (adjO S T y)‖ₑ := by
  simp only [dag]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hε, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]

theorem suppAt_cA {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem exists_detAt_cA {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : ∃ x' : (AE D)ˣ, IsDetAt (cA D e) V g x' ∧
      ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → χ x' = χ x := by
  have hi : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
  refine ⟨GlobalTheory.SplitDetCharacter.cutDet (cA D e) hi V g, ?_, fun χ n hχ => ?_⟩
  · show _ = _
    rw [GlobalTheory.SplitDetCharacter.cutDet_val]; ring
  · refine GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hχ _ _ ?_
    rw [GlobalTheory.SplitDetCharacter.cutDet_val, hx, map_add, map_mul, map_sub, map_one]
    have hd := GlobalTheory.SplitDetCharacter.det_mul_conj V g
    linear_combination (1 - cA D (Formalism.L2.Theta.mt V g).det + (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det
      - (Formalism.L2.Theta.mt V g).det) * hi + cA D e * hd

theorem exists_conj_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  intro D ψ S T χS χT ω H
  have hST : AdjLaw ψ S T := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std S T
  have hTS : AdjLaw ψ T S := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std T S
  refine ⟨conjRep hST hTS ω, ?_, fun g h f => by rw [conjRep_apply, dag_dag hST]⟩
  refine
    { std := H.std
      hecS := H.hecT
      hecT := H.hecS
      resS := H.resT
      resT := H.resS
      om_pres := fun p f hf => hST.theta _ (H.om_pres _ _ (hTS.theta f hf))
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro h g w₀ f hf
    rw [conjRep_apply, conjRep_apply]
    have e1 := hTS.Heisenberg₂ (adjO S T w₀) f
    rw [hTS.invol] at e1
    rw [← e1, H.om_heis g h (adjO S T w₀) _ (hTS.theta f hf), ← hST.act, hST.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [conjRep_apply]
    simp only [dag]
    rw [adjO_zero hST, H.om_aut γ' hγ' γ hγ _ (hTS.theta f hf)]
    simp only [dag]
    rw [adjO_zero hTS, Complex.conj_conj]
  · intro f hf w
    exact Complex.continuous_conj.comp ((H.om_cont _ (hTS.theta f hf) (adjO S T w)).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨μ', 𝓕', hμ', h𝓕', hG⟩ := unit_transport hST hTS μ 𝓕 hμ h𝓕
    have e1 : ∀ w, ‖conjRep hST hTS ω p f w‖ₑ ^ 2 = (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show ‖dag S T (ω (p.2, p.1) (dag T S f)) w‖ₑ ^ 2 = _
      rw [enorm_dag]
    have e2 : ∀ w, ‖f w‖ₑ ^ 2 = (fun v => ‖dag T S f v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show _ = ‖dag T S f (adjO S T w)‖ₑ ^ 2
      rw [enorm_dag, hTS.invol]
    simp only [e1, e2]
    exact (hG (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2)).trans
      ((H.om_unit μ' 𝓕' hμ' h𝓕' _ _ (hTS.theta f hf)).trans (hG (fun v => ‖dag T S f v‖ₑ ^ 2)).symm)
  · intro e he h g hTh hSg y x hy hx
    obtain ⟨x', hx', hxx⟩ := exists_detAt_cA he hx
    obtain ⟨y', hy', hyy⟩ := exists_detAt_cA he hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split (cA D e) (isSplitIdem_cA he) g h (suppAt_cA hSg) (suppAt_cA hTh) x' y' hx' hy'
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    let ℓω : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun F F' => by simp only [dag_add, map_add]
        map_smul' := fun c F => by simp only [dag_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
    have hinvω : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓω (heisO ψ S T u F) = ℓω F := by
      intro u hu F hF
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      have e1 := hST.Heisenberg₂ (adjO T S u) F
      rw [hST.invol] at e1
      have hh : IsHalf (cA D (cA D (cA D e))) (adjO T S u) := hTS.half _ u hu
      rw [GlobalTheory.DualPairCheck.cA_cA] at hh
      rw [← e1, hinv _ hh _ (hST.theta F hF)]
    have key := hℓ ℓω hinvω (dag T S f) (hTS.theta f hf)
    have k1 : ℓω (ω (g, h) (dag T S f)) = starRingEnd ℂ (ℓ (conjRep hST hTS ω (h, g) f)) := rfl
    have k2 : ℓω (dag T S f) = starRingEnd ℂ (ℓ f) := by
      show starRingEnd ℂ (ℓ (dag S T (dag T S f))) = _
      rw [dag_dag hTS]
    rw [k1, k2] at key
    have hsf : (starRingEnd ℂ) ((splitFacO χS χT x' y' : Circle) : ℂ) = ((splitFacO χT χS y x : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj]
      congr 1
      unfold splitFacO
      rw [hxx χT _ H.resT, hyy χS _ H.resS, _root_.mul_inv_rev, inv_inv]
    have key' := congrArg (starRingEnd ℂ) key
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hsf] at key'
    exact key'

end GlobalTheory.WeilConj
