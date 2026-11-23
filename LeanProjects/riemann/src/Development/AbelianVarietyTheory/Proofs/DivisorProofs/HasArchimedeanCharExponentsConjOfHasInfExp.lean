import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU

theorem conj_div_norm_zpow (u : ℂ) (hu : u ≠ 0) (k : ℤ) :
    (starRingEnd ℂ u / ((‖starRingEnd ℂ u‖ : ℝ) : ℂ)) ^ (-k) = (u / ((‖u‖ : ℝ) : ℂ)) ^ k := by
  have h0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hu)
  rw [Complex.norm_conj, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [inv_div, div_eq_div_iff ((map_ne_zero _).2 hu) h0, Complex.mul_conj', sq]

theorem piInf_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (w : InfinitePlace D.host.F)
    (h : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) y = starRingEnd ℂ (θ τ (infPart D y)) := by
  have hr : ∀ a : Ainf D.host.F, InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.AutFunCompare.evW w a) =
      starRingEnd ℂ (θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    intro a
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap D.host.F) a (isClosed_eq ?_ ?_) fun f => ?_
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
    · exact Complex.continuous_conj.comp (hθ τ).2
    · rw [(GlobalTheory.AutFunCompare.evW w).commutes]
      have e1 := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm f)
      have e2 : θ τ (algebraMap D.host.F (Ainf D.host.F) f ⊗ₜ[D.host.F] (1 : D.host.E)) = tauE D τ (algebraMap D.host.F D.host.E f) := by
        rw [← (hθ τ).1, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
      rw [e2]
      refine e1.trans ?_
      exact (RingHom.congr_fun h f).symm
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb, map_add (starRingEnd ℂ)]
  | tmul a x =>
    have e : θ τ (fstA D.host.F a ⊗ₜ[D.host.F] x) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
      rw [← (hθ τ).1 x, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (a ⊗ₜ[D.host.F] x) =
        infEmb (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (evInf D.host.F w a ⊗ₜ[D.host.F] x) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, compInf, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    have l2 : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := by
      simp only [infPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rw [l1, l2, infEmb_tmul, e, map_mul, ← hr]
    rfl

end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

theorem finPart_eq_one {D : D7} (z : AE D) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (z - 1)) : finPart D z = 1 := by
  let u : AF D.host.F := ⟨0, 1⟩
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
    exact map_zero _
  have h1 := hz u hu0
  have key : ∀ y : AE D, finPart D (u • y) = finPart D y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | add a b ha hb => rw [smul_add, RingHom.map_add, RingHom.map_add, ha, hb]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      simp only [finPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, smul_eq_mul, map_mul]
      congr 1
      show (1 : Af D.host.F) * sndA D.host.F a = sndA D.host.F a
      exact one_mul _
  rw [← sub_eq_zero, ← RingHom.map_one (finPart D), ← RingHom.map_sub, ← key, h1, RingHom.map_zero]
end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in

theorem hasExp_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  intro D c a ha τf hτf
  choose n hn hθ using ha
  refine ⟨fun w => -n (τf w), ?_, fun w => by push_cast; rw [hn]; ring⟩
  intro z hz
  have hf : finPart D (z : AE D) = 1 := finPart_eq_one _ hz
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ0 : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ0 (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ0 ρ hρ r1 r0
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  let zx : D.what₂.Tau → ℂˣ := fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom z
  have hzx : ∀ τ, ((zx τ : ℂˣ) : ℂ) = θ τ (infPart D (z : AE D)) := fun τ => rfl
  have hT : z = T.toHomUnits zx :=
    Units.ext (ext _ _ (hf.trans (tf _).symm) fun τ => (ti zx τ).symm)
  have single : ∀ τ (v : ℂˣ), ((c (T.toHomUnits (Pi.mulSingle τ v)) : Circle) : ℂ) =
      ((v : ℂ) / ((‖(v : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro τ v
    have h := (hθ τ).2 θ hθ0 (T.toHomUnits (Pi.mulSingle τ v)) (tf _) fun τ' hτ' => by
      show θ τ' (infPart D (t _)) = 1
      rw [ti, Pi.mulSingle_eq_of_ne hτ', Units.val_one]
    rw [h]
    show ((θ τ (infPart D (t _))) / ((‖θ τ (infPart D (t _))‖ : ℝ) : ℂ)) ^ n τ = _
    rw [ti, Pi.mulSingle_eq_same]
  have hprod : ((c z : Circle) : ℂ) = ∏ τ, ((zx τ : ℂ) / ((‖(zx τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    have e1 : T.toHomUnits zx = ∏ τ, T.toHomUnits (Pi.mulSingle τ (zx τ)) := by
      rw [← map_prod]; congr 1; exact (Finset.univ_prod_mulSingle zx).symm
    have e2 : ((c z : Circle) : ℂ) = Circle.coeHom (∏ τ, c (T.toHomUnits (Pi.mulSingle τ (zx τ)))) := by
      rw [← map_prod, ← e1, ← hT]; rfl
    rw [e2, map_prod]
    exact Finset.prod_congr rfl fun τ _ => single τ (zx τ)
  have hinj : Function.Injective τf := fun w1 w2 h => by
    have e : w1.embedding = w2.embedding := by rw [← hτf w1, ← hτf w2, h]
    rw [← InfinitePlace.mk_embedding w1, ← InfinitePlace.mk_embedding w2, e]
  have hbij : Function.Bijective τf := (Fintype.bijective_iff_injective_and_card τf).2
    ⟨hinj, (Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D)).symm⟩
  rw [hprod]
  symm
  refine Fintype.prod_bijective τf hbij _ _ fun w => ?_
  beta_reduce
  rw [piInf_eq θ hθ0 (τf w) w (hτf w), ← hzx]
  exact conj_div_norm_zpow _ (zx (τf w)).ne_zero _

end GlobalTheory.ConjInfExp
