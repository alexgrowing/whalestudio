import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijectionStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H →ₗ[ℂ] X) (hinj : Function.Injective ev) (φ : C →ₛₗ[σ] X)
    (h : ∀ f, φ f ∈ LinearMap.range ev) : EvEx σ ev φ := by
  choose x hx using h
  refine ⟨⟨⟨x, fun f f' => hinj ?_⟩, fun a f => hinj ?_⟩, hx⟩
  · rw [map_add, hx, hx, hx, map_add]
  · exact (hx _).trans (by rw [φ.map_smulₛₗ, map_smul, hx])

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

noncomputable def evLin {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]

set_option maxHeartbeats 1000000 in

theorem jEvExists (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) : JEvExists T R κ v₀ := by
  intro i σ hσ hV
  obtain ⟨hsh, -, w, hw⟩ := GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  obtain ⟨-, hχ, hfin, -⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV
  have hinj : Function.Injective (evLin R i σ (v₀ i σ)) :=
    GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW ht.hv₀ i σ hσ
  let ad := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))
  have key : holSub (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) ≤
      (LinearMap.range (evLin R i σ (v₀ i σ))).comap ad := by
    refine Submodule.span_le.2 fun P hP => ?_
    have h1 := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P fun k => (hP k).1
    have h2 := GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P hP
    have h3 : GlobalTheory.HolDict.HolForm R.θ (R.MW i σ) w (levS _ (R.βW i) (R.datWp i R.triv))
        (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (ad P) :=
      ⟨h1.aut, h1.bdd, fun k hk g => by rw [hχ k hk]; exact h1.lev k hk g, h1.hol⟩
    obtain ⟨Tm, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hsh hw (ht.hv₀ i σ).1
      (GlobalTheory.HolDict.exists_finPair GlobalTheory.Mem.VolFin.finVol D _) _ _ _ hfin h3 h2
    have hmem : Tm ∈ R.Wall i σ := Submodule.subset_span hT
    rw [← (hM.HW i σ).2.1] at hmem
    obtain ⟨x, rfl⟩ := hmem
    exact ⟨x, hTv⟩
  let φ : Cu T κ i →ₛₗ[res T σ] (GA D (Wc D i) → ℂ) :=
    ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • ad).comp
      ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
  have h := evEx_of_range (res T σ) _ hinj φ fun f =>
    Submodule.smul_mem _ _ (key (((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ))
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun f => (hj f).trans (phiC_eq T hV _ _).symm⟩

theorem jEvExists_and_jEvBar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp
  have h := jEvExists T R κ v₀ hL hM ht hp
  exact ⟨h, (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).2 h⟩

end GlobalTheory.CuspValues
