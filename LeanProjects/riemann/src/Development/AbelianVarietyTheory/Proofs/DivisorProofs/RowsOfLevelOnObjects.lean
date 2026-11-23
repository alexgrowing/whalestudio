import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedRowsIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRowsObj

open GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

variable {D : D7}

theorem not_isConjPl (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {PP PP' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : P.Div k PP) (h' : P.Div k' PP') : ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro hc
  obtain ⟨l, -, hl⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  have hle : ∀ {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.E)}, P.Div k Q → l.Mb ≤ Q.asIdeal := fun {k Q} hQ => by
    rw [hl]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    have e : Q.under (𝓞 D.host.K) = P.pb k := hQ
    rw [Ideal.map_le_iff_le_comap, ← e]
    exact le_rfl
  refine PP'.isPrime.ne_top (top_le_iff.1 (l.coprime.ge.trans (sup_le (hle h') ?_)))
  rw [Ideal.map_le_iff_le_comap]
  intro c hc0
  obtain ⟨c', h1, h2⟩ := hc c (hle h hc0)
  have e : (Formalism.L2.Pj.hostOfRecord D).bar c = c' :=
    RingOfIntegers.ext (((Formalism.L2.Pj.hostOfRecord D).bar_eq c).trans h2.symm)
  show (Formalism.L2.Pj.hostOfRecord D).bar c ∈ PP'.asIdeal
  rwa [e]

theorem liftsExist {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) : LiftsExist (Yc D 0) (L.βY 0) (L.dat0 L.triv) := by
  obtain ⟨c, hc⟩ := hL.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  obtain ⟨k', hk'⟩ := (hL.Pg PP').1 (h'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl _ hk hk'

section Mult

variable {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) :
    HasType V β (flag1L L) F := by
  intro κ hκ h
  have hl := GlobalTheory.FlagAction.isLift_one_of_mem hκ
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hl.2.2]; exact P.H.one_mem
  rw [hF κ ⟨hl.1, hl.2.1, hp⟩ h, GlobalTheory.FlagAction.levChi_flag1]
  congr 1
  unfold levChi
  rw [levFn_withP, extendOne_of_mem _ hp, show (⟨_, hp⟩ : P.H) = 1 from Subtype.ext hl.2.2, map_one, one_mul]

theorem mem_mult_withP_iff (hl : LiftsExist V β L) {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (P : LevelP L.Pg L.r ℂ) (U : MMap M) :
    U ∈ Mult θ M (levS V β (withP L P)) (levChi V β (withP L P)) ↔
      U ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) ∧
        ∀ p : P.H, postOn M (actL V β L p.1) U = ((P.chi p : ℂˣ) : ℂ) • U := by
  rw [GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, HasType V β (withP L P) (U v) := fun v κ hκ y => h.lev v κ hκ y
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ y => hasType_flag1 (hT v) κ hκ y, h.equiv, h.cont⟩, fun p => ?_⟩
    ext v y
    exact congrFun (GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (hT v) p (hl _)) y
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ y => ?_, h.equiv, h.cont⟩
    exact IsPLevel.hasType (V := V) (β := β) (L := L) (P := P)
      ⟨fun κ hκ y => h.lev v κ hκ y, fun p => congrArg (fun W : MMap M => W v) (hP p)⟩ κ hκ y

theorem gaL_actL (hl : LiftsExist V β L) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) {c : G → ℂ}
    (hc : ∀ g a, c (g * a * g⁻¹) = c a) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) (g : G) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  have hm : ∀ a b : G, actL V β L (eG a) (actL V β L (eG b) F) = actL V β L (eG (a * b)) F := fun a b => by
    rw [map_mul]
    exact (GlobalTheory.FlagAction.act_mul hF (hl _) (hl _)).symm
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun a => ?_).symm
  show _ = c (g * a * g⁻¹) • actL V β L (eG (g * a * g⁻¹ * g)) F
  rw [hc, inv_mul_cancel_right]

end Mult

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (σ : D.what₂.LL →+* ℂ) (g a : G) :
    RealDat.eC (A := A) σ (g * a * g⁻¹) = RealDat.eC (A := A) σ a := by
  have h := congrArg (fun x : MonoidAlgebra D.what₂.LL G => x.coeff (g * a)) (idemOf_central A.X hX (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    inv_mul_cancel_left] at h
  unfold RealDat.eC
  rw [h]

def rowAct (R : RealDat D A Ks) (g : G) : MMap (R.MY 0) →ₗ[ℂ] MMap (R.MY 0) :=
  postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g))

variable {R : RealDat D A Ks}

theorem hasType_of_mem {U : MMap (R.MY 0)} (hU : U ∈ R.EEat R.triv) (v : (R.MY 0).Vec) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) (U v) :=
  fun κ hκ y => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hU.1).lev v κ hκ y

theorem rowAct_mem (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    (g : G) {U : MMap (R.MY 0)} (hU : U ∈ R.EEat R.triv) : rowAct R g U ∈ R.EEat R.triv := by
  have h2 := ((mem_goodPart _ _ _ _ _ _).1 hU).2
  refine (mem_goodPart _ _ _ _ _ _).2 ⟨?_, fun v => ?_⟩
  · exact GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MY 0) hθ (R.βY 0) (R.dat0 R.triv) (R.eG g) U hU.1 _ fun _ => rfl
  · refine (gaL_actL (liftsExist hL) R.eG (eC_conj hX _) (hasType_of_mem hU v) g).trans ?_
    exact congrArg (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (h2 v)

def rowRep (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    : Representation ℂ G (R.EEat R.triv) where
  toFun g := (rowAct R g).restrict fun _ hU => rowAct_mem hL hθ hX g hU
  map_one' := by
    refine LinearMap.ext fun U => Subtype.ext (MultilinearMap.ext fun v => ?_)
    show actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) (U.1 v) = U.1 v
    rw [map_one]
    exact GlobalTheory.FlagAction.act_one (hasType_of_mem U.2 v)
  map_mul' g g' := by
    refine LinearMap.ext fun U => Subtype.ext (MultilinearMap.ext fun v => ?_)
    show actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * g')) (U.1 v) =
      actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g') (U.1 v))
    rw [map_mul]
    exact GlobalTheory.FlagAction.act_mul (hasType_of_mem U.2 v) (liftsExist hL _) (liftsExist hL _)

def withModel (R : RealDat D A Ks) (M : HMod (MMap (R.MY 0))) (ρ : Representation ℂ G M.H) (Θ : ∀ t, (R.HX t).H →ₗ[ℂ] M.H) :
    RealDat D A Ks :=
  { R with HE := M, gE := ρ, Th := Θ }

def modelEquiv {M : HMod (MMap (R.MY 0))} (hM : M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0)) : M.H ≃ₗ[ℂ] R.EEat R.triv :=
  (LinearEquiv.ofInjective M.e hM.1).trans (LinearEquiv.ofEq _ _ hM.2.1)

def modelRep (hL : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    {M : HMod (MMap (R.MY 0))} (hM : M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0)) :
    Representation ℂ G M.H :=
  (modelEquiv hM).symm.conjRingEquiv.toMonoidHom.comp (rowRep hL hθ hX)

theorem exists_model (hθ : IsInfFam R.θ) (hν : R.models_ν0)
    (hfin : FiniteDimensional ℂ (Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv))))
    (hS : SchurMult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0) :
    ∃ M : HMod (MMap (R.MY 0)), M.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D R.θ _ _ (R.MY 0) _ _ R.ν0 R.fd0 hθ hν.1.1 hν.2 hS
    (GlobalTheory.GardingVec.sm_ne_bot D _ _ _)
  exact GlobalTheory.HilbertModel.exists_hmod _ _ _ (Submodule.finiteDimensional_of_le (goodPart_le _ _ _ _ _))
    (fun x hx y hy z hz => h1 x hx.1 y hy.1 z hz.1) fun x hx => h2 x hx.1

end GlobalTheory.LevelRowsObj

end
