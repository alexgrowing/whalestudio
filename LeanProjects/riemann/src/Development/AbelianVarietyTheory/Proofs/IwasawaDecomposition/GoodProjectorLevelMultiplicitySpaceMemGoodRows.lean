import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KeepLevel

open GlobalTheory.Mem GlobalTheory.Mem.Th GlobalTheory.ChainEquiv

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank}

theorem levChi_withP (P : LevelP L.Pg L.r ℂ) (p : P.H) {κ : GA D V} (hκ : IsLevelLift V β L p κ) :
    levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]

theorem eigen_of_hasType {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ} (hf : HasType V β (withP L P) f) (p : P.H) {κ : GA D V}
    (hκ : IsLevelLift V β L p κ) (h : GA D V) : ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ) := by
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2.symm ▸ p.2
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [hf κ ⟨hκ.1, hκ.2.1, hp⟩ h, levChi_withP P p hκ]
  field_simp

theorem hasType_of_eigen {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ}
    (hf : ∀ (p : P.H) κ, IsLevelLift V β L p κ → ∀ h, ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ)) :
    HasType V β (withP L P) f := by
  intro κ hκ h
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2
  have hl : IsLevelLift V β L (⟨_, hp⟩ : P.H) κ := ⟨hκ.1, hκ.2.1, rfl⟩
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [levChi_withP P _ hl, mul_right_comm, hf _ κ hl h]
  field_simp

theorem mem_mult_of_level {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {X : MMap M} (hX : X ∈ Mult θ M J χ)
    (h : ∀ v, ∀ k ∈ J', ∀ g, X v (g * k) = χ' k * X v g) : X ∈ Mult θ M J' χ' :=
  have a := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ X).1 hX
  Submodule.subset_span ⟨a.aut, a.cusp, h, a.equiv, a.cont⟩

theorem hasType_of_comm (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {f : GA D V → ℂ}
    (h1 : HasType V β (flag1L L) f) (h2 : HasType V β (flag1L L) (e f)) (hf : HasType V β (withP L P) f)
    (hc : ∀ g, e (actL V β L g f) = actL V β L g (e f)) : HasType V β (withP L P) (e f) := by
  refine IsPLevel.hasType ⟨h2, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p
  have a : actL V β L p f = ((P.chi p : ℂˣ) : ℂ) • f := funext fun h =>
    (level_action_spec h1 ⟨κ, hκ⟩ κ hκ h).trans (eigen_of_hasType hf p hκ h).symm
  exact (hc p).symm.trans ((congrArg e a).trans (e.map_smul _ f))

end General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_lvlPart_iff (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) (U : R.CC t j) :
    U ∈ lvlPart R P t j ↔ ∀ p : P.H, Rel R t p j U (((P.chi p : ℂˣ) : ℂ) • U) := by
  constructor
  · intro hU p κ hκ v h
    have a : (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ∈ MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
      (levChi _ (R.βY j) (R.datYt t j P)) := (mem_multT R.θ (R.MY j) _ _ _).2 hU
    exact eigen_of_hasType (L := R.datYt t j R.triv) (P := P) (multT_value _ _ _ _ _ a v).2 p hκ h
  · intro hU
    refine mem_mult_of_level ((mem_multT R.θ (R.MY j) _ _ _).1 U.2) fun v => ?_
    exact hasType_of_eigen (L := R.datYt t j R.triv) (P := P) fun p κ hκ h => hU p κ hκ (PiTensorProduct.tprod ℂ v) h

theorem rel_ioY (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY)
    (hY' : R.models_νY') (hc : R.IsChain) (t : T) (g0 : G0 R.Pg D.R.r) (k : ℕ) (hn : k + 1 < D.R.m) (U U' : R.CC t (k + 1))
    (hU : Rel R t g0 (k + 1) U U') : Rel R t g0 k (R.ioY t k U) (R.ioY t k U') := by
  have hk : k < D.R.m := by omega
  intro κ hκ v g
  obtain ⟨κ', hκ'⟩ := lifts_chain R.toLevCh _ hl t (k + 1) hn g0
  exact step R.ψ R.θ hi _ _ (R.ωY t k) (hc.ωY t k hn) _ _ _ _ (R.vY t k) (hc.ptY t k hn) (R.MY k)
    (R.βY k) (R.datYt t k R.triv) rfl _ (meas_chain hY hY' t k hk).1 _ (meas_chain hY hY' t k hk).2
    (GlobalTheory.MultFinite.schurMult hD _ _)
    (R.ItY k) (hc.ItY t k hn).ne (R.CC t (k + 1)) (fun U w => (multT_value _ _ _ _ _ U.2 w).1)
    (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) _ (meas_chain hY hY' t (k + 1) hn).1 _ (meas_chain hY hY' t (k + 1) hn).2
    (R.ioY t k) (hc.ioY t k (by omega)) g0 κ hκ g0 κ' hκ' _
    (GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hl hi hc.ωY hc.vY t k hn g0 κ κ' hκ hκ') U U' (hU κ' hκ') v g

theorem ioY_mem (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY)
    (hY' : R.models_νY') (hc : R.IsChain) (P : LevelP R.Pg D.R.r ℂ) (t : T) (k : ℕ) (hn : k + 1 < D.R.m) (U : R.CC t (k + 1))
    (hU : U ∈ lvlPart R P t (k + 1)) : R.ioY t k U ∈ lvlPart R P t k :=
  (mem_lvlPart_iff P t k _).2 fun p =>
    (R.ioY t k).map_smul _ U ▸ rel_ioY hD hl hi hY hY' hc t p k hn U _ ((mem_lvlPart_iff P t (k + 1) U).1 hU p)

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hr : R.grp_record) (P : LevelP R.Pg D.R.r ℂ) (t : T)
    {X : MMap (R.MY 0)} (hX : X ∈ multAt R P t 0) : postOn (R.MY 0) R.e0 X ∈ R.EEat P := by
  have h0 := multAt_le R P t 0 hX
  rw [multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 X ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (GlobalTheory.ProjectedLift.eC_conv R hr) h0
  refine ⟨mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (X v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 h0).lev v
  refine hasType_of_comm (L := R.dat0 R.triv) (P := P) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 hX).lev v) fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact (GlobalTheory.ProjComm.proj_comm R hl hr).1 g _ a0

theorem topLift_mem (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hr : R.grp_red_R) (hM : R.IsModels) (hc : R.IsChain)
    (Q : Subgroup G) (ψ : Q →* D.what₂.LLˣ) (t : T) (f : (A.MtildeCSD t).Forms)
    (hf : f ∈ lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) Q ψ) :
    topLift R t (R.jX t f) ∈ lvlPart R (levPOf R.eG D.what₂.embLL Q ψ) t (D.R.m - 1) := by
  refine (mem_lvlPart_iff _ t _ _).2 fun p => ?_
  refine (GlobalTheory.FormAction.act_eq_translate R hr hM.jX t (R.eG.symm p) f).elim fun κ h => ?_
  have hκ : IsLevelLift D.sp.X' R.βX (R.datXt t) p.1 κ :=
    (congrArg (fun g => IsLevelLift D.sp.X' R.βX (R.datXt t) g κ) (R.eG.apply_symm_apply p.1)).mp h.1
  have a : Rel R t p (D.R.m - 1) (topLift R t (R.jX t f)) (topLift R t (R.jX t ((A.fam.R t).r (R.eG.symm p) f))) :=
    rel_ioX hl hM.inf hM.νY hM.νY' hc hM.νX hM.cX hM.HX (fun _ _ _ => GlobalTheory.MultFinite.schurMult hD _ _) t p κ hκ _ _ h.2
  have e : topLift R t (R.jX t ((A.fam.R t).r (R.eG.symm p) f)) =
      (((levPOf R.eG D.what₂.embLL Q ψ).chi p : ℂˣ) : ℂ) • topLift R t (R.jX t f) :=
    (congrArg (fun z => topLift R t (R.jX t z)) (hf ⟨R.eG.symm p, p.2⟩)).trans
      ((congrArg (topLift R t) ((R.jX t).map_smulₛₗ _ f)).trans ((topLift R t).map_smul _ _))
  exact (congrArg (Rel R t p (D.R.m - 1) (topLift R t (R.jX t f))) e).mp a

theorem keepsLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool), GlobalTheory.Published.CuspRapidDecay → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsChain → GlobalTheory.Mem.Th.KeepsLevel R F b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F b hD hl hg hM hc t
  exact ⟨fun U hU => goodProjector_levelMultiplicitySpace_mem_goodRows hl hM.inf hg.record _ t (ioY_mem hD hl hM.inf hM.νY hM.νY' hc _ t 0 D.R.two_le_m U hU),
    fun j _ hj U hU => ioY_mem hD hl hM.inf hM.νY hM.νY' hc _ t j hj U hU,
    fun f hf => topLift_mem hD hl hg.red_R hM hc _ _ t f hf⟩

theorem exists_multTie {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (hF : GlobalTheory.Published.HarishChandraFinite)
    (hD : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hg : R.IsGrp F) (hM : R.IsModels) (hc : R.IsChain)
    (hinj : Function.Injective tup) (Y : SideTie R F tup b S) :
    ∃ (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (Y' : SideTie R F tup b (withChain S c)),
      Y'.eE = Y.eE ∧ Y'.eA = Y.eA ∧ (∀ μ, (withChain S c).iota μ = S.iota μ) ∧ Nonempty (MultTie Y') :=
  GlobalTheory.Mem.Th.exists_multTie hF hD hM hc.Th (keepsLevel D G Pl0 T A Ks R F b hD hl hg hM hc) hinj Y

end GlobalTheory.KeepLevel

end
