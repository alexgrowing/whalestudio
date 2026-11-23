import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerNormOneFiniteAdeleDetClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesReferenceTupleEqEmptyStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mem_integralNormOne_of_normOneDetClass_eq_one (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (h : u1Dt H SQ x = 1) :
    x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H) := by
  obtain ⟨a, ha⟩ := exists_lift H x
  have e : (QuotientGroup.mk a : DtQ H SQ) = 1 := (normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha).symm.trans h
  have ha' : a ∈ KDq H SQ := (QuotientGroup.eq_one_iff a).1 e
  refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).2 fun w => ?_
  exact (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).1 (Subgroup.mem_sup_left (KDq_le_KD H SQ ha')) w (conjPrime₂ w)
    ((isConjPl_iff H w _).2 rfl)

theorem unitIdeleImage_eq_map_integralNormOne : UOQ H SQ = ((Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)).subgroupOf (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))).map (u1Dt H SQ) := by
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_of_idele H a
    refine ⟨x, ?_, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩
    refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a hx).2 fun w => ?_
    exact (ha w).trans (ha (conjPrime₂ w)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_lift H x
    rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, mk_mem_UOQ, KDq_sup_unitIdl]
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).2 fun w w' hw => ?_
    rw [(isConjPl_iff H w w').1 hw]
    exact (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).1 hx w

end Gen

section Main

open Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem detPt_of_reads (hI : I.Ok) (u : B.Word) (i : ℕ) {Ch : Type} {chOf : (I.stp u I.mu0 i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u I.mu0 i chOf Lb U chi y st k) (c : (I.stp u I.mu0 i).Cl)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det (y c)) :
    detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1 = u1Dt B.host I.SQ x := by
  obtain ⟨p, hp, hN⟩ := hR.k_std (chOf c)
  refine GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level B.R B.host _ _ _ _ I.SQ _ (y c) (k (chOf c)) x (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni
    (hN ▸ hp.lat) (fun P hP => ?_) hx
  refine hR.k_off _ _ (GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes B X I hI u P hP) ?_ (Or.inl rfl)
  rintro ⟨Q, hQ, -⟩
  rw [GlobalTheory.T.q_mu0_eq_empty B X I] at hQ
  exact absurd hQ (Finset.notMem_empty Q)

theorem det_reGL {a b : ℕ} (h : a = b) {A : Type} [CommRing A] (g : GL (Fin a) A) :
    Matrix.GeneralLinearGroup.det (reGL h A g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  refine Units.ext ?_
  simp [reGL, Matrix.GeneralLinearGroup.det]

variable (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : ColsTiedSym (I.rec7 l Z))

include I in

theorem det_normOne_classStepZero_trueColumns (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (c : ((I.rec7 l Z).mem u).C.cls 0)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det ((C.herm.base.lev0 u).y c).1) :
    (I.rec7 l Z).detCls u 0 c = u1Dt B.host I.SQ x := by
  obtain ⟨k, hk⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  refine detPt_of_reads I hI u 0 hk c x ?_
  have e := (C.car0 u).y_eq c
  rw [hx]
  exact (e ▸ det_reGL _ _).symm

include I in

theorem detI_std (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ B.R.m)
    (c : ((I.rec7 l Z).mem u).C.cls i) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det
      ((C.herm.base.cls u i h1 hm (C.herm.base.chOf u i c)).y ⟨c, rfl⟩).1) :
    (I.rec7 l Z).detCls u i c = u1Dt B.host I.SQ x := by
  by_cases h2 : i + 1 ≤ B.R.m
  · obtain ⟨k, hk⟩ := (hS u).mid i h1 h2
    refine detPt_of_reads I hI u i hk c x ?_
    have e := (C.carC u i h1 h2 (C.herm.base.chOf u i c)).y_eq ⟨c, rfl⟩
    rw [hx]
    exact (e ▸ det_reGL _ _).symm
  · obtain rfl : i = B.R.m := by omega
    obtain ⟨k, hk⟩ := (hS u).ends B.R.m le_rfl (Or.inr rfl)
    refine detPt_of_reads I hI u _ hk c x ?_
    have e := (C.carM u).y_eq c
    have key : ∀ (β : C.herm.base.Ch u B.R.m) (hb : C.herm.base.chOf u B.R.m c = β),
        Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm β).y ⟨c, hb⟩).1 =
          Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm (C.herm.base.chOf u B.R.m c)).y ⟨c, rfl⟩).1 := by
      rintro _ rfl
      rfl
    rw [hx, ← key _ (chOf_m C.herm.base u c)]
    exact (e ▸ det_reGL _ _).symm

def hermS (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricHermitianColumns (I.rec7 l Z) :=
  { C.herm.base with
    dt := u1Dt B.host I.SQ
    dt_surj := normOneFiniteAdeleDetClass_surjective B.host I.SQ
    dt_ker := mem_integralNormOne_of_normOneDetClass_eq_one B.host I.SQ
    dt_open := GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass B.R B.host _ I.SQ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1
    dt_UO := unitIdeleImage_eq_map_integralNormOne B.host I.SQ
    dt_rat := fun z x h => GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class B.R B.host I.SQ z x h
    det0 := fun u c x h => det_normOne_classStepZero_trueColumns I l Z C hI hS u c x h
    detI := fun u i h1 hm c x h => detI_std I l Z C hI hS u i h1 hm c x h }

theorem relDet_std (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricRelativeDeterminant (I.rec7 l Z) (hermS I l Z C hI hS) := by
  intro N L L' g _ hg x hx
  obtain ⟨idl, hp⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by ext t; exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩) (fun _ => rfl)
    (fun N L L' t h => h)
  exact GlobalTheory.Mem.NormOneIdeal.relDet_eq_of_pinned (I.rec7 l Z) idl hp _ (hermS I l Z C hI hS).dt (hermS I l Z C hI hS).dt_ker
    (hermS I l Z C hI hS).dt_UO (hermS I l Z C hI hS).dt_rat L L' g x hg hx

theorem exists_colsFullS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  intro B X I hI _ l Z C g hS hV
  let Fu : Formalism.L2.Herm.FullTiedS (I.rec7 l Z) :=
    { base := hermS I l Z C hI hS
      atT := C.herm.atT
      vol := hV
      levelZeroCompatibility := C.herm.levelZeroCompatibility
      g := g
      ad := C.herm.ad
      cof := C.herm.cof
      piG := C.herm.piG
      stabMap := C.herm.stabMap
      fvI := C.herm.fvI
      relDet := relDet_std I l Z C hI hS
      std := C.herm.std
      vpos := B.V_pos
      baseL := C.herm.baseL }
  refine ⟨⟨Fu, rfl⟩, HEq.rfl, ?_⟩
  intro x a ha
  exact normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha

end Main

end GlobalTheory.Mem.Col2.FullDt

end
