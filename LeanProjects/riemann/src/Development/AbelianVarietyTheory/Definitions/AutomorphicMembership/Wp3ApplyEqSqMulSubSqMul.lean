import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section General

variable {D : D7} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Parts (R : RealDat3 D A Ks) : Type :=
  (A.fam3.base3.Ix → Submodule ℂ R.HE.H) × (LevelP R.Pg D.R.r ℂ → Submodule ℂ (MMap (R.MY 0))) ×
    ∀ i : Fin D.R.m, A.fam3.base3.Ix → Submodule ℂ (R.HW i (sg0 D A.A)).H

def cxW (R : RealDat3 D A Ks) (F : Face3 D A) (u : Parts R) : Cx.CxData A.fam3.amb3 :=
  { R.toCx3 F with
    EEp := fun p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.1 p)) :))
    EEl := fun c => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) ((u.2.1 (R.toRealDat.levR F.lv2 c)).comap R.HE.e)) :))
    Wp := fun i p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.2.2 i p)) :)) }

def carriesW (R : RealDat3 D A Ks) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  E c ≠ ⊥ ∧ (E c).map (LinearMap.adjoint (R.Th A.A.μ0)) ≤
    Submodule.span ℂ (R.jX A.A.μ0 '' ((A.rowI A.A.μ0).inertTypeEigenspaceSum p.1 : Set (A.A.fam.R A.A.μ0).S.Forms))

def trSemW (R : RealDat3 D A Ks) (F : Face3 D A) (u : type_of% R.Carries × type_of% R.Wc')
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ j p c, u.1 p c → ∀ s : (A.liftI j A.A.μ0).OpIx → D.what₂.LL,
    (∃ x : (A.A.fam.L j A.A.μ0).S.Forms, x ∈ Cx.BlockGood.goodR (A.A.fam.L j A.A.μ0) (A.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A.liftI j A.A.μ0).opAll i x = s i • x) ∧ R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ∈ u.2 j c ∧
      R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ≠ 0) →
    ∀ k : (A.liftI j A.A.μ0).PlI × List ℕ, s (Sum.inr k) = tr j p.1.2 ((A.liftI j A.A.μ0).plI k.1, k.2)

def partAtW (F : Face3 D A) (X : Cx.CxData A.fam3.amb3) (i : Fin D.R.m) (p : A.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) : Prop :=
  ∃ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x x ≠ 0

end General

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)

theorem eec_eq : R.EEc = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEc) :)) :=
  (by with_unfolding_all exact ((congrArg (fun (m : type_of% (@partFull a.D)) (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF fun P d => c P (dualLab d)).comap
      R.HE.e) (partFull_eq b a)) :))

theorem wc_eq : R.Wc' = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wc') :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (W : type_of% R.toRealDat.Wat) (m : type_of% (@partFull a.D)) (i : Fin a.D.R.m)
      (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (W i (sg0 a.D A.A) R.triv ⊓
      m R.θ (R.MW i (sg0 a.D A.A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF c).comap
      (R.HW i _).e) (wat_eq b R.toRealDat) (partFull_eq b a)) :))

theorem carries_eq : R.Carries = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Carries) :)) :=
  (by with_unfolding_all exact ((congrArg (carriesW R) (eec_eq b R)) :))

theorem realAdelicInertTransport_typeRows_eq : R.EEp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E c) (carries_eq b R) (eec_eq b R)) :))

theorem wp3_apply_eq_sq_mul_sub_sq_mul : R.Wp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.Wc') (i : Fin a.D.R.m) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E i c) (carries_eq b R) (wc_eq b R)) :))

theorem parts_eq (_F : Face3 a.D A) : ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) =
    ((by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)), (by with_unfolding_all exact ((letI := alg b iK; (real b R.toRealDat).EEat) :)), (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :))) :=
  (by with_unfolding_all exact ((Prod.ext (realAdelicInertTransport_typeRows_eq b R) (Prod.ext (eeat_eq b R.toRealDat) (wp3_apply_eq_sq_mul_sub_sq_mul b R)) :
    ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) = (_, _, _)) :))

theorem toCx3_eq : R.toCx3 F = (@RealDat3.toCx3 (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg (cxW R F) (parts_eq b R F)) :))

theorem trISem_eq : R.TrISem F = (@RealDat3.TrISem (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun Q E => trSemW R F (Q, E)) (carries_eq b R) (wc_eq b R)) :))

variable {R F}

theorem isInert_tr (h : R.IsInert) : letI := alg b iK; (real3 b R).IsInert := by
  letI := alg b iK
  constructor
  case tie => tr_clause a b h.tie
  case onto => exact (by with_unfolding_all exact (h.onto :))
  case hR => exact (by with_unfolding_all exact (h.hR :))
  case hL => exact (by with_unfolding_all exact (h.hL :))
  case SF => exact (by with_unfolding_all exact (h.SF :))

theorem isTup_tr (h : R.IsTup) : letI := alg b iK; (real3 b R).IsTup := by
  letI := alg b iK
  constructor
  case mu_off => exact (by with_unfolding_all exact (h.mu_off :))
  case mu_used => exact (by with_unfolding_all exact (h.mu_used :))
  case mu_ne => exact (by with_unfolding_all exact (h.mu_ne :))
  case mu_conj => exact (by with_unfolding_all exact (h.mu_conj :))
  case mu_on => exact (by with_unfolding_all exact (h.mu_on :))

theorem isScal_tr (h : R.IsScal F) : letI := alg b iK; (real3 b R).IsScal (face3 b F) := by
  letI := alg b iK
  constructor
  case lam0 => tr_via (fun W : type_of% R.Wp3 => ∀ i t p (l : ℝ), W i p ≠ ⊥ →
      (∀ x ∈ W i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → R.lam3 i t p A.A.v0 = l) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.lam0
  case kap => tr_via (fun E : type_of% R.EEp3 => ∀ κ : ℝ,
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN κ →
      (∃ t p, E p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 a.D.R.m, R.lamN t j p ≠ 0) → R.kap = κ) (realAdelicInertTransport_typeRows_eq b R) h.kap
  case off => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v (l : ℝ), v ≠ A.A.v0 → partAtW F X i p v →
      (∀ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p → ∀ y,
        inner ℂ (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec x)))
            (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec y))) =
          ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x y) →
      R.lam3 i A.A.μ0 p v = l) (toCx3_eq b R F) h.off
  case abs0 => tr_via (fun u : Parts R => ∀ i t p, u.2.2 i p = ⊥ →
      R.lam3 i t p A.A.v0 = Real.exp ((F.Zsc (cxW R F u).zs).l6m i)) (parts_eq b R F) h.abs0
  case abs => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v, v ≠ A.A.v0 → ¬ partAtW F X i p v →
      R.lam3 i A.A.μ0 p v = Real.exp ((F.Zsc X.zs).l6m i)) (toCx3_eq b R F) h.abs
  case tup => exact (by with_unfolding_all exact (h.tup :))

theorem primRows3_tr (h : PrimRows3 R F) : letI := alg b iK; PrimRows3 (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke => tr_via (fun X : Cx.CxData A.fam3.amb3 => (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW) (toCx3_eq b R F) h.hecke
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv => tr_via (fun u : Parts R => Cx.GEquiv3 A (cxW R F u) ((by with_unfolding_all exact ((R.gEx F) :))) ∧ Cx.LiftGroupEquivariance A (cxW R F u) ((by with_unfolding_all exact ((R.gWx F) :)))) (parts_eq b R F) h.gEquiv
  case block => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock) (toCx3_eq b R F) h.block
  case rowTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F) h.rowTest
  case liftTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X) (toCx3_eq b R F) h.liftTest
  case liftTestB => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false) (toCx3_eq b R F) h.liftTestB
  case liftOnto => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ hW, Cx.HeckeIntertwiningLifts A X hW →
      U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW) (toCx3_eq b R F) h.liftOnto
  case pos => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ c, (Cx.lv (F.fc X.zs) c).Pos) (toCx3_eq b R F) h.pos
  case posScal => exact (by with_unfolding_all exact (h.posScal :))
  case levE => tr_via (fun u : Parts R =>
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gEx F) :))) false F.P0 F.ψ0 ∧
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gEx F) :))) true F.P1 F.ψ1) (parts_eq b R F) h.levE
  case h2P => tr_via (fun X : Cx.CxData A.fam3.amb3 =>
      Cx.PrincipalLevelBijectivity A X (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) (toCx3_eq b R F) h.h2P
  case thmB => tr_via (fun E : type_of% R.EEp3 =>
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN R.kap) (realAdelicInertTransport_typeRows_eq b R) h.thmB
  case sumE => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ c, X.PartsE c) (toCx3_eq b R F) h.sumE
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.MLat false) (toCx3_eq b R F) h.mLat
  case levW => tr_via (fun u : Parts R =>
      Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gWx F) :))) false F.P0 F.ψ0) (parts_eq b R F) h.levW
  case thmA => tr_via (fun W : type_of% R.Wp3 => ∀ i t,
      Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.thmA
  case sumW => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false) (toCx3_eq b R F) h.sumW
  case scalConj => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.GalD F.cr false) (toCx3_eq b R F) h.scalConj
  case dimParts => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.DimParts false) (toCx3_eq b R F) h.dimParts

theorem realAdelicInertTransport_furtherRows (h : UnusedChoiceStatements R F) : letI := alg b iK; UnusedChoiceStatements (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case ex => exact (by with_unfolding_all exact ((exAt_tr b h.ex) :))
  case conj => exact (by with_unfolding_all exact (h.conj :))
  case levelW => exact (by with_unfolding_all exact ((lLevelW_tr b h.levelW) :))
  case integral => exact (by with_unfolding_all exact (h.integral :))

end Three

end GlobalTheory.Mem.R3.Tr

end
