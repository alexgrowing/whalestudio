import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
set_option linter.style.haveILetI false

scoped macro "tr_via " P:term:max e:term:max h:term:max : tactic => `(tactic| kexactB (cast (congrArg $P $e) (kc% $h)))

section Spaces

variable (a) in

def goodPartB : type_of% (@goodPart b.D) := @fun V S θ M J χ e => (by with_unfolding_all exact ((@goodPart a.D ((V)) ((S)) ((θ)) (((ds a M))) ((J)) ((χ)) ((e))) : _))

variable (a) in

theorem goodPart_eq : @goodPart b.D = @goodPartB B C a b := by
  funext V S θ M J χ e
  delta goodPart
  rewrite [mult_eq a b]
  exact (by with_unfolding_all exact ((Eq.refl (@goodPartB B C a b V S θ M J χ e)) :))

variable (a) in

def partFullB : type_of% (@partFull b.D) := @fun V S θ M J χ Sb c => (by with_unfolding_all exact ((@partFull a.D ((V)) ((S)) ((θ)) (((ds a M))) ((J)) ((χ)) ((Sb)) ((c))) : _))

variable (a) in

theorem partFull_eq : @partFull b.D = @partFullB B C a b := by
  funext V S θ M J χ Sb c
  delta partFull
  rewrite [mult_eq a b]
  exact (by with_unfolding_all exact ((Eq.refl (@partFullB B C a b V S θ M J χ Sb c)) :))

end Spaces

section General

variable {D : D7} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev ccW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Submodule ℂ (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  m R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))

def pIoYW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (k : ℕ) (io : ccW (@m) R t (k + 1) →ₗ[ℂ] ccW (@m) R t k) : Prop :=
  Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k) (ccW (@m) R t (k + 1)) (ccW (@m) R t k) io

def pIoXW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T)
    (io : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] ccW (@m) R t (D.R.m - 1)) : Prop :=
  Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (ccW (@m) R t (D.R.m - 1)) io

def thDnW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (y : IoYT (@m) R) (x : IoXT (@m) R) (t : T) :
    (R.HX t).H →ₗ[ℂ] (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) :=
  (ccW (@m) R t 0).subtype ∘ₗ Lift.thetaDn (ccW (@m) R t) (y t) (D.R.m - 1) ∘ₗ x t ∘ₗ
    (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

theorem io_congr (R : RealDat D A Ks) {m m' : type_of% (@MultT D)} (e : @m = @m') {β : Type}
    (f : ∀ m : type_of% (@MultT D), IoYT (@m) R → IoXT (@m) R → β) (y : IoYT (@m) R) (x : IoXT (@m) R) :
    f (@m) y x = f (@m') (castAlong (congrArg (fun m : type_of% (@MultT D) => IoYT (@m) R) e) y).1
      (castAlong (congrArg (fun m : type_of% (@MultT D) => IoXT (@m) R) e) x).1 := by
  subst e
  exact (congrArg₂ (f (@m)) (castAlong_rfl y) (castAlong_rfl x)).symm

end General

section Two

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) {F : Face a.D A}

theorem eeat_eq : R.EEat = (@RealDat.EEat (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) := by
  funext P
  exact (by with_unfolding_all exact ((congrArg (fun m : type_of% (@goodPart a.D) =>
    m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0) (goodPart_eq b a)) :))

theorem wall_eq : R.Wall = (by with_unfolding_all exact ((letI := alg b iK; (real b R).Wall) :)) := by
  funext i σ
  exact (by with_unfolding_all exact ((congrArg (fun m : type_of% (@Mult.Mult a.D) =>
    m R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))) (mult_eq b a)) :))

theorem wat_eq : R.Wat = (by with_unfolding_all exact ((letI := alg b iK; (real b R).Wat) :)) := by
  funext i σ P
  exact (by with_unfolding_all exact ((congrArg (fun m : type_of% (@goodPart a.D) =>
    m R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (R.eWf i σ)) (goodPart_eq b a)) :))

theorem cc_eq : R.CC = (@RealDat.CC (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) :=
  (by with_unfolding_all exact ((congrArg (fun m : type_of% (@MultT a.D) => ccW (@m) R) (multT_eq b a)) :))

theorem thDn_eq : R.thDn = (@RealDat.thDn (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) :=
  (by with_unfolding_all exact ((io_congr R (multT_eq b a) (fun m y x => thDnW (@m) R y x) ((R.ioY)) ((R.ioX))) : _))

theorem pTh_eq : R.PTh = (@RealDat.PTh (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) :=
  (by with_unfolding_all exact ((congrArg (fun (d : type_of% R.thDn) (t : T) (g : (R.HX t).H →ₗ[ℂ] R.HE.H) =>
    ∀ x, R.HE.e (g x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (d t x))) (thDn_eq b R)) :))

theorem pThF_eq : R.PThF = (by with_unfolding_all exact ((letI := alg b iK; (real b R).PThF) :)) := by
  funext i t th
  have e := congrArg (fun W : type_of% R.Wall => ∀ x, th x ∈ W i (sg0 a.D A)) (wall_eq b R)
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · exact (by with_unfolding_all exact ((And.intro (cast e ((h.1))) h.2) : _))
  · refine ⟨?_, ?_⟩
    · exact (by with_unfolding_all exact ((cast e.symm ((h.1))) : _))
    · exact (by with_unfolding_all exact (h.2 :))

end Two

section Two

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A}

omit [Field Ks] [NumberField Ks] iK in

theorem levIs_tr {L : Links.LevCh a.D T} {μ0 : T} (h : L.Is μ0) : (levCh b L).Is μ0 := by
  constructor
  case mu0 => exact (by with_unfolding_all exact (h.mu0 :))
  case eta => exact (by with_unfolding_all exact (h.eta :))
  case xi => exact (by with_unfolding_all exact (h.xi :))
  case xi_inj => exact (by with_unfolding_all exact (h.xi_inj :))
  case xi_base => exact (by with_unfolding_all exact (h.xi_base :))
  case xi_fin => exact (by with_unfolding_all exact (h.xi_fin :))
  case xi_triv => exact (by with_unfolding_all exact (h.xi_triv :))
  case xi_tame => exact (by with_unfolding_all exact (h.xi_tame :))
  case Pg => exact (by with_unfolding_all exact (h.Pg :))
  case Q_pl => exact (by with_unfolding_all exact (h.Q_pl :))
  case Q_off => exact (by with_unfolding_all exact (h.Q_off :))
  case Q_de => exact (by with_unfolding_all exact (h.Q_de :))
  case Q_ram => exact (by with_unfolding_all exact (h.Q_ram :))
  case chi => exact (by with_unfolding_all exact (h.chi :))
  case xiR => exact (by with_unfolding_all exact (h.xiR :))
  case βY => exact (by with_unfolding_all exact (h.βY :))
  case βX => exact (by with_unfolding_all exact (h.βX :))
  case βV => exact (by with_unfolding_all exact (h.βV :))
  case βW => exact (by with_unfolding_all exact (h.βW :))

theorem isFam_tr (h : R.IsFam) : letI := alg b iK; (real b R).IsFam := by
  letI := alg b iK
  constructor
  case tie => tr_clause a b h.tie
  case Sb => exact (by with_unfolding_all exact (h.Sb :))
  case roots => exact (by with_unfolding_all exact (h.roots :))
  case pl_onto => exact (by with_unfolding_all exact (h.pl_onto :))
  case degR => exact (by with_unfolding_all exact (h.degR :))
  case degL => exact (by with_unfolding_all exact (h.degL :))
  case muVal => exact (by with_unfolding_all exact (h.muVal :))
  case etaVal => exact (by with_unfolding_all exact (h.etaVal :))

theorem isModels_tr (h : R.IsModels) : letI := alg b iK; (real b R).IsModels := by
  letI := alg b iK
  constructor
  case inf => exact (by with_unfolding_all exact (h.inf :))
  case vpos => exact (by with_unfolding_all exact (h.vpos :))
  case cX => exact (by with_unfolding_all exact (h.cX :))
  case cV => exact (by with_unfolding_all exact (h.cV :))
  case prX => exact (by with_unfolding_all exact (h.prX :))
  case HX => exact (by with_unfolding_all exact (h.HX :))
  case HV => exact (by with_unfolding_all exact (h.HV :))
  case HE => tr_clause a b h.HE
  case HW => tr_clause a b h.HW
  case gE => exact (by with_unfolding_all exact (h.gE :))
  case gW => exact (by with_unfolding_all exact (h.gW :))
  case jX => exact (by with_unfolding_all exact (h.jX :))
  case jV => exact (by with_unfolding_all exact (h.jV :))
  case νY => exact (by with_unfolding_all exact (h.νY :))
  case νY' => exact (by with_unfolding_all exact (h.νY' :))
  case ν0 => exact (by with_unfolding_all exact (h.ν0 :))
  case νX => exact (by with_unfolding_all exact (h.νX :))
  case νV => exact (by with_unfolding_all exact (h.νV :))
  case νW => exact (by with_unfolding_all exact (h.νW :))
  case BV => exact (by with_unfolding_all exact (h.BV :))
  case order => exact (by with_unfolding_all exact (h.order :))

set_option maxHeartbeats 800000 in

theorem isChainW_tr (h : R.IsChainW) : letI := alg b iK; (real b R).IsChainW := by
  letI := alg b iK
  constructor
  case ωY => tr_clause a b h.ωY
  case ωX => tr_clause a b h.ωX
  case vY => tr_clause a b h.vY
  case vX => tr_clause a b h.vX
  case ptY => tr_clause a b h.ptY
  case ptX => tr_clause a b h.ptX
  case ItY => tr_clause a b h.ItY
  case ItX => tr_clause a b h.ItX
  case ioY => exact (by with_unfolding_all exact ((cast (io_congr R (multT_eq b a)
      (fun m y _ => ∀ t k, k + 1 < a.D.R.m → OrZero (pIoYW (@m) R t k) (y t k)) ((R.ioY)) ((R.ioX))) ((h.ioY))) : _))
  case ioX => kexactB (cast (io_congr R (multT_eq b a)
      (fun m _ x => ∀ t, OrZero (pIoXW (@m) R t) (x t)) ((by with_unfolding_all exact (R.ioY :))) ((by with_unfolding_all exact (R.ioX :)))) ((by with_unfolding_all exact (h.ioX :))))
  case Th => tr_via (fun p : type_of% R.PTh => ∀ t, OrZero (p t) (R.Th t)) (pTh_eq b R) h.Th

set_option maxHeartbeats 800000 in

theorem isThPW_tr (h : R.IsThPW) : letI := alg b iK; (real b R).IsThPW := by
  letI := alg b iK
  constructor
  case ωP => tr_clause a b h.ωP
  case vP => tr_clause a b h.vP
  case pt_theta => tr_clause a b h.pt_theta
  case ioP => exact (by with_unfolding_all exact (h.ioP :))
  case thF => tr_via (fun p : type_of% R.PThF => ∀ i t, OrZero (p i t) (R.thF i t)) (pThF_eq b R) h.thF
  case thG => kexactB h.thG

set_option maxHeartbeats 800000 in

theorem exAt_tr (h : R.ExAt) : letI := alg b iK; (real b R).ExAt := by
  letI := alg b iK
  constructor
  case ItY => tr_clause a b h.ItY
  case ItX => tr_clause a b h.ItX
  case ioY => tr_via (fun m : type_of% (@MultT a.D) => ∀ t k, k + 1 < a.D.R.m → ∃ y, pIoYW (@m) R t k y) (multT_eq b a) h.ioY
  case ioX => tr_via (fun m : type_of% (@MultT a.D) => ∀ t, ∃ y, pIoXW (@m) R t y) (multT_eq b a) h.ioX
  case Th => tr_via (fun p : type_of% R.PTh => ∀ t, ∃ y, p t y) (pTh_eq b R) h.Th
  case ioP => exact (by with_unfolding_all exact (h.ioP :))
  case thF => tr_via (fun p : type_of% R.PThF => ∀ i t, ∃ y, p i t y) (pThF_eq b R) h.thF
  case thG => kexactB h.thG

theorem lLevelW_tr (h : R.LLevelW F) : letI := alg b iK; (real b R).LLevelW (face b F) := by
  tr_via (fun W : type_of% R.Wat => ∀ c i σ, R.WS F c i σ = (W i σ (R.levL F c σ)).comap (R.HW i σ).e) (wat_eq b R) h

end Two

end GlobalTheory.Mem.R3.Tr

end
