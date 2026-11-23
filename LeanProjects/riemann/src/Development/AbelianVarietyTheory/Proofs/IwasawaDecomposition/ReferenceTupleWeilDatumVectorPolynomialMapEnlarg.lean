import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.WeilAtExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.WeilFull GlobalTheory.Mem.R3.Rw.LiftExt

local macro "ksub " h:ident x:ident y:term : tactic => `(tactic| (
  have e : @Eq (type_of% $x) (by kexactB $y) $x := by kexactB (@eq_of_heq (type_of% $x) $x (by kexactB $y) (by kexactB $h)).symm
  clear $h
  subst e))

set_option hygiene false in

local macro "pre_sub" : tactic => `(tactic| (
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP))

local macro "keq " n:ident x:term:max y:term:max h:term:max : tactic => `(tactic|
  have $n : @Eq (type_of% $x) $x (by kexactB $y) := by kexactB (@eq_of_heq (type_of% $x) $x (by kexactB $y) (by kexactB $h)))

section Leaves

variable {B B' : Base} {C : Cols B} {C' : Cols B'} (a : Late B C) (a' : Late B' C')

private theorem thetaFun_heq (hP : B'.toPre = B.toPre) : HEq (@IsThetaFunO a'.D) (@IsThetaFunO a.D) := by
  pre_sub
  have e : @Eq (type_of% (@IsThetaFunO a.D)) ((by with_unfolding_all exact ((@IsThetaFunO a'.D) :))) (@IsThetaFunO a.D) := by
    funext ψ S T f
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsThetaFunO a'.D ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.quasi :)), (by with_unfolding_all exact (h'.level :)), (by with_unfolding_all exact (h'.cont :)), (by with_unfolding_all exact (h'.smooth :))⟩
    · have h' : @IsThetaFunO a'.D ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem vacuum_heq (hP : B'.toPre = B.toPre) : HEq (@IsVacuum a'.D) (@IsVacuum a.D) := by
  pre_sub
  have e : @Eq (type_of% (@IsVacuum a.D)) ((by with_unfolding_all exact ((@IsVacuum a'.D) :))) (@IsVacuum a.D) := by
    funext m n x1 x2 x3 x4 x5 x6 x7
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsVacuum a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.inf :)), (by with_unfolding_all exact (h'.theta :)), (by with_unfolding_all exact (h'.lat :)), (by with_unfolding_all exact (h'.fock :)), (by with_unfolding_all exact (h'.norm :))⟩
    · have h' : @IsVacuum a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) :=
        ⟨(by with_unfolding_all exact (h.inf :)), (by with_unfolding_all exact (h.theta :)), (by with_unfolding_all exact (h.lat :)), (by with_unfolding_all exact (h.fock :)), (by with_unfolding_all exact (h.norm :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem placeModel_heq (hP : B'.toPre = B.toPre) : HEq (@IsPlaceModel a'.D) (@IsPlaceModel a.D) := by
  pre_sub
  have e : @Eq (type_of% (@IsPlaceModel a.D)) ((by with_unfolding_all exact ((@IsPlaceModel a'.D) :))) (@IsPlaceModel a.D) := by
    funext m n x1 x2 x3 x4 x5 x6 x7 x8
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsPlaceModel a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.trans :)), (by with_unfolding_all exact (h'.modul :)), (by with_unfolding_all exact (h'.vac :))⟩
    · have h' : @IsPlaceModel a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) :=
        ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem pairSetup_heq (hP : B'.toPre = B.toPre) : HEq (@Fock.Sk.PairSetup a'.D) (@Fock.Sk.PairSetup a.D) := by
  pre_sub
  have e : @Eq (type_of% (@Fock.Sk.PairSetup a.D)) ((by with_unfolding_all exact ((@Fock.Sk.PairSetup a'.D) :))) (@Fock.Sk.PairSetup a.D) := by
    funext x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @Fock.Sk.PairSetup a'.D ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) ((by with_unfolding_all exact (x9 :))) ((by with_unfolding_all exact (x10 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.std :)), (by with_unfolding_all exact (h'.inf :)), (by with_unfolding_all exact (h'.cartS :)), (by with_unfolding_all exact (h'.cartT :)), (by with_unfolding_all exact (h'.onbS :)), (by with_unfolding_all exact (h'.onbT :))⟩
    · have h' : @Fock.Sk.PairSetup a'.D ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) ((by with_unfolding_all exact (x9 :))) ((by with_unfolding_all exact (x10 :))) :=
        ⟨(by with_unfolding_all exact (h.std :)), (by with_unfolding_all exact (h.inf :)), (by with_unfolding_all exact (h.cartS :)), (by with_unfolding_all exact (h.cartT :)), (by with_unfolding_all exact (h.onbS :)), (by with_unfolding_all exact (h.onbT :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

end Leaves

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D}

private theorem weilFull_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ)
    {μ η : (AE a.D)ˣ →* Circle} {μ' η' : (AE a'.D)ˣ →* Circle} (hμ : HEq μ' μ) (hη : HEq η' η)
    {ω ω'} (hω : HEq ω' ω) (h : IsWeilFull ψ V W μ (μ * η⁻¹) ω) : IsWeilFull ψ' V' W' μ' (μ' * η'⁻¹) ω' := by
  have k1 := thetaFun_heq a a' hP
  have k2 := pairSetup_heq a a' hP
  pre_sub
  ksub hV V' V
  ksub hW W' W
  ksub hψ ψ' ψ
  ksub hμ μ' μ
  ksub hη η' η
  ksub hω ω' ω
  keq e1 (@IsThetaFunO a'.D) (@IsThetaFunO a.D) k1
  keq e2 (@Fock.Sk.PairSetup a'.D) (@Fock.Sk.PairSetup a.D) k2
  refine ⟨⟨(by with_unfolding_all exact (h.datum.std :)), (by with_unfolding_all exact (h.datum.hecS :)), (by with_unfolding_all exact (h.datum.hecT :)), (by with_unfolding_all exact (h.datum.resS :)), (by with_unfolding_all exact (h.datum.resT :)), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_pres :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_heis :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_aut :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_cont :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_unit :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_split :))
  · delta SphInertAtO; rewrite [e1]; exact (by with_unfolding_all exact (h.inert :))
  · delta RealAtO; rewrite [e2, e1]; exact (by with_unfolding_all exact (h.real :))

private theorem thPVec_empty {D : D7} {ψ θ} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg ξ} (ξ') {f₀ f}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  have e : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP),
      omegaQ ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simp only [e]
  exact h

private theorem thPVec_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ)
    {θ : InfFam a.D} {θ' : InfFam a'.D} (hθ : HEq θ' θ) {s s'} (hs : HEq s' s)
    {ΛV : Submodule (𝓞 a.D.host.E) (Fin V.rank → a.D.host.E)} {ΛV' : Submodule (𝓞 a'.D.host.E) (Fin V'.rank → a'.D.host.E)}
    (hΛV : HEq ΛV' ΛV)
    {ΛW : Submodule (𝓞 a.D.host.E) (Fin W.rank → a.D.host.E)} {ΛW' : Submodule (𝓞 a'.D.host.E) (Fin W'.rank → a'.D.host.E)}
    (hΛW : HEq ΛW' ΛW) {βV βV'} (hβV : HEq βV' βV) {βW βW'} (hβW : HEq βW' βW) {Pg Pg'} (hPg : HEq Pg' Pg)
    {f₀ f₀'} (h₀ : HEq f₀' f₀) {f f'} (hf : HEq f' f)
    (h : IsThPVecOf ψ θ V W (fun _ => 1) s ΛV ΛW βV βW Pg ∅ (fun _ => 1) f₀ f) :
    IsThPVecOf ψ' θ' V' W' (fun _ => 1) s' ΛV' ΛW' βV' βW' Pg' ∅ (fun _ => 1) f₀' f' := by
  have k1 := thetaFun_heq a a' hP
  have k2 := vacuum_heq a a' hP
  have k3 := placeModel_heq a a' hP
  pre_sub
  ksub hV V' V
  ksub hW W' W
  ksub hψ ψ' ψ
  ksub hθ θ' θ
  ksub hs s' s
  ksub hΛV ΛV' ΛV
  ksub hΛW ΛW' ΛW
  ksub hβV βV' βV
  ksub hβW βW' βW
  ksub hPg Pg' Pg
  ksub h₀ f₀' f₀
  ksub hf f' f
  keq e1 (@IsThetaFunO a'.D) (@IsThetaFunO a.D) k1
  keq e2 (@IsVacuum a'.D) (@IsVacuum a.D) k2
  keq e3 (@IsPlaceModel a'.D) (@IsPlaceModel a.D) k3
  delta IsThPVecOf IsVacO IsThetaAt
  rewrite [e1, e2, e3]
  exact (by with_unfolding_all exact (h :))

variable {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

set_option hygiene false in

local macro "tie_cases" : tactic => `(tactic| (
  pre_sub
  ksub hW W' W
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ksub h1 H' M.H
  ksub h2 n' M.nacg
  ksub h3 i' M.ips
  ksub h4 s' M.σ
  ksub h5 l' M.lam
  ksub h6 ε' M.ε
  ksub h7 f' M.fr))

private theorem cart_heq (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M) : HEq (cart M') (cart M) := by
  tie_cases
  exact (by with_unfolding_all exact ((HEq.refl (cart M)) :))

private theorem ioW_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M)
    {θ : InfFam a.D} {θ' : InfFam a'.D} (hθ : HEq θ' θ)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {BV BV'} (hBV : HEq BV' BV) {io io'} (hio : HEq io' io) {ω ω'} (hω : HEq ω' ω) {v v'} (hv : HEq v' v) {Δ Δ'} (hΔ : HEq Δ' Δ)
    (h0 : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) v) Δ io) :
    IsIoW θ' M' c' ω' (pureTensorO ψ' θ' V' W' (fun _ => 1) (cart M') BV' (onb M') v') Δ' io' := by
  tie_cases
  ksub hV V' V
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ksub c1 W₁ c.W
  ksub c3 nW' c.nW
  ksub c4 iW' c.iW
  ksub c2 ρ₁ c.ρ
  ksub hθ θ' θ
  ksub hψ ψ' ψ
  ksub hBV BV' BV
  ksub hio io' io
  ksub hω ω' ω
  ksub hv v' v
  ksub hΔ Δ' Δ
  exact (by with_unfolding_all exact (h0 :))

end Comparison₂

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

set_option hygiene false in

local macro "pre_cases" : tactic => `(tactic| (
  pre_sub
  have e : @Eq (type_of% i') (by kexactB i) i' := by kexactB (Fin.ext h : @Eq (type_of% i') (by kexactB i) i')
  clear h
  subst e))

private theorem delta_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') :
    HEq (RealDat.Delta i') (RealDat.Delta i) := by
  pre_cases
  exact (by with_unfolding_all exact ((HEq.refl (RealDat.Delta i)) :))

private theorem frames_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {ΛV : ∀ i, Submodule (𝓞 a.D.host.E) (Fin (Vc a.D i).rank → a.D.host.E)}
    {ΛV' : ∀ i, Submodule (𝓞 a'.D.host.E) (Fin (Vc a'.D i).rank → a'.D.host.E)} (hΛV : HEq ΛV' ΛV)
    {ΛW : ∀ i, Submodule (𝓞 a.D.host.E) (Fin (Wc a.D i).rank → a.D.host.E)}
    {ΛW' : ∀ i, Submodule (𝓞 a'.D.host.E) (Fin (Wc a'.D i).rank → a'.D.host.E)} (hΛW : HEq ΛW' ΛW)
    {βV : ∀ i, GL (Fin (Vc a.D i).rank) (Lev.EAf a.D)} {βV' : ∀ i, GL (Fin (Vc a'.D i).rank) (Lev.EAf a'.D)} (hβV : HEq βV' βV)
    {βW : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {βW' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβW : HEq βW' βW) :
    HEq (ΛV' i') (ΛV i) ∧ HEq (ΛW' i') (ΛW i) ∧ HEq (βV' i') (βV i) ∧ HEq (βW' i') (βW i) := by
  pre_cases
  ksub hΛV ΛV' ΛV
  ksub hΛW ΛW' ΛW
  ksub hβV βV' βV
  ksub hβW βW' βW
  exact (by with_unfolding_all exact ((And.intro (HEq.refl (ΛV i)) (And.intro (HEq.refl (ΛW i)) (And.intro (HEq.refl (βV i)) (HEq.refl (βW i))))) :))

variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private def WeilAt1 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (i : Fin D.R.m) : Prop :=
  IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧
  IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q t) (R.xiR t) (R.vacP i) (R.vP i t) ∧
  IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) (R.ioP i)

private theorem exists_isOrbQuot_of_isHaarOn (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (hψ : HEq R'.ψ R.ψ) (hθ : HEq R'.θ R.θ) (hβW : HEq R'.βW R.βW) (hβV : HEq R'.βV R.βV) (hΛV : HEq R'.ΛV R.ΛV)
    (hΛW : HEq R'.ΛW R.ΛW) (hPg : HEq R'.Pg R.Pg)
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW) (hvac : HEq (R'.vacP i') (R.vacP i)) (hio : HEq (R'.ioP i') (R.ioP i))
    (hBV : HEq (R'.BV i') (R.BV i)) (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL))
    (hω : HEq (R'.ωP i' t') (R.ωP i t)) (hv : HEq (R'.vP i' t') (R.vP i t))
    (hμ : HEq (R'.toLevCh.mu t' ((i' : ℕ) + 1)) (R.toLevCh.mu t ((i : ℕ) + 1))) (hη : HEq R'.eta R.eta)
    (hQ' : R'.Q t' = ∅) (hQ : R.Q t = ∅) (h0 : WeilAt1 R t i) : WeilAt1 R' t' i' := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hW := wc_heq hP h
  have hV := vc_heq hP h
  obtain ⟨l1, l2, l3, l4⟩ := frames_heq hP h hΛV hΛW hβV hβW
  obtain ⟨w1, w2, w3⟩ := h0
  refine ⟨weilFull_of hP hV hW hψ hμ hη hω w1, ?_, ioW_of hP hV hW hM0 hθ hψ c1 c2 c3 c4 hBV hio hω hv (delta_heq hP h) w3⟩
  rw [hQ] at w2
  rw [hQ']
  exact thPVec_empty _ (thPVec_of hP hV hW hψ hθ (cart_heq hP hW hM0) l1 l2 l3 l4 hPg hvac hv (thPVec_empty _ w2))

end Fields

end GlobalTheory.Mem.R3.Rw.WeilAtExt

end

open GlobalTheory.Mem.R3.Rw.WeilAtExt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_vector_polynomialMap_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → z.R.toRealDat.ExAt → RSide z Wt' R' → LevSame z Wt' R' → WeilAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hEx hS hL i'
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  obt ⟨⟨hψ, hθ, hβW, -, -, -, hβV, hΛV, hΛW, hPg, -, -, h1, -⟩, h2⟩ := hS
  obt ⟨c1, c2, c3, c4, hvac, hio, hBV, m1, m2, m3, m4, m5, m6, m7, -⟩ := h1 i i' h
  obt ⟨hω, hv, -⟩ := h2 i i' h
  obt ⟨hμ, hη, hQ', hQ⟩ := hL
  have hb := RealDat.thP_of_weak z.pins.char.base.thP hEx
  exact exists_isOrbQuot_of_isHaarOn (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h hψ hθ hβW hβV hΛV hΛW hPg c1 c2 c3 c4 hvac hio hBV
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hω hv (hμ i i' h).1 hη hQ' hQ ⟨z.pins.char.fullP i _, hb.vP i _, hb.ioP i _⟩
