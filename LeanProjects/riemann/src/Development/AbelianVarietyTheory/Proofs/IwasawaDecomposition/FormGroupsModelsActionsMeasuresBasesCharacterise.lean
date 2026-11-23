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

namespace GlobalTheory.Mem.R3.Rw.ModWExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

local macro "ksub " h:ident x:ident y:term : tactic => `(tactic| (
  have e : @Eq (type_of% $x) (by kexactB $y) $x := by kexactB (@eq_of_heq (type_of% $x) $x (by kexactB $y) (by kexactB $h)).symm
  clear $h
  subst e))

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {W : HSp a.D} {W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

set_option hygiene false in

local macro "tie_cases" : tactic => `(tactic| (
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
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

private theorem is_of (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X)
    {U : Submodule ℂ (MMap M)} {U' : Submodule ℂ (MMap M')} (hU : HEq U' U)
    {ν : Measure (GA a.D W)} {ν' : Measure (GA a'.D W')} (hν : HEq ν' ν) {fd : Set (GA a.D W)} {fd' : Set (GA a'.D W')}
    (hfd : HEq fd' fd) (c : ℂ) (h0 : X.Is U fun T T' => c * ipM M ν fd T T') : X'.Is U' fun T T' => c * ipM M' ν' fd' T T' := by
  tie_cases
  ksub hX X' X
  ksub hU U' U
  ksub hν ν' ν
  ksub hfd fd' fd
  exact (by with_unfolding_all exact (h0 :))

private theorem act_of (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {ρ : Representation ℂ G X.H} {ρ' : Representation ℂ G' X'.H} (hρ : HEq ρ' ρ)
    {L : G → (GA a.D W → ℂ) →ₗ[ℂ] (GA a.D W → ℂ)} {L' : G' → (GA a'.D W' → ℂ) →ₗ[ℂ] (GA a'.D W' → ℂ)} (hL : HEq L' L)
    (h0 : ∀ g x, X.e (ρ g x) = postOn M (L g) (X.e x)) : ∀ g x, X'.e (ρ' g x) = postOn M' (L' g) (X'.e x) := by
  subst hG
  obtain rfl := eq_of_heq hi
  tie_cases
  ksub hX X' X
  ksub hρ ρ' ρ
  ksub hL L' L
  exact (by with_unfolding_all exact (h0 :))

end Comparison₂

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

set_option hygiene false in

local macro "pre_cases" : tactic => `(tactic| (
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% i') (by kexactB i) i' := by kexactB (Fin.ext h : @Eq (type_of% i') (by kexactB i) i')
  clear h
  subst e))

private theorem actL_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    {Pg : Finset (Pl a.D.host.E)} {Pg' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {eG : G ≃* G0 Pg a.D.R.r} {eG' : G' ≃* G0 Pg' a'.D.R.r} (he : HEq eG' eG) :
    HEq (fun g => Links.actL _ (β' i') (LiftExt.datW i' Pg') (eG' g)) (fun g => Links.actL _ (β i) (LiftExt.datW i Pg) (eG g)) := by
  subst hG
  obtain rfl := eq_of_heq hi
  pre_cases
  ksub hβ β' β
  ksub hPg Pg' Pg
  ksub he eG' eG
  exact (by with_unfolding_all exact ((HEq.refl (fun g => Links.actL _ (β i) (LiftExt.datW i Pg) (eG g))) :))

private theorem meas_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    {Pg : Finset (Pl a.D.host.E)} {Pg' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg)
    {ν : Measure (GA a.D (Wc a.D i))} {ν' : Measure (GA a'.D (Wc a'.D i'))} (hν : HEq ν' ν)
    {fd : Set (GA a.D (Wc a.D i))} {fd' : Set (GA a'.D (Wc a'.D i'))} (hfd : HEq fd' fd)
    (h0 : IsMeasFD (Wc a.D i) (lev a.D.sp.cm (Wc a.D i).gram (β i) (LiftExt.datW i Pg)) ν fd) :
    IsMeasFD (Wc a'.D i') (lev a'.D.sp.cm (Wc a'.D i').gram (β' i') (LiftExt.datW i' Pg')) ν' fd' := by
  pre_cases
  ksub hβ β' β
  ksub hPg Pg' Pg
  ksub hν ν' ν
  ksub hfd fd' fd
  exact (by with_unfolding_all exact (h0 :))

private theorem onb_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {BV : a.D.what₂.Tau → Matrix (Fin (Vc a.D i).rank) (Fin (Vc a.D i).rank) ℂ}
    {BV' : a'.D.what₂.Tau → Matrix (Fin (Vc a'.D i').rank) (Fin (Vc a'.D i').rank) ℂ} (hBV : HEq BV' BV)
    (h0 : ∀ τ, IsONBasis (gramAt a.D (Vc a.D i) τ) 1 (BV τ) (Vc a.D i).rank) :
    ∀ τ, IsONBasis (gramAt a'.D (Vc a'.D i') τ) 1 (BV' τ) (Vc a'.D i').rank := by
  pre_cases
  ksub hBV BV' BV
  exact (by with_unfolding_all exact (h0 :))

private theorem labE_heq (hP : B'.toPre = B.toPre) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x) (σ' : a'.D.what₂.LL →+* ℂ) :
    HEq (labE (D := a'.D) σ') (labE (D := a.D) (σ'.comp ι)) := by
  have e : labE (D := a.D) a.D.what₂.embLL = tauE a.D := funext fun τ => B.fields_embC τ
  have e' : labE (D := a'.D) a'.D.what₂.embLL = tauE a'.D := funext fun τ => B'.fields_embC τ
  unfold labE at *
  generalize labLL a'.D = l' at e' ⊢
  generalize labLL a.D = l at e ⊢
  generalize a'.D.what₂.embLL = j' at e' hι
  generalize a.D.what₂.embLL = j at e hι
  have ht : HEq (tauE a'.D) (tauE a.D) := by
    clear e e' hι
    rcases B' with ⟨P'⟩
    change P' = B.toPre at hP
    subst hP
    exact (by with_unfolding_all exact ((HEq.refl (tauE a.D)) :))
  rw [← e, ← e'] at ht
  clear e e'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have ht' := eq_of_heq ht
  refine heq_of_eq (funext fun τ => RingHom.ext fun x => ?_)
  have k := DFunLike.congr_fun (congrFun ht' τ) x
  exact congrArg σ' (j'.injective (k.trans (hι _).symm))

private theorem dim_eq (hP : B'.toPre = B.toPre) {W : HSp a.D} {W' : HSp a'.D} (hW : HEq W' W) {σ : a.D.what₂.LL →+* ℂ}
    {σ' : a'.D.what₂.LL →+* ℂ} (hl : HEq (labE (D := a'.D) σ') (labE (D := a.D) σ)) :
    (∏ ρ, ((dimK _ _ (kapAt W' σ' ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  unfold kapAt lab
  generalize labE (D := a'.D) σ' = l' at hl ⊢
  generalize labE (D := a.D) σ = l at hl ⊢
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ksub hW W' W
  ksub hl l' l
  exact rfl

variable {G G' : Type} [iG : Group G] [Fintype G] [iG' : Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private theorem hw_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hθ : HEq R'.θ R.θ) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x) (σ' : a'.D.what₂.LL →+* ℂ)
    (hM : DSTie (R'.MW i' σ') (R.MW i (σ'.comp ι))) (hH : HEq (R'.HW i' σ') (R.HW i (σ'.comp ι)))
    (hν : HEq (R'.νW i') (R.νW i)) (hfd : HEq (R'.fdW i') (R.fdW i)) (h0 : R.models_HW) :
    (R'.HW i' σ').Is (R'.Wall i' σ') (Links.ipAt (R'.MW i' σ') (R'.νW i') (R'.fdW i')) := by
  have hW := wc_heq hP h
  have hl := lev_heq hP h hβ hPg
  have hd := dim_eq hP hW (labE_heq hP ι hι σ')
  have f0 : (R.HW i (σ'.comp ι)).Is (Mult R.θ _ (levS _ (R.βW i) (LiftExt.datW i R.Pg)) (levChi _ (R.βW i) (LiftExt.datW i R.Pg)))
      fun T T' => (∏ ρ, ((dimK _ _ (kapAt (Wc a.D i) (σ'.comp ι) ρ) : ℚ) : ℂ)) * ipM (R.MW i (σ'.comp ι)) (R.νW i) (R.fdW i) T T' := (by with_unfolding_all exact ((h0 i (σ'.comp ι)) :))
  rw [← hd] at f0
  have k := is_of hP hW hM hH (mult_heq hP hW hM hθ hl.1 hl.2) hν hfd _ f0
  exact (by with_unfolding_all exact (k :))

private theorem gw_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hG : G' = G) (hi : HEq iG' iG) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (he : HEq R'.eG R.eG)
    {σ : a.D.what₂.LL →+* ℂ} {σ' : a'.D.what₂.LL →+* ℂ}
    (hM : DSTie (R'.MW i' σ') (R.MW i σ)) (hH : HEq (R'.HW i' σ') (R.HW i σ)) (hg : HEq (R'.gW i' σ') (R.gW i σ))
    (h0 : R.models_gW) :
    ∀ g x, (R'.HW i' σ').e (R'.gW i' σ' g x) =
      postOn _ (Links.actL (Wc a'.D i') (R'.βW i') (R'.datWp i' R'.triv) (R'.eG g)) ((R'.HW i' σ').e x) := by
  have hW := wc_heq hP h
  have f0 : ∀ g x, (R.HW i σ).e (R.gW i σ g x) =
      postOn _ ((fun g => Links.actL _ (R.βW i) (LiftExt.datW i R.Pg) (R.eG g)) g) ((R.HW i σ).e x) := (by with_unfolding_all exact ((h0 i σ) :))
  have k := act_of hP hW hM hH hG hi hg (actL_heq hP h hβ hPg hG hi he) f0
  exact (by with_unfolding_all exact (k :))

private theorem nu_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (hν : HEq (R'.νW i') (R.νW i)) (hfd : HEq (R'.fdW i') (R.fdW i))
    (h0 : R.models_νW) :
    IsMeasFD (Wc a'.D i') (lev a'.D.sp.cm (Wc a'.D i').gram (R'.βW i') (R'.datWp i' R'.triv)) (R'.νW i') (R'.fdW i') := by
  have f0 : IsMeasFD (Wc a.D i) (lev a.D.sp.cm (Wc a.D i).gram (R.βW i) (LiftExt.datW i R.Pg)) (R.νW i) (R.fdW i) := (by with_unfolding_all exact ((h0 i) :))
  have k := meas_of hP h hβ hPg hν hfd f0
  exact (by with_unfolding_all exact (k :))

private theorem modW_of (hP : B'.toPre = B.toPre) (hG : G' = G) (hi : HEq iG' iG)
    (hθ : HEq R'.θ R.θ) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (he : HEq R'.eG R.eG) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (H : ∀ (i : Fin a.D.R.m) (i' : Fin a'.D.R.m), (i : ℕ) = i' → HEq (R'.BV i') (R.BV i) ∧ HEq (R'.νW i') (R.νW i) ∧
      HEq (R'.fdW i') (R.fdW i) ∧ ∀ σ', DSTie (R'.MW i' σ') (R.MW i (σ'.comp ι)) ∧ HEq (R'.HW i' σ') (R.HW i (σ'.comp ι)) ∧
        HEq (R'.gW i' σ') (R.gW i (σ'.comp ι)))
    (h0 : R.IsModels) : ModW R' := by
  have hm := LiftExt.m_eq (a := a) (a' := a') hP
  refine ⟨fun i' σ' => ?_, fun i' σ' => ?_, fun i' => ?_, fun i' => ?_⟩
  all_goals
    have h : ((Fin.cast hm i' : Fin a.D.R.m) : ℕ) = i' := rfl
    generalize (Fin.cast hm i' : Fin a.D.R.m) = i at h
    obt ⟨hBV, hν, hfd, h2⟩ := H i i' h
  · exact hw_of hP h hθ hβ hPg ι hι σ' (h2 σ').1 (h2 σ').2.1 hν hfd h0.HW
  · exact gw_of hP h hG hi hβ hPg he (h2 σ').1 (h2 σ').2.1 (h2 σ').2.2 h0.gW
  · exact nu_of hP h hβ hPg hν hfd h0.νW
  · exact onb_of hP h hBV (h0.BV i)

end Fields

end GlobalTheory.Mem.R3.Rw.ModWExt

end

open GlobalTheory.Mem.R3.Rw.ModWExt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modW_of_rSideW : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → ModW R'.toRealDat := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hG := LiftExt.gc_eq hP hpx
  have hb := z.pins.char.base.models
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  clear_value ι
  obt ⟨-, hθ, hβ, -, -, -, -, -, -, hPg, he, -, h1, -⟩ := hS
  refine modW_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP hG.1 hG.2 hθ hβ hPg he ι hι (fun i i' h => ?_) hb
  obt ⟨-, -, -, -, -, -, hBV, -, -, -, -, -, -, -, -, -, hν, hfd, h2⟩ := h1 i i' h
  refine ⟨hBV, hν, hfd, fun σ' => ?_⟩
  obt ⟨⟨m1, m2, m3, m4, m5, m6, m7, -⟩, hH, hg, -⟩ := (h2 ι hι).1 σ'
  exact ⟨⟨m1, m2, m3, m4, m5, m6, m7⟩, hH, hg⟩
