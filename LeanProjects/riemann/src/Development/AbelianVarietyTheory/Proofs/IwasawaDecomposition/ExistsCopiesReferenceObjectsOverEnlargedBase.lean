import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt.RefType

private abbrev MM {Tau : Type} {n : ℕ} (H : Tau → Type) (na : ∀ τ, NormedAddCommGroup (H τ)) (ip : ∀ τ, InnerProductSpace ℂ (H τ))
    (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (fr : Tau → Matrix (Fin n) (Fin n) ℂ)
    (lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)) (X : Type) : Type :=
  MultilinearMap ℂ (fun τ : Tau => (Submodule.span ℂ {w | SmoothVec (lie τ) (fun g => σ τ (fr τ * g * (fr τ)⁻¹)) w} : Submodule ℂ (H τ)))
    (X → ℂ)

private theorem core {Tau Tau' : Type} {n n' : ℕ} {H : Tau → Type} {na : ∀ τ, NormedAddCommGroup (H τ)} {ip : ∀ τ, InnerProductSpace ℂ (H τ)}
    {σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)} {fr : Tau → Matrix (Fin n) (Fin n) ℂ}
    {lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)} {X : Type}
    {H' : Tau' → Type} {na' : ∀ τ, NormedAddCommGroup (H' τ)} {ip' : ∀ τ, InnerProductSpace ℂ (H' τ)}
    {σ' : ∀ τ, Matrix (Fin n') (Fin n') ℂ → (H' τ →L[ℂ] H' τ)} {fr' : Tau' → Matrix (Fin n') (Fin n') ℂ}
    {lie' : Tau' → Set (Matrix (Fin n') (Fin n') ℂ)} {X' : Type}
    {G G' C C' : Type} {nc : NormedAddCommGroup C} {ic : InnerProductSpace ℂ C} {nc' : NormedAddCommGroup C'} {ic' : InnerProductSpace ℂ C'}
    {HW : HMod (MM H na ip σ fr lie X)} {HW' : HMod (MM H' na' ip' σ' fr' lie' X')}
    (hT : Tau' = Tau) (hn : n' = n) (hlie : HEq lie' lie) (hX : X' = X) (hG : G' = G)
    (hC : HEq C' C) (hnc : HEq nc' nc) (hic : HEq ic' ic)
    (hH : HEq H' H) (hna : HEq na' na) (hip : HEq ip' ip) (hσ : HEq σ' σ) (hfr : HEq fr' fr) (hHW : HEq HW' HW)
    (K : HMod (G → C)) (th : K.H →ₗ[ℂ] MM H na ip σ fr lie X) (g : K.H →ₗ[ℂ] HW.H) :
    ∃ (K' : HMod (G' → C')) (th' : K'.H →ₗ[ℂ] MM H' na' ip' σ' fr' lie' X') (g' : K'.H →ₗ[ℂ] HW'.H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst hT hn hX hG
  cases hlie; cases hC; cases hnc; cases hic; cases hH; cases hna; cases hip; cases hσ; cases hfr; cases hHW
  exact ⟨K, th, g, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem mid {D D' : D7} {V W : HSp D} {V' W' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (c : CoefA V) (c' : CoefA V') (M : ∀ s, Formalism.IndefR.Mult.DSModel W (S s)) (M' : ∀ s, Formalism.IndefR.Mult.DSModel W' (S' s))
    (HW : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M s))) (HW' : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M' s)))
    {s t : L} {s' t' : L'} (e : t = s) (e' : t' = s')
    (hT : D'.what₂.Tau = D.what₂.Tau) (hn : W'.rank = W.rank) (hlie : HEq (lieAt W') (lieAt W)) (hX : GA D' W' = GA D W)
    (hG : (Bridge.Gf V' : Type) = Bridge.Gf V)
    (hC : HEq c'.W c.W) (hnc : HEq c'.nW c.nW) (hic : HEq c'.iW c.iW)
    (hH : HEq (M' s').H (M s).H) (hna : HEq (M' s').nacg (M s).nacg) (hip : HEq (M' s').ips (M s).ips) (hσ : HEq (M' s').σ (M s).σ)
    (hfr : HEq (M' s').fr (M s).fr) (hHW : HEq (HW' s') (HW s))
    (K : HMod (Bridge.Gf V → c.W)) (th : K.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M t)) (g : K.H →ₗ[ℂ] (HW t).H) :
    ∃ (K' : HMod (Bridge.Gf V' → c'.W)) (th' : K'.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M' t')) (g' : K'.H →ₗ[ℂ] (HW' t').H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst e e'
  exact core (lie := lieAt W) (lie' := lieAt W') (X := GA D W) (X' := GA D' W') (HW := HW t) (HW' := HW' t')
    hT hn hlie hX hG hC hnc hic hH hna hip hσ hfr hHW K th g

private theorem types (X X' : Stages) (h : X'.B.toPre = X.B.toPre) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i') :
    X'.toD7.what₂.Tau = X.toD7.what₂.Tau ∧ (Wc X'.toD7 i').rank = (Wc X.toD7 i).rank ∧ HEq (lieAt (Wc X'.toD7 i')) (lieAt (Wc X.toD7 i)) ∧
    GA X'.toD7 (Wc X'.toD7 i') = GA X.toD7 (Wc X.toD7 i) ∧ (Bridge.Gf (Vc X'.toD7 i') : Type) = Bridge.Gf (Vc X.toD7 i) ∧
    (GA X.toD7 (Vc X.toD7 i) × GA X.toD7 (Wc X.toD7 i) →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ)) =
      (GA X'.toD7 (Vc X'.toD7 i') × GA X'.toD7 (Wc X'.toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ)) ∧
    (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ) = (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ) ∧
    Measure (GA X.toD7 (Vc X.toD7 i)) = Measure (GA X'.toD7 (Vc X'.toD7 i')) ∧
    Set (GA X.toD7 (Vc X.toD7 i)) = Set (GA X'.toD7 (Vc X'.toD7 i')) := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  cases B
  cases B'
  dsimp only at h
  subst h
  obtain ⟨i, hlt⟩ := i
  obtain ⟨i', hlt'⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end GlobalTheory.Mem.R3.Rw.WeilExt.RefType

open GlobalTheory.Mem.R3.Rw.WeilExt.RefType in
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSideW z Wt' R' → ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
  ∃ (ω : GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') × GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ))
    (v : Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ) (H : HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (R'.cV i').W))
    (th : H.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A))) (g : H.H →ₗ[ℂ] (R'.HW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)).H)
    (ν : Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))) (fd : Set (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))),
    HEq ω (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq v (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq H (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq th (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq g (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq ν (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq fd (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hR i i' hi
  have hR' := hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  obtain ⟨hC, -, hnc, hic, -, -, -, hH, hna, hip, hσ, -, -, hfr, -, hHW, -⟩ := hR'
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := types (w.st Z) (w'.st Z') hE.1 i i' hi
  have key := mid (z.R.cV i) (R'.cV i') (z.R.MW i) (R'.MW i') (z.R.HW i) (R'.HW i')
    (sgAt_mk _ z.R.hv0) (sgAt_mk _ R'.hv0) t1 t2 t3 t4 t5 hC hnc hic hH hna hip hσ hfr hHW
    (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) (z.R.thF i _) (z.R.thG i _)
  obtain ⟨K, th, g, h1, h2, h3⟩ := key
  exact ⟨cast t6 (z.R.ωP i _), cast t7 (z.R.vP i _), K, th, g, cast t8 (z.R.νV i _), cast t9 (z.R.fdV i _), cast_heq _ _, cast_heq _ _,
    h1, h2, h3, cast_heq _ _, cast_heq _ _⟩
