import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.ModVExt

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

private theorem is_move (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ χ' : J →* ℂˣ) (e : χ' = χ)
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → G) (y' : I' → G) (hy : Bridge.IsReps ι J y) (hy' : Bridge.IsReps ι J y')
    (H : HMod (G → W)) (h : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) :
    H.Is (Bridge.AdForms ι ρ J χ') (Bridge.adInner ι J y') := by
  subst e
  refine ⟨h.1, h.2.1, fun x x' => ?_⟩
  rw [h.2.2]
  exact Bridge.adInnerIndep_holds ι ρ J χ' hρ hχ I I' y y' hy hy' _ (h.2.1 ▸ LinearMap.mem_range_self _ x) _
    (h.2.1 ▸ LinearMap.mem_range_self _ x')

private theorem norm_units_of_finite {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (u : H) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hfin := Fintype.ofFinite H
  have h1 : (χ u) ^ (Fintype.card H) = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have h2 : ‖((χ u : ℂˣ) : ℂ)‖ ^ (Fintype.card H) = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

end Generic

section Free

variable {D : D7}

private theorem norm_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ‖((levEnv V β L).χ k : ℂ)‖ = 1 := by
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  show ‖((levFn β (flag1L L) (Formalism.UG.bc (swapAE D) k.1.1) : ℂˣ) : ℂ)‖ = 1
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  simp only [Units.val_mul, norm_mul, Units.coe_prod, norm_prod]
  rw [show ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) x) = 1 from subgroupCharExtension_one_apply _ _]
  simp [norm_units_of_finite]

private def datC (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY _ D.R.r D.R.t 1 hr Pg Q (LevelP.triv _ _ _) (fun _ => chi) xi Frm.A

private def MV (V : HSp D) (c : CoefA V) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} [Fintype I] (y : I → Bridge.Gf V) (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V)) : Prop :=
  H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y) ∧
  IsMeasDef V (lev D.sp.cm V.gram β L) ν fd

private def RP (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} (y : I → Bridge.Gf V) : Prop := Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y

private theorem mv_move (V : HSp D) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (hr : D.R.r ≤ V.rank)
    (Pg : Finset (Pl D.host.E)) (chi xi chi' xi' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (hchi : ∀ PP ∈ Pg, chi' PP = chi PP)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → Bridge.Gf V) (y' : I' → Bridge.Gf V)
    (hy : RP V β (datC V hr Pg ∅ chi xi) y) (hy' : RP V β (datC V hr Pg ∅ chi' xi') y')
    (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V))
    (h : MV V c β (datC V hr Pg ∅ chi xi) y H ν fd) : MV V c β (datC V hr Pg ∅ chi' xi') y' H ν fd := by
  refine ⟨?_, h.2⟩
  refine is_move (Bridge.ratF V) c.coef.ρ (levEnv V β (datC V hr Pg ∅ chi xi)).J _ (levEnv V β (datC V hr Pg ∅ chi' xi')).χ ?_
    (fun γ => hc.2.1 γ.1) (norm_chi V β _) y y' hy hy' H h.1
  ext1 k
  show levFn β (flag1L (datC V hr Pg ∅ chi' xi')) (Formalism.UG.bc (swapAE D) k.1.1) =
    levFn β (flag1L (datC V hr Pg ∅ chi xi)) (Formalism.UG.bc (swapAE D) k.1.1)
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  congr 1
  congr 1
  refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
  show (chi' PP)⁻¹ _ = (chi PP)⁻¹ _
  rw [hchi PP hP]
  rfl

end Free

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

private theorem mv_of (hP : B'.toPre = B.toPre) {V : HSp a.D} {V' : HSp a'.D} (hV : HEq V' V) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf a.D)} {β' : GL (Fin V'.rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    (hr : a.D.R.r ≤ V.rank) (hr' : a'.D.R.r ≤ V'.rank)
    {Pg Q : Finset (Pl a.D.host.E)} {Pg' Q' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg) (hQ : Q = ∅) (hQ' : Q' = ∅)
    {chi xi : ∀ PP : Pl a.D.host.E, (kP PP)ˣ →* ℂˣ} {chi' xi' : ∀ PP : Pl a'.D.host.E, (kP PP)ˣ →* ℂˣ}
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (chi' PP') (chi PP))
    {I I' : Type} [Fintype I] [Fintype I'] {y : I → Bridge.Gf V} {y' : I' → Bridge.Gf V'}
    (hy : RP V β (datC V hr Pg Q chi xi) y) (hy' : RP V' β' (datC V' hr' Pg' Q' chi' xi') y')
    {H H'} (hH : HEq H' H) {ν ν'} (hν : HEq ν' ν) {fd fd'} (hfd : HEq fd' fd)
    (h0 : MV V c β (datC V hr Pg Q chi xi) y H ν fd) : MV V' c' β' (datC V' hr' Pg' Q' chi' xi') y' H' ν' fd' := by
  subst hQ hQ'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (ν')) ((by with_unfolding_all exact ((ν) :))) (ν') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ν')) (ν') (((ν))) (((hν)))).symm : _))
  clear (hν)
  subst e))
  ( (
  have e : @Eq (type_of% (fd')) ((by with_unfolding_all exact ((fd) :))) (fd') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fd')) (fd') (((fd))) (((hfd)))).symm : _))
  clear (hfd)
  subst e))
  have e : ∀ PP : Pl a.D.host.E, PP ∈ Pg → HEq (chi' ((by with_unfolding_all exact (PP :)))) (chi PP) :=
    fun PP hm => hchi ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  exact (by with_unfolding_all exact ((mv_move V c hc β hr Pg chi xi ((by with_unfolding_all exact (chi' :))) ((by with_unfolding_all exact (xi' :))) (fun PP hm => eq_of_heq ((by with_unfolding_all exact ((e PP hm) :)))) y (I' := I') ((by with_unfolding_all exact (y' :))) hy ((by with_unfolding_all exact (hy' :))) H ν fd h0) :))

private theorem beta_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Vc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Vc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β) :
    HEq (β' i') (β i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (β i)) :))

variable {G G' : Type} [iG : Group G] [Fintype G] [iG' : Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private theorem modV_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (hβ : HEq R'.βV R.βV) (hPg : HEq R'.Pg R.Pg) (hQ : R.Q t = ∅) (hQ' : R'.Q t' = ∅)
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (R.chi ((i : ℕ) + 1) PP))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hν : HEq (R'.νV i' t') (R.νV i t)) (hfd : HEq (R'.fdV i' t') (R.fdV i t))
    (hm : R.IsModels) :
    (R'.HV i' t').Is (Bridge.AdForms (Bridge.ratF (Vc a'.D i')) (R'.cV i').coef.ρ (levEnv _ (R'.βV i') (R'.datVt i' t')).J
      (levEnv _ (R'.βV i') (R'.datVt i' t')).χ)
    (Bridge.adInner (Bridge.ratF (Vc a'.D i')) (levEnv _ (R'.βV i') (R'.datVt i' t')).J (R'.B.L i' t').pres.y) ∧
  IsMeasDef (Vc a'.D i') (lev a'.D.sp.cm (Vc a'.D i').gram (R'.βV i') (R'.datVt i' t')) (R'.νV i' t') (R'.fdV i' t') :=
  mv_of hP (LiftExt.vc_heq hP h) c1 c2 c3 c4 (hm.cV i) (beta_heq hP h hβ) (r_le_V i) (r_le_V i') hPg hQ hQ' hchi
    (xi := R.xiR t) (xi' := R'.xiR t') (y := (R.B.L i t).pres.y) (y' := (R'.B.L i' t').pres.y)
    (R.B.L i t).pres.reps (R'.B.L i' t').pres.reps hHV hν hfd ⟨hm.HV i t, hm.νV i t⟩

end Comparison₂

end GlobalTheory.Mem.R3.Rw.ModVExt

end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → R'.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 → RSide z Wt' R' → LevSame z Wt' R' → ModVAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE _ hS hL i'
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  obt ⟨⟨-, -, -, -, -, -, hβ, -, -, hPg, -, -, h1, -⟩, h2⟩ := hS
  obt ⟨c1, c2, c3, c4, -⟩ := h1 i i' h
  obt ⟨-, -, hHV, -, -, hν, hfd⟩ := h2 i i' h
  exact ModVExt.modV_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h hβ hPg hL.2.2.2 hL.2.2.1 c1 c2 c3 c4
    (hL.1 i i' h).2 hHV hν hfd z.pins.char.base.models
