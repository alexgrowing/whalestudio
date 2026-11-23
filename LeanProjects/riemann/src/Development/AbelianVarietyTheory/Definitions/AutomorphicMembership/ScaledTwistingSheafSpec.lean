import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

structure CDiv (X : Scheme.{0}) : Type where

  pos : X.IdealSheafData

  neg : X.IdealSheafData
  pos_cart : FinalTheorems.EffCartier pos
  neg_cart : FinalTheorems.EffCartier neg

namespace CDiv

variable {X X' : Scheme.{0}}

def ofEff (C : EffCartierData X) : CDiv X :=
  ⟨C.idealSheaf, (EffCartierData.zero X).idealSheaf, C.effCartier_idealSheaf, (EffCartierData.zero X).effCartier_idealSheaf⟩

def opp (B : CDiv X) : CDiv X := ⟨B.neg, B.pos, B.neg_cart, B.pos_cart⟩

def Eff (B : CDiv X) : Prop := B.pos ≤ B.neg

def ZeroAt (B : CDiv X) (g : X' ⟶ X) (x : X') : Prop := FinalTheorems.stalkId (B.pos.comap g) x = FinalTheorems.stalkId (B.neg.comap g) x

def PosAt (B : CDiv X) (g : X' ⟶ X) (x : X') : Prop := FinalTheorems.stalkId (B.pos.comap g) x < FinalTheorems.stalkId (B.neg.comap g) x

def AmpleTw (B : CDiv X) (g : X' ⟶ X) (L : LB X') : Prop :=
  ∃ C₁ C₂ : EffCartierData X', C₁.idealSheaf = B.pos.comap g ∧ C₂.idealSheaf = B.neg.comap g ∧
    IsAmpleLB (GlobalTheory.CechPic.tens (GlobalTheory.CechPic.tens L C₂.lb) (GlobalTheory.CechPic.dual C₁.lb))

theorem idealSheaf_zero (X : Scheme.{0}) : (EffCartierData.zero X).idealSheaf = ⊤ := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [(EffCartierData.zero X).ideal_idealSheaf U PUnit.unit le_top]
  exact Ideal.span_singleton_eq_top.2 (isUnit_one.map _)

theorem eff_ofEff (C : EffCartierData X) : (ofEff C).Eff := by
  change C.idealSheaf ≤ (EffCartierData.zero X).idealSheaf
  rw [idealSheaf_zero]; exact le_top

theorem stalkId_comap_eq_top (I : X.IdealSheafData) (g : X' ⟶ X) (x : X') :
    FinalTheorems.stalkId (I.comap g) x = ⊤ ↔ g x ∉ I.support := by
  rw [← not_iff_not, not_not, ← ne_eq, ← mem_support_iff_stalkId, Scheme.IdealSheafData.support_comap]
  rfl

theorem posAt_ofEff (C : EffCartierData X) (g : X' ⟶ X) (x : X') :
    (ofEff C).PosAt g x ↔ g x ∈ C.idealSheaf.support := by
  have h : FinalTheorems.stalkId ((ofEff C).neg.comap g) x = ⊤ :=
    (stalkId_comap_eq_top _ g x).2 (by change _ ∉ (EffCartierData.zero X).idealSheaf.support; rw [idealSheaf_zero, Scheme.IdealSheafData.support_top]; exact fun h => h)
  rw [PosAt, h, lt_top_iff_ne_top, ne_eq, stalkId_comap_eq_top, not_not]
  rfl

theorem zeroAt_ofEff (C : EffCartierData X) (g : X' ⟶ X) (x : X') :
    (ofEff C).ZeroAt g x ↔ g x ∉ C.idealSheaf.support := by
  have h : FinalTheorems.stalkId ((ofEff C).neg.comap g) x = ⊤ :=
    (stalkId_comap_eq_top _ g x).2 (by change _ ∉ (EffCartierData.zero X).idealSheaf.support; rw [idealSheaf_zero, Scheme.IdealSheafData.support_top]; exact fun h => h)
  rw [ZeroAt, h, stalkId_comap_eq_top]
  rfl

theorem eff_opp_ofEff (C : EffCartierData X) : (ofEff C).opp.Eff ↔ C.idealSheaf = ⊤ := by
  change (EffCartierData.zero X).idealSheaf ≤ C.idealSheaf ↔ _
  rw [idealSheaf_zero, top_le_iff]

end CDiv

def LogBd {X Q : Scheme.{0}} (D : LB X) (ι : Q ⟶ X) (w : (D.pull ι).Gen) (p : ℕ) (δ : ℝ) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C], ‖(p : C)‖ = (p : ℝ)⁻¹ →
    ∀ (z : Sp ↥(intO C) ⟶ X) (y : Sp C ⟶ Q), y ≫ ι = spMap (intO C).subtype ≫ z → ∀ i : D.ι, ⊤ ≤ z ⁻¹ᵁ D.U i →
      |Real.log ‖valF y _ (w.s fun _ => i).val‖| ≤ δ

theorem norm_valF_unit {X : Scheme.{0}} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (z : Sp ↥(intO C) ⟶ X) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    ‖valF (spMap (intO C).subtype ≫ z) U u.val‖ = 1 := by
  have h' : ⊤ ≤ (spMap (intO C).subtype ≫ z) ⁻¹ᵁ U := fun x _ => h (Set.mem_univ _)
  let ev : Γ(X, U) →+* ↥(intO C) := (Scheme.ΓSpecIso (CommRingCat.of ↥(intO C))).hom.hom.comp (z.appLE U ⊤ h).hom
  have e : ∀ a, valF (spMap (intO C).subtype ≫ z) U a = (ev a : C) := fun a => by
    rw [valF, dif_pos h']
    have e1 : (spMap (intO C).subtype ≫ z).appLE U ⊤ h' = z.appLE U ⊤ h ≫ (spMap (intO C).subtype).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE (spMap (intO C).subtype) z U ⊤ ⊤ h le_top).symm
    rw [e1]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (intO C).subtype)) _
  rw [e]
  have h1 : ‖(ev u.val : C)‖ ≤ 1 := (ev u.val).2
  have h2 : ‖(ev u.inv : C)‖ ≤ 1 := (ev u.inv).2
  have h3 : ‖(ev u.val : C)‖ * ‖(ev u.inv : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, ← map_mul, u.val_inv, map_one, Subring.coe_one, norm_one]
  nlinarith [norm_nonneg (ev u.val : C), norm_nonneg (ev u.inv : C)]

theorem logBd_pullGenLB {X Q : Scheme.{0}} {D : LB X} (t : D.Gen) (ι : Q ⟶ X) (p : ℕ) :
    LogBd D ι (pullGenLB t ι) p 0 := fun C _ _ _ z y hy i hi => by
  have h' : ⊤ ≤ (y ≫ ι) ⁻¹ᵁ D.U i := by rw [hy]; exact fun x _ => hi (Set.mem_univ _)
  have hle : (D.pull ι).U (fun _ => i) ≤ ι ⁻¹ᵁ D.U i := fun _ hx => Set.mem_iInter.1 hx PUnit.unit
  have h : ⊤ ≤ y ⁻¹ᵁ (D.pull ι).U (fun _ => i) := fun x _ => Set.mem_iInter.2 fun _ => h' (Set.mem_univ x)
  have e : valF y _ ((pullGenLB t ι).s fun _ => i).val = valF (y ≫ ι) _ (t.s i).val :=
    GlobalTheory.MatchCoord.valF_appLE ι (D.U i) hle h _
  rw [e, hy, norm_valF_unit z _ hi, Real.log_one, abs_zero]

theorem LogBd.mono {X Q : Scheme.{0}} {D : LB X} {ι : Q ⟶ X} {w : (D.pull ι).Gen} {p : ℕ} {δ δ' : ℝ}
    (h : LogBd D ι w p δ) (hδ : δ ≤ δ') : LogBd D ι w p δ' :=
  fun C _ _ hp z y hy i hi => (h C hp z y hy i hi).trans hδ

def FinLB.pull {X X' : Scheme.{0}} (L : FinLB X) (f : X' ⟶ X) : FinLB X' where
  n := L.n
  U i := (L.lb.pull f).U fun _ => i
  g i k := (L.lb.pull f).g (fun _ => i) fun _ => k
  isLB := have h := LB.isLB_pull L.isLB f
    ⟨top_le_iff.1 (h.cover.ge.trans (iSup_le fun i => le_iSup_of_le (i PUnit.unit) le_rfl)),
      fun _ => h.g_self _, fun _ _ _ => h.cocycle _ _ _⟩

theorem FinLB.lbIso_pull {X X' : Scheme.{0}} (L : FinLB X) (f : X' ⟶ X) : LBIso (L.pull f).lb (L.lb.pull f) :=
  have h := LB.isLB_pull L.isLB f
  LBIso.chartPull (h := 𝟙 X') (A := L.lb.pull f) (B := L.lb.pull f) ⟨fun i _ => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩
    ⟨fun i => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩ ((GlobalTheory.CechPic.cls_eq_iff h h).1 rfl)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {l : Level H}

abbrev GModel (Xo : ∀ l : Level H, Moduli Dw l) (c : Coeff l) : Type 1 :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo l) c (algebraMap (𝓞 c.F) c.F)

def DomLoc (Y : LocFam Xo) {c : Coeff l} (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Z : GModel Xo c) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
    (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Z (Y p W hp hW ⟨l, c, hg p hp⟩) b

theorem dominates_tor {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo l) c β} (T : TorModel Z) {Y' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo l) c β'}
    {b : O →+* O'} (h : Dominates Z Y' b) : Dominates T.Z Y' b := by
  obtain ⟨f, t, m₁, m₂, hf, hj, hφ⟩ := h
  let q : pullback T.Z.s (spMap b) ⟶ pullback Z.s (spMap b) :=
    pullback.lift (pullback.fst _ _ ≫ T.b) (pullback.snd _ _) (by rw [Category.assoc, T.b_s, pullback.condition])
  have q1 : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ T.b := pullback.lift_fst _ _ _
  have q2 : q ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨t', ⟨n⟩⟩ := exists_sab q t
  obtain ⟨n₂, e₂⟩ := ObjMaps.exists_sab_comp m₂ n
  obtain ⟨n₁, e₁⟩ : ∃ k : SABMap t' Z.t (pullback.fst _ _ ≫ T.b), k.φ = n.φ ≫ m₁.φ :=
    q1 ▸ ObjMaps.exists_sab_comp m₁ n
  obtain ⟨n₀, e₀⟩ := ObjMaps.exists_sab_cancel T.pull n₁
  refine ⟨q ≫ f, t', n₀, n₂, by rw [Category.assoc, hf, q2], fun a ha => ?_, fun S g g₁ g₂ h₁ h₂ h₃ => ?_⟩
  · rw [← Category.assoc]
    exact hj _ (by rw [Category.assoc, q1, ← Category.assoc, ha, T.j_b])
  · have c₁ := T.Z.m0.toSABMap.cart.1
    have c₂ := Z.m0.toSABMap.cart.1
    have w : (g₁ ≫ T.Z.m0.toSABMap.φ) ≫ (Xo l).univ.t.G.hom = (g₁ ≫ T.Z.oF.t.G.hom) ≫ pullback.fst _ _ := by
      rw [Category.assoc, Category.assoc, c₁.w]
    have l₁ := c₂.lift_fst _ _ w
    have l₂ := c₂.lift_snd _ _ w
    rw [e₂, ← Category.assoc]
    refine hφ S _ (c₂.lift _ _ w) g₂ ?_ (l₁.trans h₂) (l₂.trans h₃)
    rw [Category.assoc, ← e₁, e₀, ← Category.assoc, h₁, Category.assoc]
    exact T.pull_univ S _ _ l₁.symm l₂.symm

structure PreCode (Xo : ∀ l : Level H, Moduli Dw l) (c : Coeff l) : Type where

  n : ℕ

  I : (PSpace (𝓞 c.F) n).IdealSheafData

  j : (Xo l).XF c ⟶ I.subscheme

variable {Y : LocFam Xo} {c : Coeff l} {hg : ∀ p : ℕ, p.Prime → l.GoodAt p}

namespace PreCode

variable (Z : PreCode Xo c)

abbrev X : Scheme.{0} := Z.I.subscheme

def s : Z.X ⟶ Sp (𝓞 c.F) := Z.I.subschemeι ≫ PSpace.str _ Z.n

def Iso (Z' : GModel Xo c) (e : Z'.X ≅ Z.X) : Prop := e.hom ≫ Z.s = Z'.s ∧ Z'.j ≫ e.hom = Z.j

abbrev gen : Scheme.{0} := pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F))

abbrev genι : Z.gen ⟶ Z.X := pullback.fst _ _

abbrev genStr : Z.gen ⟶ Sp c.F := pullback.snd _ _

theorem proj : IsProjOver Z.s := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩

end PreCode

theorem exists_preCode (Z' : GModel Xo c) : ∃ (Z : PreCode Xo c) (e : Z'.X ≅ Z.X), Z.Iso Z' e := by
  obtain ⟨n, i, hi, e⟩ := Z'.proj
  have : IsIso i.toImage := inferInstance
  refine ⟨⟨n, i.ker, Z'.j ≫ i.toImage⟩, asIso i.toImage, ?_, rfl⟩
  change i.toImage ≫ i.imageι ≫ _ = _
  rw [← Category.assoc, i.toImage_imageι, e]

structure Code (Y : LocFam Xo) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) : Type extends PreCode Xo c where
  ex : ∃ (Z' : GModel Xo c) (e : Z'.X ≅ toPreCode.X), toPreCode.Iso Z' e ∧ DomLoc Y hg Z'

theorem exists_code (Z' : GModel Xo c) (h : DomLoc Y hg Z') :
    ∃ (Z : Code Y c hg) (e : Z'.X ≅ Z.X), Z.Iso Z' e := by
  obtain ⟨Z, e, he⟩ := exists_preCode Z'
  exact ⟨⟨Z, Z', e, he, h⟩, e, he⟩

theorem exists_code_tor {Z' : GModel Xo c} (h : DomLoc Y hg Z') (T : TorModel Z') :
    ∃ (Z : Code Y c hg) (e : T.Z.X ≅ Z.X), Z.Iso T.Z e :=
  exists_code T.Z fun p W hp hW b hb => dominates_tor T (h p W hp hW b hb)

namespace Code

variable (Z : Code Y c hg)

theorem normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z.X := fun x => by
  obtain ⟨Z', e, -, -⟩ := Z.ex
  have h := Z'.normal (e.inv x)
  let r := (asIso (e.inv.stalkMap x)).commRingCatIsoToRingEquiv
  have := h.1
  have := h.2
  exact ⟨r.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv r⟩

theorem flat : Flat Z.s := by
  obtain ⟨Z', e, he, -⟩ := Z.ex
  have := Z'.flat
  rw [← e.inv_hom_id_assoc Z.s, he.1]
  infer_instance

def NoVert (B : CDiv Z.X) : Prop :=
  ∀ x : Z.X, ringKrullDim (Z.X.presheaf.stalk x) = 1 → ¬ CharZero (Z.X.residueField x) → B.ZeroAt (𝟙 _) x

def PosBd (B : CDiv Z.X) : Prop :=
  ∃ (Z' : GModel Xo c) (T : TorModel Z') (g : gen T.Z ⟶ Z.X),
    g ≫ Z.s = genStr T.Z ≫ spMap (algebraMap (𝓞 c.F) c.F) ∧ T.Z.jQ ≫ g = Z.j ∧
    ∀ x : gen T.Z, ringKrullDim ((gen T.Z).presheaf.stalk x) = 1 →
      (x ∈ genBd T.Z → B.PosAt g x) ∧ (x ∉ genBd T.Z → B.ZeroAt g x)

def AmpleHodge (m : ℕ) (B : CDiv Z.X) : Prop :=
  ∃ (Z' : GModel Xo c) (e : Z'.X ≅ Z.X), Z.Iso Z' e ∧ B.AmpleTw e.hom (lbPow (GlobalTheory.FlagMod.detOm Z') m)

theorem ampleHodge_of_ample {Z' : GModel Xo c} (T : TorModel Z') (h : IsRecTor T) (e : T.Z.X ≅ Z.X) (he : Z.Iso T.Z e)
    {B : CDiv Z.X} (h₁ : B.pos.comap e.hom = T.BD.idealSheaf) (h₂ : B.neg = ⊤) : Z.AmpleHodge T.m0 B := by
  refine ⟨T.Z, e, he, T.BD, .zero _, h₁.symm, by rw [h₂, CDiv.idealSheaf_zero, Scheme.IdealSheafData.comap_top], ?_⟩
  have a := isLB_lbPow h.isLB_detOm T.m0
  have z := (EffCartierData.zero T.Z.X).isLB_lb
  have d := GlobalTheory.CechPic.isLB_dual T.BD.isLB_lb
  have z0 : GlobalTheory.CechPic.cls _ z = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff z).2 ⟨⟨fun _ => 1⟩, fun i j => by
    have : (1 : Γ(T.Z.X, _)ˣ) = (EffCartierData.zero T.Z.X).trans i j :=
      (EffCartierData.zero T.Z.X).eq_trans i j (one_mul _).symm
    exact (map_one _).trans ((mul_one _).symm.trans (congrArg₂ (· * ·) this (map_one _).symm))⟩
  have l := GlobalTheory.CechPic.isLB_tens (GlobalTheory.CechPic.isLB_tens a z) d
  refine h.ample.of_lbIso l ((GlobalTheory.CechPic.cls_eq_iff l h.ample.isLB).1 ?_)
  exact (GlobalTheory.CechPic.cls_tens (GlobalTheory.CechPic.isLB_tens a z) d _).trans (Eq.trans
    (by rw [GlobalTheory.CechPic.cls_tens a z, z0, add_zero]) (GlobalTheory.CechPic.cls_tens a d _).symm)

theorem exists_eff_posBd {Z' : GModel Xo c} (T : TorModel Z') (e : T.Z.X ≅ Z.X) (he : Z.Iso T.Z e) :
    ∃ B : CDiv Z.X, B.pos.comap e.hom = T.BD.idealSheaf ∧ B.neg = ⊤ ∧ B.Eff ∧ Z.PosBd B := by
  let C := T.BD.pull e.inv (T.BD.keepsRegular_of_flat _)
  have hC : C.idealSheaf = T.BD.idealSheaf.comap e.inv := T.BD.idealSheaf_pull _ _
  have hs : ∀ x, e.hom x ∈ C.idealSheaf.support ↔ x ∈ T.BD.idealSheaf.support := fun x => by
    rw [hC, Scheme.IdealSheafData.support_comap]
    change e.inv (e.hom x) ∈ T.BD.idealSheaf.support ↔ _
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  refine ⟨.ofEff C, ?_, CDiv.idealSheaf_zero _, CDiv.eff_ofEff C, Z', T, genι T.Z ≫ e.hom, ?_, ?_,
    fun x _ => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · change C.idealSheaf.comap e.hom = _
    rw [hC, ← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]
  · rw [Category.assoc, he.1, pullback.condition]
  · rw [← Category.assoc]; exact he.2
  · exact (CDiv.posAt_ofEff _ _ _).2 ((hs _).2 (T.BD_pos x hx))
  · exact (CDiv.zeroAt_ofEff _ _ _).2 fun h => hx (mem_genBd_iff.2 (T.BD_supp _ ((hs _).1 h)))

section BC

variable {p : ℕ} {W : ValuationSubring ℂ} {hp : p.Prime} {hW : (p : ℂ) ∈ W.nonunits}

def IsBC (Z' : Mdl (Y p W hp hW) ⟨l, c, hg p hp⟩) : Prop :=
  ∃ hi : Z'.i = ⟨l, c, hg p hp⟩, (∀ σ, Z'.ty σ = ∅) ∧
    ∃ (b : 𝓞 c.F →+* Z'.i.c.V W) (ν : Z'.X ⟶ pullback Z.s (spMap b)),
      (∀ x, (((b x : Z'.i.c.V W) : Z'.i.c.F) : ℂ) = ((x : c.F) : ℂ)) ∧ IsFinite ν ∧ ν ≫ pullback.snd _ _ = Z'.s ∧
      pullback.fst Z'.π (Y p W hp hW Z'.i).j ≫ ν ≫ pullback.fst _ _ =
        pullback.snd Z'.π (Y p W hp hW Z'.i).j ≫ eqToHom (congrArg (fun i : Idx H p => (Xo i.l).XF i.c) hi) ≫ Z.j

end BC

end Code

structure QLB (Y : LocFam Xo) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) : Type where

  Z : Code Y c hg

  L : FinLB Z.X

  m : ℕ
  m_pos : 0 < m

namespace QLB

variable (M : QLB Y c hg)

def NefFib : Prop :=
  ∀ (P : Ideal (𝓞 c.F)) [P.IsPrime],
    letI := algebraΓOfHom (pullback.snd M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField)))
    IsNef P.ResidueField (M.L.lb.pull (pullback.fst M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField))))

def AmpleGen : Prop := IsAmpleLB (M.L.lb.pull M.Z.genι)

def LimRA : Prop :=
  ∃ T : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ (X' : Scheme.{0}) (b : X' ⟶ M.Z.X) (ι : M.Z.gen ⟶ X') (k : ℕ) (L' : LB X')
    (w : ((LB.div L' (lbPow (M.L.lb.pull b) k)).pull ι).Gen),
    IsProjOver (b ≫ M.Z.s) ∧ Flat (b ≫ M.Z.s) ∧
    IsPullback ι M.Z.genStr (b ≫ M.Z.s) (spMap (algebraMap (𝓞 c.F) c.F)) ∧ ι ≫ b = M.Z.genι ∧
    0 < k ∧ IsAmpleLB L' ∧ w.IsGen ∧
    ∀ p : ℕ, p.Prime → LogBd _ ι w p (if p ∈ T then ε * (k * M.m) else 0)

variable {M}

theorem nefFib_of_ample (h : IsAmpleLB M.L.lb) : M.NefFib := fun P _ =>
  letI := algebraΓOfHom (pullback.snd M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField)))
  haveI := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField))).flip inferInstance
  (h.pull_of_isAffineHom _).isNef

theorem ampleGen_of_ample (h : IsAmpleLB M.L.lb) : M.AmpleGen :=
  haveI := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback M.Z.s (spMap (algebraMap (𝓞 c.F) c.F))).flip inferInstance
  h.pull_of_isAffineHom _

theorem limRA_of_ample (h : IsAmpleLB M.L.lb) : M.LimRA := by
  have hA : IsAmpleLB (lbPow (M.L.lb.pull (𝟙 _)) 1) :=
    (isAmpleLB_pow_iff (LB.isLB_pull h.isLB _) le_rfl).2 (h.pull_of_isAffineHom _)
  obtain ⟨t, ht⟩ : LBIso (lbPow (M.L.lb.pull (𝟙 _)) 1) (lbPow (M.L.lb.pull (𝟙 _)) 1) :=
    (GlobalTheory.CechPic.cls_eq_iff hA.isLB hA.isLB).1 rfl
  refine ⟨∅, fun ε _ => ⟨M.Z.X, 𝟙 _, M.Z.genι, 1, _, pullGenLB t _, ?_, ?_, ?_, Category.comp_id _, one_pos, hA,
    pullGenLB_isGen ht _, fun p _ => ?_⟩⟩
  · rw [Category.id_comp]; exact M.Z.proj
  · rw [Category.id_comp]; exact M.Z.flat
  · rw [Category.id_comp]; exact IsPullback.of_hasPullback _ _
  · rw [if_neg (Finset.notMem_empty p)]; exact logBd_pullGenLB t _ p

open GlobalTheory.CechPic in

theorem LimRA.ampleGen (h : M.LimRA) : M.AmpleGen := by
  obtain ⟨_, h⟩ := h
  obtain ⟨X', b, ι, k, L', w, -, -, hp, hι, hk, hL, hw, -⟩ := h 1 one_pos
  have : IsAffineHom ι := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  have h₀ := M.L.isLB
  have h₁ := LB.isLB_pull h₀ b
  have h₂ := isLB_lbPow h₁ k
  have h₃ := LB.isLB_div hL.isLB h₂
  have h₄ := LB.isLB_pull h₀ M.Z.genι
  have e := (cls_eq_zero_iff (LB.isLB_pull h₃ ι)).2 ⟨w, hw⟩
  rw [cls_pull h₃, cls_div hL.isLB h₂, cls_lbPow h₁, cls_pull h₀, map_sub, map_nsmul, ← pull_comp, hι, sub_eq_zero] at e
  refine (isAmpleLB_pow_iff h₄ hk).1 ((hL.pull_of_isAffineHom ι).of_lbIso (isLB_lbPow h₄ k)
    ((cls_eq_iff (isLB_lbPow h₄ k) (LB.isLB_pull hL.isLB ι)).1 ?_))
  rw [cls_lbPow h₄, cls_pull h₀, cls_pull hL.isLB, e]

def scaledTwistingSheaf (Z : Code Y c hg) (m : ℕ) : QLB Y c hg :=
  ⟨Z, FinLB.pull ⟨Z.n + 1, (GlobalTheory.ProjSpace.O1 _ Z.n).U, (GlobalTheory.ProjSpace.O1 _ Z.n).g, GlobalTheory.ProjSpace.O1_isLB _ Z.n⟩
    Z.I.subschemeι, m + 1, m.succ_pos⟩

theorem scaledTwistingSheaf_spec (Z : Code Y c hg) (m : ℕ) : (scaledTwistingSheaf Z m).NefFib ∧ (scaledTwistingSheaf Z m).AmpleGen ∧ (scaledTwistingSheaf Z m).LimRA :=
  have h : IsAmpleLB (scaledTwistingSheaf Z m).L.lb :=
    ((isAmple_projective_O_one _ Z.n).pull_of_isAffineHom Z.I.subschemeι).of_lbIso (scaledTwistingSheaf Z m).L.isLB (FinLB.lbIso_pull _ _)
  ⟨nefFib_of_ample h, ampleGen_of_ample h, limRA_of_ample h⟩

end QLB

end Free

variable {D : D7} {A : Amb D} {N j : ℕ}

abbrev CodeAt (S : Sig A N j) (κ : Lv A) : Type := Code S.sys.Y κ.c κ.good

def IsBCAt {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) (Z' : ct.Mdl) : Prop :=
  Z.IsBC (hp := ct.hp) (hW := ct.hW) Z'

open Classical in

def bcOf {S : Sig A N j} {κ : Lv A} {M : ℕ → Type} (dflt : ∀ p, M p) (a : ∀ p, p.Prime → At S κ p)
    (emb : ∀ p hp, (a p hp).Mdl → M p) (p : ℕ) (Z : CodeAt S κ) : M p :=
  if hp : p.Prime then
    if h : ∃ Z', IsBCAt (a p hp) Z Z' then emb p hp h.choose else dflt p
  else dflt p

theorem bcOf_eq {S : Sig A N j} {κ : Lv A} {M : ℕ → Type} (dflt : ∀ p, M p) (a : ∀ p, p.Prime → At S κ p)
    (emb : ∀ p hp, (a p hp).Mdl → M p) {p : ℕ} (hp : p.Prime) (Z : CodeAt S κ) (h : ∃ Z', IsBCAt (a p hp) Z Z') :
    bcOf dflt a emb p Z = emb p hp h.choose := by
  classical
  have e : bcOf dflt a emb p Z = if h : ∃ Z', IsBCAt (a p hp) Z Z' then emb p hp h.choose else dflt p := by
    delta bcOf
    exact dif_pos hp
  exact e.trans (dif_pos h)

theorem choose_eq_blowUp {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) (X : ct.Mdl) (J : ct.Idl X)
    (h : ∃ Z', IsBCAt ct Z Z') (hJ : ∀ Z', IsBCAt ct Z Z' ↔ IsNBlow X J Z') : h.choose = ct.blowUp X J := by
  have key : ∀ {α : Type} {P Q : α → Prop} (_ : P = Q) (h : ∃ x, P x) (h' : ∃ x, Q x), h.choose = h'.choose :=
    fun e _ _ => by subst e; rfl
  have h' : ∃ Z', IsNBlow X J Z' := h.imp fun Z' => (hJ Z').1
  have e₂ : GlobalTheory.LocM.blowUp X J = h'.choose := by
    delta GlobalTheory.LocM.blowUp
    exact dif_pos h'
  exact (key (funext fun Z' => propext (hJ Z')) h h').trans e₂.symm

def globSt (S : Sig A N j) (κ : Lv A) (M : ℕ → Type) (dflt : ∀ p, M p) (a : ∀ p, p.Prime → At S κ p)
    (emb : ∀ p hp, (a p hp).Mdl → M p) : GlobSt M where
  Xg := CodeAt S κ
  bc := bcOf dflt a emb
  DivG Z := CDiv Z.X
  effD B := B.Eff
  noVertD {Z} B := Z.NoVert B
  posBdD {Z} B := Z.PosBd B
  ampleOnAbelianBase Z m B := Z.AmpleHodge m B
  Met := QLB S.sys.Y κ.c κ.good
  nefFibM := QLB.NefFib
  ampleGen := QLB.AmpleGen
  limRA := QLB.LimRA

theorem exists_codeAt_iso_with_positive_ample_divisor {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) :
    ∃ (Z : CodeAt S κ) (e : s.T.Z.X ≅ Z.X) (B : CDiv Z.X), Z.Iso s.T.Z e ∧ B.pos.comap e.hom = s.T.BD.idealSheaf ∧
      B.neg = ⊤ ∧ B.Eff ∧ Z.PosBd B ∧ Z.AmpleHodge s.T.m0 B := by
  obtain ⟨Z, e, he⟩ := exists_code_tor (Y := S.sys.Y) (hg := κ.good) s.glob.2.1 s.T
  obtain ⟨B, h₁, h₂, h₃, h₄⟩ := Z.exists_eff_posBd s.T e he
  exact ⟨Z, e, B, he, h₁, h₂, h₃, h₄, Z.ampleHodge_of_ample s.T s.isRec e he h₁ h₂⟩

instance nonempty_codeAt (S : Sig A N j) (κ : Lv A) : Nonempty (CodeAt S κ) :=
  (exists_code (Y := S.sys.Y) _ (S.tor.glob κ.l κ.c κ.good).2.1).elim fun Z _ => ⟨Z⟩

example (S : Sig A N j) (κ : Lv A) : ∃ M : QLB S.sys.Y κ.c κ.good, M.NefFib ∧ M.AmpleGen ∧ M.LimRA :=
  (nonempty_codeAt S κ).elim fun Z => ⟨_, QLB.scaledTwistingSheaf_spec Z 0⟩

example {S : Sig A N j} {κ : Lv A} (Z : CodeAt S κ) :
    (CDiv.ofEff (.zero Z.X)).Eff ∧ Z.NoVert (.ofEff (.zero Z.X)) :=
  ⟨CDiv.eff_ofEff _, fun _ _ _ => rfl⟩

end GlobalTheory.ShFam.Pad
