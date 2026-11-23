import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FullLevelModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaOfPushInvertible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Models GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel

noncomputable section

namespace GlobalTheory.ModelTypings

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H}

def fullPull {N : ℕ} {B : Type} [CommRing B] {ρ ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N ρ ζ s) {f : S' ⟶ S} {t' : SAB H S'} (m : SABMap t' o.t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hlv : ∀ a, (lv a).left ≫ m.φ = f ≫ (o.lev a).left) {s' : S' ⟶ Sp B}
    (hs : f ≫ s = s') : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N ρ ζ s' :=
  have hlv' : ∀ a, lv a = GlobalTheory.ObjPull.secPull m.cart (o.lev a) := fun a => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · exact (hlv a).trans (GlobalTheory.ObjPull.secPull_left m.cart _).symm
    · rw [Over.w, Over.w]
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    lev := lv
    lev_add := fun a c => by rw [hlv', hlv', hlv', o.lev_add, map_mul]
    lev_lin := fun c a => by
      apply Over.OverMorphism.ext
      apply m.cart.1.hom_ext
      · refine (hlv _).trans ?_
        rw [o.lev_lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ _) (hlv a).symm
      · rw [Over.w, Over.w]
    lev_ker := fun a => by rw [hlv', o.lev_ker a, map_one]
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨h₁, h₂, h₃⟩ := o.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
      obtain ⟨e, he⟩ := LevelFibre.exists_ptEquiv m.cart x _ rfl
      have hl : ∀ a, e (toUnit _ ≫ lv a) = toUnit _ ≫ o.lev a := fun a => by
        apply Over.OverMorphism.ext
        rw [he, LevelFibre.unit_left, LevelFibre.unit_left, Category.assoc, Category.assoc]
        exact congrArg _ (hlv a)
      refine ⟨fun a => by rw [← h₁, ← hl, map_eq_one_iff e e.injective], fun g hg => ?_, fun a b => ?_⟩
      · obtain ⟨a, ha⟩ := h₂ (e g) (by rw [← map_pow, hg, map_one])
        exact ⟨a, e.injective ((hl a).trans ha)⟩
      · refine (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ o.t.PP.isLB t'.PP.isLB m.cart hL
          (Over.mk x) N _ _ (e _) (e _) _ (he _) (he _)).2 ?_
        rw [hl, hl]
        exact h₃ a b
    geom0 := fun k _ _ _ x β hx =>
      (FamAut.geomAt_iff m hlv x _ _).2 (o.geom0 k (x ≫ f) β (by rw [Category.assoc, hs, hx])) }

abbrev inc (H : Host E) (S A : ℕ) : RZ H S A →+* oRing H A S := Subring.inclusion (RZ_eq H S A).le

abbrev inc' (H : Host E) (S A : ℕ) : oRing H A S →+* RZ H S A := Subring.inclusion (RZ_eq H S A).symm.le

instance (S A : ℕ) : IsIso (spMap (inc H S A)) := isIso_incl (RZ_eq H S A)

instance (S A : ℕ) : IsIso (spMap (inc' H S A)) := isIso_incl (RZ_eq H S A).symm

theorem isInc_incl {R R' : Subring ℂ} (h : R ≤ R') : IsInc R.subtype R'.subtype (Subring.inclusion h) := fun _ => rfl

theorem isInc_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {i : R →+* ℂ} {i' : R' →+* ℂ}
    {i'' : R'' →+* ℂ} {a : R →+* R'} {b : R' →+* R''} (hb : IsInc i' i'' b) (ha : IsInc i i' a) :
    IsInc i i'' (b.comp a) := fun x => (hb _).trans (ha x)

theorem isInc_unique {R R' : Type} [CommRing R] [CommRing R'] {i : R →+* ℂ} {i' : R' →+* ℂ} {a b : R →+* R'}
    (hi : Function.Injective i') (ha : IsInc i i' a) (hb : IsInc i i' b) : a = b :=
  RingHom.ext fun x => hi ((ha x).trans (hb x).symm)

theorem oRt_coe (N c : ℕ) : ((oRt H N c : oRing H N c) : ℂ) = H.rt0 := by
  show (2 : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem inc'_rt (S A : ℕ) : inc' H S A (oRt H A S) = RZ.rt H S A :=
  Subtype.ext ((Subring.coe_inclusion (RZ_eq H S A).symm.le (oRt H A S)).trans
    ((oRt_coe (H := H) A S).trans (RZ.rt_coe (H := H) S A).symm))

theorem inc'_ze (S A : ℕ) : inc' H S A (oZeta H A S) = RZ.ze H S A :=
  Subtype.ext (Subring.coe_inclusion (RZ_eq H S A).symm.le (oZeta H A S))

theorem fullObj_of_second_typing {n N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (oRing H N n)}
    (o : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) s) :
    Models.FullObj D (s ≫ spMap (inc H n N)) o.t o.lev := by
  refine ⟨o.proper, o.ample, o.ktriv, o.lev_add, o.lev_ker, fun k _ _ _ x β hx => ?_⟩
  have h := o.geom0 k x (β.comp (inc' H n N)) (by
    rw [spMap_comp, ← hx, Category.assoc, Category.assoc, incl_incl (RZ_eq H n N), Category.comp_id])
  rwa [RingHom.comp_apply, RingHom.comp_apply, inc'_rt, inc'_ze] at h

theorem siegData_congr {T : Scheme.{0}} {O O' : Type} [CommRing O] [CommRing O'] {sT : T ⟶ Sp O} {sT' : T ⟶ Sp O'}
    {t : SAB H T} {lev : D.La → (𝟙_ (Over T) ⟶ t.G)} {g p N : ℕ} {Ag : SiegelFamily g p N} {z : ZP p N →+* O}
    {z' : ZP p N →+* O'} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La} {w : T ⟶ pullback Ag.s (spMap z)}
    {w' : T ⟶ pullback Ag.s (spMap z')} (h : SiegData sT' t lev Ag z' bas w') (e : sT' ≫ spMap z' = sT ≫ spMap z)
    (h₁ : w ≫ pullback.fst _ _ = w' ≫ pullback.fst _ _) (h₂ : w ≫ pullback.snd _ _ = sT) :
    SiegData sT t lev Ag z bas w := by
  obtain ⟨o, φ, φ₂, a₁, a₂, a₃, a₄, -, a₅⟩ := h
  unfold SiegData
  rw [h₁]
  generalize sT' ≫ spMap z' = q at e o φ φ₂ a₁ a₂ a₃ a₄ a₅
  subst e
  exact ⟨o, φ, φ₂, a₁, a₂, a₃, a₄, h₂, a₅⟩

def SiegelClauseFullLevel {N n : ℕ} {XX : Scheme.{0}} (w : XX ⟶ Sp (oRing H N n))
    (oX : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) w) : Prop :=
  ∀ (p : ℕ) (hn : n.Coprime p), p.Prime →
    ∃ (Ag : SiegelFamily (gDim D) p N) (bas : (Fin (gDim D) ⊕ Fin (gDim D) → ℤ) ≃ₗ[ℤ] D.La)
      (cl : pullback w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ⟶
        pullback Ag.s (spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
      (o : SiegPre (gDim D) N (zetaZP p N)
        (pullback.snd w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ≫
          spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
      (φ : o.A.left ⟶ oX.t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 oX.t.G).left),
      (∀ a b, D.EF (bas a) (bas b) = omegaStd a b) ∧
      IsGrpPullback o.A oX.t.G (pullback.fst _ _) φ ∧ IsSquare φ φ₂ ∧
      LBIso o.P ((abelian₂ oX.t.G oX.t.PP.L).pull φ₂) ∧
      (∀ a, (o.lev a).left ≫ φ = pullback.fst _ _ ≫ (oX.lev (bas a)).left) ∧
      cl ≫ pullback.snd _ _ = pullback.snd _ _ ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧
      IsFinite cl ∧ FormallyUnramified cl

open GlobalTheory.SiegelPullComp in

theorem ident_iff {g N : ℕ} {B : Type} [CommRing B] {ζ : B} {T X : Scheme.{0}} {s : T ⟶ Sp B} (o : SiegPre g N ζ s)
    {f : T ⟶ X} {t : SAB H X} {t' : SAB H T} (ν : SABMap t' t f) {κ : Type} (σ : κ → (𝟙_ (Over T) ⟶ o.A))
    (lev : κ → (𝟙_ (Over X) ⟶ t.G)) (lv : κ → (𝟙_ (Over T) ⟶ t'.G)) (h : ∀ x, (lv x).left ≫ ν.φ = f ≫ (lev x).left) :
    (∃ (φ : o.A.left ⟶ t'.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t'.G).left), IsGrpPullback o.A t'.G (𝟙 T) φ ∧
      IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t'.G t'.PP.L).pull φ₂) ∧ ∀ u, (σ u).left ≫ φ = (lv u).left) ↔
    ∃ (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left), IsGrpPullback o.A t.G f φ ∧
      IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧ ∀ u, (σ u).left ≫ φ = f ≫ (lev u).left := by
  have hp := ν.cart.1
  obtain ⟨ν₂, hν₂⟩ : ∃ ν₂ : (G2 t'.G).left ⟶ (G2 t.G).left, Geo.Tor.IsSquare ν.φ ν₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hp.w⟩
  have hlam := (GlobalTheory.LamPull.lam_pull E H X T t t' f).2 ν ν₂ hν₂
  have hL : (abelian₂ t.G t.PP.L).IsLB := DVR.linComb_isLB _ t.PP.isLB _ _
  have hL' : (abelian₂ t'.G t'.PP.L).IsLB := DVR.linComb_isLB _ t'.PP.isLB _ _
  have hiso : ∀ F₂ : (G2 o.A).left ⟶ (G2 t'.G).left,
      LBIso ((abelian₂ t'.G t'.PP.L).pull F₂) ((abelian₂ t.G t.PP.L).pull (F₂ ≫ ν₂)) := fun F₂ =>
    (iso_pull F₂ hlam).trans (pull_isLB hL' _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (iso_pull_pull hL ν₂ F₂)
  constructor
  · rintro ⟨F, F₂, h₁, h₂, h₃, h₄⟩
    refine ⟨F ≫ ν.φ, F₂ ≫ ν₂, (h₁.comp ν.cart).congr (Category.id_comp _) rfl, SiegelDataPull.isSquare_comp h₂ hν₂,
      h₃.trans o.isLB (pull_isLB hL' _) (pull_isLB hL _) (hiso F₂), fun u => ?_⟩
    rw [← Category.assoc, h₄]
    exact h u
  · rintro ⟨φ, φ₂, h₁, h₂, h₃, h₄⟩
    let F : o.A.left ⟶ t'.G.left := hp.lift φ (o.A.hom ≫ 𝟙 T) (by rw [Category.comp_id]; exact h₁.1.w)
    have hF : F ≫ ν.φ = φ := hp.lift_fst _ _ _
    have hFw : F ≫ t'.G.hom = o.A.hom ≫ 𝟙 T := hp.lift_snd _ _ _
    obtain ⟨F₂, hF₂⟩ : ∃ F₂ : (G2 o.A).left ⟶ (G2 t'.G).left, Geo.Tor.IsSquare F F₂ :=
      ⟨_, GlobalTheory.LamPull.exists_isSquare hFw⟩
    have e₂ : φ₂ = F₂ ≫ ν₂ := by
      refine GlobalTheory.LamPull.isSquare_unique (φ := φ) h₂ ?_
      have e := SiegelDataPull.isSquare_comp hF₂ hν₂
      rwa [hF] at e
    subst e₂
    refine ⟨F, F₂, ν.cart.cancel (h₁.congr (Category.id_comp _).symm hF.symm) hFw, hF₂,
      h₃.trans o.isLB (pull_isLB hL _) (pull_isLB hL' _) (hiso F₂).symm, fun u => ?_⟩
    apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((h₄ u).trans (h u).symm))
    · have a₁ : (σ u).left ≫ o.A.hom = 𝟙 T := Over.w (σ u)
      have a₂ : (lv u).left ≫ t'.G.hom = 𝟙 T := Over.w (lv u)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((Category.comp_id _).trans (a₁.trans a₂.symm))))

theorem exists_fromLoc {p N n : ℕ} {O : Type} [CommRing O] {i : O →+* ℂ} (hi : Function.Injective i)
    {z : ZP p N →+* O} {b : RZ H n N →+* O} (hz : IsInc (ZP p N).subtype i z) (hb : IsInc (RZ H n N).subtype i b) :
    ∃ c : oLoc H p N →+* O, IsInc (oLoc H p N).subtype i c := by
  have hle : oLoc H p N ≤ i.range := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | hx)
    · exact ⟨_, hb ⟨_, Subring.subset_closure (Or.inl rfl)⟩⟩
    · exact ⟨_, hz ⟨_, Subring.subset_closure hx⟩⟩
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))⟩

theorem siegClause_iff {N n : ℕ} (hn : n.Prime) {XX : Scheme.{0}} (w : XX ⟶ Sp (oRing H N n))
    (oX : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) w) :
    SiegClause D (w ≫ spMap (inc H n N)) oX.t oX.lev ↔ SiegelClauseFullLevel w oX := by
  have hpb : ∀ (p : ℕ) (hc : n.Coprime p), IsPullback (pullback.fst w (spMap (Subring.inclusion
      (oRing_le_oLoc (H := H) p N n hc)))) (pullback.snd _ _) (w ≫ spMap (inc H n N))
      (spMap ((Subring.inclusion (oRing_le_oLoc (H := H) p N n hc)).comp (inc H n N))) := fun p hc => by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (spMap (inc H n N)))
      (by simp) (by simp) (by simp) (by simp)
  constructor
  · intro h p hc hp
    obtain ⟨Ag, bas, hbas, h⟩ := h p hp (by
      rintro rfl
      exact hp.one_lt.ne' (Nat.coprime_self _ |>.1 hc))
    obtain ⟨t₀, ν₀, lv, hlv⟩ := (fullObj_pull E H D n N _ _ (w ≫ spMap (inc H n N)) oX.t oX.lev (pullback.fst w
      (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hc))))).1
    obtain ⟨cl, ⟨o, φ, φ₂, a₁, a₂, a₃, a₄, a₅, a₆⟩, hf, hu⟩ := h (oLoc H p N) (oLoc H p N).subtype
      (Subring.inclusion (ZP_le_oLoc (H := H) p N)) _ Subtype.val_injective (isInc_incl _)
      (isInc_comp (isInc_incl _) (isInc_incl _)) _ _ _ t₀ ν₀ lv
      (hpb p hc) hlv
    obtain ⟨ψ, ψ₂, b₁, b₂, b₃, b₄⟩ := (ident_iff o ν₀ o.lev (fun u => oX.lev (bas u)) (fun u => lv (bas u))
      fun u => hlv _).1 ⟨φ, φ₂, a₁, a₂, a₃, a₄⟩
    exact ⟨Ag, bas, cl, o, ψ, ψ₂, hbas, b₁, b₂, b₃, b₄, a₅, a₆, hf, hu⟩
  · intro h p hp hpn
    have hc : n.Coprime p := (Nat.coprime_primes hn hp).2 hpn.symm
    obtain ⟨Ag, bas, cl, o, ψ, ψ₂, hbas, b₁, b₂, b₃, b₄, a₅, a₆, hf, hu⟩ := h p hc hp
    refine ⟨Ag, bas, hbas, fun O _ i z b hi hz hb T sT f tT ν levT hT hlevT => ?_⟩
    obtain ⟨t₀, ν₀, lv, hlv⟩ := (fullObj_pull E H D n N _ _ (w ≫ spMap (inc H n N)) oX.t oX.lev (pullback.fst w
      (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hc))))).1
    obtain ⟨φ, φ₂, a₁, a₂, a₃, a₄⟩ := (ident_iff o ν₀ o.lev (fun u => oX.lev (bas u)) (fun u => lv (bas u))
      fun u => hlv _).2 ⟨ψ, ψ₂, b₁, b₂, b₃, b₄⟩
    have h₀ : SiegData _ t₀ lv Ag _ bas cl := ⟨o, φ, φ₂, a₁, a₂, a₃, a₄, a₅, a₆⟩
    obtain ⟨c, hci⟩ := exists_fromLoc hi hz hb
    have hcb : c.comp ((Subring.inclusion (oRing_le_oLoc (H := H) p N n hc)).comp (inc H n N)) = b :=
      isInc_unique hi (isInc_comp hci (isInc_comp (isInc_incl _) (isInc_incl _))) hb
    have hcz : c.comp (Subring.inclusion (ZP_le_oLoc (H := H) p N)) = z :=
      isInc_unique hi (isInc_comp hci (isInc_incl _)) hz
    have hP := hpb p hc
    subst hcb hcz
    rw [spMap_comp] at hT
    let g := hP.lift f (sT ≫ spMap c) (hT.w.trans (Category.assoc _ _ _).symm)
    have g₁ : g ≫ pullback.fst _ _ = f := hP.lift_fst _ _ _
    have g₂ : g ≫ pullback.snd _ _ = sT ≫ spMap c := hP.lift_snd _ _ _
    have hg : IsPullback g sT (pullback.snd _ _) (spMap c) := IsPullback.of_right (by rw [g₁]; exact hT) g₂ hP
    obtain ⟨mu, hmu⟩ := sab_cancel ν₀ ν g₁
    have h₁ := SiegelDataPull.siegData_pull E H D _ _ _ _ g t₀ tT mu lv levT _ p N Ag _ bas cl (fun x =>
      ObjComp.sec_cancel ν₀.cart.1 mu.cart.1.w (Over.w _) (Over.w _) (hlv x)
        ((congrArg (_ ≫ ·) hmu.symm).trans ((hlevT x).trans (congrArg (· ≫ _) g₁.symm)))) h₀
    have e : (g ≫ pullback.snd _ _) ≫ spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N)) =
        sT ≫ spMap (c.comp (Subring.inclusion (ZP_le_oLoc (H := H) p N))) := by
      rw [g₂, spMap_comp, Category.assoc]
    have e' : ((g ≫ cl) ≫ pullback.fst _ _) ≫ Ag.s = sT ≫ spMap (c.comp (Subring.inclusion (ZP_le_oLoc (H := H) p N))) := by
      rw [← e, Category.assoc, pullback.condition, Category.assoc, reassoc_of% a₅, Category.assoc]
    let q : pullback Ag.s (spMap (c.comp (Subring.inclusion (ZP_le_oLoc (H := H) p N)))) ⟶
        pullback Ag.s (spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c) (by
        rw [pullback.condition, spMap_comp, Category.assoc])
    have hq : IsPullback q (pullback.snd _ _) (pullback.snd _ _) (spMap c) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
      rw [pullback.lift_fst, ← spMap_comp]
      exact IsPullback.of_hasPullback _ _
    have hw : IsPullback g (pullback.lift _ _ e') cl q := by
      refine IsPullback.of_bot ?_ ?_ hq
      · rw [pullback.lift_snd, a₅]
        exact hg
      · apply pullback.hom_ext
        · simp [q]
        · simp [q, a₅, g₂]
    exact ⟨pullback.lift _ _ e', siegData_congr h₁ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      MorphismProperty.of_isPullback (P := @IsFinite) hw hf,
      MorphismProperty.of_isPullback (P := @FormallyUnramified) hw hu⟩

structure Fam {N n : ℕ} (Z : FullPre D N n) where
  XX : Scheme.{0}
  w : XX ⟶ Sp (oRing H N n)
  oX : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) w
  u : Z.U.toScheme ⟶ XX
  fm : FullMap Z.ab oX u
  W : XX.Opens
  red : IsReduced XX
  flat : Flat w
  overB : u ≫ w = Z.U.ι ≫ Z.s
  fin : IsFinite u
  surj : Surjective u
  iso : IsIso (u ∣_ W)
  gen : ∀ x : XX, CharZero (XX.residueField x) → x ∈ W
  sieg : SiegelClauseFullLevel w oX

theorem siegelFinite_iff {N n : ℕ} (Z : FullPre D N n) : Z.SiegelFinite ↔ Nonempty (Fam Z) :=
  ⟨fun ⟨XX, w, oX, u, fm, W, a, b, c, d, e, f, g, h⟩ => ⟨⟨XX, w, oX, u, fm, W, a, b, c, d, e, f, g, h⟩⟩,
    fun ⟨F⟩ => ⟨F.XX, F.w, F.oX, F.u, F.fm, F.W, F.red, F.flat, F.overB, F.fin, F.surj, F.iso, F.gen, F.sieg⟩⟩

theorem charZero_of_bot {R : Type} [CommRing R] [CharZero R] {X : Scheme.{0}} (s : X ⟶ Sp R) (x : X)
    (hx : (s x).asIdeal = ⊥) : CharZero (X.residueField x) := by
  obtain ⟨φ, hφ⟩ := LevelFibre.exists_spMap (A := R) (B := X.residueField x) (X.fromSpecResidueField x ≫ s)
  refine charZero_of_injective_ringHom (f := φ) ((RingHom.injective_iff_ker_eq_bot _).2 ?_)
  let y : Sp (X.residueField x) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.residueField x))
  have h : spMap φ y = s x := by
    exact (congrArg (fun q => q y) hφ).symm.trans (congrArg s (Scheme.fromSpecResidueField_apply x y))
  rw [← h] at hx
  exact hx

theorem charZero_residueField {k : Type} [Field k] [CharZero k] {S : Scheme.{0}} (s : S ⟶ Sp k) (p : S) :
    CharZero (S.residueField p) := by
  obtain ⟨φ, -⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  exact charZero_of_injective_ringHom (R := k) φ.hom.injective

theorem isReduced_moduli {l : Level H} (Xo : Moduli D l) : IsReduced Xo.X := by
  have := Xo.smooth
  exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1

theorem isInc_toKA (l : Level H) {N : ℕ} (h : zeta N ∈ KA l) (c : ℕ) :
    IsInc (oRing H N c).subtype (KA l).val.toRingHom (toKA l h c) := fun _ => rfl

theorem toKA_injective (l : Level H) {N : ℕ} (h : zeta N ∈ KA l) (c : ℕ) : Function.Injective (toKA l h c) :=
  fun x y e => Subtype.ext ((isInc_toKA l h c x).symm.trans ((congrArg Subtype.val e).trans (isInc_toKA l h c y)))

theorem incl_incl_apply {R R' : Subring ℂ} (h : R ≤ R') (h' : R' ≤ R) (x : R') :
    Subring.inclusion h (Subring.inclusion h' x) = x := rfl

theorem exists_sigma (l : Level H) {N : ℕ} (h : l.A = N) (n : ℕ) (hz : zeta N ∈ KA l) (σ : KA l ≃+* KA l)
    (hσ : σ (baseKA l).ρ = (baseKA l).ρ) : ∃ (σ₀ : oRing H N n ≃+* oRing H N n) (ν : ℕ),
      (toKA l hz n).comp σ₀.toRingHom = σ.toRingHom.comp (toKA l hz n) ∧ σ₀ (oW H N n) = oW H N n ∧
      σ₀ (oZeta H N n) = oZeta H N n ^ ν := by
  subst h
  have hβ := isInc_comp (isInc_toKA l hz n) (isInc_incl (RZ_eq H n l.A).le)
  have hinj := toKA_injective l hz n
  have key : ∀ σ : KA l →+* KA l, σ (baseKA l).ρ = (baseKA l).ρ →
      ∃ τ : oRing H l.A n →+* oRing H l.A n, ∀ x, toKA l hz n (τ x) = σ (toKA l hz n x) := fun σ hσ => by
    obtain ⟨τ, hτ⟩ := FamAut.exists_restrict l n _ hβ σ hσ
    refine ⟨(inc H n l.A).comp (τ.comp (inc' H n l.A)), fun x => ?_⟩
    have h := RingHom.congr_fun hτ (inc' H n l.A x)
    simp only [RingHom.comp_apply] at h ⊢
    rwa [incl_incl_apply] at h
  obtain ⟨τ, hτ⟩ := key σ.toRingHom hσ
  obtain ⟨τ', hτ'⟩ := key σ.symm.toRingHom (σ.symm_apply_eq.2 hσ.symm)
  have : NeZero l.A := ⟨l.A_pos.ne'⟩
  obtain ⟨i, -, hi⟩ := (baseKA l).ζ_prim.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one])
  have hζ : toKA l hz n (oZeta H l.A n) = (baseKA l).ζ := Subtype.ext (isInc_toKA l hz n (oZeta H l.A n))
  have hw : toKA l hz n (oW H l.A n) = (1 + (baseKA l).ρ) / 2 := by
    have h2 : ((2 : KA l) : ℂ) = 2 := map_ofNat (KA l).val 2
    refine Subtype.ext ((isInc_toKA l hz n (oW H l.A n)).trans ?_)
    simp [baseKA, h2, oW, w0C]
  refine ⟨RingEquiv.ofRingHom τ τ' (RingHom.ext fun x => hinj (by simp [hτ, hτ']))
    (RingHom.ext fun x => hinj (by simp [hτ, hτ'])), i, RingHom.ext hτ, hinj ((hτ _).trans ?_), hinj ((hτ _).trans ?_)⟩
  · rw [hw, map_div₀, map_add, map_one, map_ofNat]
    exact congrArg (fun x => (1 + x) / 2) hσ
  · rw [map_pow, hζ]
    exact hi.symm

theorem isSimMod_of_levels {Q k : Type} [Group Q] [Field k] {N ν : ℕ} {P : D.La → Q} (hP : ∀ a c, P (a + c) = P a * P c)
    (g : D.La →ₗ[𝓞 E] D.La) {e : Q → Q → kˣ → Prop} (he : ∀ x y c c', e x y c → e x y c' → c = c') {z : kˣ}
    (hz : IsPrimitiveRoot z N) (h₁ : ∀ a, P a = 1 ↔ ∃ b, a = N • b) (h₂ : ∀ a, P (g a) = 1 ↔ ∃ b, a = N • b)
    (h₃ : ∀ a, ∃ c, P (g c) = P a) (h₄ : ∀ a b, e (P a) (P b) (z ^ D.EF a b))
    (h₅ : ∀ a b, e (P (g a)) (P (g b)) ((z ^ ν) ^ D.EF a b)) : IsSimMod D N g ν := by
  refine ⟨?_, fun a b => ?_⟩
  · have := D.proj
    let K : Submodule (𝓞 E) D.La := LinearMap.range (N • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
    have hK : ∀ x, x ∈ K ↔ D.ModN N x := fun x => exists_congr fun b => eq_comm
    obtain ⟨gi, hgi⟩ := Module.projective_lifting_property (K.mkQ ∘ₗ g) K.mkQ fun y => by
      obtain ⟨a, rfl⟩ := K.mkQ_surjective y
      obtain ⟨c, hc⟩ := h₃ a
      exact ⟨c, (Submodule.Quotient.eq K).2 ((hK _).2 ((h₁ _).1 (LevelFibre.sub_eq_one _ hP hc)))⟩
    have hr : ∀ a, D.ModN N (g (gi a) - a) := fun a =>
      (hK _).1 ((Submodule.Quotient.eq K).1 (LinearMap.congr_fun hgi a))
    refine ⟨gi, fun a => ⟨(h₂ _).1 ((h₁ _).2 ?_), hr a⟩⟩
    rw [map_sub]
    exact hr _
  · have h := he _ _ _ _ (h₄ (g a) (g b)) (h₅ a b)
    rw [← hz.zpow_eq_one_iff_dvd, zpow_sub, h, zpow_mul, zpow_natCast, mul_inv_cancel]

theorem exists_finite_open {Z X B B₁ F : Scheme.{0}} (U : Z.Opens) (s : Z ⟶ B) (i : B ⟶ B₁) [IsIso i] (b : F ⟶ B)
    (e : X ⟶ pullback (U.ι ≫ s) b) [IsFinite e] [Surjective e] {b₁ : F ⟶ B₁} (hb : b₁ = b ≫ i) :
    ∃ f : X ⟶ (pullback.fst (s ≫ i) b₁ ⁻¹ᵁ U).toScheme, IsFinite f ∧ Surjective f ∧
      f ≫ (pullback.fst (s ≫ i) b₁ ⁻¹ᵁ U).ι ≫ pullback.fst _ _ = e ≫ pullback.fst _ _ ≫ U.ι ∧
      f ≫ (pullback.fst (s ≫ i) b₁ ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = e ≫ pullback.snd _ _ := by
  subst hb
  have h₁ := (isPullback_morphismRestrict (pullback.fst (s ≫ i) (b ≫ i)) U).paste_vert
    (IsPullback.of_hasPullback (s ≫ i) (b ≫ i))
  have h₂ : IsPullback (pullback.fst (U.ι ≫ s) b) (pullback.snd _ _) (U.ι ≫ s ≫ i) (b ≫ i) :=
    (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso i)
      (by simp) (by simp) (by simp) (by simp)
  refine ⟨e ≫ (h₂.isoIsPullback _ _ h₁).hom, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst_assoc]
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd]

variable {Xo : ∀ l : Level H, Moduli D l} {n J : ℕ}

theorem three_le (Z : FullModel Xo n J) : 3 ≤ n ^ J := by
  have h2 := Z.aux.prime.two_le
  obtain ⟨c, hc⟩ := Z.aux.odd
  exact le_trans (by omega) (Nat.le_self_pow (by have := Z.J_pos; omega) n)

theorem eq_of_level (Z : FullModel Xo n J) {S : Scheme.{0}} (hr : IsReduced S)
    (hc : ∀ x : S, CharZero (S.residueField x)) {t : SAB H S} (lv : D.La → (𝟙_ (Over S) ⟶ t.G))
    {a a' : S ⟶ Z.U.toScheme} (ν : SABMap t Z.ab.t a) (ν' : SABMap t Z.ab.t a')
    (h : ∀ x, (lv x).left ≫ ν.φ = a ≫ (Z.ab.lev x).left) (h' : ∀ x, (lv x).left ≫ ν'.φ = a' ≫ (Z.ab.lev x).left)
    (hs : a ≫ Z.U.ι ≫ Z.s = a' ≫ Z.U.ι ≫ Z.s) : a = a' ∧ ν.φ = ν'.φ := by
  obtain rfl : a = a' := (Z.univ S _ hr hc (fullPull Z.ab ν lv h rfl)).unique ⟨rfl, ⟨⟨ν, h⟩⟩⟩ ⟨hs.symm, ⟨⟨ν', h'⟩⟩⟩
  exact ⟨rfl, fullObj_rigid allSixLaws.1 E H D n _ _ _ _ _ _ _ a ν ν' lv (three_le Z) Z.aux.odd.pow
    (fullObj_of_second_typing Z.ab) hr hc h h'⟩

theorem exists_sym (Z : FullModel Xo n J) (l : Level H) (h : l.A = n ^ J) (r : (Xo l).X ≅ (Xo l).X)
    (ν : SABMap (Xo l).univ.t (Xo l).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l ≃+* KA l)
    (hσ : σ (baseKA l).ρ = (baseKA l).ρ) (hr : r.hom ≫ (Xo l).s = (Xo l).s ≫ spMap σ.toRingHom)
    (hν : ∀ x, ((Xo l).univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l).univ.etaA x).left) :
    ∃ ρ : Z.X ≅ Z.X, (Z.cover l h ≫ Z.U.ι) ≫ ρ.hom = r.hom ≫ Z.cover l h ≫ Z.U.ι := by
  rcases isEmpty_or_nonempty (Xo l).X with hX | ⟨⟨p⟩⟩
  · exact ⟨Iso.refl _, (isInitialOfIsEmpty (X := (Xo l).X)).hom_ext _ _⟩
  obtain ⟨σ₀, i, hσ₀, hw, hζ⟩ := exists_sigma l h n (zeta_mem_of_eq l h) σ hσ
  have hlv : ∀ x, ((Xo l).univ.etaA (g x)).left ≫ (sabCmp ν (Z.coverM l h)).φ =
      (r.hom ≫ Z.cover l h) ≫ (Z.ab.lev x).left := fun x => by
    rw [sabCmp_φ]
    exact ObjComp.sec_comp (Z.cover_lev l h x) (hν x)
  have hbase : (r.hom ≫ Z.cover l h) ≫ Z.U.ι ≫ Z.s =
      (Xo l).s ≫ spMap (toKA l (zeta_mem_of_eq l h) n) ≫ spMap σ₀.toRingHom := by
    rw [Category.assoc, Z.cover_over, reassoc_of% hr, ← spMap_comp, ← spMap_comp, hσ₀]
  have hsim : IsSimMod D (n ^ J) g i := by
    let k := AlgebraicClosure ((Xo l).X.residueField p)
    obtain ⟨y⟩ : Nonempty (Sp k ⟶ (Xo l).X) :=
      ⟨spMap (algebraMap ((Xo l).X.residueField p) k) ≫ (Xo l).X.fromSpecResidueField p⟩
    obtain ⟨c, hc⟩ := LevelFibre.exists_spMap (y ≫ (Xo l).s)
    have hpos : 0 < n ^ J := h ▸ l.A_pos
    have hprim : IsPrimitiveRoot (c (toKA l (zeta_mem_of_eq l h) n (oZeta H (n ^ J) n))) (n ^ J) :=
      (IsPrimitiveRoot.of_map_of_injective (f := (KA l).val.toRingHom)
        (Complex.isPrimitiveRoot_exp _ hpos.ne') Subtype.val_injective).map_of_injective c.injective
    obtain ⟨z, hz⟩ := hprim.isUnit hpos.ne'
    obtain ⟨a₁, -, a₃⟩ := (fullPull Z.ab (Z.coverM l h) _ (Z.cover_lev l h) (Z.cover_over l h)).geom k y
      (c.comp (toKA l (zeta_mem_of_eq l h) n)) z (by rw [spMap_comp, ← hc, Category.assoc]) hz
    obtain ⟨b₁, b₂, b₃⟩ := (fullPull Z.ab (sabCmp ν (Z.coverM l h)) _ hlv hbase).geom k y
      ((c.comp (toKA l (zeta_mem_of_eq l h) n)).comp σ₀.toRingHom) (z ^ i)
      (by rw [spMap_comp, spMap_comp, ← hc, Category.assoc, Category.assoc])
      (by rw [Units.val_pow_eq_pow_val, hz, ← map_pow, ← map_pow, ← hζ]; rfl)
    refine isSimMod_of_levels (P := fun a => toUnit (Over.mk y) ≫ (Xo l).univ.etaA a)
      (fun a c => by rw [(Xo l).univ.etaA_add, MonObj.comp_mul]) g
      (e := fun x x' u => Out.WeilIs (Xo l).univ.t.G (Xo l).univ.t.PP.L ((n ^ J : ℕ) : ℤ) x x' (unitOn u))
      (weilIs_unique_fieldPoint _ _ _ (Xo l).univ.t.PP.isLB k y _) (IsPrimitiveRoot.coe_units_iff.1 (hz ▸ hprim))
      a₁ b₁ (fun a => b₂ _ ?_) a₃ b₃
    have hadd : ∀ m : ℕ, (Xo l).univ.etaA (m • a) = (Xo l).univ.etaA a ^ m := fun m => by
      induction m with
      | zero => simpa using (Xo l).univ.etaA_ker 0
      | succ m ih => rw [succ_nsmul, (Xo l).univ.etaA_add, ih, pow_succ]
    show (toUnit (Over.mk y) ≫ (Xo l).univ.etaA a) ^ n ^ J = 1
    rw [← MonObj.comp_pow, ← hadd, ← h, (Xo l).univ.etaA_ker, MonObj.comp_one]
  obtain ⟨ρ, mu, ρU, h₁, h₂, h₃⟩ := Z.acts σ₀ g i hsim hw hζ
  obtain ⟨κ, hκ⟩ := sab_cancel Z.mU (sabCmp Z.mU mu) h₂
  rw [sabCmp_φ] at hκ
  have hmono : Mono Z.mU.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) Z.mU.cart.1.flip
    (inferInstanceAs (Mono Z.U.ι))
  have hκl : ∀ x, (Z.ab.lev (g x)).left ≫ κ.φ = ρU ≫ (Z.ab.lev x).left := fun x => by
    rw [← cancel_mono Z.mU.φ, Category.assoc, ← hκ]
    exact (h₃ x).trans (Category.assoc _ _ _).symm
  have e := (eq_of_level Z (isReduced_moduli _) (charZero_residueField (Xo l).s) (fun x => (Xo l).univ.etaA (g x))
    (sabCmp (Z.coverM l h) κ) (sabCmp ν (Z.coverM l h)) (fun x => by
      rw [sabCmp_φ]
      exact ObjComp.sec_comp (hκl x) (Z.cover_lev l h (g x))) hlv (by
      rw [hbase, Category.assoc, reassoc_of% h₂, h₁, reassoc_of% Z.cover_over l h])).1
  exact ⟨ρ, by rw [Category.assoc, ← h₂, reassoc_of% e]⟩

def toTop (Z : FullModel Xo n J) (F : Fam Z.toFullPre) : Top Xo n (n ^ J) where
  Z := Z.X
  s := Z.s ≫ spMap (inc H n (n ^ J))
  normal := Z.normal
  proj := isProjOver_incl (RZ_eq H n _) Z.proj
  flat := by
    have := Z.flat
    infer_instance
  t := Z.t
  qproj := by
    rw [← Category.assoc]
    exact isQProjOver_incl (RZ_eq H n _) Z.qproj
  good := by
    refine ⟨⟨Z.U, Z.U_eq, ?_⟩, splitFib_of_splitFibres Z.toPModel Z.split, hasTheta_of_pushInvertible Z.theta⟩
    have := Z.ab.proper
    have hp := (isPullback_morphismRestrict Z.t.G.hom Z.U).flip
    rw [← hp.isoIsPullback_hom_snd _ _ Z.mU.cart.1]
    infer_instance
  ga := by
    have := projProper _ _ _ (isProjOver_incl (RZ_eq H n (n ^ J)) Z.proj)
    have := BaseRing.finiteType_RZ H n (n ^ J)
    have : IsNoetherianRing (RZ H n (n ^ J)) := Algebra.FiniteType.isNoetherianRing ℤ _
    have := LocallyOfFiniteType.isLocallyNoetherian (Z.s ≫ spMap (inc H n (n ^ J)))
    have : IsDominant Z.U.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact Z.U_dense⟩
    rw [← Z.U_eq, ← Scheme.Opens.range_ι]
    exact genericPoints_subset_range_of_isDominant Z.U.ι
  a l h := Z.cover l h ≫ Z.U.ι
  m l h := sabCmp (Z.coverM l h) Z.mU
  fin l h β hβ := by
    obtain rfl : β = (toKA l (zeta_mem_of_eq l h) n).comp (inc H n (n ^ J)) :=
      isInc_unique Subtype.val_injective hβ (isInc_comp (isInc_toKA _ _ _) (isInc_incl _))
    obtain ⟨a₁, -, a₂⟩ := Z.cover_fet l h (pullback.lift _ _ (Z.cover_over l h)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    obtain ⟨f, b₁, b₂, b₃, b₄⟩ := exists_finite_open Z.U Z.s (spMap (inc H n (n ^ J))) _
      (pullback.lift _ _ (Z.cover_over l h)) (spMap_comp _ _)
    exact ⟨_, f, by rw [← Z.U_eq]; rfl, b₁, b₂, b₃.trans (pullback.lift_fst_assoc _ _ _ _),
      b₄.trans (pullback.lift_snd _ _ _)⟩
  compat l l' h h' r ν k hk hr hν := by
    have hk' : k.comp (toKA l (zeta_mem_of_eq l h) n) = toKA l' (zeta_mem_of_eq l' h') n :=
      isInc_unique Subtype.val_injective (isInc_comp hk (isInc_toKA _ _ _)) (isInc_toKA _ _ _)
    obtain ⟨e₁, e₂⟩ := eq_of_level Z (isReduced_moduli _) (charZero_residueField (Xo l').s) (Xo l').univ.etaA
      (sabCmp ν (Z.coverM l h)) (Z.coverM l' h') (fun x => by
        rw [sabCmp_φ]
        exact ObjComp.sec_comp (Z.cover_lev l h x) (hν x)) (Z.cover_lev l' h') (by
        rw [Category.assoc, Z.cover_over, Z.cover_over, reassoc_of% hr, ← spMap_comp, hk'])
    refine ⟨by rw [reassoc_of% e₁], ?_⟩
    rw [sabCmp_φ, sabCmp_φ, ← e₂, sabCmp_φ, Category.assoc]
  sym := exists_sym Z
  U := Z.U
  U_eq := Z.U_eq
  MM := F.XX
  sM := F.w ≫ spMap (inc H n (n ^ J))
  tM := F.oX.t
  lev := F.oX.lev
  MM_red := F.red
  MM_flat := by
    have := F.flat
    infer_instance
  MM_ab := F.oX.proper
  u := F.u
  u_over := by rw [reassoc_of% F.overB]
  u_fin := F.fin
  u_surj := F.surj
  u_gen := ⟨F.W, fun x hx => F.gen x (charZero_of_bot _ x hx), F.iso⟩
  tU := Z.ab.t
  mU := Z.mU
  mM := F.fm.toSABMap
  lev_eq l h a' x y ha hy := by
    obtain rfl : a' = Z.cover l h := by rwa [← cancel_mono Z.U.ι]
    have : Mono Z.mU.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) Z.mU.cart.1.flip
      (inferInstanceAs (Mono Z.U.ι))
    obtain rfl : y = ((Xo l).univ.etaA x).left ≫ (Z.coverM l h).φ := by
      rw [← cancel_mono Z.mU.φ, hy, sabCmp_φ, Category.assoc]
    exact (congrArg (· ≫ _) (Z.cover_lev l h x)).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (F.fm.lev x)))
  sieg := (siegClause_iff Z.aux.prime F.w F.oX).2 F.sieg

end GlobalTheory.ModelTypings

end
