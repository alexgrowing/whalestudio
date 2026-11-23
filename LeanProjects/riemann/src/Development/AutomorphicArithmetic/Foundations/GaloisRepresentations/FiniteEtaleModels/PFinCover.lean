import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelGroupAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUniqueStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem level_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (hl : IsEtLevOver o 𝔞 r l) {u v : D.La}
    (e : (wSub D 𝔞 r).mkQ u = (wSub D 𝔞 r).mkQ v) : l u = l v := by
  have hmem : u - v ∈ wSub D 𝔞 r := (Submodule.Quotient.eq _).mp e
  have h1 : l (u - v) = 1 := hl.2.2.1 _ hmem
  calc l u = l ((u - v) + v) := by rw [sub_add_cancel]
    _ = l (u - v) * l v := hl.1 _ _
    _ = l v := by rw [h1, _root_.one_mul]

private theorem rep_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {Y : Scheme.{0}} {π : Y ⟶ S}
    {lu : D.La → (Over.mk π ⟶ o.A)} (hlu : IsEtLevOver o 𝔞 r lu)
    (hrep : ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o 𝔞 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y)
    {T : Over S} {f f' : T ⟶ Over.mk π} (h : ∀ y, f ≫ lu y = f' ≫ lu y) : f = f' := by
  obtain ⟨g, -, huniq⟩ := hrep T (fun y => f ≫ lu y)
    (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu f hlu)
  rw [huniq f (fun y => rfl), huniq f' (fun y => (h y).symm)]

theorem UpperTheory.Gal.FiniteEtaleModels.finCover_holds :
    RepAll → PtAll → GrpFin → FinCover := by
  intro hRep hPt hGrp p _ D R _ b N 𝔞 r hN hcop het S _ s o
  obtain ⟨Y, π, lu, hfin, het', hlu, hrep⟩ := hRep p D R b N 𝔞 r hcop het S s o
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y s π o
  have hpb := m.cart.1
  have hluw : ∀ y, (lu y).left ≫ o.A.hom = 𝟙 Y ≫ π := fun y => by
    rw [Category.id_comp]; exact Over.w (lu y)
  let lv : D.La → (𝟙_ (Over Y) ⟶ o'.A) := fun y =>
    Over.homMk (hpb.lift (lu y).left (𝟙 Y) (hluw y)) (by rw [hpb.lift_snd]; rfl)
  have hlv : ∀ y, (lv y).left ≫ m.φ = (lu y).left := fun y => hpb.lift_fst _ _ _
  have hlv2 : ∀ y, (lv y).left ≫ o'.A.hom = 𝟙 Y := fun y => hpb.lift_snd _ _ _
  have hpt : ∀ y, ptOf m (lv y) = lu y := fun y => by
    ext1; exact hlv y
  have hcomp : ∀ (a c : LevGrp D 𝔞 r) (y : D.La), lu (levAct a (levAct c y)) = lu (levAct (a * c) y) :=
    fun a c y => level_congr hlu (by rw [mkQ_levAct, mkQ_levAct, mkQ_levAct]; rfl)
  have hone : ∀ y, lu (levAct (1 : LevGrp D 𝔞 r) y) = lu y :=
    fun y => level_congr hlu (by rw [mkQ_levAct]; rfl)
  have hact : ∀ g : LevGrp D 𝔞 r, ∃ f : Over.mk π ⟶ Over.mk π, ∀ y, f ≫ lu y = lu (levAct g y) :=
    fun g => (hrep _ _ (GlobalTheory.T.etale_level_group_action p D R b N S s o 𝔞 r _ lu g hlu)).exists
  choose fg hfg using hact
  have hfgeq : ∀ (f : Over.mk π ⟶ Over.mk π) (g : LevGrp D 𝔞 r),
      (∀ y, f ≫ lu y = lu (levAct g y)) → f = fg g :=
    fun f g hf => rep_ext hlu hrep (fun y => by rw [hf, hfg])
  refine ⟨Y, π, o', m, lv, fun g => (fg g).left, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S Y s π (π ≫ s) o o' m 𝔞 r lv]
    simpa only [hpt] using hlu
  · refine ⟨(hGrp p D 𝔞 r het.1).2, ?_, ?_, ?_, hfin, het', ?_, ?_⟩
    · show (fg 1).left = 𝟙 Y
      rw [← hfgeq (𝟙 _) 1 (fun y => by rw [Category.id_comp, hone])]
      rfl
    · intro a c
      show (fg (a * c)).left = (fg a).left ≫ (fg c).left
      rw [← hfgeq (fg a ≫ fg c) (a * c) (fun y => by rw [Category.assoc, hfg, hfg, hcomp])]
      rfl
    · intro a
      exact Over.w (fg a)
    · constructor
      intro x
      obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point S x
      obtain ⟨l, hl⟩ := hPt p D R b N 𝔞 r hcop het S s o k a
      obtain ⟨f, -, -⟩ := hrep _ l hl
      have hx : x ∈ Set.range ⇑a := by rw [ha]; rfl
      obtain ⟨q, hq⟩ := hx
      have hw : f.left ≫ π = a := Over.w f
      refine ⟨f.left q, ?_⟩
      rw [← hq, ← Scheme.Hom.comp_apply, hw]
    · intro K _ _ y y' hyy
      let j : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y rfl
      let j' : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y' hyy.symm
      have hl := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j hlu
      have hl' := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j' hlu
      obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver p D R b N S s o 𝔞 r K (y ≫ π) _ _ hl hl'
      refine ⟨g, ?_, ?_⟩
      · have : j ≫ fg g = j' := rep_ext hlu hrep (fun z => by rw [Category.assoc, hfg]; exact hg z)
        exact congrArg (fun q => Over.Hom.left q) this
      · intro a ha
        apply hguniq
        intro z
        show j ≫ lu (levAct a z) = j' ≫ lu z
        have : j ≫ fg a = j' := by ext1; exact ha
        rw [← hfg, ← Category.assoc, this]
  · intro T t o₁ m₁ l hl
    have hl' := (GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S T s t (t ≫ s) o o₁ m₁ 𝔞 r l).mp hl
    obtain ⟨g, hg, hguniq⟩ := hrep (Over.mk t) _ hl'
    have hgw : g.left ≫ π = t := Over.w g
    have hφ : ∀ (f : T ⟶ Y) (_ : f ≫ π = t) (m₃ : GlobalTheory.UPel.HT.ObjMap o₁ o (f ≫ π)), m₃.φ = m₁.φ :=
      fun f hf m₃ => Rigid.objMap_phi_unique p D R b N hN hcop S T s (t ≫ s) o o₁ (f ≫ π) t m₃ m₁ hf
    have hgl : ∀ y, (l y).left ≫ m₁.φ = g.left ≫ (lu y).left := fun y => by
      have := congrArg (fun q => Over.Hom.left q) (hg y)
      exact this.symm
    refine ⟨g.left, ⟨hgw, ?_⟩, ?_⟩
    · obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ
        (by rw [hgw]; exact m₁ : GlobalTheory.UPel.HT.ObjMap o₁ o (g.left ≫ π)) m
      refine ⟨m₂, fun y => ?_⟩
      apply hpb.hom_ext
      · rw [Category.assoc, hm₂, hφ _ hgw, Category.assoc, hlv, hgl]
      · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (l y), Category.assoc, hlv2,
          Category.comp_id]
        exact Category.id_comp _
    · rintro f' ⟨hf', m₂', hm₂'⟩
      obtain ⟨m₃, hm₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂' m
      have : (Over.homMk f' hf' : Over.mk t ⟶ Over.mk π) = g := by
        apply hguniq
        intro y
        ext1
        show f' ≫ (lu y).left = (l y).left ≫ m₁.φ
        rw [← hlv, ← Category.assoc, ← hm₂' y, Category.assoc, ← hm₃, hφ f' hf' m₃]
      exact congrArg (fun q => Over.Hom.left q) this
