import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEtaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FineAgree

theorem sec_hom {S : Scheme.{0}} {G : Over S} (x : 𝟙_ (Over S) ⟶ G) : x.left ≫ G.hom = 𝟙 S := Over.w x

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A] [IsDomain A] (f₁ f₂ : L.W →+* A), f₁.comp L.b = f₂.comp L.b → ∀ (B' : Over (Sp A)) [GrpObj B'] (π₁ π₂ : B'.left ⟶ L.D.P.A.left) (act' : 𝓞 E → (B'.left ⟶ B'.left)), IsGrpPullback B' L.D.P.A (spMap f₁) π₁ → IsGrpPullback B' L.D.P.A (spMap f₂) π₂ → (letI := H.starRing; ∀ x, act' x ≫ π₁ = π₁ ≫ (L.oa.onB.act x).left) → (letI := H.starRing; ∀ x, act' x ≫ π₂ = π₂ ≫ (L.oa.onB.act x).left) → (∀ x, act' x ≫ B'.hom = B'.hom) → LBIso (L.D.P.L.pull π₁) (L.D.P.L.pull π₂) → ∀ (F : Type) [Field F] (j : A →+* F), Function.Injective j → (∀ a, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.o.etaA a).left ≫ L.φB ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.o.etaA a).left ≫ L.φB) → (∀ y, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.D.c y).left ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.D.c y).left) → f₁ = f₂ ∧ π₁ = π₂ := by
  intro E _ _ _ H D' l c L A _ _ f₁ f₂ hb B' _ π₁ π₂ act' h₁ h₂ ha₁ ha₂ hab hL F _ j hj hη hc
  letI := H.starRing
  obtain ⟨o', ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D' (LowDat.lowLevel l) _ _ (baseKA _) (baseKA _) (RingHom.id _) _ _
    (lowMap c L.b) (lowMap c (f₁.comp L.b)) (spMap f₁) rfl rfl (by
      simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) L.o
  have hφ₁ : IsGrpPullback o'.t.G L.D.P.A (spMap f₁) (m₁.φ ≫ L.φB) :=
    (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hφ₁ h₁
  haveI := he
  have hew : e.hom.left ≫ B'.hom = o'.t.G.hom := Over.w e.hom
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : o'.t.G.left ⟶ L.o.t.G.left, ψ ≫ L.φB = e.hom.left ≫ π₂ ∧
      ψ ≫ L.o.t.G.hom = o'.t.G.hom ≫ spMap f₂ :=
    ⟨L.ab.1.1.lift (e.hom.left ≫ π₂) (o'.t.G.hom ≫ spMap f₂) (by
      rw [Category.assoc, h₂.1.w, ← Category.assoc, hew, Category.comp_id]), IsPullback.lift_fst _ _ _ _,
      IsPullback.lift_snd _ _ _ _⟩
  have hψ : IsGrpPullback o'.t.G L.o.t.G (spMap f₂) ψ := by
    have n : IsGrpPullback o'.t.G L.D.P.A (spMap f₂ ≫ 𝟙 _) (ψ ≫ L.φB) := by
      rw [hψ₁, Category.comp_id]
      exact ((isGrpPullback_of_iso e).comp h₂).congr (Category.id_comp _) rfl
    exact L.ab.1.cancel n hψ₂
  have hact : ∀ x, (o'.t.act.act x).left ≫ ψ = ψ ≫ (L.o.t.act.act x).left := by
    intro x
    have key : (o'.t.act.act x).left ≫ e.hom.left = e.hom.left ≫ act' x := by
      apply h₁.1.hom_ext
      · have e1 : (o'.t.act.act x).left ≫ m₁.φ = m₁.φ ≫ (L.o.t.act.act x).left := m₁.act x
        calc ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₁ = ((o'.t.act.act x).left ≫ m₁.φ) ≫ L.φB := by
              rw [Category.assoc, heq, Category.assoc]
          _ = m₁.φ ≫ (L.o.t.act.act x).left ≫ L.φB := by rw [e1, Category.assoc]
          _ = (m₁.φ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [L.ab.2.1, Category.assoc]
          _ = (e.hom.left ≫ act' x) ≫ π₁ := by rw [← heq, Category.assoc, Category.assoc, ha₁]
      · rw [Category.assoc, hew, Category.assoc, hab, hew, Over.w (o'.t.act.act x)]
    apply L.ab.1.1.hom_ext
    · calc ((o'.t.act.act x).left ≫ ψ) ≫ L.φB = ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₂ := by
            rw [Category.assoc, hψ₁, Category.assoc]
        _ = (ψ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [key, Category.assoc, ha₂, hψ₁, Category.assoc]
        _ = (ψ ≫ (L.o.t.act.act x).left) ≫ L.φB := by rw [Category.assoc, Category.assoc, L.ab.2.1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (o'.t.act.act x), Category.assoc,
        Over.w (L.o.t.act.act x), hψ₂]

  have hLψ : LBIso o'.t.PP.L (L.o.t.PP.L.pull ψ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    have K1 : LBIso o'.t.PP.L (L.D.P.L.pull (m₁.φ ≫ L.φB)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB ⟨w, hw⟩ L.ab.2.2
    rw [← heq] at K1
    have K2 : LBIso o'.t.PP.L ((L.D.P.L.pull π₂).pull e.hom.left) :=
      GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K1 hL.symm
    have K3 : LBIso o'.t.PP.L (L.D.P.L.pull (e.hom.left ≫ π₂)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K2
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB L.D.P.isLB _))
    rw [← hψ₁] at K3
    exact GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB K3 L.ab.2.2
  obtain ⟨n, hn⟩ := GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o'.t L.o.t (spMap f₂) ψ L.o.proper hψ hact hLψ
  haveI : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  haveI := L.o.proper
  have transfer : ∀ (u : Sp A ⟶ o'.t.G.left) (v : Sp L.W ⟶ L.o.t.G.left), u ≫ o'.t.G.hom = 𝟙 _ →
      v ≫ L.o.t.G.hom = 𝟙 _ → u ≫ m₁.φ = spMap f₁ ≫ v →
      (∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ v ≫ L.φB ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ v ≫ L.φB) → u ≫ ψ = spMap f₂ ≫ v := by
    intro u v hu hv huv ⟨z, hz0, hz1, hz2⟩
    have hz : spMap j ≫ u ≫ e.hom.left = z := by
      apply h₁.1.hom_ext
      · rw [hz1, Category.assoc, Category.assoc, heq, ← Category.assoc u, huv, Category.assoc]
      · rw [hz0, Category.assoc, Category.assoc, hew, hu, Category.comp_id]
    refine ext_of_isDominant_of_isSeparated (X := Sp A) L.o.t.G.hom ?_ (spMap j) ?_
    · rw [Category.assoc, hψ₂, ← Category.assoc, hu, Category.id_comp, Category.assoc, hv, Category.comp_id]
    · apply L.ab.1.1.hom_ext
      · rw [Category.assoc, Category.assoc, hψ₁, ← Category.assoc u, ← Category.assoc, hz, hz2,
          Category.assoc, Category.assoc]
      · rw [Category.assoc, Category.assoc, hψ₂, ← Category.assoc u, hu, Category.id_comp, Category.assoc,
          Category.assoc, hv, Category.comp_id]
  have hetaA : ∀ a, (o'.etaA a).left ≫ n.φ = spMap f₂ ≫ (L.o.etaA a).left := by
    intro a
    rw [hn]
    exact transfer _ _ (sec_hom _) (sec_hom _) (m₁.etaA a) (hη a)
  have heta := GlobalTheory.T.sabMap_keeps_levelEta c A L.W (f₁.comp L.b) L.b o' L.o f₂ hb.symm n hetaA
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ObjMap o' L.o (spMap f₂), m₂.φ = ψ := ⟨⟨n, heta, hetaA⟩, hn⟩

  have hcy : ∀ y, ∃ cy : Sp L.W ⟶ L.o.t.G.left, cy ≫ L.φB = (L.D.c y).left ∧ cy ≫ L.o.t.G.hom = 𝟙 _ := fun y =>
    ⟨L.ab.1.1.lift (L.D.c y).left (𝟙 _) (by rw [sec_hom, Category.comp_id]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose cy hcy₁ hcy₂ using hcy
  have hx : ∀ y, ∃ x : Sp A ⟶ o'.t.G.left, x ≫ m₁.φ = spMap f₁ ≫ cy y ∧ x ≫ o'.t.G.hom = 𝟙 _ := fun y =>
    ⟨m₁.cart.1.lift (spMap f₁ ≫ cy y) (𝟙 _) (by
      rw [Category.assoc, hcy₂, Category.comp_id, Category.id_comp]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose x hx₁ hx₃ using hx
  have hf : f₁ = f₂ := by
    refine L.fineRed A f₁ f₂ hb o' m₁ m₂ x (fun y => ?_) (fun y => ?_) hx₃
    · rw [← Category.assoc, hx₁, Category.assoc, hcy₁]
    · rw [hm₂, ← Category.assoc, transfer (x y) (cy y) (hx₃ y) (hcy₂ y) (hx₁ y) (by
        obtain ⟨z, hz⟩ := hc y
        exact ⟨z, by simpa only [hcy₁] using hz⟩), Category.assoc, hcy₁]
  subst hf
  refine ⟨rfl, ?_⟩
  have hu : m₁.φ = m₂.φ := GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical A
    (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) _ _ o' L.o (spMap f₁) m₁ m₂
  have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  apply (cancel_epi e.hom.left).1
  rw [heq, hu, hm₂, hψ₁]

end GlobalTheory.UCanon.FineAgree
