import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

namespace UpperTheory.Gal.G3.HopfLiesOver

private theorem isTr_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} (p : Z ⟶ B)
    {q q' : Y ⟶ B} (e : q = q') (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p) (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} (r : X ⟶ B) (t : Y ⟶ X) (a : t ≫ r = q) (a' : t ≫ r = q') (y : T.H r),
        tr' (T.pull t a' y) = tr (T.pull t a y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ _ => rfl⟩

private theorem unit_l (l : ℕ) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (hl : (l : k) ≠ 0) :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h0
    apply hl
    apply (algebraMap k Ω).injective
    simpa using h0
  have h2 := (h1.isUnit).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem low_fet (hF : FEtBasic) {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) : FEt ((low D).s g) (D.d g) := by
  have hp : IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g)
      (pullback.fst C.p (gen O k)) := by
    refine (IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k)).flip).flip
    · change IsPullback (bcMap (gen O k) (D.s g) rfl ≫ pullback.snd C.p (gen O k)) _ _ _
      rw [bcMap_snd]
      exact (IsPullback.of_hasPullback _ _).flip
    · exact bcMap_fst (gen O k) (D.s g) rfl
  exact hF.1 _ _ _ _ _ hp (D.fet g)

end UpperTheory.Gal.G3.HopfLiesOver

open UpperTheory.Gal.G3.HopfLiesOver in
theorem UpperTheory.Gal.G3.jHopLies :
    EtGood → BcGood.{1} → FEtBasic → HopSpec → LiesOp.{1} → HopLies := by
  intro hEt hBc hF hHop hLies l _ k L O _ _ _ _ hl H θ C D hN Ω _ _ g
  have hT : (etG l k Ω).Good := hBc _ _ (hEt l (sp Ω) (unit_l l hl))
  obtain ⟨d, hd⟩ := hN.2.2 g
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  obtain ⟨trg, htrg⟩ := hT.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  have hfet := low_fet hF D g
  obtain ⟨tr, htr⟩ := @Th.Good.tr _ _ _ _ hT _ _ (pullback.snd C.p (gen O k))
    (pullback.snd (D.s g ≫ C.p) (gen O k)) ((low D).s g) hfet.1 hfet.2.1
    (bcMap_snd (gen O k) (D.s g) rfl)
  have hq : pullback.snd (D.s g ≫ C.p) (gen O k) = (low D).s g ≫ (low D).q :=
    (bcMap_snd (gen O k) (D.s g) rfl).symm
  obtain ⟨tr', htr', hrel⟩ := isTr_congr (etG l k Ω) _ hq _ tr htr
  rw [(hHop l hl H Ω g d hd).2 trg htrg, (hHop l hl (low D) Ω g (D.d g) hfet).2 tr' htr']
  apply LinearMap.ext
  intro x
  have e := hLies C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet (etG l k Ω) hT tr trg
    htr htrg x
  have e2 := hrel _ _ (bcMap_snd (gen O k) (D.t g) (D.comm g))
    ((bcMap_snd (gen O k) (D.t g) (D.comm g)).trans hq) x
  exact e.trans (congrArg (fun y => (D.m g : ℚ_[l]) • (etG l k Ω).pull (piK C) (piK_snd C) y) e2.symm)
