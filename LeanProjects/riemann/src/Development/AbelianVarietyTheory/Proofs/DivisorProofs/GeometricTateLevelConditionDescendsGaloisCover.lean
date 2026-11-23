import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.GeomDesc

theorem diag_comp {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left := by
  apply pullback.hom_ext
  · have h1 := sq.1
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := sq.2
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P₀ : LB (G2 A₀).left}
    (hP : P.IsLB) (hP₀ : P₀.IsLB) (pol : LBIso P (P₀.pull φ₂)) :
    LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) := by
  have h₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp pol _ (diag_comp sq).symm
  have h₂ : LBIso ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) φ rfl
  exact LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.GeomDesc

open GlobalTheory.UPel.HT.GeomDesc in

theorem GlobalTheory.UPel.HT.geom_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ N φ₂ P P₀ eta eta₀ hG hA hA₀ gp hact sq hP hP₀ pol heta hgeom k _ _ x β hx
  have := hG.etale
  have := hG.onto
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  obtain ⟨I, hI⟩ := hgeom k y β (by rw [← Category.assoc, hx])
  have iso := diag_lbIso sq hP hP₀ pol
  refine ⟨GlobalTheory.UPel.HT.TateIsoO.transport (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g ≫ act.act c).left ≫ φ = (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y) g ≫ act₀.act c).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X A₀ A π φ _ _ (pull_isLB hP₀ _) (pull_isLB hP _) gp iso
      (Over.mk y) n g g' _ _ _ (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g)
      (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g')).1 hc
  · rw [GlobalTheory.UPel.HT.TateIsoO.transport_ev, ← hI a]
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left]
    show (toUnit (Over.mk (y ≫ π)) ≫ eta₀ a).left = (toUnit (Over.mk y) ≫ eta a).left ≫ φ
    rw [Over.comp_left, Over.comp_left, Category.assoc, heta a, ← Category.assoc]
    congr 1

end
