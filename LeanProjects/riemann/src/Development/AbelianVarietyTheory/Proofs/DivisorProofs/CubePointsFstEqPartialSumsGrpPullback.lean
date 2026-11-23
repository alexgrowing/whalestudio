import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.PairPts

private theorem psum_two_01 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd, pzero, Hom.mul_def, Hom.one_def]

private theorem psum_two_e {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero, Hom.one_def]

private theorem psum_two_0 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  have := psum_two_e G u v
  rw [psum] at this
  simp only [List.foldr_cons, List.foldr_nil, List.filter] at this ⊢
  show u * pzero G T = u
  simp [pzero, Hom.one_def] at this ⊢

private theorem psum_two_1 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  show v * pzero G T = v
  simp [pzero, Hom.one_def]

theorem lamPts_fst_eq_psum : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  intro S₀ S B₀ _ _ B _ _ f β β₂ hβ hsq Y x y x' y' hx hy k
  have hm : ((lift x y).left ≫ β₂) ≫ (G2 B).hom = (Over.mk (Y.hom ≫ f)).hom := by
    have h1 : (G2 B).hom = (fst B B).left ≫ B.hom := (Over.w (fst B B)).symm
    rw [h1, Category.assoc, ← Category.assoc β₂, hsq.1, Category.assoc, hβ.1.w, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Category.assoc x.left, Over.w x]
    rfl
  let u : Over.mk (Y.hom ≫ f) ⟶ G2 B := Over.homMk ((lift x y).left ≫ β₂) hm
  have key : ∀ g : G2 B ⟶ B, (lift x y).left ≫ β₂ ≫ g.left = (u ≫ g).left := fun g => by
    simp [u]
  have hu1 : (u ≫ fst B B).left = x.left ≫ β := by
    rw [← key, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have hu2 : (u ≫ snd B B).left = y.left ≫ β := by
    rw [← key, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have h := isGrpPullback_pullback B f
  have m : (x' * y').left ≫ pullback.fst B.hom f = ((u ≫ fst B B) * (u ≫ snd B B)).left :=
    (h.2 Y x' y' _ _ (hu1.trans hx.symm) (hu2.trans hy.symm)).symm
  have o : (1 : Y ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (Y.hom ≫ f) ⟶ B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h Y))
  have hx2 : x2 B = ![fst B B, snd B B] := rfl
  fin_cases k
  · show (x' * y').left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0, 1}).left
    rw [hx2, psum_two_01, key, comp_mul, m]
  · show x'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0}).left
    rw [hx2, psum_two_0, key, hu1, hx]
  · show y'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {1}).left
    rw [hx2, psum_two_1, key, hu2, hy]
  · show (1 : Y ⟶ (Over.pullback f).obj B).left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ∅).left
    rw [hx2, psum_two_e, key, o]
    congr 1
    simp [Hom.one_def]

end GlobalTheory.PairPts
