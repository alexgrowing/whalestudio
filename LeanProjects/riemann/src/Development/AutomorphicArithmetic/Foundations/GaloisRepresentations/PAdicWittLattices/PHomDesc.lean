import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem pow_left {S S' : Scheme.{0}} {c : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {a : A'.left ⟶ A.left} (h : IsGrpPullback A' A c a) (d : ℕ) :
    ((𝟙 A') ^ d).left ≫ a = a ≫ ((𝟙 A) ^ d).left := by
  have e1 := GlobalTheory.ObjPull.pushEquiv_left h A' ((𝟙 A') ^ d)
  have e2 := GlobalTheory.ObjPull.pushEquiv_left h A' (𝟙 A')
  rw [map_pow] at e1
  have e3 : (GlobalTheory.ObjPull.pushEquiv h A' (𝟙 A')) ^ d = GlobalTheory.ObjPull.pushEquiv h A' (𝟙 A') ≫ (𝟙 A) ^ d := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e1, e3, Over.comp_left, e2]
  simp

private theorem push_comp {S S' : Scheme.{0}} {c : S' ⟶ S} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left} (hA : IsGrpPullback A' A c a)
    (hB : IsGrpPullback B' B c b) (ψ : A ⟶ B) (ψ' : A' ⟶ B') (e : ψ'.left ≫ b = a ≫ ψ.left) (T : Over S') (x : T ⟶ A') :
    GlobalTheory.ObjPull.pushEquiv hA T x ≫ ψ = GlobalTheory.ObjPull.pushEquiv hB T (x ≫ ψ') := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, GlobalTheory.ObjPull.pushEquiv_left, GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc,
    Category.assoc, e]

private theorem monHom_desc {S S' : Scheme.{0}} (c : S' ⟶ S) [Flat c] [Surjective c] {A B : Over S} {A' B' : Over S'}
    [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hA : IsGrpPullback A' A c a) (hB : IsGrpPullback B' B c b) (ψ : A ⟶ B) (ψ' : A' ⟶ B')
    (e : ψ'.left ≫ b = a ≫ ψ.left) [IsMonHom ψ'] : IsMonHom ψ := by
  apply GlobalTheory.Serre.isMonHom_of_mul_comp
  intro T x y
  let T' : Over S' := Over.mk (pullback.snd T.hom c)
  let q : Over.mk (T'.hom ≫ c) ⟶ T := Over.homMk (pullback.fst T.hom c) (by simp [T', pullback.condition])
  have hq : Epi (pullback.fst T.hom c) := Flat.epi_of_flat_of_surjective _
  have hx : q ≫ x = GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ x)) := by simp
  have hy : q ≫ y = GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ y)) := by simp
  set x' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ x)
  set y' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ y)
  have key : q ≫ ((x * y) ≫ ψ) = q ≫ (x ≫ ψ * y ≫ ψ) := by
    calc q ≫ ((x * y) ≫ ψ) = (q ≫ x * q ≫ y) ≫ ψ := by rw [← Category.assoc, MonObj.comp_mul]
      _ = GlobalTheory.ObjPull.pushEquiv hA T' (x' * y') ≫ ψ := by rw [hx, hy, map_mul]
      _ = GlobalTheory.ObjPull.pushEquiv hB T' (x' ≫ ψ' * y' ≫ ψ') := by
        rw [push_comp hA hB ψ ψ' e, MonObj.mul_comp]
      _ = (GlobalTheory.ObjPull.pushEquiv hA T' x' ≫ ψ) * (GlobalTheory.ObjPull.pushEquiv hA T' y' ≫ ψ) := by
        rw [map_mul, push_comp hA hB ψ ψ' e, push_comp hA hB ψ ψ' e]
      _ = q ≫ (x ≫ ψ * y ≫ ψ) := by
        rw [← hx, ← hy, MonObj.comp_mul, Category.assoc, Category.assoc]
  ext1
  have hl := congrArg Over.Hom.left key
  simp only [Over.comp_left, q, Over.homMk_left] at hl
  exact (cancel_epi _).1 hl

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pHomDesc :
    EtDesc → HomDesc := by
  intro etd S S' _ c _ _ _ A B _ _ _ _ A' B' _ _ _ _ hAab hBab hB'ab a b hA hB ψ ψ' e hψ'
  haveI : Flat c := inferInstance
  have hψ : IsMonHom ψ := monHom_desc c hA hB ψ ψ' e
  refine ⟨hψ, ?_⟩
  intro χ' d hχ' hsurj hfin h1 h2
  haveI : Smooth B'.hom := hB'ab.smooth
  haveI : AlgebraicGeometry.IsReduced B'.left := GlobalTheory.isReduced_of_smooth_of_isReduced B'.hom
  haveI : IsFinite b := MorphismProperty.of_isPullback (P := @IsFinite) hB.1.flip ‹_›
  haveI : Etale b := MorphismProperty.of_isPullback (P := @Etale) hB.1.flip ‹_›
  haveI : Surjective b := MorphismProperty.of_isPullback (P := @Surjective) hB.1.flip ‹_›
  haveI : Flat a := MorphismProperty.of_isPullback (P := @Flat) hA.1.flip ‹_›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) hA.1.flip ‹_›
  haveI : IsProper A.hom := hAab.proper
  have ea : a ≫ A.hom = A'.hom ≫ c := hA.1.w
  have eb : b ≫ B.hom = B'.hom ≫ c := hB.1.w
  have hcond : (χ'.left ≫ a) ≫ A.hom = b ≫ B.hom := by
    rw [Category.assoc, ea, ← Category.assoc, Over.w χ', eb]
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ B'.left), x ≫ b = y ≫ b →
      x ≫ (χ'.left ≫ a) = y ≫ (χ'.left ≫ a) := by
    intro Ω _ _ x y hxy
    haveI := hfin
    have lift : ∀ z : sp Ω ⟶ B'.left, ∃ z' : sp Ω ⟶ A'.left, z' ≫ ψ'.left = z := by
      intro z
      obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
      obtain ⟨z', hz', -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ'.left Ω z v hv
      exact ⟨z', hz'⟩
    obtain ⟨x', hx'⟩ := lift x
    obtain ⟨y', hy'⟩ := lift y
    have red : ∀ (z : sp Ω ⟶ B'.left) (z' : sp Ω ⟶ A'.left), z' ≫ ψ'.left = z →
        z ≫ χ'.left ≫ a = z' ≫ a ≫ ((𝟙 A) ^ d).left := by
      intro z z' hz
      rw [← hz, ← pow_left hA d, ← h1, Over.comp_left]
      simp only [Category.assoc]
    rw [red x x' hx', red y y' hy']
    have hx2 : x' ≫ A'.hom = x ≫ B'.hom := by rw [← hx', Category.assoc, Over.w ψ']
    have hy2 : y' ≫ A'.hom = y ≫ B'.hom := by rw [← hy', Category.assoc, Over.w ψ']
    have hyx : (y ≫ B'.hom) ≫ c = (x ≫ B'.hom) ≫ c := by
      rw [Category.assoc, Category.assoc, ← eb, ← Category.assoc, ← Category.assoc, hxy]
    let T' : Over S' := Over.mk (x ≫ B'.hom)
    let U : Over.mk (T'.hom ≫ c) ⟶ A := Over.homMk (x' ≫ a) (by
      show (x' ≫ a) ≫ A.hom = (x ≫ B'.hom) ≫ c
      rw [Category.assoc, ea, ← Category.assoc, hx2])
    let V : Over.mk (T'.hom ≫ c) ⟶ A := Over.homMk (y' ≫ a) (by
      show (y' ≫ a) ≫ A.hom = (x ≫ B'.hom) ≫ c
      rw [Category.assoc, ea, ← Category.assoc, hy2, hyx])
    have hUV : U ≫ ψ = V ≫ ψ := by
      ext1
      simp only [Over.comp_left, U, V, Over.homMk_left]
      rw [Category.assoc, ← e, ← Category.assoc, hx', Category.assoc, ← e, ← Category.assoc, hy', hxy]
    have hW : (U / V) ≫ ψ = 1 := by
      rw [div_eq_mul_inv, MonObj.mul_comp, GrpObj.inv_comp, hUV, mul_inv_cancel]
    have hW' : GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (U / V)) = U / V := by simp
    set W' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (U / V)
    have hW'ψ : W' ≫ ψ' = 1 := by
      apply (GlobalTheory.ObjPull.pushEquiv hB T').injective
      rw [← push_comp hA hB ψ ψ' e, hW', hW, map_one]
    have hpow : W' ^ d = 1 := by
      calc W' ^ d = W' ≫ (𝟙 A') ^ d := by rw [MonObj.comp_pow, Category.comp_id]
        _ = W' ≫ ψ' ≫ χ' := by rw [h1]
        _ = 1 := by rw [← Category.assoc, hW'ψ, MonObj.one_comp]
    have hWd : (U / V) ^ d = 1 := by rw [← hW', ← map_pow, hpow, map_one]
    have hUd : U ^ d = V ^ d := by rwa [div_pow, div_eq_one] at hWd
    have hU : U ^ d = U ≫ (𝟙 A) ^ d := by rw [MonObj.comp_pow, Category.comp_id]
    have hV : V ^ d = V ≫ (𝟙 A) ^ d := by rw [MonObj.comp_pow, Category.comp_id]
    have hl := congrArg Over.Hom.left hUd
    rw [hU, hV, Over.comp_left, Over.comp_left] at hl
    simpa only [U, V, Over.homMk_left, Category.assoc] using hl
  obtain ⟨hbe, g, hg⟩ := etd b B.hom A.hom (χ'.left ≫ a) hcond hpts
  have hgA : g ≫ A.hom = B.hom := by
    rw [← cancel_epi b, ← Category.assoc, hg, hcond]
  have ha : Epi a := Flat.epi_of_flat_of_surjective a
  refine ⟨Over.homMk g hgA, hg.symm, ?_, ?_⟩
  · ext1
    rw [← cancel_epi a]
    simp only [Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, ← e, Category.assoc, hg, ← Category.assoc, ← Over.comp_left, h1, pow_left hA d]
  · ext1
    rw [← cancel_epi b]
    simp only [Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, hg, Category.assoc, ← e, ← Category.assoc, ← Over.comp_left, h2, pow_left hB d]
