import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isQProjOver_opens_of_noetherian {o : Type} [CommRing o] [IsNoetherianRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (h : IsQProjOver s) (U : X.Opens) : IsQProjOver (U.ι ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str o N)
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by simp⟩

theorem isIso_of_closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (z : Z ⟶ Sp R)
    [IsOpenImmersion z] (h : (IsLocalRing.closedPoint R : Sp R) ∈ Set.range z) : IsIso z := by
  have hs : Function.Surjective z := by
    intro p
    exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open z.isOpenEmbedding.isOpen_range h
  have : Epi z.base := (TopCat.epi_iff_surjective _).2 hs
  exact IsOpenImmersion.isIso z

theorem TObj.exists_hasTh_of_isLocalRing (h1 : Out.Laws) (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (hN : Odd N') {R : Type} [CommRing R] [IsLocalRing R] {s' : Sp R ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s') : ∃ v, t.HasTh (𝟙 (Sp R)) v := by
  obtain ⟨R', _, z, v, hz, hp, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base h1 h2 o g N' J b _ s' t hN (IsLocalRing.closedPoint R)
  have := isIso_of_closedPoint_mem_range z hp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (inv z)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s' t R' R φ.hom z v hv
  have e : spMap φ.hom ≫ z = 𝟙 (Sp R) := by
    change Spec.map φ ≫ z = _
    rw [hφ, IsIso.inv_hom_id]
  rw [e] at this
  exact ⟨_, this⟩

theorem WFam.qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  intro h1 h2 o _ g n N' J b em C Mat κ F hN
  have := F.Y.flat
  have := F.Y.reduced
  refine ⟨?_, inferInstance, isReduced_of_isOpenImmersion F.U.ι, ?_⟩
  · by_cases hn : IsNoetherianRing o
    · exact Or.inl (isQProjOver_opens_of_noetherian F.Y.qproj F.U)
    · exact Or.inr hn
  · intro R _ _ x y s' t hxy hx hy
    obtain ⟨v, hv⟩ := TObj.exists_hasTh_of_isLocalRing h1 h2 hN t
    have vx := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t x R (𝟙 _) v hx).1 hv
    have vy := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t y R (𝟙 _) v hy).1 hv
    rw [Category.id_comp] at vx vy
    have cx := (F.th R x v).1 vx
    have cy := (F.th R y v).1 vy
    obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ F.U.ι ≫ F.Y.s)
    have bx : (x ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hβ]; rfl
    have by' : (y ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hxy, ← hβ]; rfl
    have hin := F.Y.loc R β.hom _ v bx cx
    have := (F.Y.pts R β.hom v hin).unique ⟨bx, cx⟩ ⟨by', cy⟩
    exact (cancel_mono F.U.ι).1 this

end GlobalTheory.ZM
