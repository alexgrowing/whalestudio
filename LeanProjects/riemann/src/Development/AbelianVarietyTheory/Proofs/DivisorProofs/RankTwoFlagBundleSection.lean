import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.CovTest.Multisection

theorem nonempty_flag_of_field (K : Type) [Field K] (F : (Spec (CommRingCat.of K)).Modules)
    (hF : VB.IsVB F 2) : Nonempty (Vert.Flag F 2) := by
  have key : ∀ (G : (Spec (CommRingCat.of K)).Modules) (r : ℕ), VB.IsVB G r →
      ∃ e : Fin r → Γ(G, ⊤), VB.IsFrame e := by
    intro G r h
    obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint K)
    have hU : ⊤ ≤ U := fun x _ => (Subsingleton.elim x (IsLocalRing.closedPoint K)) ▸ hx
    exact ⟨_, he.res hU⟩
  have hO := VB.isVB_structureModule (Spec (CommRingCat.of K))
  obtain ⟨e, he⟩ := key F 2 hF
  obtain ⟨e', he'⟩ := key _ 2 (hO.biprod hO)
  exact ⟨(Vert.Flag.ofBiprod hO hO).ofIso (he'.iso he)⟩

theorem exists_multisection : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  intro k _ B Y _ _ q p d hq hp π w E hE fl hfl
  let K : Type := B.residueField (genericPoint B)
  let g : Spec (CommRingCat.of K) ⟶ B := B.fromSpecResidueField (genericPoint B)
  obtain ⟨fl'⟩ := nonempty_flag_of_field K ((Scheme.Modules.pullback g).obj E) (hE.pullback g)
  obtain ⟨g', ⟨hg', -⟩, -⟩ := hfl _ g (fun _ => fl')
  have hc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g'
  obtain ⟨e₁, d₁⟩ := ProjDrop.deg_eq_of_fieldPoint π (g' (IsLocalRing.closedPoint K)) (genericPoint B)
    (Ω := K) _ (𝟙 (B.residueField (genericPoint B)) : B.residueField (genericPoint B) ⟶ CommRingCat.of K)
    (by rw [hc, hg', Spec.map_id]; exact (Category.id_comp _).symm)
  have h1 : ProjDrop.deg (𝟙 (B.residueField (genericPoint B)) :
      B.residueField (genericPoint B) ⟶ CommRingCat.of K).hom = 1 := by
    rw [CommRingCat.hom_id]
    exact ProjDrop.deg_equiv (RingEquiv.refl K)
  have hn : π.residueDegree (g' (IsLocalRing.closedPoint K)) ≠ 0 := by
    intro h
    rw [h1, h, zero_mul] at d₁
    exact one_ne_zero d₁
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (g' (IsLocalRing.closedPoint K))
  have g₁ : (i ≫ π) (genericPoint Z) = genericPoint B := by rw [Scheme.Hom.comp_apply, hi, e₁]
  have n₁ : (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact hn
  have hproj : IsProjOver (i ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp.isProjOver
  have hflat : Flat ((i ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    haveI := hq.flat
    haveI : CharZero (B.residueField ((i ≫ π) (genericPoint Z))) :=
      g₁.symm ▸ DimCover.charZero_residueField (q ≫ spMap (Int.castRingHom k))
    haveI := (RingHom.charZero_iff ((i ≫ π).residueFieldMap (genericPoint Z)).hom.injective).mp this
    exact ProjDrop.charZero_of_residueField (genericPoint Z)
  refine ⟨Z, inferInstance, i, ⟨hq.isDomain, hq.finite, inferInstance, hproj, hflat,
    DimCover.topologicalKrullDim_eq k B Z q (i ≫ p) d hq hproj hflat (i ≫ π)
      (by rw [Category.assoc, w]) g₁ n₁⟩, g₁, n₁⟩

end GlobalTheory.CovTest.Multisection

end
