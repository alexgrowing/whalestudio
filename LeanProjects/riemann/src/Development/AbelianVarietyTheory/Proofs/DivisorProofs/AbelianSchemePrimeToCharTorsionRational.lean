import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsRat

theorem exists_factor_of_isFinite {K₀ K : Type} [Field K₀] [IsAlgClosed K₀] [Field K]
    (e : K₀ →+* K) {Z : Scheme.{0}} (s : Z ⟶ Sp K₀) [IsFinite s] (w : Sp K ⟶ Z)
    (hw : w ≫ s = spMap e) : ∃ w₀ : Sp K₀ ⟶ Z, w = spMap e ≫ w₀ := by
  haveI : IsAffine Z := isAffine_of_isAffineHom s
  let φ : CommRingCat.of K₀ ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ s)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ s := Spec.map_preimage _
  have hF : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hF' : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hF
  let ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w ≫ Z.isoSpec.hom)
  have hψ : Spec.map ψ = w ≫ Z.isoSpec.hom := Spec.map_preimage _
  have hφψ : φ ≫ ψ = CommRingCat.ofHom e := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw]
  letI : Algebra K₀ Γ(Z, ⊤) := φ.hom.toAlgebra
  letI : Algebra K₀ K := e.toAlgebra
  haveI : Module.Finite K₀ Γ(Z, ⊤) := hF'
  have hmem : ∀ b, ψ.hom b ∈ e.range := by
    intro b
    have hb : IsIntegral K₀ b := Algebra.IsIntegral.isIntegral b
    let ψa : Γ(Z, ⊤) →ₐ[K₀] K :=
      { ψ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hφψ }
    have hi : IsIntegral K₀ (ψ.hom b) := hb.map ψa
    exact minpoly.mem_range_of_degree_eq_one K₀ _
      (IsAlgClosed.degree_eq_one_of_irreducible K₀ (minpoly.irreducible hi))
  let E : K₀ ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b h => e.injective (congrArg Subtype.val h), e.rangeRestrict_surjective⟩
  let ψ₀ : Γ(Z, ⊤) →+* K₀ := E.symm.toRingHom.comp (ψ.hom.codRestrict e.range hmem)
  refine ⟨Spec.map (CommRingCat.ofHom ψ₀) ≫ Z.isoSpec.inv, ?_⟩
  have h2 : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom e = ψ := by
    ext b
    show e (E.symm ⟨ψ.hom b, hmem b⟩) = ψ.hom b
    exact congrArg Subtype.val (E.apply_symm_apply ⟨ψ.hom b, hmem b⟩)
  rw [← Category.assoc, ← Spec.map_comp, h2, hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsion_point_rational : ∀ (K₀ K : Type) [Field K₀] [IsAlgClosed K₀] [Field K] (e : K₀ →+* K)
    (Y : Over (Sp K₀)) [GrpObj Y],
    IsAbelianScheme Y → ∀ n : ℕ, IsUnit (n : K₀) → ∀ y : Over.mk (spMap e) ⟶ Y, y ^ n = 1 →
    ∃ y₀ : Sp K₀ ⟶ Y.left, y.left = spMap e ≫ y₀ := by
  intro K₀ K _ _ _ e Y _ hY n hn y hy
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn
    · exact h
  haveI := GlobalTheory.MulFiniteAny.isFinite_mulA K₀ Y hY n hn1
  let o : Sp K₀ ⟶ Y.left := (η[Y] : 𝟙_ (Over (Sp K₀)) ⟶ Y).left
  have hyo : y.left ≫ (mulA Y n).left = spMap e ≫ o := by
    have h1 : y ≫ mulA Y n = 1 := by
      rw [mulA, MonObj.comp_pow, Category.comp_id, hy]
    have h2 : y.left ≫ (mulA Y n).left = (toUnit (Over.mk (spMap e)) ≫ η[Y]).left := by
      rw [← Over.comp_left, h1, Hom.one_def]
    have h3 : (toUnit (Over.mk (spMap e))).left = spMap e := by
      have := Over.w (toUnit (Over.mk (spMap e)))
      simpa using this
    rw [h2, Over.comp_left, h3]
  obtain ⟨w₀, hw₀⟩ := exists_factor_of_isFinite e (pullback.snd (mulA Y n).left o)
    (pullback.lift y.left (spMap e) hyo) (pullback.lift_snd _ _ _)
  refine ⟨w₀ ≫ pullback.fst (mulA Y n).left o, ?_⟩
  rw [← Category.assoc, ← hw₀, pullback.lift_fst]

end GlobalTheory.TorsRat
