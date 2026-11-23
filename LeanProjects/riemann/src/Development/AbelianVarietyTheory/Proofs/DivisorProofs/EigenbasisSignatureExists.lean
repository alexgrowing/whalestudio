import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.EigBasisExist

theorem exists_eigBasis_of_lieMult {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* k) {n : ℕ} (h : LieMult act (𝟙 (Sp k)) χ n) :
    ∃ x : Fin n → (epsR k ⟶ G), EigenvectorLieDegree.IsEigBasis act χ x := by
  obtain ⟨b⟩ := (Serre.Lie.lieMult_id_iff act χ n).1 h
  have hm : ∀ v : Serre.Lie act, v ∈ Serre.Lie.eig act χ ↔ EigenvectorLieDegree.IsEigVec act χ v.hom := fun v =>
    ⟨fun hv => ⟨v.isTangent, fun a => congrArg (fun z : Serre.Lie act => z.hom.left) (hv a)⟩,
      fun hv a => Serre.Lie.ext (Over.OverMorphism.ext (hv.2 a))⟩
  refine ⟨fun i => (b i : Serre.Lie act).hom, fun i => (hm _).1 (b i).2, fun w hw => ?_⟩
  let z : Serre.Lie.eig act χ := ⟨Serre.Lie.mk act w hw.1, (hm _).2 hw⟩
  have key : ∀ c : Fin n → k, IsLieComb c (fun i => (b i : Serre.Lie act).hom) w ↔ b.equivFun z = c := fun c => by
    rw [Serre.Lie.isLieComb_iff c (fun i => (b i : Serre.Lie act)) w, ← LinearEquiv.eq_symm_apply,
      Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact ⟨fun e => Serre.Lie.ext e, fun e => congrArg Serre.Lie.hom e⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

theorem exists_eigBases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  intro E _ _ _ H D l c k _ _ j o τ hτ
  let φ : k →+* AlgebraicClosure k := algebraMap k _
  have := o.t.semi.smooth
  have d := (o.geom (AlgebraicClosure k) (spMap φ)
    (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom))
    (by rw [spMap_comp_spMap, spMap_comp_spMap])).1
  have iff : ∀ σ : E →+* ℂ, (φ.comp ((EigenvectorLieDegree.embIn c j σ).comp (algebraMap (𝓞 E) E))) H.rt =
      (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ ↔ σ (H.rt : E) = H.rt0 := fun σ =>
    (φ.injective.eq_iff.trans j.injective.eq_iff).trans Subtype.ext_iff
  have ne : conjEmb τ (H.rt : E) ≠ H.rt0 := fun e => by
    have e' : (starRingEnd ℂ) H.rt0 = H.rt0 := by rw [← hτ]; exact e.trans hτ.symm
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e'
    have h := H.sqrt_neg_disc_sq
    rw [hr] at h
    have h' : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg r]
  exact ⟨exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).1 ((iff τ).2 hτ))),
    exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).2 fun e => ne ((iff _).1 e)))⟩

end GlobalTheory.EigBasisExist
