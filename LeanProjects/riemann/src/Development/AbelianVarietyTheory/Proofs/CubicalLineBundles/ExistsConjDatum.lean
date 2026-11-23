import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CM.ConjDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E)) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def ConjLat {H : Host E} (D : Datum H) : Type := D.La

instance {H : Host E} (D : Datum H) : AddCommGroup (ConjLat D) := D.acg

instance {H : Host E} (D : Datum H) : Module (𝓞 E) (ConjLat D) :=
  Module.compHom D.La (H.bar : 𝓞 E →+* 𝓞 E)

def toLat {H : Host E} (D : Datum H) : ConjLat D ≃+ D.La := AddEquiv.refl _

theorem toLat_smul {H : Host E} (D : Datum H) (s : 𝓞 E) (a : ConjLat D) :
    toLat D (s • a) = H.bar s • toLat D a := rfl

theorem finite {H : Host E} (D : Datum H) : Module.Finite (𝓞 E) (ConjLat D) := by
  have := D.fin
  let f : D.La →ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { toFun := (toLat D).symm
      map_add' := map_add _
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Finite.of_surjective f (toLat D).symm.surjective

theorem projective {H : Host E} (D : Datum H) : Module.Projective (𝓞 E) (ConjLat D) := by
  have := D.proj
  have i1 : RingHomInvPair (H.bar : 𝓞 E →+* 𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) :=
    ⟨RingHom.ext (bar_bar H), RingHom.ext (bar_bar H)⟩
  let f : D.La ≃ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { (toLat D).symm with
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Projective.of_equiv f

theorem finrank_eq {H : Host E} (D : Datum H) :
    Module.finrank (𝓞 E) (ConjLat D) = Module.finrank (𝓞 E) D.La := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv H.bar (toLat D) H.bar.bijective (toLat_smul D)]

def conj {H : Host E} (D : Datum H) : Datum H where
  La := ConjLat D
  fin := finite D
  proj := projective D
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := fun a x y => D.adj (H.bar a) x y
  p := D.q
  q := D.p
  rank := by rw [finrank_eq, D.rank]; push_cast; ring
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨J, h1, h2, h3, fun a A t hA ht => h4 (H.bar a) A t hA ?_⟩
    rw [ht]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [emb_bar, Complex.conj_conj, add_comm]

end GlobalTheory.CM.ConjDatum

namespace GlobalTheory.CM

theorem exists_conjDatum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∃ (D' : Datum H) (e : D'.La ≃+ D.La), D'.p = D.q ∧ D'.q = D.p ∧ (∀ (s : 𝓞 E) a, e (s • a) = H.bar s • e a) ∧ ∀ a b, D'.EF a b = D.EF (e a) (e b) :=
  fun _ _ _ _ _ D => ⟨ConjDatum.conj D, ConjDatum.toLat D, rfl, rfl, ConjDatum.toLat_smul D, fun _ _ => rfl⟩

end GlobalTheory.CM
end
