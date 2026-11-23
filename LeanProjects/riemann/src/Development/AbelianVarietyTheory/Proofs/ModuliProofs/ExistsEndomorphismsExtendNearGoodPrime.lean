import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElementStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.EndBuild

theorem exists_endomorphism_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ i hden hfam hsm => ?_⟩
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hrep, hp⟩, -, hfib⟩ := hfam
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z.hom (spMap x) ⟶ Z.left) → Prop := fun K _ x f =>
    ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (φ : t.A.left ⟶ Z.left)
      (hφ : Fib (n ^ 2) M th sc x t φ), Good b Mat κ β v x t ∧
      f = hφ.1.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
  have hG : ∀ q ∈ objPrimes b Mat κ β v,
      ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ := by
    intro q hq
    obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t ht
    exact ⟨K, inferInstance, x, _, hx, inferInstance, s, t, φ, hφ, ht, rfl⟩
  obtain ⟨K₀, _, x₀, φ₀, hx₀, hG₀⟩ := hG q₀ hden.2
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d G
    hrep hrep hprop hprop hsm (by
      rintro K _ x f ⟨_, s, t, φ, ⟨hφ, ⟨σ, hE, hσ⟩, hb, hl⟩, ⟨hs, ht, -⟩, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t.A ⟶ t.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · rw [← spMap_comp] at hs
        subst hs
        exact fun p' q' f hf h => hQ K (x.comp β) t σ p' q' f ht hf hE h)
    (fun r hr => hden.1 r fun q hq hqp => hr q (hG q hq) hqp) K₀ x₀ φ₀ hG₀
  refine ⟨f, fun h => hf (by rw [← hx₀] at h; exact h), fun R' _ ρ hu Z' π hpb => ?_⟩
  obtain ⟨F₀, hF₀, hF⟩ := H R' ρ hu Z'.left π Z'.hom hpb.w
  refine ⟨Over.homMk (hpb.lift F₀ Z'.hom hF₀) (hpb.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ ht hφ hw
  have e := hF K (x.comp ρ) _ ⟨inferInstance, s, t, φ ≫ π, hφ, ht, rfl⟩ (hφ.1.isoPullback.inv ≫ φ)
    (by rw [Category.assoc, IsPullback.isoPullback_inv_fst])
  rw [Category.assoc, cancel_epi] at e
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, e]
    exact congrArg (φ ≫ ·) (hpb.lift_fst _ _ _)
  · rw [Category.assoc, Category.assoc, Over.w, hw, ← Category.assoc, Over.w]

end GlobalTheory.ZM.NearBuild
end
