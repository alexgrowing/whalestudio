import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem isPreirreducible_connectedComponent_of_smooth {K : Type} [Field K] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] (z : Z) : IsPreirreducible (connectedComponent z) := by
  have hK : GlobalTheory.IsNormalScheme (Spec (.of K)) := inferInstance
  have : GlobalTheory.IsNormalScheme Z := (GlobalTheory.isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((GlobalTheory.isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  rw [GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent]
  exact isIrreducible_irreducibleComponent.2

theorem apply_eq_of_isPreirreducible {T F : Type} [CommRing T] [Field F] (f g : T →+* F)
    (C : Set (PrimeSpectrum T)) (hC : IsPreirreducible C) (z : PrimeSpectrum F)
    (hf : PrimeSpectrum.comap f z ∈ C) (hg : PrimeSpectrum.comap g z ∈ C)
    (e : T) (he : IsIdempotentElem e) : f e = g e := by
  have hz : ∀ a : F, a ∈ z.asIdeal ↔ a = 0 := by
    intro a
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
    rw [this, Ideal.mem_bot]
  have key : ∀ (f g : T →+* F), PrimeSpectrum.comap f z ∈ C → PrimeSpectrum.comap g z ∈ C →
      f e = 0 → g e = 1 → False := by
    intro f g hf hg h0 h1
    obtain ⟨x, -, hx1, hx2⟩ := hC (PrimeSpectrum.basicOpen (1 - e)) (PrimeSpectrum.basicOpen e)
      (PrimeSpectrum.basicOpen _).2 (PrimeSpectrum.basicOpen _).2
      ⟨_, hf, by simp [hz, h0]⟩ ⟨_, hg, by simp [hz, h1]⟩
    have h : (1 - e) * e ∈ x.asIdeal := by
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]; exact x.asIdeal.zero_mem
    exact (x.2.mem_or_mem h).elim hx1 hx2
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map f) with h | h <;>
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map g) with h' | h'
  · rw [h, h']
  · exact (key f g hf hg h h').elim
  · exact (key g f hg hf h' h).elim
  · rw [h, h']

theorem lift_eq_of_sameComp_of_isIdempotentElem :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  intro K _ _ X s R _ _ i p q hs hi his ⟨hp, hq, hpq⟩ e he
  let T := ℂ ⊗[K] R
  let j : Sp T ⟶ pullback s (spMap (algebraMap K ℂ)) :=
    (pullbackSpecIso K ℂ R).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap (algebraMap K R)) (spMap (algebraMap K ℂ)) s (spMap (algebraMap K ℂ)) i (𝟙 _) (𝟙 _)
      (by rw [his, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : ℂ →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* T := (Algebra.TensorProduct.includeRight (R := K) (A := ℂ) (B := R) : R →+* T)
  have hj1 : j ≫ pullback.fst _ _ = spMap iR ≫ i := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd _ _ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  have hl : ∀ (r : R →ₐ[K] ℂ) (hr : (spMap r.toRingHom ≫ i) ≫ s = 𝟙 _ ≫ spMap (algebraMap K ℂ)),
      pullback.lift (spMap r.toRingHom ≫ i) (𝟙 _) hr =
        spMap (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _)).toRingHom ≫ j := by
    intro r hr
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hj1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      change r x = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) (1 ⊗ₜ[K] x)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    · rw [pullback.lift_snd, Category.assoc, hj2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      change (x : ℂ) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) ((x : ℂ) ⊗ₜ[K] 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl
  let z : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := hpq z
  have hC := isPreirreducible_connectedComponent_of_smooth (pullback.snd s (spMap (algebraMap K ℂ)))
    (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  have h2 := mem_connectedComponent (x := pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  generalize connectedComponent (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z) = C at h1 h2 hC
  rw [hl] at h1 h2
  exact apply_eq_of_isPreirreducible _ _ (j ⁻¹' C) (hC.preimage j.isOpenEmbedding) z h1 h2 e he

end GlobalTheory.KeyFam
