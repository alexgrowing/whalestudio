import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverDeg

theorem residueDegree_eq_one_of_surjectiveOnStalks {X Y : Scheme} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : f.residueDegree x = 1 := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨s, rfl⟩ := Scheme.residue_surjective X x y
    obtain ⟨t, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (f := f) x s
    exact ⟨Y.residue (f x) t, rfl⟩
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have hb : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective (algebraMap (Y.residueField (f x)) (X.residueField x)), hs⟩
  have e := (AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f x)) (X.residueField x)) hb).toLinearEquiv
  unfold Scheme.Hom.residueDegree
  rw [← e.finrank_eq, Module.finrank_self]

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

theorem j_genericPoint {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    V.j (genericPoint V.G) = genericPoint V.X := by
  haveI := V.int
  haveI := V.intG

  let η : Sp F := ⟨⊥, Ideal.bot_prime⟩
  have hη : ∀ w : Sp F, (spMap (algebraMap (𝓞 F) F) w).asIdeal = ⊥ := by
    intro w
    have hw : w.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top w.asIdeal with h | h
      · exact h
      · exact absurd h w.isPrime.ne_top
    change Ideal.comap _ w.asIdeal = ⊥
    rw [hw, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (NumberField.RingOfIntegers.coe_injective)
  have hw := V.pb.w
  have hpj : ∀ z : V.G, (V.p (V.j z)).asIdeal = ⊥ := by
    intro z
    have : V.p (V.j z) = spMap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) z) := by
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    rw [this, hη]
  have hpX : V.p (genericPoint V.X) = spMap (algebraMap (𝓞 F) F) η := by
    apply PrimeSpectrum.ext
    rw [hη]
    have hs : genericPoint V.X ⤳ V.j (genericPoint V.G) := genericPoint_specializes _
    have := (PrimeSpectrum.le_iff_specializes _ _).mpr (hs.map V.p.continuous)
    exact le_bot_iff.mp ((hpj _) ▸ this)
  obtain ⟨w, hw'⟩ : genericPoint V.X ∈ Set.range (Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨η, hpX.symm⟩
  have hz : V.j (V.pb.isoPullback.inv w) = genericPoint V.X := by
    have e : V.pb.isoPullback.inv ≫ V.j = Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F)) := by
      rw [Iso.inv_comp_eq, V.pb.isoPullback_hom_fst]
    rw [← hw', ← e, Scheme.Hom.comp_apply]
  have h1 : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
    rw [← hz]; exact (genericPoint_specializes _).map V.j.continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

theorem j_residueDegree {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (x : V.G) :
    V.j.residueDegree x = 1 := by
  haveI := CoverHt.isPreimmersion_j V
  exact residueDegree_eq_one_of_surjectiveOnStalks V.j x

theorem map_genericPoint_and_deg : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (V' : Cover Y) (b : V'.X ⟶ V.X) (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G),
    V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π → g (genericPoint V'.G) = genericPoint V.G →
    b (genericPoint V'.X) = genericPoint V.X ∧ b.residueDegree (genericPoint V'.X) * V.deg = V'.deg := by
  intro F _ _ Y V V' b _ g hjb hπ hg
  have hpt : b (genericPoint V'.X) = genericPoint V.X := by
    rw [← j_genericPoint V', ← Scheme.Hom.comp_apply, hjb, Scheme.Hom.comp_apply, hg, j_genericPoint V]
  refine ⟨hpt, ?_⟩
  have h1 := CurveDegreesCompare.residueDegree_comp V'.j b (genericPoint V'.G)
  have h2 := CurveDegreesCompare.residueDegree_comp g V.j (genericPoint V'.G)
  have h3 := CurveDegreesCompare.residueDegree_comp g V.π (genericPoint V'.G)
  rw [hjb, h2] at h1
  rw [j_residueDegree, j_residueDegree, mul_one, one_mul, j_genericPoint V'] at h1
  unfold Cover.deg
  rw [← hπ, h3, hg, h1, mul_comm]

end GlobalTheory.CoverDeg
