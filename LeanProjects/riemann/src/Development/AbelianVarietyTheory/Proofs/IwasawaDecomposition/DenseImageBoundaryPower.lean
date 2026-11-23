import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.BlowSupp

theorem dense_compl_support_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (ρ : gen Y ⟶ gen X) (n : ℕ),
    Y.jQ ≫ ρ = X.jQ → ρ ⁻¹' Set.range X.jQ = Set.range Y.jQ → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    Dense (((((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support : Set X.X)ᶜ) := by
  intro E _ _ _ H D l Xo c X Y BY ρ n _ hpre hab
  obtain ⟨⟨_, _⟩, -, _⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1
  have hdom := (GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F X.X _ X.s X.jQ X.flat X.proj X.jQ_open X.jQ_dense).2.2.2.2.2.1
  have hd : Dense (Set.range X.j) := hdom.denseRange

  have hb : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hι : IsPreimmersion (genι X) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hemb : Topology.IsEmbedding (genι X) := (genι X).isEmbedding
  have hQ : QuasiCompact (ρ ≫ genι X) := by
    have hYc : CompactSpace Y.X :=
      (GlobalTheory.genericPart_dense_proOpen c.F c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.1
    have hXs : X.X.IsSeparated :=
      (GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F X.X _ X.s X.jQ X.flat X.proj X.jQ_open X.jQ_dense).2.2.1
    have hiso : IsIso (spMap (RingHom.id c.F)) := by
      have e : spMap (RingHom.id c.F) = 𝟙 _ := by
        first | (unfold spMap; exact Spec.map_id _) | (simp [spMap]) | rfl
      rw [e]; infer_instance
    have : CompactSpace (gen Y) := QuasiCompact.compactSpace_of_compactSpace (genι Y)
    exact quasiCompact_of_compactSpace _
  refine hd.mono ?_
  haveI := X.jQ_open
  rintro _ ⟨z, rfl⟩ hz
  rw [Scheme.IdealSheafData.support_map] at hz
  have hz' : (X.j z) ∈ closure ((ρ ≫ genι X) '' ((((BY.idealSheaf ^ n).comap (genι Y)).support : Set _))) := hz
  have hj : X.j z = genι X (X.jQ z) := rfl
  rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, ← Set.mem_preimage,
    ← hemb.isInducing.closure_eq_preimage_closure_image] at hz'
  obtain ⟨_, ⟨v, rfl⟩, ⟨y, hy, hyv⟩⟩ := mem_closure_iff.1 hz' _ (X.jQ.isOpenEmbedding.isOpen_range) ⟨z, rfl⟩
  have hy' : y ∈ Set.range Y.jQ := by rw [← hpre]; exact ⟨v, hyv.symm⟩
  obtain ⟨u, rfl⟩ := hy'
  rw [Scheme.IdealSheafData.support_comap] at hy
  have hsupp : genι Y (Y.jQ u) ∈ BY.idealSheaf.support := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hy
    · rw [Scheme.IdealSheafData.support_pow _ _ hn.ne'] at hy; exact hy
  exact hab _ hsupp (by
    have : Y.jQ u ∈ pullback.fst Y.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨u, rfl⟩
    exact this)

end GlobalTheory.BlowSupp
