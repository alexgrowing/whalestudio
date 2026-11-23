import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFinite

theorem finiteDimensional_of_trdeg_eq (F A B K L : Type) [Field F] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra F A] [Algebra A B] [Algebra F B]
    [IsScalarTower F A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.FiniteType A B] (n : ℕ) (hA : Algebra.trdeg F A = n) (hB : Algebra.trdeg F B = n) :
    FiniteDimensional K L := by
  letI : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  letI : Algebra F L := ((algebraMap B L).comp (algebraMap F B)).toAlgebra
  haveI : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F K L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap B L (algebraMap F B x) = algebraMap K L (algebraMap A K (algebraMap F A x))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply F A B]
  haveI : FaithfulSMul F A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F A).injective
  haveI : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B L)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hK : Algebra.trdeg F K = n := (trdeg_eq_of_isAlgebraic_top F A K).trans hA
  have hL : Algebra.trdeg F L = n := (trdeg_eq_of_isAlgebraic_top F B L).trans hB
  have h0 : Algebra.trdeg K L = 0 := by
    have e := trdeg_add_eq F K (A := L)
    rw [hK, hL] at e
    rcases (Cardinal.add_eq_left_iff).1 e with h | h
    · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 (Cardinal.natCast_lt_aleph0))
    · exact h
  haveI : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let g : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
  let T : IntermediateField K L := IntermediateField.adjoin K (g '' (s : Set B))
  have hfin : FiniteDimensional K T :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hrange : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    have : g b ∈ (Algebra.adjoin A (s : Set B)).map g := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin A (g '' (s : Set B)) ≤ T.toSubalgebra.restrictScalars A :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin K _)
    exact hle this
  have htop : T = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact T.div_mem (hrange x) (hrange y)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end GlobalTheory.GenFinite

namespace GlobalTheory.GenFinite

theorem trdeg_affineOpen_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp F) [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) [Algebra F Γ(Y, U)] [Algebra.FiniteType F Γ(Y, U)] (n : ℕ)
    (hn : topologicalKrullDim Y = n) : Algebra.trdeg F Γ(Y, U) = n := by
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  have e : topologicalKrullDim (U : Set Y) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F q U hne, hn] at e
  have hd : d = n := by exact_mod_cast e.symm
  rw [h₂, hd]

theorem residueDegree_genericPoint_ne_zero : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  intro F _ M W _ _ p f n hp hf hs hM hW
  have hη : f (genericPoint M) = genericPoint W := by
    have := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec W)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  have hA : Algebra.trdeg F Γ(W, V) = n := trdeg_affineOpen_eq F p hV ⟨_, hx⟩ n hW
  have hB : Algebra.trdeg F Γ(M, U) = n := trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  letI := (M.evaluation U _ hy).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
  letI : Algebra Γ(W, V) (M.residueField (genericPoint M)) :=
    (f.appLE V U e ≫ M.evaluation U _ hy).hom.toAlgebra
  haveI : IsScalarTower Γ(W, V) Γ(M, U) (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI : IsScalarTower Γ(W, V) (W.residueField (f (genericPoint M)))
      (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' congr($(nat).hom)
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  haveI := GenFiniteEtale.isFractionRing_eval M hU rfl hy
  have := finiteDimensional_of_trdeg_eq F Γ(W, V) Γ(M, U) (W.residueField (f (genericPoint M)))
    (M.residueField (genericPoint M)) n hA hB
  change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
  exact Module.finrank_pos.ne'

end GlobalTheory.GenFinite
