import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonMajorizingLattice
import Lemmata.GeneralBFactSecondRest.Imports

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

def majLattice_u (z : ι → mixedSpace K) (v : InfinitePlace K) : ι → ℂ :=
  fun i => (z i).2 ⟨v, IsTotallyComplex.isComplex v⟩

def majLattice_Traw (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun z p := if p.2.2 = 0 then (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).re
    else (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).im
  map_add' z z' := by
    funext p
    have : majLattice_u (z + z') p.1 = majLattice_u z p.1 + majLattice_u z' p.1 := rfl
    simp only [this, Matrix.mulVec_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r z := by
    funext p
    have : majLattice_u (r • z) p.1 = r • majLattice_u z p.1 := rfl
    simp only [this, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def majLattice_alt (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    majLattice_Traw X

theorem majLattice_realize_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    realize b X x = majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) := by
  rfl

theorem majLattice_T_injective (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (majLattice_alt X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hu : ∀ v, majLattice_u z v = 0 := by
    intro v
    have hw : (X v)⁻¹ *ᵥ majLattice_u z v = 0 := by
      funext i
      have h0 := congrArg (fun w => w (v, i, 0)) hz
      have h1 := congrArg (fun w => w (v, i, 1)) hz
      simp [majLattice_alt, majLattice_Traw] at h0 h1
      exact Complex.ext h0 h1
    have := congrArg (fun w => X v *ᵥ w) hw
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using this
  funext i
  refine Prod.ext (funext fun w => absurd w.2
    (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))) (funext fun w => ?_)
  simpa [majLattice_u] using congrFun (hu w.1) i

theorem majLattice_finrank :
    finrank ℝ (ι → mixedSpace K) =
      finrank ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
  have hc : nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
    classical
    rw [nrComplexPlaces]
    convert Fintype.card_congr (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := K)))
  rw [finrank_euclideanSpace, Module.finrank_pi_fintype]
  simp only [mixedEmbedding.finrank, IsTotallyComplex.finrank, hc, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  ring

def majLattice_B (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ
      (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
  (Pi.basis fun _ : ι => latticeBasis K).map
    (LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
      majLattice_finrank)

theorem majLattice_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : ∀ i, IsIntegral ℤ (b.repr x i)) :
    realize b X x ∈ Submodule.span ℤ (Set.range (majLattice_B X hX)) := by
  refine ((majLattice_B X hX).mem_span_iff_repr_mem ℤ _).mpr fun k => ?_
  have hr : (majLattice_B X hX).repr (realize b X x) k =
      (latticeBasis K).repr (mixedEmbedding K (b.repr x k.1)) k.2 := by
    rw [majLattice_realize_eq, show majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) =
      LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
        majLattice_finrank (fun i => mixedEmbedding K (b.repr x i)) from rfl]
    simp only [majLattice_B, Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Pi.basis_repr]
  rw [hr]
  have hmem : mixedEmbedding K (b.repr x k.1) ∈
      Submodule.span ℤ (Set.range (latticeBasis K)) := by
    rw [mem_span_latticeBasis]
    exact LinearMap.mem_range.mpr ⟨⟨_, hx k.1⟩, rfl⟩
  exact ((latticeBasis K).mem_span_iff_repr_mem ℤ _).mp hmem k.2

theorem majLattice_B_apply (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (k : Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) :
    majLattice_B X hX k = realize b X (integralBasis K k.2 • b k.1) := by
  rw [majLattice_realize_eq]
  have : (fun i => mixedEmbedding K (b.repr (integralBasis K k.2 • b k.1) i)) =
      Pi.single k.1 (latticeBasis K k.2) := by
    funext i
    rcases eq_or_ne i k.1 with rfl | h
    · simp [Algebra.smul_def]
    · simp [h]
  rw [this]
  simp [majLattice_B]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add, Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

theorem majLattice_mem_zmap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ zmap (realize b X) L ↔ ∃ x ∈ L, realize b X x = w := Iff.rfl

end MajLatticeMain

theorem majLattice : MajLattice := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX L hL
  obtain ⟨d, hd, hdL⟩ := majLattice_exists_d b L hL.fg
  have hd' : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  constructor
  · have hmaps : Set.MapsTo (fun w => (d : ℝ) • w)
        (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
        (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (majLattice_mem_zmap b X L w).mp hw
      have h1 : (d : ℝ) • realize b X x = realize b X (d • x) := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      simp only [h1]
      apply majLattice_mem_span
      intro i
      have h2 : b.repr (d • x) i = (d : K) * b.repr x i := by
        rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
      rw [h2]
      exact hdL x hx i
    have : DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :=
      inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX))))
    refine DiscreteTopology.of_continuous_injective
      ((continuous_const_smul (d : ℝ)).restrict hmaps) ?_
    intro p q hpq
    apply Subtype.ext
    have := congrArg Subtype.val hpq
    exact smul_right_injective _ hd' this
  · rw [eq_top_iff, ← (majLattice_B X hX).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc, hcL⟩ := majLattice_exists_c L hL.span_eq_top (b k.1)
    have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hmem : (c : ℝ) • majLattice_B X hX k ∈ zmap (realize b X) L := by
      refine (majLattice_mem_zmap b X L _).mpr
        ⟨(RingOfIntegers.basis K k.2) • (c • b k.1), L.smul_mem _ hcL, ?_⟩
      rw [majLattice_B_apply b, integralBasis_apply, algebraMap_smul, smul_comm, map_zsmul,
        Int.cast_smul_eq_zsmul]
    have := Submodule.smul_mem (Submodule.span ℝ
      (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))
      (c : ℝ)⁻¹ (Submodule.subset_span hmem)
    rwa [inv_smul_smul₀ hc'] at this

end Formalism.HermitianLatticesTheory
