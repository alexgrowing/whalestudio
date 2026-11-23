import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscreteTopologyOfZsmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VolumeNormSqLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FundamentalDomainPiBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthBasisMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq

open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallD

open BallB BallC

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def emb (b : Basis (Fin (finrank K V)) K V) : V →+ (Fin (finrank K V) → mixedSpace K) where
  toFun x := fun i => mixedEmbedding K (b.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_apply (b : Basis (Fin (finrank K V)) K V) (x : V) (i : Fin (finrank K V)) :
    emb b x i = mixedEmbedding K (b.repr x i) := rfl

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_injective (b : Basis (Fin (finrank K V)) K V) : Function.Injective (emb b) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  exact mixedEmbedding_injective K (congrFun hxy i)

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem psi_emb [IsEmpty {w : InfinitePlace K // w.IsReal}] (b : Basis (Fin (finrank K V)) K V)
    (x : V) (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin (finrank K V)) :
    psi K (Fin (finrank K V)) (emb b x) w i = w.1.embedding (b.repr x i) := by
  rw [psi_apply, emb_apply, mixedEmbedding_apply_isComplex]

def lat (b : Basis (Fin (finrank K V)) K V) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (Fin (finrank K V) → mixedSpace K) :=
  AddSubgroup.toIntSubmodule (L.toAddSubgroup.map (emb b))

omit [StarRing K] [IsScalarTower (𝓞 K) K V] in
theorem mem_lat {b : Basis (Fin (finrank K V)) K V} {L : Submodule (𝓞 K) V}
    {y : Fin (finrank K V) → mixedSpace K} : y ∈ lat b L ↔ ∃ x ∈ L, emb b x = y := Iff.rfl

omit [StarRing K] in
theorem lat_span (b : Basis (Fin (finrank K V)) K V) :
    lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (piBasis K (Fin (finrank K V)))) := by
  ext y
  rw [mem_span_piBasis, mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨a, ha⟩ := (b.mem_span_iff_repr_mem (𝓞 K) x).1 hx i
    exact ⟨a, by rw [ha]; rfl⟩
  · intro hy
    choose a ha using hy
    have hr : ∀ i, b.repr (b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i)) i =
        algebraMap (𝓞 K) K (a i) := by
      intro i
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i),
      (b.mem_span_iff_repr_mem (𝓞 K) _).2 fun i => ⟨a i, (hr i).symm⟩, funext fun i => ?_⟩
    rw [emb_apply, hr, ha]

def ballSet [IsEmpty {w : InfinitePlace K // w.IsReal}] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (b : Basis (Fin (finrank K V)) K V) : Set (Fin (finrank K V) → mixedSpace K) :=
  (psi K (Fin (finrank K V))) ⁻¹' Set.pi Set.univ fun w =>
    ell fun i => (w.1.embedding (h (b i) (b i))).re

variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem measurableSet_ballSet : MeasurableSet (ballSet h b) :=
  ((isClosed_set_pi fun _ _ => isClosed_ell _).preimage
    (psi K (Fin (finrank K V))).toContinuousLinearEquiv.continuous).measurableSet

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem convex_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Convex ℝ (ballSet h b) :=
  (convex_pi fun w _ => convex_ell (hA w)).linear_preimage (psi K (Fin (finrank K V))).toLinearMap

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isBounded_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Bornology.IsBounded (ballSet h b) := by
  have h1 : ballSet h b = (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm ''
      Set.pi Set.univ fun w => ell fun i => (w.1.embedding (h (b i) (b i))).re :=
    ((psi K (Fin (finrank K V))).toContinuousLinearEquiv.image_symm_eq_preimage _).symm
  rw [h1]
  exact (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm.lipschitz.isBounded_image
    (Bornology.IsBounded.pi fun w => isBounded_ell (hA w))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem volume_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    volume.real (ballSet h b) =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ InfinitePlace.nrComplexPlaces K /
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have hm : MeasurableSet (Set.pi Set.univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      ell fun i => (w.1.embedding (h (b i) (b i))).re) :=
    (isClosed_set_pi fun _ _ => isClosed_ell _).measurableSet
  rw [measureReal_def, ballSet,
    (measurePreserving_psi K (Fin (finrank K V))).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (volume (ell fun i => (w.1.embedding (h (b i) (b i))).re)).toReal =
        Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ) /
          ∏ i, (w.1.embedding (h (b i) (b i))).re := by
    intro w
    rw [volume_ell (hA w), ENNReal.toReal_ofReal]
    exact div_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (hA w i).le)
  simp only [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

theorem card_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ∀ x : V, (j : ℝ)⁻¹ • emb b x ∈ ballSet h b ↔
      ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ (j : ℝ) ^ 2 := by
    intro x
    rw [forall_embedding_iff hK b ho x]
    simp only [ballSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ell,
      map_smul]
    refine forall_congr' fun w => ?_
    have h1 : ∀ i, Complex.normSq (((j : ℝ)⁻¹ • psi K (Fin (finrank K V)) (emb b x)) w i) =
        ((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i)) := by
      intro i
      rw [Pi.smul_apply, Pi.smul_apply, psi_emb, Complex.real_smul, map_mul, Complex.normSq_ofReal]
      field_simp
    simp only [h1]
    have h2 : ∑ i, (w.1.embedding (h (b i) (b i))).re *
        (((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i))) =
        (∑ i, (w.1.embedding (h (b i) (b i))).re *
          Complex.normSq (w.1.embedding (b.repr x i))) / (j : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, div_le_one (by positivity)]
  unfold ballCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(j : ℝ)⁻¹ • emb b x.1, (key x.1).2 x.2.2,
      Set.smul_mem_smul_set ⟨x.1, x.2.1, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : (j : ℝ)⁻¹ • emb b x.1 = (j : ℝ)⁻¹ • emb b y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (emb_injective b (smul_right_injective _ (inv_ne_zero hj'.ne') h1))
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy2
    exact ⟨⟨x, hx, (key x).1 hy1⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.BallD
