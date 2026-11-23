import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ

open Module NumberField

noncomputable section

namespace Formalism.HN.DualPolygon

section Defs

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi (fun p : InfinitePlace K × ι × Fin 2 =>
      (if p.2.2 = 0 then (1 : ℝ) else -1) • LinearMap.proj p)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).toLinearMap

theorem cE_apply (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (p : InfinitePlace K × ι × Fin 2) :
    cE w p = (if p.2.2 = 0 then (1 : ℝ) else -1) * w p := by
  simp only [cE, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  split_ifs with h <;> simp [h]

def tdualLat (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, ∃ z : ℤ, Algebra.trace ℚ K (f x) = z}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf (r • x) (A.smul_mem r hx)
    have e : (r • f) x = f (r • x) := by
      rw [LinearMap.smul_apply, ← algebraMap_smul K r x, map_smul, algebraMap_smul]
    exact ⟨a, e ▸ ha⟩

def annO (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ N, f x = 0}
  zero_mem' := fun x _ => by simp
  add_mem' := by
    rintro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    rintro r f hf x hx
    simp [hf x hx]

end Defs

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

theorem ident_trace_eq {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

section Assumptions

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem cE_cE (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) : cE (cE w) = w := by
  ext p
  rw [cE_apply, cE_apply]
  split_ifs <;> ring

theorem inner_cE (w w' : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    inner ℝ (cE w) (cE w') = inner ℝ w w' := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cE_apply, RCLike.inner_apply, conj_trivial]
  split_ifs <;> ring

theorem ident_fcoord_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (f : Module.Dual K V) :
    Formalism.HermitianLatticesTheory.fcoord b.dualBasis (dualFrame X) v f =
      (X v).transpose.mulVec (fun i => v.embedding (f (b i))) := by
  have hT : IsUnit (X v).transpose.det := by rw [Matrix.det_transpose]; exact hX v
  have hv : Formalism.HermitianLatticesTheory.vecAt b.dualBasis v f = fun i => v.embedding (f (b i)) := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr]
  simp only [Formalism.HermitianLatticesTheory.fcoord, dualFrame, hv, Matrix.nonsing_inv_nonsing_inv _ hT]

theorem ident_sum_fcoord (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (f : Module.Dual K V) (x : V) :
    ∑ i, Formalism.HermitianLatticesTheory.fcoord b.dualBasis (dualFrame X) v f i * Formalism.HermitianLatticesTheory.fcoord b X v x i =
      v.embedding (f x) := by
  rw [ident_fcoord_dual b X hX]
  change ((X v).transpose.mulVec _) ⬝ᵥ ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)) = _
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul, dotProduct, Formalism.HermitianLatticesTheory.vecAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem inner_realize_alt [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (f : Module.Dual K V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) ((2 : ℝ) • cE (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
  rw [ident_trace_eq, PiLp.inner_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, PiLp.smul_apply, cE_apply,
    PlaceLattice.realize_apply0, PlaceLattice.realize_apply1, RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← ident_sum_fcoord b X hX v f x, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.mul_re, if_true, show ¬ ((1 : Fin 2) = 0) from by decide, if_false]
  ring

theorem ident_mem_zl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E)
    (N : Submodule (𝓞 K) V) (w : E) : w ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = w :=
  Iff.rfl

theorem span_zl_top [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
      Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = ⊤ := by
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX N hN
  have : DiscreteTopology (zl (Formalism.HermitianLatticesTheory.realize b X) N) := hlat.2
  let bz := Module.finBasis ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N)
  have hv := Formalism.F.linearIndependent_coe_basis''' _ bz
  have hspZ := Formalism.F.span_range_coe_basis' _ bz
  apply Submodule.eq_top_of_finrank_eq
  rw [← hspZ, Submodule.span_span_of_tower, finrank_span_eq_card hv, Fintype.card_fin,
    finrank_euclideanSpace]
  have h1 : Module.finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) = rk (Formalism.HermitianLatticesTheory.realize b X) N := rfl
  have h2 : rkK N = Fintype.card ι := by
    unfold rkK; rw [hsp, finrank_top, finrank_eq_card_basis b]
  rw [h1, hrk, h2, sizeMu_finrank_eq, nPl]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem ident_inner_span_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (z : E) (h : ∀ u ∈ S, inner ℝ u z = 0) :
    ∀ u ∈ Submodule.span ℝ S, inner ℝ u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [real_inner_smul_left, hu, mul_zero]

theorem ident_inner_spanZ_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (z : E) (h : ∀ u ∈ S, inner ℝ u z = 0) :
    ∀ u ∈ Submodule.span ℤ S, inner ℝ u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu =>
    rw [show (c • u : E) = (c : ℝ) • u from (Int.cast_smul_eq_zsmul ℝ c u).symm,
      real_inner_smul_left, hu, mul_zero]

theorem dualZ_zl_eq [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V) :
    dualZ (zl (Formalism.HermitianLatticesTheory.realize b X) A) ⊓
        ((Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ).restrictScalars ℤ =
      (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (tdualLat A ⊓ annO N)).map
        (((2 : ℝ) • (cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _)).restrictScalars ℤ) := by
  classical
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hTdef
  have hT : ∀ (x : V) (f : Module.Dual K V), inner ℝ (ρ x) (T (ρ' f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
    intro x f
    rw [hTdef, LinearMap.smul_apply]
    exact inner_realize_alt b X hX x f
  have hspanA := span_zl_top b X hX A hA hsp
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
    LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨hy1, hy2⟩
    rw [duality_mem_dualZ] at hy1
    obtain ⟨-, hy1⟩ := hy1
    obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
    have : FiniteDimensional K V := Module.Finite.of_basis b
    let _ : Fintype s := hli.setFinite.fintype
    let e : s → V := Subtype.val
    have he : ∀ j : s, (j : V) ∈ A := fun j => hsA j.2
    have hmemA : ∀ (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (j : s), integralBasis K k • (j : V) ∈ A := by
      intro k j
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ (he j)
    have hex : ∀ (j : s) (k : Free.ChooseBasisIndex ℤ (𝓞 K)),
        ∃ n : ℤ, (n : ℝ) = inner ℝ (ρ (integralBasis K k • (j : V))) y :=
      fun j k => hy1 _ ⟨_, hmemA k j, rfl⟩
    choose t ht using hex
    let ω' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
    have hω : ∀ k l, Algebra.trace ℚ K (integralBasis K l * ω' k) = if l = k then 1 else 0 := by
      intro k l
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ k l
    let c : s → K := fun j => ∑ k, ((t j k : ℚ)) • ω' k
    have hc : ∀ j l, Algebra.trace ℚ K (integralBasis K l * c j) = (t j l : ℚ) := by
      intro j l
      simp only [c, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsp' : ⊤ ≤ Submodule.span K (Set.range e) := by
      rw [show Set.range e = s from Subtype.range_coe, hspan, hsp]
    let eB : Basis s K V := Basis.mk hli hsp'
    let f : Module.Dual K V := ∑ j, c j • eB.coord j
    have hfe : ∀ j : s, f (j : V) = c j := by
      intro j
      have : (j : V) = eB j := by simp [eB]
      rw [this]
      simp [f, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    have hTy : T (ρ' f) = y := by
      set z := T (ρ' f) - y
      have hgen : ∀ u ∈ Set.range (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × s =>
          ρ (integralBasis K p.1 • e p.2)), inner ℝ u z = 0 := by
        rintro u ⟨⟨k, j⟩, rfl⟩
        simp only [z, inner_sub_right, hT, map_smul, smul_eq_mul, e, hfe, hc, ← ht]
        push_cast; ring
      have hM : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) :
          Set V) = ⊤ := by
        rw [Submodule.span_span_of_tower]; exact top_le_iff.mp hsp'
      have hsM := span_zl_top b X hX _ (Submodule.fg_span (Set.finite_range e)) hM
      have hzl := PlaceLattice.zl_span_eq (K := K) ρ e
      have h1 : ∀ u ∈ (zl ρ (Submodule.span (𝓞 K) (Set.range e)) : Set _), inner ℝ u z = 0 := by
        intro u hu
        rw [hzl] at hu
        exact ident_inner_spanZ_eq_zero _ z hgen u hu
      have h2 := ident_inner_span_eq_zero _ z h1 z (by rw [hsM]; trivial)
      have : z = 0 := inner_self_eq_zero.mp h2
      exact sub_eq_zero.mp this
    refine ⟨ρ' f, ⟨f, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩, hTy⟩
    · intro x hx
      obtain ⟨n, hn⟩ := hy1 (ρ x) ⟨x, hx, rfl⟩
      refine ⟨n, ?_⟩
      have h3 := hT x f
      rw [hTy, ← hn] at h3
      exact_mod_cast h3.symm
    · intro x hx
      have h0 : ∀ r : 𝓞 K, Algebra.trace ℚ K ((r : K) * f x) = 0 := by
        intro r
        have hm : ρ (r • x) ∈ Submodule.span ℝ (zl ρ N : Set _) :=
          Submodule.subset_span ⟨r • x, N.smul_mem r hx, rfl⟩
        have h1 := Submodule.inner_right_of_mem_orthogonal hm hy2
        rw [← hTy, hT] at h1
        have h4 : f (r • x) = (r : K) * f x := by
          rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]
        rw [h4] at h1
        exact_mod_cast h1
      have hz : Algebra.traceForm ℚ K (f x) = 0 :=
        (integralBasis K).ext (fun k => by
          rw [LinearMap.zero_apply, Algebra.traceForm_apply, integralBasis_apply, mul_comm]
          exact h0 _)
      exact (traceForm_nondegenerate ℚ K).1 (f x) (fun n => by rw [hz]; rfl)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (ident_mem_zl _ _ _).1 hw
    have hf' := Submodule.mem_inf.mp hf
    refine ⟨?_, ?_⟩
    · rw [duality_mem_dualZ]
      refine ⟨by rw [hspanA]; trivial, ?_⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hz
      obtain ⟨n, hn⟩ := hf'.1 x hx
      exact ⟨n, by rw [hT, hn]; simp⟩
    · rw [Submodule.mem_orthogonal]
      intro u hu
      refine ident_inner_span_eq_zero _ _ (fun u hu => ?_) u hu
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hu
      rw [hT, hf'.2 x hx]
      simp

end Assumptions

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Zlat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem dualZ_inf_orth (L S : Submodule ℤ E) (hS : S ≤ L) :
    dualZ L ⊓ ((Submodule.span ℝ (S : Set E))ᗮ).restrictScalars ℤ = dualZ (Formalism.F.quot L S) := by
  set W := Submodule.span ℝ (S : Set E) with hW
  have hQW : Submodule.span ℝ (Formalism.F.quot L S : Set E) ≤ Wᗮ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.1 hz
    exact Wᗮ.starProjection_apply_mem x
  apply le_antisymm
  · rintro y ⟨hyD, hyO⟩
    have hyO' : y ∈ Wᗮ := hyO
    have hyD : y ∈ dualZ L := hyD
    rw [duality_mem_dualZ] at hyD ⊢
    obtain ⟨hyL, hint⟩ := hyD
    refine ⟨?_, ?_⟩
    · have hPy : Wᗮ.starProjection y = y := Submodule.starProjection_eq_self_iff.2 hyO'
      have hspan : Submodule.span ℝ (Formalism.F.quot L S : Set E) =
          (Submodule.span ℝ (L : Set E)).map (Wᗮ.starProjection : E →L[ℝ] E).toLinearMap := by
        rw [← Submodule.span_image]
        congr 1
      rw [hspan, ← hPy]
      exact Submodule.mem_map_of_mem hyL
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      obtain ⟨n, hn⟩ := hint x hx
      refine ⟨n, ?_⟩
      rw [hn]
      have h0 : inner ℝ (W.starProjection x) y = 0 :=
        Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem x) hyO'
      show inner ℝ x y = inner ℝ (Wᗮ.starProjection x) y
      rw [Submodule.starProjection_orthogonal_val, inner_sub_left, h0, sub_zero]
  · intro y hy
    refine ⟨duality_dualZ_quot_le L S hS hy, ?_⟩
    have := ((duality_mem_dualZ _ y).1 hy).1
    exact hQW this

theorem covol_map_scaled (φ : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hφ : ∀ x y, inner ℝ (φ x) (φ y) = c ^ 2 * inner ℝ x y) (M : Submodule ℤ E)
    [DiscreteTopology M] :
    DiscreteTopology (M.map (φ.restrictScalars ℤ)) ∧
      Formalism.F.rk (M.map (φ.restrictScalars ℤ)) = Formalism.F.rk M ∧
      Formalism.F.covol (M.map (φ.restrictScalars ℤ)) = c ^ Formalism.F.rk M * Formalism.F.covol M := by
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hφ x x
    rw [hx, inner_zero_left] at h1
    have h2 : inner ℝ x x = (0 : ℝ) := by
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
      exact (mul_eq_zero.1 h1.symm).resolve_left hc2
    exact inner_self_eq_zero.1 h2
  have hinjZ : Function.Injective (φ.restrictScalars ℤ) := hinj
  set M' := M.map (φ.restrictScalars ℤ) with hM'
  let e : M ≃ₗ[ℤ] M' := Submodule.equivMapOfInjective (φ.restrictScalars ℤ) hinjZ M
  let φe : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo φ hinj
  have hdisc : DiscreteTopology M' := by
    let g : M' → M := fun y => ⟨φe.symm (y : E), by
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      have : φe.symm (y : E) = x := by
        rw [← hxy]
        show φe.symm (φe x) = x
        exact φe.symm_apply_apply x
      rw [this]; exact hx⟩
    refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
    · have hc' : Continuous (φe.symm : E → E) :=
        LinearMap.continuous_of_finiteDimensional (φe.symm : E →ₗ[ℝ] E)
      exact Continuous.subtype_mk (hc'.comp continuous_subtype_val) _
    · intro y y' h
      have h' : φe.symm (y : E) = φe.symm (y' : E) := congrArg Subtype.val h
      exact Subtype.ext (φe.symm.injective h')
  have hrk : Formalism.F.rk M' = Formalism.F.rk M := by
    unfold Formalism.F.rk
    exact e.finrank_eq.symm
  refine ⟨hdisc, hrk, ?_⟩
  let b := Module.finBasis ℤ M
  let b' : Basis (Fin (finrank ℤ M)) ℤ M' := b.map e
  rw [Formalism.F.covolEqGram E M' _ b', Formalism.F.covolEqGram E M _ b]
  have hb' : ∀ i, (b' i : E) = φ (b i : E) := by
    intro i
    rw [Basis.map_apply]
    rfl
  have hG : Matrix.gram ℝ (fun i => (b' i : E)) = (c ^ 2) • Matrix.gram ℝ (fun i => (b i : E)) := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hb']
    rw [hφ]
  rw [hG, Matrix.det_smul, Fintype.card_fin]
  have hnn : 0 ≤ (c ^ 2) ^ finrank ℤ M := by positivity
  rw [Real.sqrt_mul hnn, ← pow_mul, mul_comm 2, pow_mul, Real.sqrt_sq (by positivity)]
  rfl

end Zlat

section Diff

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

open nonZeroDivisors

theorem misc_mem_dual_one (t : K) :
    t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (t * (s : K)) = z := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h1]
  constructor
  · intro h s
    obtain ⟨z, hz⟩ := h (s : K) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
  · intro h a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := h s
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩

theorem misc_diff_mul :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
  exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

theorem dual_inf_ann_eq (A N : Submodule (𝓞 K) V) :
    dualLat A ⊓ annO N = (differentIdeal ℤ (𝓞 K)) • (tdualLat A ⊓ annO N) := by
  set D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
  set 𝔡 := differentIdeal ℤ (𝓞 K)
  apply le_antisymm
  · rintro f ⟨hfA, hfN⟩

    have key : ∀ t ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K),
        t • f ∈ 𝔡 • (tdualLat A ⊓ annO N) := by
      intro t ht
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro r hr η hη
        obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
        have hηf : η • f ∈ tdualLat A ⊓ annO N := by
          refine ⟨?_, ?_⟩
          · intro x hx
            obtain ⟨s, hs⟩ := hfA x hx
            have hη' := (misc_mem_dual_one η).1 hη s
            obtain ⟨z, hz⟩ := hη'
            refine ⟨z, ?_⟩
            simp only [LinearMap.smul_apply, smul_eq_mul]
            rw [← hs]
            exact hz
          · intro x hx
            simp [hfN x hx]
        have : (algebraMap (𝓞 K) K r₀ * η) • f = r₀ • (η • f) := by
          rw [mul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul hr₀ hηf
      · intro t₁ t₂ h₁ h₂
        rw [add_smul]
        exact add_mem h₁ h₂
    have h1 : (1 : K) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [misc_diff_mul]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    simpa using key 1 h1
  · rw [Submodule.smul_le]
    rintro r hr g ⟨hgA, hgN⟩
    refine ⟨?_, (annO N).smul_mem r hgN⟩
    intro x hx
    have hgx : g x ∈ D1 := by
      rw [misc_mem_dual_one]
      intro s
      obtain ⟨z, hz⟩ := hgA (s • x) (A.smul_mem s hx)
      refine ⟨z, ?_⟩
      rw [← hz, ← algebraMap_smul K s x, map_smul, smul_eq_mul, mul_comm]
    have hr' : (algebraMap (𝓞 K) K r) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' hgx
    rw [misc_diff_mul] at hm
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    refine ⟨s, ?_⟩
    rw [hs, LinearMap.smul_apply, ← algebraMap_smul K r (g x), smul_eq_mul]

end Diff

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Twist

attribute [local instance] Ideal.Quotient.field

variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]

theorem twist_span_smul (X : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)) (h : 𝔞 ≠ ⊥) :
    Submodule.span K ((𝔞 • X : Submodule (𝓞 K) W) : Set W) = Submodule.span K (X : Set W) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right)
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hmem : α • x ∈ 𝔞 • X := Submodule.smul_mem_smul hα hx
    have hK : (algebraMap (𝓞 K) K α) ≠ 0 := by
      intro h0
      exact hα0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
    have hx' : x = (algebraMap (𝓞 K) K α)⁻¹ • (α • x) := by
      rw [← algebraMap_smul K α x, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [SetLike.mem_coe, hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem twist_prime_le (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔭 : Ideal (𝓞 K))
    [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) :
    (𝔭 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔭 ^ finrank K (Submodule.span K (X : Set W)) := by
  change Nat.card (X ⧸ (𝔭 • X).comap X.subtype) ≤ _
  let e : (X ⧸ (𝔭 • X).comap X.subtype) ≃ₗ[𝓞 K] (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Submodule.quotEquivOfEq _ _ (Submodule.map_injective_of_injective X.injective_subtype
      (by simp [Submodule.smul_le_right]))
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Finite (𝓞 K ⧸ 𝔭) := (Ideal.absNorm_ne_zero_iff 𝔭).1
    (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  have : Module.Finite (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := Module.finite_of_finite (𝓞 K ⧸ 𝔭)
  have hcard : Nat.card (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) =
      Nat.card (𝓞 K ⧸ 𝔭) ^ finrank (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := by
    haveI := Fintype.ofFinite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
    haveI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hN : Nat.card (𝓞 K ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard, hN]
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)))
  let B := Module.finBasis (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
  have hsurj := Submodule.mkQ_surjective (𝔭 • (⊤ : Submodule (𝓞 K) X))
  choose b' hb' using fun i => hsurj (B i)
  have hli : LinearIndependent (𝓞 K ⧸ 𝔭)
      ((Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b') := by
    have : (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b' = B := funext hb'
    rw [this]; exact B.linearIndependent
  have hRS : RingHom.ker (algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭)) ≠ ⊤ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact h𝔭.ne_top
  have hli2 := Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial K hRS X.subtype
    X.injective_subtype (Submodule.mkQ _) hli
  let g : Fin _ → Submodule.span K (X : Set W) :=
    fun i => ⟨(b' i : W), Submodule.subset_span (b' i).2⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp (Submodule.span K (X : Set W)).subtype
    exact hli2
  simpa using hg.fintype_card_le_finrank

theorem twist_le (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) : ∀ (X : Submodule (𝓞 K) W), X.FG →
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  revert h𝔟
  refine UniqueFactorizationMonoid.induction_on_prime 𝔟 ?_ ?_ ?_
  · intro h
    exact absurd Submodule.zero_eq_bot h
  · intro x hx _ X _
    rw [Ideal.isUnit_iff.1 hx, Submodule.top_smul, Ideal.absNorm_top, one_pow,
      AddSubgroup.relIndex_self]
  · intro a p ha hp ih _ X hX
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hab : a ≠ ⊥ := ha
    haveI : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpb
    rw [Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • a • X).toAddSubgroup
      (a • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)]
    have h1 := twist_prime_le (a • X) (Submodule.FG.smul (IsNoetherian.noetherian a) hX) p hpb
    rw [twist_span_smul X a hab] at h1
    have h2 := ih hab X hX
    rw [map_mul, mul_pow]
    exact Nat.mul_le_mul h1 h2

omit [FiniteDimensional K W] in
include K in
theorem twist_torsionFree : IsAddTorsionFree W := ⟨fun n hn a c h => by
  have h' : (n : K) • a = (n : K) • c := by simpa [Nat.cast_smul_eq_nsmul] using h
  exact smul_right_injective W (Nat.cast_ne_zero.2 hn) h'⟩

example (X : Submodule (𝓞 K) W) : Module.IsTorsionFree ℤ X := by
  have := twist_torsionFree (K := K) (W := W)
  infer_instance
example (X : Submodule (𝓞 K) W) (hX : X.FG) : Module.Finite ℤ X := by
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  exact Module.Finite.trans (𝓞 K) X

end Twist

section TwistInt

open scoped Pointwise

variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]

theorem twist_finrank_int [StarRing K] (X : Submodule (𝓞 K) W) (hX : X.FG) :
    finrank ℤ X = finrank ℚ K * finrank K (Submodule.span K (X : Set W)) := by
  let b := Module.finBasis K W
  let Xf : InfinitePlace K → Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := fun _ => 1
  have hXf : ∀ v, IsUnit (Xf v).det := fun v => by simp [Xf]
  obtain ⟨-, hrk, -⟩ := place_lattice_structure K W (Fin (finrank K W)) b Xf hXf X hX
  have hinj := Formalism.HN.PlaceLattice.realize_injective b Xf hXf
  let e : X.toAddSubgroup ≃+ (X.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b Xf)) :=
    AddSubgroup.equivMapOfInjective _ _ hinj
  have h1 : finrank ℤ X = finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b Xf) X) :=
    e.toIntLinearEquiv.finrank_eq
  rw [h1]
  exact hrk

theorem twist_int (X : Submodule (𝓞 K) W) (hX : X.FG) (m : ℕ) (hm : m ≠ 0) :
    ((Ideal.span {(m : 𝓞 K)}) • X).toAddSubgroup.relIndex X.toAddSubgroup =
      m ^ finrank ℤ X := by
  have htf := twist_torsionFree (K := K) (W := W)
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 K) X
  rw [Submodule.ideal_span_singleton_smul]
  set H := ((m : 𝓞 K) • X).toAddSubgroup.addSubgroupOf X.toAddSubgroup with hH
  have hcoe : ∀ x : X, ((m • x : X) : W) = (m : 𝓞 K) • (x : W) := by
    intro x
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 K)]
  have hmem : ∀ x : X, m • x ∈ H.toIntSubmodule := by
    intro x
    show m • x ∈ H
    rw [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hcoe]
    exact Submodule.smul_mem_pointwise_smul _ _ _ x.2
  let f : X →+ H.toIntSubmodule :=
    { toFun := fun x => ⟨m • x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : ((m • x : X) : W) = ((m • y : X) : W) := by
        have := congrArg (fun z : H.toIntSubmodule => ((z : X) : W)) hxy
        simpa [f] using this
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower] at h1
      exact Subtype.ext (htf.nsmul_right_injective hm h1)
    · rintro ⟨z, hz⟩
      have hz' : (z : W) ∈ (m : 𝓞 K) • X := by
        have : z ∈ H := hz
        rwa [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at this
      obtain ⟨x, hx, hxz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hz'
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hcoe]
      exact hxz
  let e := AddEquiv.ofBijective f hf
  have key := Submodule.natAbs_det_equiv H.toIntSubmodule e
  have hlin : H.toIntSubmodule.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : X →+ H.toIntSubmodule) =
      (m : ℤ) • LinearMap.id := by
    ext x
    simp [e, f]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one] at key
  change H.index = _
  rw [Int.natAbs_pow, Int.natAbs_natCast] at key
  exact key.symm

theorem twist_absNorm_nat (m : ℕ) :
    Ideal.absNorm (Ideal.span {(m : 𝓞 K)}) = m ^ finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

theorem twist_index {K W : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W] (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔟 : Ideal (𝓞 K))
    (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := finrank K (Submodule.span K (X : Set W)) with hr
  have hall := twist_int X hX m hm
  rw [twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup
      (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 X hX
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)
  rw [twist_span_smul X 𝔟 h𝔟] at hb
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup *
      (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1

end TwistInt

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Main

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem dualFrame_unit (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    ∀ v, IsUnit (dualFrame X v).det := fun v => by
  unfold dualFrame
  exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)

theorem dualFrame_dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    dualFrame (dualFrame X) = X := by
  funext v
  unfold dualFrame
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (hX v)]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_basis_in (A : Submodule (𝓞 K) V) [FiniteDimensional K V]
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Basis (Fin n) K V), ∀ i, e i ∈ A := by
  obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let e0 : Basis s K V := Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  refine ⟨Fintype.card s, e0.reindex (Fintype.equivFin s), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hsA (Subtype.mem _)

omit [Fintype ι] [DecidableEq ι] in
theorem exists_int_smul_mem {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) (w : V) : ∃ c : ℤ, c ≠ 0 ∧ ((c : K)) • w ∈ A := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => e.repr w i)
  refine ⟨y, hy, ?_⟩
  rw [← e.sum_repr w, Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  have hi : IsIntegral ℤ (y • e.repr w i) :=
    hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • e.repr w i, hi⟩
  have hr : ((y : K)) • (e.repr w i • e i) = r • e i := by
    rw [← algebraMap_smul K r, smul_smul]
    congr 1
    show (y : K) * e.repr w i = y • e.repr w i
    rw [zsmul_eq_mul]
  rw [hr]
  exact Submodule.smul_mem _ _ (he i)

omit [Fintype ι] [DecidableEq ι] in
theorem dualLat_le_span {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) : dualLat A ≤ Submodule.span (𝓞 K) (Set.range e.dualBasis) := by
  intro f hf
  have h : ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = f (e i) := fun i => hf (e i) (he i)
  choose a ha using h
  have hf' : f = ∑ i, a i • e.dualBasis i := by
    conv_lhs => rw [← e.dualBasis.sum_repr f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Basis.dualBasis_repr, ← ha i, algebraMap_smul]
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
theorem dualLat_fg [FiniteDimensional K V] (A : Submodule (𝓞 K) V)
    (hsp : Submodule.span K (A : Set V) = ⊤) : (dualLat A).FG := by
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) (dualLat_le_span A e he)

omit [Fintype ι] [DecidableEq ι] in
theorem dualLat_span [FiniteDimensional K V] (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    Submodule.span K (dualLat A : Set (Module.Dual K V)) = ⊤ := by
  classical
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  obtain ⟨y, hy, hAy⟩ := Formalism.HN.PlaceLattice.exists_denom e A hA
    (fun x _ => by rw [e.span_eq]; trivial)
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.2 hy
  have hmem : ∀ i, ((y : K)) • e.dualBasis i ∈ dualLat A := by
    intro i
    suffices H : ∀ x ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a),
        (((y : K)) • e.dualBasis i) x ∈ Set.range (algebraMap (𝓞 K) K) from
      fun x hx => H x (hAy hx)
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      by_cases h : a = i
      · refine ⟨1, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h, hyK]
      · refine ⟨0, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨c, hc⟩ := hw
      exact ⟨a + c, by rw [map_add, map_add, ha, hc]⟩
    | smul r z _ hz =>
      obtain ⟨a, ha⟩ := hz
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul K r z, map_smul, map_mul, ha, smul_eq_mul]
  rw [eq_top_iff, ← e.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : e.dualBasis i = ((y : K))⁻¹ • (((y : K)) • e.dualBasis i) := by
    rw [smul_smul, inv_mul_cancel₀ hyK, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))

end Main

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

theorem eq_mul_of_log_eq_add {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Real.log a = Real.log b + Real.log c) : a = b * c := by
  rw [← Real.log_mul hb.ne' hc.ne'] at h
  exact Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (mul_pos hb hc)) h

section Key

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem key_lemma (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    rkK (dualLat A ⊓ annO N) + rkK N = finrank K V ∧
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)) *
              Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) *
              2 ^ (finrank ℚ K * rkK (dualLat A ⊓ annO N)) =
      |(NumberField.discr K : ℝ)| ^ rkK (dualLat A ⊓ annO N) *
        Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set Rp := tdualLat A ⊓ annO N with hRp
  set R := dualLat A ⊓ annO N with hR
  set 𝔡 := differentIdeal ℤ (𝓞 K) with h𝔡
  have h𝔡0 : 𝔡 ≠ ⊥ := differentIdeal_ne_bot
  have hRdR : R = 𝔡 • Rp := dual_inf_ann_eq A N
  have hNA : N ≤ A := hN.1
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  have hdfg : (dualLat A).FG := dualLat_fg A hsp
  have hRfg : R.FG := Submodule.FG.of_le hdfg inf_le_left
  have hRpfg : Rp.FG := by
    set m : ℕ := Ideal.absNorm 𝔡 with hm
    have hm0 : m ≠ 0 := fun h => h𝔡0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
    have hmem : (m : 𝓞 K) ∈ 𝔡 := Ideal.absNorm_mem 𝔡
    let ψ : Module.Dual K V →ₗ[𝓞 K] Module.Dual K V :=
      (((m : K)⁻¹) • (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)).restrictScalars (𝓞 K)
    refine Submodule.FG.of_le (hdfg.map ψ) ?_
    intro g hg
    refine ⟨(m : 𝓞 K) • g, ?_, ?_⟩
    · have : (m : 𝓞 K) • g ∈ R := by rw [hRdR]; exact Submodule.smul_mem_smul hmem hg
      exact this.1
    · show ((m : K)⁻¹) • ((m : 𝓞 K) • g) = g
      rw [← algebraMap_smul K ((m : 𝓞 K)) g, map_natCast, smul_smul, inv_mul_cancel₀ hmK, one_smul]
  have hspR : Submodule.span K (R : Set (Module.Dual K V)) = Submodule.span K (Rp : Set _) := by
    rw [hRdR]; exact twist_span_smul Rp 𝔡 h𝔡0
  have hrkR : rkK R = rkK Rp := by unfold rkK; rw [hspR]
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR', -⟩ := place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨hlatRp, hrkRp', -⟩ :=
    place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' Rp hRpfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  set L := zl ρ A with hL
  set S := zl ρ N with hS
  haveI hLd : DiscreteTopology L := hlatA.2
  have hSsat : Formalism.F.IsSaturated L S := hN.2
  obtain ⟨hQd, hrkQ, hdegQ⟩ := Formalism.F.degQuot _ L S hLd hSsat
  haveI := hQd
  obtain ⟨hDd, hrkD, hdegD, -⟩ := duality_basic (Formalism.F.quot L S)
  haveI := hDd
  have hSL : S ≤ L := hSsat.1
  have hE1 := dualZ_inf_orth L S hSL
  have hE2 := dualZ_zl_eq b X hX A hA hsp N
  set M' := zl ρ' Rp with hM'def
  set φ2 : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hφ2
  set φh : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := ((1 : ℝ) / 2) • cE with hφh
  have hcomp : φh.restrictScalars ℤ ∘ₗ φ2.restrictScalars ℤ = LinearMap.id := by
    ext w
    simp only [hφh, hφ2, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply, map_smul, cE_cE, smul_smul, LinearMap.id_apply]
    norm_num
  have hM' : M' = (dualZ (Formalism.F.quot L S)).map (φh.restrictScalars ℤ) := by
    rw [← hE1, hE2, ← Submodule.map_comp, hcomp, Submodule.map_id]
  have hφhi : ∀ x y, inner ℝ (φh x) (φh y) = ((1 : ℝ) / 2) ^ 2 * inner ℝ x y := by
    intro x y
    simp only [hφh, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, inner_cE]
    ring
  obtain ⟨hM'd, hrkM', hcovM'⟩ :=
    covol_map_scaled φh ((1 : ℝ) / 2) (by norm_num) hφhi (dualZ (Formalism.F.quot L S))
  rw [← hM'] at hM'd hrkM' hcovM'
  haveI := hM'd
  have hRRp : R ≤ Rp := by rw [hRdR]; exact Submodule.smul_le_right
  have hzlle : zl ρ' R ≤ M' := shiftInv_zl_mono ρ' hRRp
  have hn0 : 0 < finrank ℚ K := Module.finrank_pos
  have hrkeq : Formalism.F.rk (zl ρ' R) = Formalism.F.rk M' := by
    have h1 : Formalism.HN.rk ρ' R = Formalism.HN.rk ρ' Rp := by rw [hrkR', hrkRp', hrkR]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (zl ρ' R) M' hzlle hrkeq
  have hρ'inj := Formalism.HN.PlaceLattice.realize_injective b.dualBasis (dualFrame X) hX'
  have hidx : (zl ρ' R).toAddSubgroup.relIndex M'.toAddSubgroup =
      R.toAddSubgroup.relIndex Rp.toAddSubgroup := by
    simp only [hM'def, zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hρ'inj
  have htw : R.toAddSubgroup.relIndex Rp.toAddSubgroup = Ideal.absNorm 𝔡 ^ rkK Rp := by
    rw [hRdR]; exact twist_index Rp hRpfg 𝔡 h𝔡0
  have hnorm : (Ideal.absNorm 𝔡 : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [h𝔡, NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]

  have hSd : DiscreteTopology S := Formalism.F.discreteTopology_of_le hSL
  have hcL := Formalism.F.covolPos _ L hLd
  have hcS := Formalism.F.covolPos _ S hSd
  have hcQ := Formalism.F.covolPos _ _ hQd
  have hcD := Formalism.F.covolPos _ _ hDd
  have hLSQ : Formalism.F.covol L = Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S) := by
    apply eq_mul_of_log_eq_add hcL hcS hcQ
    unfold Formalism.F.deg at hdegQ
    linarith
  have hDQ : Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S) = 1 := by
    have h1 : Real.log (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) = 0 := by
      rw [Real.log_mul hcD.ne' hcQ.ne']
      unfold Formalism.F.deg at hdegD
      linarith
    have h2 := Real.eq_one_of_pos_of_log_eq_zero (mul_pos hcD hcQ) h1
    exact h2

  have hrkL : Formalism.F.rk L = finrank ℚ K * finrank K V := by
    have : Formalism.HN.rk ρ A = _ := hrkA
    rw [hrkAd] at this
    exact this
  have hrkS : Formalism.F.rk S = finrank ℚ K * rkK N := hrkN
  have hrkM'2 : Formalism.F.rk M' = finrank ℚ K * rkK Rp := hrkRp'
  have hrkQ' : Formalism.F.rk (Formalism.F.quot L S) = finrank ℚ K * rkK Rp := by
    rw [← hrkM'2, hrkM', hrkD]
  have hdim : rkK Rp + rkK N = finrank K V := by
    have h1 : finrank ℚ K * finrank K V = finrank ℚ K * rkK N + finrank ℚ K * rkK Rp := by
      rw [← hrkL, ← hrkS, ← hrkQ', hrkQ]
    have h2 : finrank ℚ K * finrank K V = finrank ℚ K * (rkK Rp + rkK N) := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hn0 h2).symm
  refine ⟨by rw [hrkR]; exact hdim, ?_⟩
  rw [hcov, hidx, htw, hrkR, hcovM', hrkD, hrkQ', Nat.cast_pow, hnorm, hLSQ]
  have h2 : ((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp) = 1 := by
    rw [← mul_pow]; norm_num
  calc |(NumberField.discr K : ℝ)| ^ rkK Rp *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * Formalism.F.covol (dualZ (Formalism.F.quot L S))) *
          (Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S)) * 2 ^ (finrank ℚ K * rkK Rp)
        = |(NumberField.discr K : ℝ)| ^ rkK Rp * Formalism.F.covol S *
          (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp)) := by ring
    _ = _ := by rw [hDQ, h2]; ring

end Key

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

theorem rpow_neg_half_nat_pow {D : ℝ} (hD : 0 < D) (k : ℕ) :
    D ^ (-(k : ℝ) / 2) = (D ^ (-(1 : ℝ) / 2)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  congr 1
  ring

theorem rpow_neg_half_sq_mul {D : ℝ} (hD : 0 < D) : (D ^ (-(1 : ℝ) / 2)) ^ 2 * D = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hD.ne']

theorem ht_alg (f r j : ℕ) (D u cR cL cS : ℝ) (hu : u ^ 2 * D = 1)
    (h : cR * cL * 2 ^ (2 * f * r) = D ^ r * cS) :
    2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL) =
      2 ^ (f * j) * u ^ j * cS := by
  calc 2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL)
      = 2 ^ (f * j) * u ^ j * (u ^ 2) ^ r * (cR * cL * 2 ^ (2 * f * r)) := by ring
    _ = 2 ^ (f * j) * u ^ j * (u ^ 2 * D) ^ r * cS := by rw [h]; ring
    _ = _ := by rw [hu, one_pow, mul_one]

section HtDual

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem ht_dual_ann (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    ht b.dualBasis (dualFrame X) (dualLat A ⊓ annO N) * ht b X A = ht b X N := by
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn : finrank ℚ K = 2 * nPl K := sizeMu_finrank_eq K
  unfold ht
  rw [hrkAd, ← hdim, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD]
  rw [hn] at hcov
  push_cast
  exact ht_alg (nPl K) _ _ _ _ _ _ _ (rpow_neg_half_sq_mul hD) hcov

theorem ht_bot (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    ht b X (⊥ : Submodule (𝓞 K) V) = 1 := by
  have h1 : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK; simp
  have h2 : zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := satBasic_zl_bot _
  unfold ht
  rw [h1, h2, (Formalism.F.covolBasic _).1]
  simp

omit [StarRing K] [IsTotallyComplex K] [Fintype ι] [DecidableEq ι] in
theorem annO_bot : annO (⊥ : Submodule (𝓞 K) V) = ⊤ := by
  ext f
  simp only [Submodule.mem_top, iff_true]
  intro x hx
  rw [Submodule.mem_bot] at hx
  simp [hx]

theorem ht_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ht b.dualBasis (dualFrame X) (dualLat A) * ht b X A = 1 := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥ :=
    (saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat).2.2.2.2.2.1
  have := ht_dual_ann b X hX A hA hsp ⊥ hsat
  rwa [annO_bot, inf_top_eq, ht_bot] at this

theorem rkK_dualLat (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) : rkK (dualLat A) = finrank K V := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  rw [dualLat_span A hA hsp, finrank_top, Subspace.dual_finrank_eq]

end HtDual

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section DD

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem realize_eval (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) :
    Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)) (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.realize b X x := by
  rw [dualFrame_dualFrame X hX]
  have hvec : ∀ v, Formalism.HermitianLatticesTheory.vecAt b.dualBasis.dualBasis v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.vecAt b v x := by
    intro v
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr, Basis.dualBasis_apply]
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b.dualBasis.dualBasis X v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    simp only [Formalism.HermitianLatticesTheory.fcoord, hvec]
  ext p
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, hf]

theorem dual_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) = A := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set A2 := (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) with hA2
  set e := Module.evalEquiv K V with he
  have hee : ∀ x, e x = Module.Dual.eval K V x := fun x => rfl
  have hAA2 : A ≤ A2 := by
    intro x hx f hf
    exact hf x hx
  have hdfg := dualLat_fg A hsp
  have hdsp := dualLat_span A hA hsp
  have hddfg : (dualLat (dualLat A)).FG := dualLat_fg (dualLat A) hdsp
  have hddsp := dualLat_span (dualLat A) hdfg hdsp
  have hmap : A2.map (e.toLinearMap.restrictScalars (𝓞 K)) = dualLat (dualLat A) := by
    apply Submodule.map_comap_eq_of_surjective
    exact e.surjective
  have hA2fg : A2.FG := by
    have : A2 = (dualLat (dualLat A)).map (e.symm.toLinearMap.restrictScalars (𝓞 K)) := by
      ext x
      simp only [hA2, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        rw [← hee, e.apply_symm_apply]
        exact hy
    rw [this]
    exact hddfg.map _
  have hA2sp : Submodule.span K (A2 : Set V) = ⊤ :=
    eq_top_iff.2 (hsp ▸ Submodule.span_mono hAA2)

  have hht1 := ht_dual b X hX A hA hsp
  have hht2 := ht_dual b.dualBasis (dualFrame X) hX' (dualLat A) hdfg hdsp
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)))
      (dualLat (dualLat A)) = zl (Formalism.HermitianLatticesTheory.realize b X) A2 := by
    rw [← hmap]
    ext w
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (realize_eval b X hX x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, realize_eval b X hX x⟩
  have hrk1 : rkK (dualLat (dualLat A)) = finrank K V := by
    unfold rkK
    rw [hddsp, finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]
  have hrk2 : rkK A2 = finrank K V := by unfold rkK; rw [hA2sp, finrank_top]
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hhtA2 : ht b X A2 = ht b X A := by
    have h3 : ht b.dualBasis.dualBasis (dualFrame (dualFrame X)) (dualLat (dualLat A)) =
        ht b X A2 := by
      unfold ht; rw [hzl, hrk1, hrk2]
    rw [← h3]
    have hpos : 0 < ht b.dualBasis (dualFrame X) (dualLat A) :=
      (place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg).2.2
    field_simp at hht1 hht2 ⊢
    nlinarith [hht1, hht2, hpos]

  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hcovEq : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A2) =
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by
    unfold ht at hhtA2
    rw [hrk2, hrkA] at hhtA2
    have hc : (0 : ℝ) < (2 : ℝ) ^ (nPl K * finrank K V) *
        |(NumberField.discr K : ℝ)| ^ (-(finrank K V : ℝ) / 2) := by positivity
    exact mul_left_cancel₀ hc.ne' hhtA2
  obtain ⟨hlat2, hrkz2, -⟩ := place_lattice_structure K V ι b X hX A2 hA2fg
  obtain ⟨hlat1, hrkz1, -⟩ := place_lattice_structure K V ι b X hX A hA
  haveI := hlat2.2
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A2) := by
    have h : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A2 := by
      rw [hrkz1, hrkz2, hrkA, hrk2]
    exact h
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _
    (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hAA2) hrkeq
  have hpos := Formalism.F.covolPos _ _ hlat2.2
  rw [hcovEq] at hcov
  have hidx1 : ((zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup : ℝ) = 1 := by
    have hp1 : 0 < Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by rw [← hcovEq]; exact hpos
    field_simp at hcov
    nlinarith [hcov, hp1]
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : A.toAddSubgroup.relIndex A2.toAddSubgroup = 1 := by
    have h : (zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
        (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup = A.toAddSubgroup.relIndex A2.toAddSubgroup := by
      simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
      exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
    rw [← h]
    exact_mod_cast hidx1
  have hle : A2.toAddSubgroup ≤ A.toAddSubgroup := AddSubgroup.relIndex_eq_one.1 hidx
  exact le_antisymm (fun x hx => hle hx) hAA2

end DD

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section HNDual

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem sat_exists (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG) (N : Submodule (𝓞 K) V)
    (hNA : N ≤ A) :
    ∃ N', N ≤ N' ∧ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N' ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ deg (Formalism.HermitianLatticesTheory.realize b X) N' := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨N', h1, h2, h3⟩ := real_saturation_property (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A N hlat hNA
  obtain ⟨s1, -, s3⟩ := Formalism.F.saturProps _ (zl (Formalism.HermitianLatticesTheory.realize b X) A)
    (zl (Formalism.HermitianLatticesTheory.realize b X) N) hlat.2 (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNA)
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
    unfold Formalism.HN.rk; rw [h3]; exact s3
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  exact ⟨N', h1, ⟨h2, by rw [h3]; exact s1⟩, hrk, (hSB.2.1 N N' h1 h2).2 hrk.symm⟩

theorem sat_of_ann (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) :
    ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧ R ≤ dualLat A ⊓ annO N ∧
      rkK R + rkK N = finrank K V := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  set W : Submodule K V := (Submodule.span K (R : Set (Module.Dual K V))).dualCoannihilator with hW
  set N : Submodule (𝓞 K) V := A ⊓ W.restrictScalars (𝓞 K) with hN
  have hNA : N ≤ A := inf_le_left
  have hspN : Submodule.span K (N : Set V) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · intro w hw
      obtain ⟨c, hc, hcw⟩ := exists_int_smul_mem A e he w
      have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.2 hc
      have hmem : (c : K) • w ∈ N := ⟨hcw, W.smul_mem _ hw⟩
      have : w = ((c : K))⁻¹ • ((c : K) • w) := by rw [smul_smul, inv_mul_cancel₀ hcK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hdim : rkK R + rkK N = finrank K V := by
    unfold rkK
    rw [hspN]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    rw [shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat N]
    refine ⟨hNA, fun N'' h1 h2 h3 => ?_⟩
    have hfg'' : N''.FG := Submodule.FG.of_le hA h2
    have hNfg : N.FG := Submodule.FG.of_le hA hNA
    obtain ⟨-, hr1, -⟩ := place_lattice_structure K V ι b X hX N'' hfg''
    obtain ⟨-, hr2, -⟩ := place_lattice_structure K V ι b X hX N hNfg
    have hn0 : 0 < finrank ℚ K := Module.finrank_pos
    have hrkK : rkK N'' = rkK N := by
      rw [hr1, hr2] at h3
      exact Nat.eq_of_mul_eq_mul_left hn0 h3
    have hsp_eq : Submodule.span K (N : Set V) = Submodule.span K (N'' : Set V) :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) hrkK.symm
    apply le_antisymm _ h1
    intro x hx
    refine ⟨h2 hx, ?_⟩
    show x ∈ W
    rw [← hspN, hsp_eq]
    exact Submodule.subset_span hx
  refine ⟨N, hsat, fun f hf => ⟨hR hf, fun x hx => ?_⟩, hdim⟩
  have hxW : x ∈ W := hx.2
  exact (Submodule.mem_dualCoannihilator x).1 hxW f (Submodule.subset_span hf)

theorem deg_R (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) =
        deg (Formalism.HermitianLatticesTheory.realize b X) N - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  have hX' := dualFrame_unit X hX
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hNfg : N.FG := Submodule.FG.of_le hA hN.1
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hdfg := dualLat_fg A hsp
  have hRfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR, -⟩ :=
    place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A ⊓ annO N) hRfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn0 : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcR := Formalism.F.covolPos _ _ hlatR.2
  have hcA := Formalism.F.covolPos _ _ hlatA.2
  have hcN := Formalism.F.covolPos _ _ hlatN.2
  have hlog := congrArg Real.log hcov
  rw [Real.log_mul (mul_pos hcR hcA).ne' (by positivity), Real.log_mul hcR.ne' hcA.ne',
    Real.log_mul (by positivity) hcN.ne', Real.log_pow, Real.log_pow] at hlog
  set r := rkK (dualLat A ⊓ annO N) with hr
  refine ⟨?_, ?_⟩
  · unfold deg Formalism.F.deg
    rw [hrkR]
    have h1 : (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
        ((finrank ℚ K * r : ℕ) : ℝ) = ((finrank ℚ K * r : ℕ) : ℝ) * Real.log 2 -
          (r : ℝ) * Real.log |(NumberField.discr K : ℝ)| := by
      push_cast
      field_simp
    rw [h1]
    push_cast at hlog ⊢
    linarith
  · rw [hrkR, hrkA, hrkN, hrkAd, ← hdim]
    push_cast
    ring

theorem corr_R (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) : ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) ∧
      deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hSB' := saturation_basic_properties (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat'
  obtain ⟨N, hN, hRN, hdim⟩ := sat_of_ann b X hX A hA hsp R hR
  obtain ⟨hdimN, -⟩ := key_lemma b X hX A hA hsp N hN
  have hRfg : R.FG := Submodule.FG.of_le hdfg hR
  have hRNfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨-, r1, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨-, r2, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' _ hRNfg
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
    calc _ = finrank ℚ K * rkK R := r1
      _ = finrank ℚ K * rkK (dualLat A ⊓ annO N) := by congr 1; omega
      _ = _ := r2.symm
  exact ⟨N, hN, hrk, (hSB'.2.1 R _ hRN inf_le_left).2 hrk⟩

theorem dual_ne_bot (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) : dualLat A ≠ ⊥ := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  intro h
  have h1 := rkK_dualLat b A hA hsp
  rw [h] at h1
  have h2 : rkK (⊥ : Submodule (𝓞 K) (Module.Dual K V)) = 0 := by unfold rkK; simp
  have hpos : 0 < finrank K V := by
    obtain ⟨x, -, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
    haveI : Nontrivial V := ⟨⟨x, 0, hx0⟩⟩
    exact Module.finrank_pos
  omega

theorem deg_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  have hsat0 : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥ := hSB.2.2.2.2.2.1
  obtain ⟨hdeg0, hrk0⟩ := deg_R b X hX A hA hsp ⊥ hsat0
  rw [annO_bot, inf_top_eq] at hdeg0 hrk0
  have hdegbot : deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 := hSB.2.2.2.2.1
  have hrkbot : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 :=
    (hSB.2.2.2.1 ⊥ bot_le).2 rfl
  have hb : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) : ℝ) = 0 := by
    exact_mod_cast hrkbot
  have hP : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by linarith
  refine ⟨?_, hP⟩
  have e0 := congrArg (fun t => (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| /
    (finrank ℚ K : ℝ)) * t) hP
  linarith

theorem key_one (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (θ : ℝ) :
    (∀ R : Submodule (𝓞 K) (Module.Dual K V), R ≤ dualLat A →
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
          θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N) ≤
          deg (Formalism.HermitianLatticesTheory.realize b X) A - deg (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') by
          linarith)
    nlinarith [e1, hd, h3, hdeg]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) by
          linarith)
    have e2 := congrArg (fun t => θ * t) hx
    nlinarith [e1, e2, hd, h3, hdeg]

theorem key_two (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (θ : ℝ) :
    (∀ R : Submodule (𝓞 K) (Module.Dual K V), R ≤ dualLat A →
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
              Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ≤
          deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) -
            deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hdeg0, hrk0⟩ := deg_dual b X hX A hA hsp
  have e0 := congrArg (fun t => c2 * t) hrk0
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    have e3 := congrArg (fun t => θ * t) hc
    nlinarith [e0, e1, e2, e3, hd, h3, hdeg, hdeg0]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    nlinarith [e0, e1, e2, hd, h3, hdeg, hdeg0]

theorem mu_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) :
    muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMax (Formalism.HermitianLatticesTheory.realize b X) A := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hd0 := dual_ne_bot b A hA hsp hA0
  have m1 := slope_characterization (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat' hd0
  have m2 := slope_characterization (𝓞 K) V _ _ A hlat hA0
  have key1 : ∀ θ : ℝ, muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ≤ θ ↔
      c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) A := fun θ =>
    (m1.1 θ).trans ((key_one b X hX A hA hsp θ).trans (m2.2.1 (c2 - θ)).symm)
  have key2 : ∀ θ : ℝ, c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ↔
      muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ θ := fun θ =>
    (m1.2.1 (c2 - θ)).trans ((key_two b X hX A hA hsp θ).trans (m2.1 θ).symm)
  refine ⟨le_antisymm ((key1 _).2 (by linarith)) ?_, le_antisymm ?_ ((key2 _).2 le_rfl)⟩
  · have := (key1 (muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1 le_rfl
    linarith
  · have := (key2 (c2 - muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1
      (by linarith)
    linarith

end HNDual

end Formalism.HN.DualPolygon

namespace Formalism.HN

open DualPolygon

theorem dual_polygon_identity : DualPl := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hht := ht_dual b X hX A hA hsp
  have hpos := (place_lattice_structure K V ι b X hX A hA).2.2
  have hhtinv : ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹ :=
    eq_inv_of_mul_eq_one_left hht
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hrkD := rkK_dualLat b A hA hsp
  have hdfg := dualLat_fg A hsp
  have hc2 : ∀ m : ℝ, (Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) -
      ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - m) =
      -((Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) - m) := by
    intro m
    unfold logDisc
    ring
  refine ⟨hdfg, dualLat_span A hA hsp, hhtinv, ?_, ?_, ?_, dual_dual b X hX A hA hsp⟩
  · unfold size
    rw [hhtinv, hrkD, hrkA]
    exact Real.inv_rpow hpos.le _
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have h1 : leastSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, -, hR0, -⟩
        exact hR0 (eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f))
      have h2 : largestSize b X A = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, hS, hSA, -⟩
        exact hSA (le_antisymm hS.1 (by rw [hA0]; exact bot_le))
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, -, hg, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, hl', -, -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hl', hg, (mu_dual b X hX A hA hsp hA0).1, ← Real.exp_neg, hc2]
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have hbot : ∀ R : Submodule (𝓞 K) (Module.Dual K V), R = ⊥ := fun R =>
        eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f)
      have h1 : largestSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, -, hSA, -⟩
        exact hSA (by rw [hbot S, hbot (dualLat A)])
      have h2 : leastSize b X A = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, hR, hR0, -⟩
        exact hR0 (le_antisymm (by rw [← hA0]; exact hR) bot_le)
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, hl, -, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, -, hg', -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hg', hl, (mu_dual b X hX A hA hsp hA0).2, ← Real.exp_neg, hc2]

end Formalism.HN
