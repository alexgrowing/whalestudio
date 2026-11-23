import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import GroundTheory.Brauer.TensorSimple
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.CoordArch

variable {p : ℕ} [Fact p.Prime]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_infinitePlace_embedding (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] (w : InfinitePlace K → ℂ) :
    w ∈ Submodule.span ℝ (Set.range fun (f : K) (u : InfinitePlace K) => u.embedding f) := by
  have hc : ∀ u : InfinitePlace K, u.IsComplex := fun u => IsTotallyComplex.isComplex u
  let P : mixedEmbedding.mixedSpace K →ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun x u => x.2 ⟨u, hc u⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : ∀ f : K, P (mixedEmbedding K f) = fun u => u.embedding f := by
    intro f; funext u
    exact mixedEmbedding.mixedEmbedding_apply_isComplex K f ⟨u, hc u⟩
  have hmem : ((0, fun u => w u.1) : mixedEmbedding.mixedSpace K) ∈
      Submodule.span ℝ (Set.range (mixedEmbedding.latticeBasis K)) := by
    rw [(mixedEmbedding.latticeBasis K).span_eq]; trivial
  have hmap := Submodule.mem_map_of_mem (f := P) hmem
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨_, (by rw [mixedEmbedding.latticeBasis_apply, hP])⟩

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
private theorem mem_span_range_psi {p : ℕ} [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p)
    (v : InfinitePlace G.F) (M : Matrix (Fin G.n) (Fin G.n) ℂ) :
    M ∈ Submodule.span ℂ (Set.range (G.psi v)) := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hsc : ∀ f : G.F, algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) f =
      Matrix.scalar (Fin G.n) (v.embedding f) := by
    intro f; ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      RingHom.algebraMap_toAlgebra]
  let ψ : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun f => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [G.psi_F, hsc] }
  let φ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ (fun z c => Algebra.commutes z _)
  have hφ : ∀ (z : ℂ) (c : G.C), φ (z ⊗ₜ c) = z • G.psi v c := by
    intro z c
    change (Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψ _) (z ⊗ₜ[G.F] c) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
  have hn : 0 < G.n := G.n_pos
  have hinj : Function.Injective φ := by
    let χ : G.C ⊗[G.F] ℂ →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
      φ.toRingHom.comp (Algebra.TensorProduct.comm G.F G.C ℂ).toRingEquiv.toRingHom
    have hker : TwoSidedIdeal.ker χ = ⊥ := by
      by_contra h
      obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot (TwoSidedIdeal.ker χ) h
      rw [TwoSidedIdeal.mem_ker] at hmem
      have h1 : χ (1 ⊗ₜ b) = b • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
        change φ ((Algebra.TensorProduct.comm G.F G.C ℂ) (1 ⊗ₜ b)) = _
        rw [Algebra.TensorProduct.comm_tmul, hφ, map_one]
      rw [hmem] at h1
      have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
      simp at h2
      exact hb h2.symm
    have hχ : Function.Injective χ := (TwoSidedIdeal.ker_eq_bot χ).1 hker
    intro x y hxy
    apply (Algebra.TensorProduct.comm G.F G.C ℂ).symm.injective
    apply hχ
    simpa [χ] using hxy
  have hrank : Module.finrank ℂ (ℂ ⊗[G.F] G.C) =
      Module.finrank ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, G.rankC, Module.finrank_matrix,
      Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  obtain ⟨t, rfl⟩ := hsurj M
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z c =>
    change φ (z ⊗ₜ c) ∈ _
    rw [hφ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in

theorem _root_.GlobalTheory.CoordArch.coord_bound : ∀ (p : ℕ) [Fact p.Prime] (G : _root_.GlobalTheory.LKTrip.HTGroup p), ∃ R : ℝ, ∀ (c : G.C) (i : Fin (Module.finrank ℚ G.C)),
    |((Module.finBasis ℚ G.C).repr c i : ℝ)| ≤ R * ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, ‖G.psi w c a b‖ := by
  intro p _ G
  classical
  let B := Module.finBasis ℚ G.C
  let Φ : G.C → (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := fun c u => G.psi u c
  let L : (Fin (Module.finrank ℚ G.C) → ℝ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    Fintype.linearCombination ℝ (fun i => Φ (B i))
  have hL : ∀ c : G.C, L (fun i => (B.repr c i : ℝ)) = Φ c := by
    intro c
    funext u a b
    have h := congrArg (fun x => G.psi u x a b) (B.sum_repr c)
    simp only [map_sum, Matrix.sum_apply, map_rat_smul] at h
    simp only [L, Φ, Fintype.linearCombination_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.smul_def]
  have hF : ∀ (w : InfinitePlace G.F → ℂ) (c : G.C),
      (fun u => w u • G.psi u c) ∈ Submodule.span ℝ (Set.range Φ) := by
    intro w c
    have hw := mem_span_infinitePlace_embedding G.F w
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      refine Submodule.subset_span ⟨algebraMap G.F G.C f * c, ?_⟩
      funext u
      simp only [Φ, map_mul, G.psi_F]
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    | zero =>
      convert Submodule.zero_mem (Submodule.span ℝ (Set.range Φ)) using 1
      funext u
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext u
      simp [add_smul]
    | smul r x _ hx =>
      convert Submodule.smul_mem _ r hx using 1
      funext u
      simp only [Pi.smul_apply]
      exact smul_assoc _ _ _
  have hspan : ∀ y : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ,
      y ∈ Submodule.span ℝ (Set.range Φ) := by
    intro y
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun u _ => ?_
    suffices h : ∀ M ∈ Submodule.span ℂ (Set.range (G.psi u)), ∀ z : ℂ,
        Pi.single u (z • M) ∈ Submodule.span ℝ (Set.range Φ) by
      simpa using h _ (mem_span_range_psi G u (y u)) 1
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      intro z
      convert hF (Pi.single u z) c using 1
      funext u'
      by_cases h : u' = u
      · subst h; simp
      · simp [h]
    | zero =>
      intro z
      rw [smul_zero, Pi.single_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro z
      rw [smul_add, Pi.single_add]
      exact Submodule.add_mem _ (hx z) (hy z)
    | smul z' x _ hx =>
      intro z
      rw [smul_smul]
      exact hx _
  have hrange : LinearMap.range L = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    refine Submodule.span_le.mpr ?_ (hspan y)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, hL c⟩
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℚ G.C) → ℝ) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank G.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces G.F
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero G.F
    have h4 := Module.finrank_mul_finrank ℚ G.F G.C
    have h5 := G.rankC
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← h4, h5, ← h1, h2, h3]
    ring
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
      (LinearMap.range_eq_top.1 hrange)
  let E : (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) ≃ₗ[ℝ]
      (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    LinearEquiv.piCongrRight fun _ => (Matrix.ofLinearEquiv ℝ).symm
  obtain ⟨K, -, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (E.toLinearMap ∘ₗ L)).1 (E.injective.comp hinj)
  refine ⟨K, fun c i => ?_⟩
  have hx := hK.le_mul_dist (fun j => (B.repr c j : ℝ)) 0
  rw [dist_zero_right, map_zero, dist_zero_right] at hx
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hL] at hx
  rw [← Real.norm_eq_abs]
  refine (norm_le_pi_norm (fun j => (B.repr c j : ℝ)) i).trans (hx.trans ?_)
  gcongr
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun u => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  exact (Finset.single_le_sum (f := fun b => ‖G.psi u c a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans ((Finset.single_le_sum (f := fun a => ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ a)).trans
    (Finset.single_le_sum (f := fun u => ∑ a, ∑ b, ‖G.psi u c a b‖)
    (fun _ _ => by positivity) (Finset.mem_univ u)))

end GlobalTheory.CoordArch
