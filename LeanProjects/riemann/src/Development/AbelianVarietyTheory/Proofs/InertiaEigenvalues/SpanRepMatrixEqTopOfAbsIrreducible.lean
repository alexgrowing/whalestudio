import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BurnsideField

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isAlgClosed {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_mat_eq_top_of_isIrrSub {Γ K : Type} [Group Γ] [Field K] [IsAlgClosed K] {r : ℕ}
    (σ : Γ →* GL (Fin r) K) (h : IsIrrSub σ ⊤) : Submodule.span K (Set.range (mat σ)) = ⊤ := by
  classical
  let τ : Representation K Γ (Fin r → K) :=
    { toFun := fun g => Matrix.toLin' (mat σ g)
      map_one' := by simp [mat]; rfl
      map_mul' := fun g g' => by simp [mat, Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (mat σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      exact (congrArg Subrepresentation.toSubmodule hbt).symm
    refine ⟨fun W => ?_⟩
    rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isAlgClosed τ hirr
  have hm : Set.range (mat σ) = (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (mat σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

theorem span_eq_top_of_span_map {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k)
    (h : Submodule.span K (Set.range fun g => (M g).map (algebraMap k K)) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let F : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
    { toFun := fun X => ∑ i, ∑ j, X i j * algebraMap k K (f (Matrix.single i j 1))
      map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }
  have hF : ∀ X : Matrix (Fin r) (Fin r) k, F (X.map (algebraMap k K)) = algebraMap k K (f X) := by
    intro X
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    change ∑ i, ∑ j, algebraMap k K (X i j) * algebraMap k K (f (Matrix.single i j 1)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, map_mul]
  have hker : (⊤ : Submodule K (Matrix (Fin r) (Fin r) K)) ≤ LinearMap.ker F := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have : f (M g) = 0 := hf (Submodule.subset_span ⟨g, rfl⟩)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
  apply hf0
  refine LinearMap.ext fun X => ?_
  have h1 : F (X.map (algebraMap k K)) = 0 := hker trivial
  rw [hF] at h1
  exact (algebraMap k K).injective (by rw [h1]; simp)

theorem span_mat_eq_top_of_absIrrSub :
    ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  intro Γ k _ _ r ρ h
  classical
  have htop : Submodule.span (AlgebraicClosure k)
      ((fun v : Fin r → k => (algebraMap k (AlgebraicClosure k)) ∘ v) ''
      ((⊤ : Submodule k (Fin r → k)) : Set (Fin r → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub at h
  rw [htop] at h
  have h2 := span_mat_eq_top_of_isIrrSub _ h
  have h3 : mat (mapRep (algebraMap k (AlgebraicClosure k)) ρ) =
      fun g => (mat ρ g).map (algebraMap k (AlgebraicClosure k)) := by
    funext g
    ext p q
    simp [mat, mapRep]
  rw [h3] at h2
  exact span_eq_top_of_span_map (mat ρ) h2

end GlobalTheory.BurnsideField
