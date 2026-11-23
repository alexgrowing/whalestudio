import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceRankOneSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorResidueNonzeroOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankEigenspaceEmbeddingOneStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

namespace GlobalTheory.RedEig

theorem rTensor_mul_one_tmul {O R k : Type} [CommRing O] [CommRing R] [CommRing k] (ρ₀ : R →+* k) (χ : O →+* R) (e : R ⊗[ℤ] O)
    (he : ∀ a : O, e * ((1 : R) ⊗ₜ[ℤ] a) = χ a • e) (a : O) :
    ρ₀.toIntAlgHom.toLinearMap.rTensor O e * ((1 : k) ⊗ₜ[ℤ] a) = ρ₀ (χ a) • ρ₀.toIntAlgHom.toLinearMap.rTensor O e := by
  let Φ := Algebra.TensorProduct.map ρ₀.toIntAlgHom (AlgHom.id ℤ O)
  have hΦ : ∀ t, ρ₀.toIntAlgHom.toLinearMap.rTensor O t = Φ t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r b => simp [Φ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsm : ∀ (r : R) t, Φ (r • t) = ρ₀ r • Φ t := fun r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s b => simp [Φ, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  rw [hΦ, ← hsm, ← he a, map_mul]
  simp [Φ]

theorem span_rTensor_range_tensorAction {O R k Λ : Type} [CommRing O] [CommRing R] [CommRing k] [AddCommGroup Λ] [Module O Λ]
    (ρ₀ : R →+* k) (e : R ⊗[ℤ] O) :
    Submodule.span k ((ρ₀.toIntAlgHom.toLinearMap.rTensor Λ) ''
      (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
    = LinearMap.range (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
        (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) := by
  set red := ρ₀.toIntAlgHom.toLinearMap.rTensor Λ
  have key : ∀ (e : R ⊗[ℤ] O) (m : R ⊗[ℤ] Λ),
      red (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e m)
        = tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e) (red m) := by
    intro e m
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [LinearMap.rTensor_tmul, tensorAction_tmul, tensorAction_tmul]
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul s l => simp [red, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, map_add, map_add, smul_add]
    | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, map_add, LinearMap.add_apply]
  have hspan : Submodule.span k (Set.range red) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c l =>
      have : c ⊗ₜ[ℤ] l = c • red (1 ⊗ₜ l) := by simp [red, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have himg : (red '' (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
      = (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) '' Set.range red := by
    ext y
    simp only [LinearMap.coe_range, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨red m, ⟨m, rfl⟩, (key e m).symm⟩
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨_, ⟨m, rfl⟩, key e m⟩
  rw [himg, Submodule.span_image, hspan, Submodule.map_top]

theorem baseChangeAction_regular_apply {O R : Type} [CommRing O] [CommRing R] (a : O) (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * ((1 : R) ⊗ₜ[ℤ] a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add x y hx hy => rw [map_add, hx, hy, add_mul]

theorem exists_generator {V M : Type} [CommRing V] [Nontrivial V] [AddCommGroup M] [Module V M] (P : Submodule V M)
    [Module.Free V P] [Module.Finite V P] (h1 : Module.finrank V P = 1) {Q : Submodule V M} (hQ : IsCompl P Q) :
    ∃ e ∈ P, P ≤ Submodule.span V {e} ∧ ∃ f : M →ₗ[V] V, f e = 1 := by
  let b := Module.finBasisOfFinrankEq V P h1
  refine ⟨b 0, (b 0).2, fun x hx => ?_, (b.coord 0).comp (Submodule.linearProjOfIsCompl P Q hQ), ?_⟩
  · have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [LinearMap.comp_apply, show P.linearProjOfIsCompl Q hQ (b 0) = b 0 from
      Submodule.linearProjOfIsCompl_apply_left hQ _]
    simp

theorem exists_eigBar_eq_range : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (τ : PsiT D),
  ∃ ε : ct.kbar ⊗[ℤ] 𝓞 D.host.E, ε ≠ 0 ∧
    (∀ a : 𝓞 D.host.E, ε * ((1 : ct.kbar) ⊗ₜ[ℤ] a) = ct.ρ₀ (embV κ.c ct.W (embOf D τ) a) • ε) ∧
    ct.eigBar τ = LinearMap.range (tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) ε) := by
  intro D A N j S κ p ct τ
  let σ : (D.host.E →+* ℂ) → 𝓞 D.host.E →+* ct.V₀ := fun i => embV κ.c ct.W i
  have hσ : Function.Injective σ := by
    intro i i' h
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.host.E)) (RingHom.ext fun a => ?_)
    have := congrArg (fun g : 𝓞 D.host.E →+* ct.V₀ => (((g a : ct.V₀) : κ.c.F) : ℂ)) h
    exact this
  have hc : Fintype.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := NumberField.Embeddings.card _ _
  have h1 := GlobalTheory.T.finrank_eigenspace_embedding_one σ hσ hc (embOf D τ)
  set P := eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ)) with hP
  have : Module.Free ct.V₀ P := free_eigenSub_of_valuationRing _ _
  have : Module.Finite ct.V₀ P := finite_eigenSub_of_valuationRing _ _
  obtain ⟨Q, hQ⟩ := exists_isCompl_eigenSub_of_valuationRing
    (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ))
  obtain ⟨e, he, hle, f, hf⟩ := exists_generator P h1 hQ
  have heig : ∀ a : 𝓞 D.host.E, e * ((1 : ct.V₀) ⊗ₜ[ℤ] a) = σ (embOf D τ) a • e := fun a => by
    rw [← baseChangeAction_regular_apply]; exact mem_eigenSub.1 he a
  have hρ : ∀ x, ct.ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal ct.V₀ := fun x hx => by
    rw [At.ρ₀, RingHom.comp_apply] at hx
    exact (IsLocalRing.residue_eq_zero_iff x).1 ((algebraMap (IsLocalRing.ResidueField ct.V₀) ct.kbar).injective (hx.trans (map_zero _).symm))
  have : Module.Finite (𝓞 D.host.E) S.Dw.La := S.Dw.fin
  have : Module.Projective (𝓞 D.host.E) S.Dw.La := S.Dw.proj
  refine ⟨ct.ρ₀.toIntAlgHom.toLinearMap.rTensor _ e, GlobalTheory.T.rTensor_residue_nonzero_of_split ct.ρ₀ hρ e f hf, rTensor_mul_one_tmul ct.ρ₀ _ e heig, ?_⟩
  rw [At.eigBar, At.eigLat, GlobalTheory.T.eigenspace_rank_one_span (σ (embOf D τ)) e he hle]
  exact span_rTensor_range_tensorAction ct.ρ₀ e

end GlobalTheory.RedEig
