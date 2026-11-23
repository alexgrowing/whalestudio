import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

noncomputable section

namespace UpperTheory.V.Af.Gk

private theorem map_qdet_conj {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (f : A →+* A)
    (hf : ∀ c : ℂ, f (algebraMap ℂ A c) = algebraMap ℂ A (starRingEnd ℂ c)) (X : Fin n → Fin n → A)
    (hX : ∀ i j, f (X i j) = X i j) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet X (starRingEnd ℂ u) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm, map_add, hX, apply_ite f, hf, map_zero, map_sub, map_natCast]

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def conjOp : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z := (conjFn E a).toLinearMap ∘ₛₗ (z ∘ₛₗ (conjFn E a).toLinearMap)
  map_one' := LinearMap.ext fun φ => conjFn_conjFn φ
  map_mul' x y := LinearMap.ext fun φ => by
    change conjFn E a (x (y (conjFn E a φ))) = conjFn E a (x (conjFn E a (conjFn E a (y (conjFn E a φ)))))
    rw [conjFn_conjFn]
  map_zero' := LinearMap.ext fun φ => map_zero (conjFn E a)
  map_add' x y := LinearMap.ext fun φ => map_add (conjFn E a) _ _

private theorem conjOp_apply (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjOp z φ = conjFn E a (z (conjFn E a φ)) := rfl

private theorem conjOp_algebraMap (c : ℂ) :
    conjOp (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjOp_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smulₛₗ, conjFn_conjFn]

private theorem conjOp_Eop (v : InfinitePlace E) (i j : Fin a) : conjOp (Eop v i j) = Eop v i j :=
  LinearMap.ext fun φ => (congrArg (conjFn E a) (act_conjFn (.lie _) φ)).trans (conjFn_conjFn _)

private theorem conjOp_cap (v : InfinitePlace E) (u : ℂ) :
    conjOp (cap (a := a) v u) = cap v (starRingEnd ℂ u) := by
  refine (map_qdet_conj (conjOp (E := E) (a := a)) conjOp_algebraMap (Eop v) (conjOp_Eop v) _).trans ?_
  refine congrArg (Formalism.REAL.qdet (Eop (a := a) v)) ?_
  simp only [map_add, map_div₀, map_sub, map_natCast, map_one, map_ofNat]

private theorem conjOp_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjOp z ∈ Zalg E a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    rw [conjOp_cap]
    exact Algebra.subset_adjoin ⟨τ, _, rfl⟩
  | algebraMap c => rw [conjOp_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem fin_of_conj {s t : Set (Sm E a)} (h : FiniteDimensional ℂ (Submodule.span ℂ s))
    (hst : ∀ y ∈ t, ∃ x ∈ s, conjFn E a x = y) : FiniteDimensional ℂ (Submodule.span ℂ t) := by
  have h1 : (Submodule.span ℂ s).FG := Module.Finite.iff_fg.1 h
  have h2 : FiniteDimensional ℂ ((Submodule.span ℂ s).map (conjFn E a).toLinearMap) :=
    Module.Finite.iff_fg.2 (h1.map _)
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ s).map (conjFn E a).toLinearMap)
    (Submodule.span_le.2 fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := hst y hy
  exact ⟨x, Submodule.subset_span hx, rfl⟩

private theorem isAutForm_conjFn {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (conjFn E a φ) where
  left γ g := by rw [conjFn_apply, conjFn_apply, h.left]
  level := by
    convert h.level using 1
    ext k
    exact (Iff.of_eq (congrArg (· = conjFn E a φ) (act_conjFn (.fin k) φ))).trans (conjFn E a).injective.eq_iff
  kfin := fin_of_conj h.kfin (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, (act_conjFn (.cpt k) φ).symm⟩)
  zfin := fin_of_conj h.zfin (by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨_, ⟨conjOp z, conjOp_mem hz, rfl⟩, ?_⟩
    beta_reduce
    rw [conjOp_apply, conjFn_conjFn])
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    refine ⟨C, N, fun y => ?_⟩
    rw [conjFn_apply, Complex.norm_conj]
    exact h1 y

end UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.conjCusp :
    UpperTheory.V.Af.Gk.ConjCusp := by
  intro F _ _ _ a φ h
  refine ⟨isAutForm_conjFn h.1, ?_⟩
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  have key := h.2 r h0 h1 μ 𝓕 hμ hF g
  simp only [conjFn_apply]
  rw [integral_conj, key, map_zero]
