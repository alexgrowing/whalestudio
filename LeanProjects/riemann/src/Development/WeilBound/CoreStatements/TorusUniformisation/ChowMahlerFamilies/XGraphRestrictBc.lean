import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_graph_restrict_bc

section Span

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] {RC : Subalgebra o C}
  {A B : Type} [AddCommGroup A] [Module C A] [AddCommGroup B] [Module C B]

theorem mem_span {S : Set A} {e : A} (he : e ∈ S) : e ∈ spanOver RC S :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, e, he, (one_smul _ _).symm⟩

theorem smul_mem {S : Set A} {a : C} (ha : a ∈ RC) {x : A} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, RC.mul_mem ha hc, e, he, (mul_smul _ _ _).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem map_mem (T : A →ₗ[C] B) {S : Set A} {S' : Set B} (h : ∀ e ∈ S, T e ∈ spanOver RC S')
    {x : A} (hx : x ∈ spanOver RC S) : T x ∈ spanOver RC S' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    rw [map_smul]
    exact smul_mem hc (h e he)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

end Span

theorem exists_section {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {V Z : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Z] [Module Ω Z]
    (Δ : AddSubgroup (V × Z)) (N : ℕ) (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ)
    (hL : LocFree R N (Δ.map (AddMonoidHom.fst V Z))) :
    ∃ σ : V →ₗ[Ω] Z, ∀ v ∈ Δ.map (AddMonoidHom.fst V Z), (v, σ v) ∈ Δ := by
  let L : Submodule R V :=
    { carrier := Δ.map (AddMonoidHom.fst V Z)
      add_mem' := fun ha hb => AddSubgroup.add_mem _ ha hb
      zero_mem' := AddSubgroup.zero_mem _
      smul_mem' := fun a x hx => hL.1 a a.2 x hx }
  have hL' : LocFree R N L.toAddSubgroup := hL
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis hL'
  have hz : ∀ i, ∃ z : Z, ((v i : V), z) ∈ Δ := by
    intro i
    obtain ⟨⟨x, z⟩, hx, h⟩ := (v i).2
    have h' : x = v i := h
    exact ⟨z, h' ▸ hx⟩
  choose z hz using hz
  refine ⟨∑ i, (φ i).smulRight (z i), fun e he => ?_⟩
  have : (e, (∑ i, (φ i).smulRight (z i)) e) = ∑ i, φ i e • ((v i : V), z i) := by
    ext
    · simp [Prod.fst_sum, hv]
    · simp [Prod.snd_sum]
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => hΔ _ (hφ i e he) _ (hz i)

end PositivityTheory.Xgn.A_graph_restrict_bc

open PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.t_graph_restrict_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
  intro o Ω C _ _ _ _ _ _ _ R RC _ V Vc _ _ _ _ _ _ Z Zc _ _ _ _ _ _ b b' hb _ Δ H N hΔ hL hH _
  obtain ⟨σ, hσ⟩ := exists_section R Δ N hΔ hL
  obtain ⟨τ, hτ⟩ : ∃ τ : Vc →ₗ[C] Zc, ∀ v, τ (b v) = b' (σ v) :=
    ⟨hb.lift (b' ∘ₗ σ), fun v => hb.lift_eq _ v⟩
  have K1 : ∀ x ∈ spanOver RC (Prod.map b b' '' Δ),
      x.2 - τ x.1 ∈ spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
    intro x hx
    refine map_mem (LinearMap.snd C Vc Zc - τ ∘ₗ LinearMap.fst C Vc Zc) ?_ hx
    rintro _ ⟨⟨v, z⟩, hvz, rfl⟩
    refine mem_span ⟨z - σ v, ?_, by simp [hτ]⟩
    have := Δ.sub_mem hvz (hσ v ⟨(v, z), hvz, rfl⟩)
    simpa using this
  have K2 : ∀ y ∈ spanOver RC (b '' H), (y, τ y) ∈
      spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) := by
    intro y hy
    refine map_mem (LinearMap.prod LinearMap.id τ) ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨(v, σ v), ⟨hσ v (hH hv), hv, trivial⟩, ?_⟩
    simp [hτ]
  have K3 : ∀ z ∈ spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)), ((0 : Vc), z) ∈
      spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) := by
    intro z hz
    refine map_mem (LinearMap.inr C Vc Zc) ?_ hz
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨(0, v), ⟨hv, H.zero_mem, trivial⟩, ?_⟩
    simp
  have K4 : ∀ x ∈ spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))),
      x ∈ spanOver RC (Prod.map b b' '' Δ) := by
    intro x hx
    refine map_mem LinearMap.id ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨v, hv.1, rfl⟩
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · rintro ⟨y, z⟩ ⟨h1, h2, -⟩
    have := AddSubgroup.add_mem _ (K2 y h2) (K3 _ (K1 _ h1))
    simpa using this
  · intro x hx
    refine ⟨K4 x hx, ?_, trivial⟩
    refine map_mem (LinearMap.fst C Vc Zc) ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨v.1, hv.2.1, rfl⟩
  · intro z hz
    simpa using K1 _ hz
  · intro z hz
    exact K4 _ (K3 z hz)
