import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfInvLie
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private def invSub (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.SInv φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, by simp⟩
  add_mem' := by
    intro φ ψ h h'
    refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g),
      fun t g => congrArg₂ (· + ·) (h.centre t g) (h'.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    have h2 : IsOpen {k | finRep E a k ψ = ψ} := h'.level
    refine open_stab (finRep E a) _ (h1.inter h2) ⟨by simp, by simp⟩ ?_
    rintro k ⟨e1, e2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) e1 e2)
  smul_mem' := by
    intro c φ h
    refine ⟨fun γ g => congrArg (c • ·) (h.left γ g), fun t g => congrArg (c • ·) (h.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    refine open_stab (finRep E a) _ h1 (by simp) ?_
    intro k e1
    exact (map_smul _ _ _).trans (congrArg (c • ·) e1)

theorem UpperTheory.V.Lit.Geo.Pf.twLie :
    UpperTheory.V.Lit.Geo.Pf.TwLie := by
  intro E _ _ _ a Ξ r χ hχ X x hx
  let N : Submodule ℂ (Sm E a) := (invSub E a).comap (mulChi a χ).toLinearMap
  have hiff : ∀ y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ), Pf.TwInv χ y ↔ y ∈ tens Ξ.d N := fun y => by
    rw [mem_tens]; rfl
  rw [hiff] at hx
  rw [hiff, hiff]
  have hA : smA Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    have h0 : cmp j x ∈ N := mem_tens.1 hx j
    have h1 : lie E a X (cmp j x) + ((r * ell E a X : ℝ) : ℂ) • cmp j x ∈ N := by
      change Pf.SInv (mulChi a χ _)
      rw [← hχ.2]
      exact (Pf.invLie E a _ h0).2 X
    exact (N.add_mem_iff_left (N.smul_mem _ h0)).1 h1
  have hB : smB Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
