import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def othW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else lam0 s

def Pr {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
    [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [AddCommGroup V] [Module Kf V] [Module O V]
    (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) (M : Submodule O V₁) (N : Submodule O V₂) : Submodule O V :=
  Submodule.span O {x | ∃ F ∈ M, ∃ r ∈ N, x = μ F r}

def RestTensor : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∃ (μ : Vsp R.Kf (topW TT lam0) →ₗ[R.Kf] Vsp R.Kf (othW TT lam0) →ₗ[R.Kf] Vsp R.Kf lam0)
      (ν : Module.Dual R.Kf (Vsp R.Kf (topW TT lam0)) →ₗ[R.Kf] Module.Dual R.Kf (Vsp R.Kf (othW TT lam0)) →ₗ[R.Kf]
        Module.Dual R.Kf (Vsp R.Kf lam0)),
      (∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) ∧
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        HL (O := R.O) R.ι R.σ lam0 L =
          Pr μ (HL (O := R.O) R.ι R.σ (topW TT lam0) L) (HL (O := R.O) R.ι R.σ (othW TT lam0) L)) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        HLe p R.ι R.σ R.w lam0 e =
          Pr μ (HLe p R.ι R.σ R.w (topW TT lam0) e) (HLe p R.ι R.σ R.w (othW TT lam0) e)) ∧
      dimV R.Kf lam0 = dimV R.Kf (topW TT lam0) * dimV R.Kf (othW TT lam0)

def RestOrdBound : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ), IsDominant lamO →
    (∀ s i, |lamO s i| ≤ c) → ∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
      Re p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ))) (HL R.ι R.σ lamO e.src) ∧
      Re' p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ)))
          (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (HL (O := R.O) R.ι R.σ lamO e.tgt))

section Formal

variable {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
  [IsScalarTower O Kf V₁] [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [IsScalarTower O Kf V₂] [AddCommGroup V]
  [Module Kf V] [Module O V] [IsScalarTower O Kf V]

theorem scale_mono (c : Kf) {M M' : Submodule O V} (h : M ≤ M') : scale c M ≤ scale c M' := Submodule.map_mono h

theorem scale_scale_mem {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale a (scale b M)) :
    x ∈ scale (a * b) M := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mem_scale_scale {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale (a * b) M) :
    x ∈ scale a (scale b M) := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp h
  refine Submodule.mem_map.mpr ⟨b • z, Submodule.mem_map.mpr ⟨z, hz, by simp⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂} {F : V₁} {r : V₂}
    (hF : F ∈ scale a M) (hr : r ∈ scale b N) : μ F r ∈ scale (a * b) (Pr μ M N) := by
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨r0, hr0, rfl⟩ := Submodule.mem_map.mp hr
  refine Submodule.mem_map.mpr ⟨μ F0 r0, Submodule.subset_span ⟨F0, hF0, r0, hr0, rfl⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem nu_dual (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M)
    (hρ : ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf N) : ν G ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, r, hr, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG F hF
    obtain ⟨b, hb⟩ := hρ r hr
    exact ⟨a * b, by rw [hν, map_mul, ha, hb]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, ← algebraMap_smul Kf c x, map_smul, smul_eq_mul]⟩

theorem nu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ scale a (Formalism.GradedWeylDivisibility.dualLat O Kf M))
    (hρ : ρ ∈ scale b (Formalism.GradedWeylDivisibility.dualLat O Kf N)) :
    ν G ρ ∈ scale (a * b) (Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N)) := by
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hG
  obtain ⟨ρ0, hρ0, rfl⟩ := Submodule.mem_map.mp hρ
  refine Submodule.mem_map.mpr ⟨ν G0 ρ0, nu_dual μ ν hν hG0 hρ0, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

end Formal

theorem FactorsLE_of_index {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A : Submodule O V} {A' : Submodule O V'} {D : ℝ} {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (hcard : Fintype.card I = n) (x : I → V) (y : I → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O)
    (M : Matrix I I O) (hz : z ≠ 0) (hv : vLEO p z D)
    (hM : ∀ i j, ∑ l, be (x i) (y l) * algebraMap O Kf (M l j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' n D := by
  unfold FactorsLE
  right
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => x (e i), fun i => y (e i), fun i => hx _, fun i => hy _, z, M.submatrix e e, hz, hv, fun i j => ?_⟩
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun l => be (x (e i)) (y l) * algebraMap O Kf (M l (e j))), hM]
  simp [e.injective.eq_iff]

theorem othW_dom {n' m : ℕ} {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant lam0) :
    IsDominant (othW TT lam0) := by
  show ∀ s, Antitone (othW TT lam0 s)
  intro s
  simp only [othW]
  split_ifs
  · exact antitone_const
  · exact h s

theorem Ar_add {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Ar 1 lam0 = Ar 1 (topW TT lam0) + Ar 1 (othW TT lam0) := by
  unfold Ar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lamAt topW othW
  by_cases hs : s ∈ TT <;> by_cases he : Even (s : ℕ) <;> simp [hs, he]

end Formalism.MainNotions.flipOneThree.Pf

end
