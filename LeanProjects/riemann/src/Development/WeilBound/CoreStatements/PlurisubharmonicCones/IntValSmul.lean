import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundle

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

noncomputable section
namespace LevelTowerAlt.Lin

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O]
    (ρ : O →+* Module.End R W) (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

def intVal (σ : 𝓞 E →+* L) (a : 𝓞 E) : 𝓞 L :=
  ⟨σ a, (NumberField.RingOfIntegers.isIntegral a).map σ.toIntAlgHom⟩

theorem intVal_coe (σ : 𝓞 E →+* L) (a : 𝓞 E) : ((intVal σ a : 𝓞 L) : L) = σ a := rfl

theorem intVal_smul (σ : 𝓞 E →+* L) (a : 𝓞 E) (x : V) : intVal σ a • x = σ a • x := by
  rw [← intVal_coe σ a]
  exact (algebraMap_smul L (intVal σ a) x).symm

structure Pre (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (V₀ : Type) [AddCommGroup V₀] [Module (𝓞 L) V₀]
    (B : HermitianBundle.{0} L) where
  ρ : 𝓞 E →+* Module.End L V
  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)
  fin : Module.Finite (𝓞 L) V₀
  j : V₀ →ₗ[𝓞 L] V
  j_inj : Function.Injective j
  span : Submodule.span L (Set.range j) = ⊤
  ρ₀ : 𝓞 E → V₀ → V₀
  j_ρ : ∀ a x, j (ρ₀ a x) = ρ a (j x)
  r : ℕ
  ε : Fin r → V₀
  ε_li : LinearIndependent (𝓞 L) ε
  I_stable : ∀ a, ∀ x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)),
    ρ a x ∈ AddSubgroup.closure (Set.range fun i => j (ε i))
  f : V₀ →ₗ[𝓞 L] B.carrier
  ker : LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε)
  full : ∀ y, ∃ (a : 𝓞 L) (x : V₀), a ≠ 0 ∧ f x = a • y
  ρ' : 𝓞 E → B.carrier → B.carrier
  f_ρ : ∀ a x, f (ρ₀ a x) = ρ' a (f x)
  bar : 𝓞 E → 𝓞 E
  bar_conj : ∀ (τ : 𝓞 E →+* ℂ), Function.Injective τ → ∀ a, τ (bar a) = starRingEnd ℂ (τ a)
  adj : ∀ (ι : L →+* ℂ) a x y, (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] y) =
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] ρ' (bar a) y)

variable {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] {B : HermitianBundle.{0} L} (P : Pre E L Ψ V V₀ B)

theorem Pre.eig {s : Ψ ⊕ Ψ} {x : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s)) (a : 𝓞 E) :
    P.ρ' a (P.f x) = intVal (P.σ s) a • P.f x := by
  have h1 : P.ρ₀ a x = intVal (P.σ s) a • x := by
    apply P.j_inj
    rw [P.j_ρ, map_smul, intVal_smul]
    exact (mem_eigSp _ _ _).1 hx a
  rw [← P.f_ρ, h1, map_smul]

theorem Pre.orth {s s' : Ψ ⊕ Ψ} (h : s ≠ s') (ι : L →+* ℂ) {x y : V₀} (hx : P.j x ∈ eigSp P.ρ (P.σ s))
    (hy : P.j y ∈ eigSp P.ρ (P.σ s')) :
    (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, P.σ s a ≠ P.σ s' a := by
    by_contra hc
    push_neg at hc
    exact h (P.σ_bij.1 (RingHom.ext hc))
  have key : ∀ (c : 𝓞 L) (u : B.carrier), ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] (c • u) : Fibre ι B.carrier) =
      (ι (c : L) : ℂ) • ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] u) := by
    intro c u
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  have hτ : Function.Injective (ι.comp (P.σ s')) := ι.injective.comp (P.σ_inj s')
  have e := P.adj ι a (P.f x) (P.f y)
  rw [P.eig hx, P.eig hy, key, key, (B.metric.form ι).smul_left,
    InnerProductSpace.Core.inner_smul_right (c := (B.metric.form ι).toCore), intVal_coe, intVal_coe] at e
  have hb := P.bar_conj _ hτ a
  simp only [RingHom.comp_apply] at hb
  rw [hb] at e
  have hne : (starRingEnd ℂ) (ι (P.σ s a)) ≠ (starRingEnd ℂ) (ι (P.σ s' a)) := by
    intro heq
    exact ha (ι.injective ((starRingEnd ℂ).injective heq))
  have : ((starRingEnd ℂ) (ι (P.σ s a)) - (starRingEnd ℂ) (ι (P.σ s' a))) *
      (B.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f x) ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] P.f y) = 0 := by
    rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem Pre.li {ι : Type} {x : ι → V₀} (hx : LinearIndependent (𝓞 L) x) : LinearIndependent L fun i => P.j (x i) := by
  have h := hx.map' P.j (LinearMap.ker_eq_bot.2 P.j_inj)
  exact h.localization (Rₛ := L) (S := nonZeroDivisors (𝓞 L))

def Pre.inv : LinearMap.range P.j →ₗ[𝓞 L] V₀ := (LinearEquiv.ofInjective P.j P.j_inj).symm.toLinearMap

theorem Pre.j_inv (x : LinearMap.range P.j) : P.j (P.inv x) = x := by
  have := (LinearEquiv.ofInjective P.j P.j_inj).apply_symm_apply x
  exact congrArg Subtype.val this

theorem Pre.inv_j (x : V₀) : P.inv ⟨P.j x, x, rfl⟩ = x := P.j_inj (P.j_inv _)

def Pre.lin : LinPt E L Ψ V where
  ρ := P.ρ
  σ := P.σ
  σ_bij := P.σ_bij
  σ_inj := P.σ_inj
  Λ := LinearMap.range P.j
  fg := by
    haveI := P.fin
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span := P.span
  stable := by
    rintro a _ ⟨x, rfl⟩
    exact ⟨_, P.j_ρ a x⟩
  I := AddSubgroup.closure (Set.range fun i => P.j (P.ε i))
  I_le := fun x hx => (AddSubgroup.closure_le (LinearMap.range P.j).toAddSubgroup).2
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  I_stable := P.I_stable
  I_basis := ⟨P.r, _, P.li P.ε_li, rfl⟩
  Bq := B
  f := P.f.comp P.inv
  ker := fun x => by
    have e : Submodule.span (𝓞 L) (AddSubgroup.closure (Set.range fun i => P.j (P.ε i)) : Set V) =
        (Submodule.span (𝓞 L) (Set.range P.ε)).map P.j := by
      rw [Submodule.map_span, ← Set.range_comp]
      refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono AddSubgroup.subset_closure)
      exact (AddSubgroup.closure_le (Submodule.span (𝓞 L) (Set.range (P.j ∘ P.ε))).toAddSubgroup).2
        Submodule.subset_span hy
    rw [e, ← P.ker, LinearMap.comp_apply]
    constructor
    · intro h
      exact ⟨_, h, P.j_inv x⟩
    · rintro ⟨y, hy, hxy⟩
      have : P.inv x = y := P.j_inj ((P.j_inv x).trans hxy.symm)
      rw [this]
      exact hy
  full := fun y => by
    obtain ⟨a, x, ha, h⟩ := P.full y
    exact ⟨a, ⟨P.j x, x, rfl⟩, ha, by rw [LinearMap.comp_apply, P.inv_j, h]⟩
  orth := by
    rintro s s' h ι _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact P.orth h ι (by rw [P.j_inv]; exact hx) (by rw [P.j_inv]; exact hy)

include P in
theorem Pre.rank_le [Module.Finite L V] : Module.finrank (𝓞 L) B.carrier ≤ Module.finrank L V := by
  have h2 : Module.rank (𝓞 L) V₀ ≤ (Module.finrank L V : Cardinal) := by
    apply _root_.rank_le
    intro s hs
    have := (P.li hs).fintype_card_le_finrank
    simpa using this
  have hq : Module.rank (𝓞 L) (B.carrier ⧸ LinearMap.range P.f) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, x, ha, h⟩ := P.full y
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← h]
    exact ⟨x, rfl⟩
  have h1 : Module.rank (𝓞 L) B.carrier ≤ Module.rank (𝓞 L) V₀ := by
    rw [← rank_quotient_add_rank_of_isDomain (LinearMap.range P.f), hq, zero_add]
    exact rank_range_le P.f
  exact Module.finrank_le_of_rank_le (h1.trans h2)

end LevelTowerAlt.Lin
