import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolFan

section Extend

variable {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]

theorem mem_balForms_of_smul {n : ℤ} (hn : n ≠ 0) {β : LinearMap.BilinForm ℤ X} (h : n • β ∈ balForms bar X) :
    β ∈ balForms bar X := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun y z => mul_left_cancel₀ hn (by simpa using h1 y z),
    fun a y z => mul_left_cancel₀ hn (by simpa using h2 a y z)⟩

theorem exists_extend_balForms [Module.Free ℤ X] [Module.Finite ℤ X] (f : balForms bar X →ₗ[ℤ] ℤ) :
    ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ β : balForms bar X, ℓ β = f β := by
  let P := balForms bar X
  haveI : NoZeroSMulDivisors ℤ (LinearMap.BilinForm ℤ X ⧸ P) := by
    constructor
    intro n q h
    induction q using Submodule.Quotient.induction_on with
    | H β =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      by_cases hn : n = 0
      · exact Or.inl hn
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero _).2 (mem_balForms_of_smul hn h))
  haveI : Module.Free ℤ (LinearMap.BilinForm ℤ X ⧸ P) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
  have hr : ∀ β, β - s (P.mkQ β) ∈ P := fun β => by
    rw [← Submodule.Quotient.mk_eq_zero]
    change P.mkQ (β - s (P.mkQ β)) = 0
    rw [map_sub, ← LinearMap.comp_apply P.mkQ s, hs]
    simp
  let r : LinearMap.BilinForm ℤ X →ₗ[ℤ] P := (LinearMap.id - s ∘ₗ P.mkQ).codRestrict P hr
  refine ⟨f ∘ₗ r, fun β => ?_⟩
  have : r β = β := Subtype.ext (by simp [r, (Submodule.Quotient.mk_eq_zero P).2 β.2])
  simp only [LinearMap.comp_apply, this]

end Extend

end GlobalTheory.PolFan

namespace GlobalTheory.ChartMono

theorem exists_intPiece : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (k : ℕ)
    (δ : Fin k → LinearMap.BilinForm ℤ X) (N : ℕ) (S : Set (LinearMap.BilinForm ℤ X)), IsPolFanOn H.bar φ X →
    IsCone H.bar φ δ → (∀ β ∈ S, ∃ (M : ℕ) (a : Fin k → ℤ), 0 < M ∧ (M : ℤ) • β = ∑ i, a i • δ i) →
    ∀ be : LinearMap.BilinForm ℤ X, GlobalTheory.ChartMono.InRealCone δ be → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (ℓ be : ℝ) = N * φ.evalZ be ∧ ∀ β ∈ S, β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β := by
  intro E _ _ _ H φ X _ _ _ _ k δ N S hF hC hS be hbe
  haveI : Module.Finite ℤ X := Module.Finite.trans (R := ℤ) (𝓞 E) X
  haveI : NoZeroSMulDivisors ℤ X := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) X)
    have hinj : Function.Injective (s.restrictScalars ℤ) :=
      Function.LeftInverse.injective (g := Finsupp.linearCombination (𝓞 E) id) fun x => LinearMap.congr_fun hs x
    exact Function.Injective.noZeroSMulDivisors _ hinj (map_zero _) fun n x => map_zsmul _ n x
  haveI : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'

  choose v hv using fun i => hF.integral (δ i) (hC.mem i) (hC.nonneg i)

  obtain ⟨n, b, hb⟩ := hC.basis
  let f : balForms H.bar X →ₗ[ℤ] ℤ := b.constr ℤ (Sum.elim (fun i => (N : ℤ) * v i) 0)
  obtain ⟨ℓ, hℓ⟩ := exists_extend_balForms f
  have hδ : ∀ i, ℓ (δ i) = (N : ℤ) * v i := fun i => by
    have := hℓ ⟨δ i, hC.mem i⟩
    have hbi : b (Sum.inl i) = ⟨δ i, hC.mem i⟩ := hb i
    rw [← hbi] at this
    simp only [f, Module.Basis.constr_basis, Sum.elim_inl] at this
    rwa [hbi] at this
  have hδR : ∀ i, (ℓ (δ i) : ℝ) = N * φ.evalZ (δ i) := fun i => by rw [hδ i, hv i]; push_cast; ring
  refine ⟨ℓ, ?_, fun β hβS hβ hp => ?_⟩
  · obtain ⟨c, hc0, hc⟩ := hbe
    have e1 : φ.evalZ be = ∑ i, c i * φ.evalZ (δ i) := by
      rw [← evalR_toReal, hc]
      exact (linearOn_iff φ δ).1 hC.linear c hc0
    have e2 := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) Function.injective_id ℓ
      (β := Sum.elim δ fun _ : Unit => be) (c := Sum.elim c fun _ => -1) (by
        rw [Fintype.sum_sum_type]
        simp [hc])
    rw [Fintype.sum_sum_type] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, LinearMap.id_apply] at e2
    rw [e1, Finset.mul_sum]
    have e3 : (ℓ be : ℝ) = ∑ i, c i * (ℓ (δ i) : ℝ) := by linarith
    rw [e3]
    exact Finset.sum_congr rfl fun i _ => by rw [hδR i]; ring
  · obtain ⟨M, a, hM, hMa⟩ := hS β hβS
    obtain ⟨N₀, ℓ₁, hN₀, h1, h2, -⟩ := hC.strict
    have k1 : (M : ℝ) * ℓ β = ∑ i, (a i : ℝ) * ℓ (δ i) := by
      have := congrArg ℓ hMa
      simp only [map_smul, map_sum, smul_eq_mul] at this
      exact_mod_cast this
    have k2 : (M : ℝ) * ℓ₁ β = ∑ i, (a i : ℝ) * ℓ₁ (δ i) := by
      have := congrArg ℓ₁ hMa
      simp only [map_smul, map_sum, smul_eq_mul] at this
      exact_mod_cast this
    have k3 : (M : ℝ) * ((N₀ : ℝ) * ℓ β) = (M : ℝ) * ((N : ℝ) * ℓ₁ β) := by
      rw [mul_left_comm, k1, mul_left_comm (M : ℝ) (N : ℝ), k2, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hδR i, h1 i]; ring
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have k4 : (N₀ : ℝ) * ℓ β = (N : ℝ) * ℓ₁ β := mul_left_cancel₀ hMpos.ne' k3
    have k5 := h2 β hβ hp
    have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
    have k6 : (N : ℝ) * ((N₀ : ℝ) * φ.evalZ β) ≤ (N : ℝ) * ℓ₁ β :=
      mul_le_mul_of_nonneg_left k5 (Nat.cast_nonneg N)
    have : (N₀ : ℝ) * ((N : ℝ) * φ.evalZ β) ≤ (N₀ : ℝ) * ℓ β := by nlinarith
    exact le_of_mul_le_mul_left this hN₀pos

end GlobalTheory.ChartMono
