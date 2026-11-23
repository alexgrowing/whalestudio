import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.DiagMat

def act (M : Matrix (Fin 8) (Fin 8) ℤ) (X : Type) [AddCommGroup X] : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun c := fun v => ∑ u, M v u • c u
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [smul_add, Finset.sum_add_distrib]

theorem act_apply (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) (v : Fin 8) :
    act M X c v = ∑ u, M v u • c u := rfl

theorem act_act (M N : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) :
    act M X (act N X c) = act (M * N) X c := by
  ext v
  simp only [act_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem act_one {X : Type} [AddCommGroup X] (c : Fin 8 → X) : act 1 X c = c := by
  ext v
  simp [act_apply, Matrix.one_apply]

theorem act_comp {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁] (M : Matrix (Fin 8) (Fin 8) ℤ)
    (π : X₀ →+ X₁) (c : Fin 8 → X₀) : act M X₁ (fun u => π (c u)) = fun u => π (act M X₀ c u) := by
  ext v
  simp [act_apply, map_sum, map_zsmul]

theorem matRel_iff (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) :
    MatRel W a b y y' ↔ act (W + W.transpose) X y' = Pi.single b (act (W + W.transpose) X y a) := by
  constructor
  · intro h; ext v; rw [act_apply, h v, Pi.single_apply]; rfl
  · intro h v; have := congrFun h v; rw [act_apply] at this; rw [this, Pi.single_apply]; rfl

end GlobalTheory.Poinc.Eq8.DiagMat

open GlobalTheory.Poinc.Eq8.DiagMat in

theorem GlobalTheory.Poinc.Eq8.exists_diag_of_matRel : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (Y X₀ X₁ : Type) [AddCommGroup Y] [AddCommGroup X₀] [AddCommGroup X₁] (m : Fin 8 → Fin 8 → (Y →+ Y)) (e₀ : Y ≃+ (Fin 8 → X₀)) (ρ : Y →+ (Fin 8 → X₁)), Function.Surjective ρ → (∀ a b y, MatRel W a b (e₀ y) (e₀ (m a b y))) → (∀ a b y, MatRel W a b (ρ y) (ρ (m a b y))) → ∃ π : X₀ →+ X₁, Function.Surjective π ∧ ∀ y u, ρ y u = π (e₀ y u) := by
  intro W hW Y X₀ X₁ _ _ _ m e₀ ρ hρ h₀ h₁
  set Q := W + W.transpose with hQ
  have hdet : IsUnit Q.det := by rw [hW.2]; exact isUnit_one
  have hQP : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have hPQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet

  let Ψ : (Fin 8 → X₀) →+ (Fin 8 → X₁) :=
    (act Q X₁).comp (ρ.comp ((e₀.symm : (Fin 8 → X₀) →+ Y).comp (act Q⁻¹ X₀)))
  have hΨ : ∀ z, Ψ (act Q X₀ (e₀ z)) = act Q X₁ (ρ z) := by
    intro z
    simp only [Ψ, AddMonoidHom.comp_apply, act_act, hPQ, act_one]
    simp
  have hE : ∀ a b c, Ψ (Pi.single b (c a)) = Pi.single b (Ψ c a) := by
    intro a b c
    set z := e₀.symm (act Q⁻¹ X₀ c) with hz
    have hc : act Q X₀ (e₀ z) = c := by simp [hz, act_act, hQP, act_one]
    have r0 := (matRel_iff W a b _ _).1 (h₀ a b z)
    have r1 := (matRel_iff W a b _ _).1 (h₁ a b z)
    rw [← hQ, hc] at r0
    rw [← hQ] at r1
    rw [← r0, hΨ, r1, ← hΨ, hc]
  let π : X₀ →+ X₁ := (Pi.evalAddMonoidHom (fun _ => X₁) 0).comp (Ψ.comp (AddMonoidHom.single (fun _ => X₀) 0))
  have hπ : ∀ b x, Ψ (Pi.single b x) = Pi.single b (π x) := by
    intro b x
    have := hE 0 b (Pi.single 0 x)
    simpa [π] using this
  have hdiag : ∀ c, Ψ c = fun u => π (c u) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    simp only [hπ]
    rw [← Finset.univ_sum_single (fun u => π (c u))]
  have key : ∀ y u, ρ y u = π (e₀ y u) := by
    intro y u
    have h1 : act Q X₁ (ρ y) = fun u => π (act Q X₀ (e₀ y) u) := by rw [← hΨ, hdiag]
    have h2 := congrArg (act Q⁻¹ X₁) h1
    rw [act_act, hPQ, act_one, act_comp, act_act, hPQ, act_one] at h2
    exact congrFun h2 u
  refine ⟨π, ?_, key⟩
  intro x
  obtain ⟨y, hy⟩ := hρ (fun _ => x)
  exact ⟨e₀ y 0, by rw [← key, hy]⟩
