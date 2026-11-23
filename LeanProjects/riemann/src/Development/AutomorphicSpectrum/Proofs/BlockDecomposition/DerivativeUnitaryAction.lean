import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExpSkewHermitian

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.IntegrateK

variable {n : ℕ}

theorem exp_smul_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

def onePar (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_smul_mem_unitary X hX s⟩

theorem onePar_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : onePar X hX 0 = 1 := by
  apply Subtype.ext
  simp [onePar]

theorem onePar_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (h s : ℝ) :
    onePar X hX (h + s) = onePar X hX h * onePar X hX s := by
  apply Subtype.ext
  have hc : Commute ((h : ℂ) • X) ((s : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = _ * _
  simp only [onePar]
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

theorem inner_sum_left {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Kf : Fin n → Fin n → Module.End ℂ V)
    (hs : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (x y : V) :
    ⟪∑ a, ∑ b, X a b • Kf a b x, y⟫_ℂ = -⟪x, ∑ a, ∑ b, X a b • Kf a b y⟫_ℂ := by
  have hent : ∀ a b, (starRingEnd ℂ) (X a b) = -X b a := by
    intro a b
    have := congrFun (congrFun hX b) a
    simpa [Matrix.conjTranspose_apply] using this
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hs, hent]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem intertwines_unitary : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  intro n H V _ _ _ _ _ ρ G hG σ Kf hK hskew T hT k w
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryExp.exists_skew_exp_eq n k
  have hk1 : onePar X hX 1 = k := by
    apply Subtype.ext
    have := congrArg Units.val hk
    have h4 : ((uG k : _ˣ) : Matrix (Fin n) (Fin n) ℂ) = k.1 := rfl
    rw [h4] at this
    simpa [onePar] using this.symm
  let Tc : H →L[ℝ] V :=
    (⟨T, T.continuous_of_finiteDimensional⟩ : H →L[ℂ] V).restrictScalars ℝ
  have hsub : ∀ u s : ℝ, onePar X hX (u - s) * onePar X hX s = onePar X hX u := by
    intro u s
    rw [← onePar_add, sub_add_cancel]
  have hY : ∀ s, HasDerivAt (fun s => T (ρ (onePar X hX s) w))
      (∑ a, ∑ b, X a b • Kf a b (T (ρ (onePar X hX s) w))) s := by
    intro s
    have h0 := hG X (onePar X hX) hX (fun _ => rfl) (ρ (onePar X hX s) w)
    have h1 : HasDerivAt (fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
        (T (∑ a, ∑ b, X a b • G a b (ρ (onePar X hX s) w))) 0 :=
      Tc.hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := HasDerivAt.comp_sub_const (f := fun t => T (ρ (onePar X hX t) (ρ (onePar X hX s) w)))
      s s (by simpa using h1)
    have e : (fun u => T (ρ (onePar X hX (u - s)) (ρ (onePar X hX s) w)))
        = fun u => T (ρ (onePar X hX u) w) := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    simpa only [hT] using h2
  have hU : ∀ (v : V) (s : ℝ), HasDerivAt (fun s => σ (onePar X hX s) v)
      (∑ a, ∑ b, X a b • Kf a b (σ (onePar X hX s) v)) s := by
    intro v s
    obtain ⟨S, _, hmem, _, _, hd⟩ := hK.2 (σ (onePar X hX s) v)
    have h0 := hd X (onePar X hX) (fun _ => rfl) _ hmem
    have h2 := HasDerivAt.comp_sub_const (f := fun t => σ (onePar X hX t) (σ (onePar X hX s) v))
      s s (by simpa using h0)
    have e : (fun u => σ (onePar X hX (u - s)) (σ (onePar X hX s) v))
        = fun u => σ (onePar X hX u) v := by
      funext u
      rw [← hsub u s, map_mul]
      rfl
    rw [e] at h2
    exact h2
  have hconst : ∀ v : V, ⟪T (ρ k w), σ k v⟫_ℂ = ⟪T w, v⟫_ℂ := by
    intro v
    have hf : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ⟪T (ρ (onePar X hX s) w), σ (onePar X hX s) v⟫_ℂ) 0 s := by
      intro s
      have h := (hY s).inner ℂ (hU v s)
      rw [inner_sum_left Kf hskew X hX, add_neg_cancel] at h
      exact h
    have h := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) 1 0
    simp only [hk1, onePar_zero, map_one] at h
    simpa using h
  have horth : ∀ v : V, ⟪T (ρ k w) - σ k (T w), σ k v⟫_ℂ = 0 := by
    intro v
    rw [inner_sub_left, hconst v, hK.1 k, sub_self]
  have hsurj : σ k (σ k⁻¹ (T (ρ k w) - σ k (T w))) = T (ρ k w) - σ k (T w) := by
    have : (σ k * σ k⁻¹) (T (ρ k w) - σ k (T w)) = T (ρ k w) - σ k (T w) := by
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact this
  have hz := horth (σ k⁻¹ (T (ρ k w) - σ k (T w)))
  rw [hsurj, inner_self_eq_zero] at hz
  exact sub_eq_zero.1 hz

end GlobalTheory.CompanionTheory.RealCount.IntegrateK
