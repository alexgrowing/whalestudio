import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F κ) in

abbrev V : Type := κ → mixedEmbedding.mixedSpace F

variable (F κ) in

abbrev Pt : Type := (κ → AF F) × (κ → AF F)

def inf (a : mixedEmbedding.mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def emb (w : V F κ × V F κ) : Pt F κ := (fun i => inf (w.1 i), fun i => inf (w.2 i))

def IntF (a : AF F) : Prop := a.1 = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F

def IntP (w : Pt F κ) : Prop := (∀ i, IntF (w.1 i)) ∧ ∀ i, IntF (w.2 i)

def IsHaar (μ : @Measure (κ → AF F) (borel _)) : Prop := @Measure.IsAddHaarMeasure _ _ _ (borel _) μ

def nsq (μ : @Measure (κ → AF F) (borel _)) (Φ : (κ → AF F) → ℂ) : ℝ≥0∞ := ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ

structure Impl (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : Pt F κ →ₗ[AF F] Pt F κ) : Prop where
  pres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ
  impl : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ (s w) Φ) = schr ψ w (T Φ)
  unit : ∀ μ, IsHaar μ → ∀ Φ ∈ schA F κ, nsq μ (T Φ) = nsq μ Φ

structure Bd (s : Pt F κ →ₗ[AF F] Pt F κ) (d : ℕ) (c : ℝ) : Prop where
  fin : ∀ w, IntP w → IntP ((d : AF F) • s w)
  inf : ∀ w : V F κ × V F κ, ∃ w', s (emb w) = emb w' ∧ ‖w'‖ ≤ c * ‖w‖

def dR (ψ : AddChar (AF F) ℂ) (w : V F κ × V F κ) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => deriv (fun t : ℝ => schr ψ (emb (t • w)) Φ x) 0

def word (ψ : AddChar (AF F) ℂ) (l : List (V F κ × V F κ)) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := l.foldr (dR ψ) Φ

def Lev (m : ℕ) (Θ : (κ → AF F) → ℂ) : Prop := ∀ u : κ → AF F, (∀ i, IntF (u i)) → ∀ x, Θ (x + (m : AF F) • u) = Θ x

section Pair

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def sOf (M : Model σ X W) (g : UA σ X.J) (h : UA σ W.J) : Pt F (Fin n × Fin d) →ₗ[AF F] Pt F (Fin n × Fin d) where
  toFun w := M.co.e (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ)
  map_add' a b := by rw [map_add, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c a := by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]; rfl

theorem impl_sOf {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil B.ψ χX χW om)
    (g : UA σ X.J) (h : UA σ W.J) : Impl B.ψ (om (g, h)) (sOf M g h) := by
  have hs := IsUWeilPair.isUSplitting hw
  refine ⟨hs.pres _, fun w Φ hΦ => ?_, fun μ hμ Φ hΦ => hs.unit μ hμ _ Φ hΦ⟩
  have := hs.impl (g, h) (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) Φ hΦ
  have e : actAB (cA σ) (g, h) (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) = M.co.e.symm w := by
    change mat g * (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) * (mat h)ᵀ = _
    have e1 : mat g * mat g⁻¹ = 1 := congrArg mat (mul_inv_cancel g)
    have e2 : mat h * mat h⁻¹ = 1 := congrArg mat (mul_inv_cancel h)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2,
      Matrix.transpose_one, Matrix.mul_one]
  rw [e] at this
  simp only [Darboux.rho, LinearEquiv.apply_symm_apply] at this
  exact this

end Pair

def HtBd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n)
    (W : Spc F E d) (M : Model σ X W), ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ∧
      Bd (sOf M g h) m (C * ((ht g : ℝ) * ht h))

def FinInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ Φ ∈ schA F κ,
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ T s d c, Impl ψ T s → Bd s d c → ∀ w, IntP w → schr ψ (((m₀ * d : ℕ) : AF F) • w) (T Φ) = T Φ

def DerivOK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ w : V F κ × V F κ,
    ∀ Φ ∈ schA F κ, dR ψ w Φ ∈ schA F κ ∧ (∀ x, HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (dR ψ w Φ x) 0) ∧
      ∀ m, Lev m Φ → Lev m (dR ψ w Φ)

def Sob : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ μ, IsHaar μ ∧ ∃ (S : List (List (V F κ × V F κ))) (C : ℝ≥0) (k : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ Θ ∈ schA F κ, Lev m Θ →
      ∀ x, ‖Θ x‖ₑ ^ 2 ≤ C * (m : ℝ≥0∞) ^ k * (S.map fun l => nsq μ (word ψ l Θ)).sum

def TrBd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℝ, 0 ≤ c ∧ ∀ x : V F κ, ∃ b : V F κ, ‖b‖ ≤ 1 ∧
    ‖x‖ ≤ c * |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)|

end PositivityTheory.ThKF0.Grow
