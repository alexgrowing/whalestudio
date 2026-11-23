import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem cT_cT {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {a b : Type} (A : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ A) = A := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_add (σ : L →+* L) {a b : Type} (A B : Matrix a b L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_zero (σ : L →+* L) {a b : Type} : Formalism.UG.cT σ (0 : Matrix a b L) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_herm {σ : L →+* L} {a : ℕ} {J : Matrix (Fin a) (Fin a) L} (h : ∀ i j, σ (J i j) = J j i) :
    Formalism.UG.cT σ J = J := by
  ext i j; simp [Formalism.UG.cT, h]

theorem inv_mul_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem mul_inv_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    (J : Matrix (Fin a) (Fin a) L) * (((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem cT_inv_herm {σ : L →+* L} {a : ℕ} (J : GL (Fin a) L) (h : Formalism.UG.cT σ (J : Matrix (Fin a) (Fin a) L) = J) :
    Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (J⁻¹ : GL (Fin a) L) := by
  have h1 : Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (J : Matrix (Fin a) (Fin a) L) = 1 := by
    conv_lhs => rw [← h]
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc _ = Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) *
        ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) := by rw [Units.mul_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem trace_cT (σ : L →+* L) {a : ℕ} (A : Matrix (Fin a) (Fin a) L) :
    σ (Matrix.trace A) = Matrix.trace (Formalism.UG.cT σ A) := by
  simp [Formalism.UG.cT, Matrix.trace, map_sum]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X : Matrix (Fin n) (Fin n') L) :
    Matrix (Fin n') (Fin n) L :=
  ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ X * (JS : Matrix (Fin n) (Fin n) L)

theorem adj_add (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X Y : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT (X + Y) = adj σ JS JT X + adj σ JS JT Y := by
  simp [adj, cT_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_zero (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) :
    adj σ JS JT (0 : Matrix (Fin n) (Fin n') L) = 0 := by
  simp [adj, cT_zero]

theorem adj_pre {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (x : Matrix (Fin n') (Fin n) L) :
    adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) = x := by
  simp only [adj, cT_cT hσ, Matrix.mul_assoc, inv_mul_cl, Units.inv_mul, Matrix.mul_one]

theorem locH_adj {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {δ : L} (hδ : σ δ = -δ) {n n' : ℕ} (JS : GL (Fin n) L)
    (JT : GL (Fin n') L) (hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS)
    (hTi : Formalism.UG.cT σ ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = (JT⁻¹ : GL (Fin n') L))
    (X Y : Matrix (Fin n) (Fin n') L) :
    σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) = locH σ (-δ) JT JS X Y := by
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  simp only [locH, hc, adj, Formalism.UG.cT_mul, cT_cT hσ, hS, hTi, Matrix.mul_assoc, inv_mul_cl, map_mul, hδ, trace_cT]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem adj_norm (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (h : GL (Fin n) L) (g : GL (Fin n') L)
    (hh : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (h : Matrix (Fin n) (Fin n) L) = JS)
    (hg : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) *
      ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = JT)
    (X : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT ((h : Matrix (Fin n) (Fin n) L) * X * ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) =
      (g : Matrix (Fin n') (Fin n') L) * adj σ JS JT X * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  have e2 : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) =
      (JS : Matrix (Fin n) (Fin n) L) * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    conv_rhs => rw [← hh]
    rw [Matrix.mul_assoc _ (h : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.mul_one]
  have e1 : ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) =
      (g : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    have e3 : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) =
        (JT : Matrix (Fin n') (Fin n') L) * (g : Matrix (Fin n') (Fin n') L) := by
      conv_rhs => rw [← hg]
      rw [Matrix.mul_assoc _ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L), Units.inv_mul, Matrix.mul_one]
    calc _ = ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          ((JT : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L))) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc (Formalism.UG.cT σ _), e3, Matrix.mul_assoc, inv_mul_cl]
  unfold adj
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) *
        Formalism.UG.cT σ X * (Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e1, e2]; simp only [Matrix.mul_assoc]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : A ∈ HoweDuality.intMat L a b) (hB : B ∈ HoweDuality.intMat L b c) : A * B ∈ HoweDuality.intMat L a c := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem intMat_cT {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : A ∈ HoweDuality.intMat L a b) : Formalism.UG.cT σ A ∈ HoweDuality.intMat L b a := fun i j => by
  have h := hA j i
  simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at h ⊢
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hv]
  exact h

theorem glint_int {a : ℕ} {J : GL (Fin a) L} (h : J ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    (J : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a ∧
      ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp [Formalism.UG.bc]
  · rw [← map_inv]; simp [Formalism.UG.bc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

theorem locPair_swap : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have hσ : ∀ x, σ (σ x) = x := hp.unr.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hp.unr.2.1
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := cT_herm hp.hermS
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := cT_herm hp.hermT
  have hTi := cT_inv_herm JT hT
  obtain ⟨hS1, hS2⟩ := glint_int hp.intS
  obtain ⟨hT1, hT2⟩ := glint_int hp.intT
  have hai : ∀ X : Matrix (Fin n) (Fin n') L, X ∈ HoweDuality.intMat L n n' → adj σ JS JT X ∈ HoweDuality.intMat L n' n :=
    fun X hX => intMat_mul (intMat_mul hT2 (intMat_cT hv hX)) hS1
  have hprei : ∀ x : Matrix (Fin n') (Fin n) L, x ∈ HoweDuality.intMat L n' n →
      Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∈ HoweDuality.intMat L n n' :=
    fun x hx => intMat_cT hv (intMat_mul (intMat_mul hT1 hx) hS2)
  have hvac : ∀ s, LocVac ρ s → LocVac (fun X => ρ (adj σ JS JT X)) s := fun s hs u hu => hs _ (hai u hu)
  have hvac' : ∀ s, LocVac (fun X => ρ (adj σ JS JT X)) s → LocVac ρ s := fun s hs u hu => by
    have h1 := hs _ (hprei u hu)
    simp only [adj_pre hσ] at h1
    exact h1
  have hrange : ∀ s : M, Set.range (fun x => ρ x s) ⊆ Set.range (fun X => ρ (adj σ JS JT X) s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), by simp only [adj_pre hσ]⟩
  refine ⟨?_, hvac, fun s hs => ?_⟩
  · refine ⟨hp.unr, hp.odd, hp.intT, hp.intS, hp.hermT, hp.hermS,
      ⟨by rw [Valuation.map_neg]; exact hp.delta.1, by rw [map_neg, hp.delta.2]⟩, hp.psi_int, hp.psi_ne, ?_, ?_, ?_, ?_, ?_⟩
    · show ρ (adj σ JS JT 0) = 1
      rw [adj_zero]; exact hp.rho_zero
    · intro X Y
      show ρ (adj σ JS JT X) * ρ (adj σ JS JT Y) = _ • ρ (adj σ JS JT (X + Y))
      have hb := locH_adj hσ hp.delta.2 JS JT hS hTi X Y
      have ha : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) = σ (locH σ (-δ) JT JS X Y) := by rw [← hb, hσ]
      have key : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) + σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) =
          locH σ (-δ) JT JS X Y + σ (locH σ (-δ) JT JS X Y) := by
        rw [hb]; linear_combination ha
      rw [hp.rho_mul, adj_add, key]
    · rw [eq_top_iff, ← hp.span]
      apply Submodule.span_mono
      rintro w ⟨x, s, hs, rfl⟩
      refine ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), s, hvac s hs, ?_⟩
      show ρ x s = ρ (adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) s
      rw [adj_pre hσ]
    · intro g h x
      show ω (h, g) * ρ (adj σ JS JT _) = ρ (adj σ JS JT _) * ω (h, g)
      rw [hp.norm h g, adj_norm σ JS JT (h : GL (Fin n) L) (g : GL (Fin n') L) h.2 ((Formalism.UG.UJ σ _).inv_mem g.2)]
    · intro g h hg hh s hs
      exact hp.fix h g hh hg s (hvac' s hs)
  · rw [eq_top_iff, ← hs]
    exact Submodule.span_mono (hrange s)

end GlobalTheory.Hk3.HoweSwap
