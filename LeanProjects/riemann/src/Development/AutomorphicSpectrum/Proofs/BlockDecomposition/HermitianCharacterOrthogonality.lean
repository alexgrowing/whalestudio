import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth

variable {R : Type} [CommRing R]

theorem red_add' (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j
  simp [red]

theorem red_neg' (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by
  ext i j
  simp [red]

theorem cT_add' (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j
  simp [cT]

theorem cT_neg' (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_single' (σ : R →+* R) {n : ℕ} (i j : Fin n) (c : R) :
    cT σ (Matrix.single i j c) = Matrix.single j i (σ c) := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_single, Matrix.transpose_single]

theorem trace_single_mul' {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]

theorem trace_red_mul (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by
  unfold PositivityTheory.PfSWUS.Loc.red
  rw [← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

theorem tsum_eq_zero_of_shift {G : Type} [AddCommGroup G] (H : Set G)
    (hadd : ∀ a b, a ∈ H → b ∈ H → a + b ∈ H) (hneg : ∀ a, a ∈ H → -a ∈ H)
    (f : G → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) (B₀ : G) (hB₀ : B₀ ∈ H) (h : f B₀ ≠ 1) :
    ∑' B : H, f B.1 = 0 := by
  let e : H ≃ H :=
    { toFun := fun B => ⟨B₀ + B.1, hadd _ _ hB₀ B.2⟩
      invFun := fun B => ⟨-B₀ + B.1, hadd _ _ (hneg _ hB₀) B.2⟩
      left_inv := fun B => Subtype.ext (by simp)
      right_inv := fun B => Subtype.ext (by simp) }
  have key : ∑' B : H, f B.1 = f B₀ * ∑' B : H, f B.1 := by
    calc ∑' B : H, f B.1 = ∑' B : H, f (e B).1 := (e.tsum_eq (fun B : H => f B.1)).symm
      _ = ∑' B : H, f B₀ * f B.1 := tsum_congr fun B => by
          show f (B₀ + B.1) = _
          exact hf _ _
      _ = f B₀ * ∑' B : H, f B.1 := tsum_mul_left
  have hzero : (f B₀ - 1) * ∑' B : H, f B.1 = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'

theorem hermMod_add {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  have hb'' : PositivityTheory.PfSWUS.Loc.cT σ b' = b' := hb'
  refine ⟨a' + b', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_add' _ _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (a' + b') = a' + b'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', ha'', hb'']

theorem hermMod_neg {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k) :
    -a ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  refine ⟨-a', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_neg' _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (-a') = -a'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_neg', ha'']

theorem red_eq_zero_of_trivial {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by
  have hσσ : ∀ a, σ (σ a) = a := hR.1
  ext i j
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.zero_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply GlobalTheory.CompanionTheory.SiegLoc.trace_nondeg hR hψ k (y i j)
  intro t
  have hyji : σ (y i j) = y j i := by
    have hentry := congrFun (congrFun hy j) i
    simpa [PositivityTheory.PfSWUS.Loc.cT] using hentry
  have hb : PositivityTheory.PfSWUS.Loc.cT σ (Matrix.single j i t + Matrix.single i j (σ t)) =
      Matrix.single j i t + Matrix.single i j (σ t) := by
    rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single',
      hσσ, add_comm]
  have htr := h _ hb
  rw [Matrix.add_mul, Matrix.trace_add, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul',
    GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul'] at htr
  rw [map_mul σ, hyji]
  exact htr

theorem orth_hermMod (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)]
    (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (hψ : IsLevelChars σ ϖ ψ) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) =
        (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · subst h0
    simp only [Matrix.mul_zero, Matrix.trace_zero, AddChar.map_zero_eq_one]
    rw [tsum_const, nsmul_eq_mul, mul_one]
  · have hY' := hY
    unfold PositivityTheory.PfSWUS.Loc.hermMod at hY'
    obtain ⟨y, hy, rfl⟩ := hY'
    by_contra hsum
    apply hne
    apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial hR hψ n k y hy
    intro b hb
    rw [← GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul]
    by_contra hb1
    exact hsum (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift _
      (fun a₁ a₂ h₁ h₂ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add a₁ a₂ h₁ h₂)
      (fun a₁ h₁ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg a₁ h₁)
      (fun B => ψ k (Matrix.trace (B * PositivityTheory.PfSWUS.Loc.red ϖ k y)))
      (fun a₁ a₂ => by simp only [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul])
      (PositivityTheory.PfSWUS.Loc.red ϖ k b) ⟨b, hb, rfl⟩ hb1)

end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
