import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.DlRescale

def mulN (N : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (N : ℚ)

theorem mulN_le (N : ℕ) (hN : 0 < N) (g g' : ℚ) : mulN N g ≤ mulN N g' ↔ g ≤ g' := by
  have : (0:ℚ) < N := by exact_mod_cast hN
  simp [mulN, mul_le_mul_iff_of_pos_left this]

theorem mulN_inj (N : ℕ) (hN : 0 < N) : Function.Injective (mulN N) := fun g g' h =>
  le_antisymm ((mulN_le N hN g g').1 h.le) ((mulN_le N hN g' g).1 h.ge)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def resc (N : ℕ) (hN : 0 < N) : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω :=
  HahnSeries.embDomainRingHom (mulN N) (mulN_inj N hN) (mulN_le N hN)

theorem resc_coeff (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) (r : ℚ) :
    (resc N hN ψ).coeff r = ψ.coeff (r / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : r = mulN N (r / N) := by simp [mulN]; field_simp
  conv_lhs => rw [e]
  simp only [resc, HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (f := ⟨⟨mulN N, mulN_inj N hN⟩, mulN_le N hN _ _⟩)

theorem forall_div (N : ℕ) (hN : 0 < N) (Q : ℚ → Prop) : (∀ r : ℚ, Q (r / N)) ↔ ∀ r, Q r := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun h r => ?_, fun h r => h _⟩
  have := h (N * r)
  rwa [mul_div_cancel_left₀ r hN'] at this

theorem theta_resc (N : ℕ) (hN : 0 < N) (s : ℚ) (ψ : HahnSeries ℚ Ω) :
    theta (s / N) (resc N hN ψ) = resc N hN (theta s ψ) := by
  ext r
  simp only [theta, resc_coeff]
  congr 2
  ring

theorem prim_resc (A : ValuationSubring Ω) (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) :
    Prim A (resc N hN ψ) ↔ Prim A ψ := by
  unfold Prim
  simp only [resc_coeff]
  rw [forall_div N hN (fun r => ψ.coeff r ∈ A)]
  constructor
  · rintro ⟨h1, r, h2, h3⟩; exact ⟨h1, r / N, h2, h3⟩
  · rintro ⟨h1, r, h2, h3⟩
    have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨h1, N * r, ?_⟩
    rw [mul_div_cancel_left₀ r hN']; exact ⟨h2, h3⟩

theorem eOm_zero (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

theorem exp_sl_diag (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) (hN : 0 < N) (u : X.K) :
    X.exp (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) u) = resc N hN (X.exp u) := by
  have hdet : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hN
  have e00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  rw [resc_coeff]
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) e10 u (r / N)
  rw [e00, e01, e11, mul_zero, zero_div, eOm_zero, one_mul, div_one, div_mul_cancel₀ r hN'] at h
  exact h

end GlobalTheory.DlRescale

end

open GlobalTheory.DlRescale in
theorem GlobalTheory.Glue.isDl_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  intro Ω _ _ _ ε X _ l _ A _ n N s f φ φ' hN hφ
  have hφ' : φ' = resc N hN φ := by ext r; rw [hφ, resc_coeff]
  subst hφ'
  have hexp := exp_sl_diag ε X N hN
  set g := toGQ !![(N : ℤ), 0; 0, 1]
  have key : ∀ a b : X.K, (∀ r, CgA A l n ((resc N hN φ * X.exp (X.sl g a) * X.exp (X.sl g b)).coeff r)
      ((theta (s / N) (X.exp (X.sl g a)) * X.exp (X.sl g b) - X.exp (X.sl g a) * theta (s / N) (X.exp (X.sl g b))).coeff r)) ↔
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r) := by
    intro a b
    simp only [hexp, theta_resc, ← map_mul, ← map_sub, resc_coeff]
    exact forall_div N hN (fun r => CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r))
  have hA : (∀ r, (resc N hN φ).coeff r ∈ A) ↔ ∀ r, φ.coeff r ∈ A := by
    simp only [resc_coeff]; exact forall_div N hN (fun r => φ.coeff r ∈ A)
  constructor
  · rintro ⟨h0, a, b, κ, hκ, hfb, pa, pb, hc⟩
    refine ⟨hA.2 h0, X.sl g a, X.sl g b, κ, hκ, ?_, ?_, ?_, (key a b).2 hc⟩
    · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
    · rw [hexp]; exact (prim_resc A N hN _).2 pa
    · rw [hexp]; exact (prim_resc A N hN _).2 pb
  · rintro ⟨h0, a', b', κ, hκ, hfb, pa, pb, hc⟩
    obtain ⟨a, rfl⟩ := (X.sl g).surjective a'
    obtain ⟨b, rfl⟩ := (X.sl g).surjective b'
    refine ⟨hA.1 h0, a, b, κ, hκ, ?_, ?_, ?_, (key a b).1 hc⟩
    · apply (X.sl g).injective
      rw [map_mul, map_mul, AlgEquiv.commutes]; exact hfb
    · rw [hexp] at pa; exact (prim_resc A N hN _).1 pa
    · rw [hexp] at pb; exact (prim_resc A N hN _).1 pb
