import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.IsMonomialConjTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

section Gen

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem frame_inv {s : Matrix n n ℂ} {x : Matrix m m ℂ} {F : Matrix n m ℂ}
    (hs : IsUnit s.det) (hx : IsUnit x.det) (h : s * F = F * x) : s⁻¹ * F = F * x⁻¹ := by
  calc s⁻¹ * F = s⁻¹ * (F * x * x⁻¹) := by rw [Matrix.mul_assoc F, mul_nonsing_inv x hx, Matrix.mul_one]
    _ = s⁻¹ * (s * F) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
    _ = F * x⁻¹ := by rw [← Matrix.mul_assoc s⁻¹, nonsing_inv_mul s hs, Matrix.one_mul]

end Gen

variable {k r : ℕ}

theorem uw_frame {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h * Ff k r z = Ff k r z := by
  have hfix : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with ha
    · exact (hh.2.1 ⟨b.val, ha⟩).1
    · exact hh.2.2
  have := mul_of_col z h 1 (fun b => by
    rw [hfix b]
    simp [Matrix.one_apply])
  rwa [Matrix.mul_one] at this

theorem pair_lt {m : ℕ} {P b u' : Matrix (Fin m) (Fin m) ℂ} (hb : b ∈ UTset m) (h : bᴴ * P * u' = P)
    (hP : IsUnit P.det) : P * u' * P⁻¹ ∈ LTset m := by
  have iL := lt_inv (ut_conjTranspose hb)
  have e : P * u' * P⁻¹ = (bᴴ)⁻¹ := by
    calc P * u' * P⁻¹ = (bᴴ)⁻¹ * (bᴴ * P * u') * P⁻¹ := by
          rw [show (bᴴ)⁻¹ * (bᴴ * P * u') = ((bᴴ)⁻¹ * bᴴ) * P * u' by simp only [Matrix.mul_assoc], iL.2.1,
            Matrix.one_mul]
      _ = (bᴴ)⁻¹ := by rw [h, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]
  rw [e]; exact iL.2.2

theorem pair_of_lt {m : ℕ} {P a : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det) (ha : P * a * P⁻¹ ∈ LTset m) :
    ∃ b, b ∈ UTset m ∧ bᴴ * P * a = P := by
  have iA := lt_inv ha
  refine ⟨((P * a * P⁻¹)⁻¹)ᴴ, lt_conjTranspose iA.2.2, ?_⟩
  rw [conjTranspose_conjTranspose]
  calc (P * a * P⁻¹)⁻¹ * P * a = (P * a * P⁻¹)⁻¹ * (P * a * P⁻¹) * P := by
        simp only [Matrix.mul_assoc]; rw [nonsing_inv_mul P hP, Matrix.mul_one]
    _ = P := by rw [iA.2.1, Matrix.one_mul]

theorem mirrorDecomp_of (hC : CurvatureConditionOneClauseThree) (hT : TauMem) (hLS : LowSplit) : MirrorDecomp := by
  intro k r z z' γ hS hP hmono s' hs'
  have hz' : StdZ k r z' := hS.2.2
  have hγ : γ ∈ B.GV k r := hP.1
  have hPd : IsUnit (Zhat k r z z' γ).det := isUnit_iff_ne_zero.mpr (det_Zhat_ne z z' hS γ hP)
  obtain ⟨hbij, -, hinj⟩ := hC k r z z' γ hS hP

  have hRS : ∀ ρ ∈ Rst k r z z' γ, γ⁻¹ * ρ * γ ∈ Sset k r z' := by
    intro ρ hρ
    obtain ⟨s0, hs0, he⟩ := hρ.1.2
    rw [(rho_conj γ hγ ρ s0 he).1]; exact hs0
  have hRL : ∀ ρ ∈ Rst k r z z' γ,
      Zhat k r z z' γ * uMap k r z' (γ⁻¹ * ρ * γ) * (Zhat k r z z' γ)⁻¹ ∈ LTset (r + 1) := by
    intro ρ hρ
    obtain ⟨hb, -, he⟩ := hbij.1 hρ
    exact pair_lt hb he hPd

  have hSgF : ∀ σ ∈ Sg' k r z z' γ, ∃ v, v ∈ UTset (r + 1) ∧
      Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧ σ * Ff k r z' = Ff k r z' * v := by
    rintro σ ⟨n0, hn0, v, hv, hvP, h, hh, rfl⟩
    obtain ⟨-, hn0F, -⟩ := Sset_frame z' hz' n0 ⟨1, ⟨by show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r; simp,
      fun a => ⟨by simp, by simp⟩, by simp⟩, n0, hn0.1, (Matrix.one_mul _).symm⟩
    rw [hn0.2, Matrix.mul_one] at hn0F
    have hτ := hT k r z' hz' v hv
    have hτF : tauM k r z' v * Ff k r z' = Ff k r z' * v := mul_of_col z' _ v hτ.2.1
    refine ⟨v, hv, hvP, ?_⟩
    calc n0 * tauM k r z' v * h * Ff k r z' = n0 * (tauM k r z' v * (h * Ff k r z')) := by
          simp only [Matrix.mul_assoc]
      _ = Ff k r z' * v := by rw [uw_frame hh, hτF, ← Matrix.mul_assoc, hn0F]

  have hdata : ∀ ρ σ, ρ ∈ Rst k r z z' γ → σ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ * γ * σ →
      ∃ v, Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧
        uMap k r z' s' = uMap k r z' (γ⁻¹ * ρ * γ) * v := by
    intro ρ σ hρ hσ he
    obtain ⟨v, -, hvP, hσF⟩ := hSgF σ hσ
    obtain ⟨-, hxF, -⟩ := Sset_frame z' hz' _ (hRS ρ hρ)
    refine ⟨v, hvP, uMap_eq z' hz' s' _ ?_⟩
    rw [he]
    calc γ⁻¹ * ρ * γ * σ * Ff k r z' = (γ⁻¹ * ρ * γ) * (σ * Ff k r z') := by rw [Matrix.mul_assoc]
      _ = Ff k r z' * (uMap k r z' (γ⁻¹ * ρ * γ) * v) := by
          rw [hσF, ← Matrix.mul_assoc, hxF, Matrix.mul_assoc]

  have huniq : ∀ ρ₁ σ₁ ρ₂ σ₂, ρ₁ ∈ Rst k r z z' γ → σ₁ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ₁ * γ * σ₁ →
      ρ₂ ∈ Rst k r z z' γ → σ₂ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ₂ * γ * σ₂ → ρ₁ = ρ₂ ∧ σ₁ = σ₂ := by
    intro ρ₁ σ₁ ρ₂ σ₂ h1 h1' e1 h2 h2' e2
    obtain ⟨v₁, hv₁, hu₁⟩ := hdata ρ₁ σ₁ h1 h1' e1
    obtain ⟨v₂, hv₂, hu₂⟩ := hdata ρ₂ σ₂ h2 h2' e2
    have ha := split_unique hPd (hRL ρ₁ h1) (hRL ρ₂ h2) hv₁ hv₂ (hu₁.symm.trans hu₂)
    have hρ : ρ₁ = ρ₂ := hinj h1 h2 ha
    subst hρ
    refine ⟨rfl, ?_⟩
    have hx : IsUnit (γ⁻¹ * ρ₁ * γ).det := isUnit_det_of_mem_GV (Sset_frame z' hz' _ (hRS ρ₁ h1)).1
    have e3 := e1.symm.trans e2
    calc σ₁ = (γ⁻¹ * ρ₁ * γ)⁻¹ * (γ⁻¹ * ρ₁ * γ * σ₁) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hx, Matrix.one_mul]
      _ = (γ⁻¹ * ρ₁ * γ)⁻¹ * (γ⁻¹ * ρ₁ * γ * σ₂) := by rw [e3]
      _ = σ₂ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hx, Matrix.one_mul]

  obtain ⟨h, hh, m, hm, hsm⟩ := hs'
  obtain ⟨-, hs'F, huUT⟩ := Sset_frame z' hz' s' ⟨h, hh, m, hm, hsm⟩
  obtain ⟨a, v, haU, hvU, haL, hvP, hsplit⟩ := split_exists hLS hmono hPd huUT
  obtain ⟨b, hbU, hbP⟩ := pair_of_lt hPd haL
  have hmem : ((b, a) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) ∈
      {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
        p.1 ∈ UTset (r + 1) ∧ p.2 ∈ UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨hbU, haU, hbP⟩
  obtain ⟨ρ, hρ, hρe⟩ := hbij.2.2 hmem
  have hxa : uMap k r z' (γ⁻¹ * ρ * γ) = a := (Prod.ext_iff.mp hρe).2
  obtain ⟨x, hxdef⟩ : ∃ x, x = γ⁻¹ * ρ * γ := ⟨_, rfl⟩
  have hxS : x ∈ Sset k r z' := by rw [hxdef]; exact hRS ρ hρ
  obtain ⟨h₂, hh₂, m₂, hm₂, hx2⟩ := id hxS
  obtain ⟨hxG, hxF, -⟩ := Sset_frame z' hz' x hxS
  rw [hxdef, hxa, ← hxdef] at hxF
  have hxU := isUnit_det_of_mem_GV hxG
  have iA := ut_inv haU
  have hxiF : x⁻¹ * Ff k r z' = Ff k r z' * a⁻¹ :=
    frame_inv hxU (by rw [det_ut haU]; exact isUnit_one) hxF
  obtain ⟨h₃, hh3def⟩ : ∃ h₃, h₃ = h₂⁻¹ * h := ⟨_, rfl⟩
  have hh₃ : h₃ ∈ UWset k r z' := by rw [hh3def]; exact uw_mul (uw_inv hh₂) hh
  have ih₃ := uh_inv hh₃.1
  have hcm : h₃ * m * h₃⁻¹ ∈ Nset k r := by
    have := conj_n (uw_inv hh₃) hm
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GV hh₃.1)] at this
  obtain ⟨n, hndef⟩ : ∃ n, n = m₂⁻¹ * (h₃ * m * h₃⁻¹) := ⟨_, rfl⟩
  have hn : n ∈ Nset k r := by rw [hndef]; exact n_mul (n_inv hm₂) hcm
  have hσ_eq : x⁻¹ * s' = n * h₃ := by
    have e1 : x⁻¹ * s' = m₂⁻¹ * (h₃ * m) := by
      rw [hx2, hsm, Matrix.mul_inv_rev, hh3def]; simp only [Matrix.mul_assoc]
    rw [e1, hndef]
    simp only [Matrix.mul_assoc]
    rw [ih₃.2.1, Matrix.mul_one]
  have hσF : x⁻¹ * s' * Ff k r z' = Ff k r z' * v := by
    rw [Matrix.mul_assoc, hs'F, hsplit, ← Matrix.mul_assoc, hxiF, Matrix.mul_assoc, ← Matrix.mul_assoc a⁻¹,
      iA.2.1, Matrix.one_mul]
  have hnF : n * Ff k r z' = Ff k r z' * v := by
    calc n * Ff k r z' = n * (h₃ * Ff k r z') := by rw [uw_frame hh₃]
      _ = x⁻¹ * s' * Ff k r z' := by rw [← Matrix.mul_assoc, hσ_eq]
      _ = Ff k r z' * v := hσF
  have hτ := hT k r z' hz' v hvU
  have hτF : tauM k r z' v * Ff k r z' = Ff k r z' * v := mul_of_col z' _ v hτ.2.1
  have iτ := uh_inv hτ.1.1
  have hvd : IsUnit v.det := by rw [det_ut hvU]; exact isUnit_one
  have hτiF : (tauM k r z' v)⁻¹ * Ff k r z' = Ff k r z' * v⁻¹ :=
    frame_inv (isUnit_det_of_mem_GV hτ.1.1) hvd hτF
  have hn0 : n * (tauM k r z' v)⁻¹ ∈ Nset k r := n_mul hn (n_inv hτ.1)
  have hn0F : n * (tauM k r z' v)⁻¹ * Ff k r z' = Ff k r z' * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
    rw [Matrix.mul_assoc, hτiF, ← Matrix.mul_assoc, hnF, Matrix.mul_assoc, (ut_inv hvU).1]
  have hn0u : uMap k r z' (n * (tauM k r z' v)⁻¹) = 1 := uMap_eq z' hz' _ _ hn0F
  have hσmem : x⁻¹ * s' ∈ Sg' k r z z' γ := by
    refine ⟨n * (tauM k r z' v)⁻¹, ⟨hn0, hn0u⟩, v, hvU, hvP, h₃, hh₃, ?_⟩
    rw [hσ_eq, Matrix.mul_assoc n, iτ.2.1, Matrix.mul_one]
  have heq : s' = γ⁻¹ * ρ * γ * (x⁻¹ * s') := by
    rw [← hxdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hxU, Matrix.one_mul]
  refine ⟨(ρ, x⁻¹ * s'), ⟨hρ, hσmem, heq⟩, ?_⟩
  rintro ⟨ρ', σ'⟩ ⟨h1, h2, h3⟩
  obtain ⟨e1, e2⟩ := huniq ρ' σ' ρ _ h1 h2 h3 hρ hσmem heq
  exact Prod.ext e1 e2

end PI.MirrorSection₂
