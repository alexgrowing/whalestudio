import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_trOne (D : Formalism.BasicNotions.D7) : ∃ x : D.host.E, IsIntegral ℤ x ∧ x + D.host.conj x = 1 := by
  have hc := Formalism.BasicNotions.Examples₂.conj_bE (H := D.host)
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB (H := D.host), ?_⟩
  first
    | (rw [Formalism.BasicNotions.Examples₂.conj_half (H := D.host), hc]; ring)
    | (rw [map_div₀, map_add, map_one, hc, map_ofNat]; ring)

theorem trace_iE_eq_one (D : Formalism.BasicNotions.D7) (p : PlF D) (x : D.host.E) (hx1 : x + D.host.conj x = 1) :
    Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιE x) = 1 := by
  haveI := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep := by
    first
      | exact Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
      | exact Module.finite_of_finrank_eq_succ (D.s.atP p).rank
      | exact FiniteDimensional.of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hsum : (D.s.atP p).ιE x + (D.s.atP p).cj ((D.s.atP p).ιE x) = 1 := by
    rw [(D.s.atP p).cj_ιE, D.conjF_eq, ← map_add, hx1, map_one]
  have hinv : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).cj ((D.s.atP p).ιE x)) =
      Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιE x) := by
    first
      | exact Algebra.trace_eq_of_algEquiv (D.s.atP p).cj _
      | exact (Algebra.trace_eq_of_algEquiv (D.s.atP p).cj _).symm
  have hone : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep 1 = 2 := by
    have h := Algebra.trace_algebraMap (S := (D.s.atP p).Ep) (1 : (D.s.atP p).Fp)
    rw [map_one, (D.s.atP p).rank] at h
    rw [h]
    norm_num
  have h2 : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιE x + (D.s.atP p).cj ((D.s.atP p).ιE x)) =
      Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [hsum]
  rw [map_add, hinv, hone] at h2
  linear_combination h2 / 2

theorem norm_trace_le_of_psi {ℓ : ℕ} [Fact ℓ.Prime] {Fp Ep : Type} [Field Fp] [CommRing Ep] [Algebra Fp Ep]
    [Algebra ℚ_[ℓ] Fp] (ψ : AddChar Ep ℂ)
    (hψ : ∀ y : Ep, ∃ a : ℚ, (∃ n : ℕ, a.den = ℓ ^ n) ∧
      ‖(letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra;
        Algebra.trace ℚ_[ℓ] Ep y) - (a : ℚ_[ℓ])‖ ≤ 1 ∧
      ψ y = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)))
    (y : Ep) (h1 : ψ y = 1) :
    ‖(letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra; Algebra.trace ℚ_[ℓ] Ep y)‖ ≤ 1 := by
  obtain ⟨a, -, hle, hexp⟩ := hψ y
  rw [h1] at hexp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp.symm
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have ha : (a : ℂ) = ((n : ℚ) : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]
    push_cast
    ring
  have haq : a = (n : ℚ) := by exact_mod_cast ha
  have hna : ‖((a : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [haq]
    push_cast
    first
      | exact Padic.norm_int_le_one n
      | exact PadicInt.norm_le_one (n : ℤ_[ℓ])
      | simpa using (PadicInt.norm_le_one (n : ℤ_[ℓ]))
  have key : ∀ T : ℚ_[ℓ], ‖T - ((a : ℚ) : ℚ_[ℓ])‖ ≤ 1 → ‖T‖ ≤ 1 := by
    intro T hT
    calc ‖T‖ = ‖(T - ((a : ℚ) : ℚ_[ℓ])) + ((a : ℚ) : ℚ_[ℓ])‖ := by rw [sub_add_cancel]
      _ ≤ max ‖T - ((a : ℚ) : ℚ_[ℓ])‖ ‖((a : ℚ) : ℚ_[ℓ])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hT hna
  exact key _ hle

theorem trace_tower_theta {ℓ : ℕ} [Fact ℓ.Prime] {Fp Ep : Type} [Field Fp] [CommRing Ep] [Algebra Fp Ep]
    [Algebra ℚ_[ℓ] Fp] [FiniteDimensional ℚ_[ℓ] Fp] [Module.Free Fp Ep] [Module.Finite Fp Ep]
    (θ : Ep) (hθ : Algebra.trace Fp Ep θ = 1) (z : Fp) :
    (letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra;
      Algebra.trace ℚ_[ℓ] Ep (θ * algebraMap Fp Ep z)) = Algebra.trace ℚ_[ℓ] Fp z := by
  letI : Algebra ℚ_[ℓ] Ep := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[ℓ] Fp Ep := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Algebra.trace Fp Ep (θ * algebraMap Fp Ep z) = z := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, hθ, smul_eq_mul, mul_one]
  have h2 := Algebra.trace_trace (R := ℚ_[ℓ]) (S := Fp) (T := Ep) (θ * algebraMap Fp Ep z)
  rw [h1] at h2
  exact h2.symm

theorem trace_dual_lattice : TrDual := by
  intro D δ M hA p c hc
  have h := hA p
  simp only [Agree] at h
  obtain ⟨-, -, -, hO, hpsi, -⟩ := h
  obtain ⟨x, hxint, hx1⟩ := exists_trOne D
  have htr := trace_iE_eq_one D p x hx1
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).qlFin
  haveI := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep := by
    first
      | exact Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
      | exact Module.finite_of_finrank_eq_succ (D.s.atP p).rank
      | exact FiniteDimensional.of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have hθO : (D.s.atP p).ιE x ∈ (D.s.atP p).O := by
    rw [(D.s.atP p).O_def]
    exact (hxint.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  have hcO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
    rw [(D.s.atP p).O_def]
    have hi := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := ⟨c, hc⟩)
    first
      | exact hi
      | simpa [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] using hi
  have hyO : -((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c) ∈ (M p).L.O := by
    rw [hO]
    exact neg_mem (mul_mem hθO hcO)
  have h1 : (M p).L.psi0 (-((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c)) = 1 := by
    have h0 := ((M p).L.additive_character_dual_ring _).mpr hyO 1 (one_mem _)
    rwa [mul_one] at h0
  rw [hpsi] at h1
  have hAB : (D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (c * (δ p)⁻¹)
      = -(-((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c) *
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) := by
    rw [map_mul]
    ring
  have h2 : (D.s.atP p).psiE
      ((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (c * (δ p)⁻¹)) = 1 := by
    rw [hAB]
    exact h1
  have key := norm_trace_le_of_psi (D.s.atP p).psiE (D.s.atP p).psiE_def _ h2
  rw [trace_tower_theta _ htr] at key
  exact key

end PI.CntNotIntW
