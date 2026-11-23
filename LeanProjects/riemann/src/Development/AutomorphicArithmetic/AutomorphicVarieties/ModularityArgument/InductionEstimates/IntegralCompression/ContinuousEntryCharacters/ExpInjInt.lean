import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem scal_comm (t : ℝ) (a : GL (Fin 2) ℂ) :
    Commute ((kC (tC t t) : GL2C) : GL (Fin 2) ℂ) a := by
  apply Units.ext
  show ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ) * (a : Matrix (Fin 2) (Fin 2) ℂ) =
    (a : Matrix (Fin 2) (Fin 2) ℂ) * ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ)
  have h : ((tC t t : U2) : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.exp (t * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [coe_tC]; ext r s; fin_cases r <;> fin_cases s <;> simp
  rw [h]; simp

private theorem T_cont (n : ℕ) (q : ℤ) : Continuous (T n q) :=
  continuous_const.mul (KT.continuous_conj_psi n q n)

private theorem T_shift (n : ℕ) (q : ℤ) (t : ℝ) (m : U2) :
    T n q ((tC t t)⁻¹ * m) = Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) * T n q m := by
  have hinv : (tC t t)⁻¹ = tC (-t) (-t) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    rw [Matrix.UnitaryGroup.mul_val, coe_tC, coe_tC]
    ext r s; fin_cases r <;> fin_cases s <;> simp [← Complex.exp_add]
  rw [hinv]
  simp only [T]
  rw [KT.psi_tC_mul n q le_rfl, map_mul, ← Complex.exp_conj]
  have h : conj (Complex.I * ((((n : ℝ) + q) * (-t) + ((n : ℝ) - n + q) * (-t) : ℝ) : ℂ)) =
      Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h]; ring

private theorem exp_inj_int {a b : ℤ} (h : ∀ t : ℝ, Complex.exp (Complex.I * ((a : ℂ) * t)) =
    Complex.exp (Complex.I * ((b : ℂ) * t))) : a = b := by
  by_contra hab
  have hne : ((a : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hne' : ((a : ℝ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have h1 := h (Real.pi / ((a : ℝ) - b))
  have h2 : Complex.exp (Complex.I * ((a : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) -
      Complex.I * ((b : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ))) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : Complex.I * ((a : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) -
      Complex.I * ((b : ℂ) * ((Real.pi / ((a : ℝ) - b) : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (R : UnitaryRep G H) (u : U2 → G)

private theorem eig_abs (hu : ∀ a b, u (a * b) = u a * u b) (hc : Continuous u) (n : ℕ) (q : ℤ) (t : ℝ) (v : H) :
    R (u (tC t t)) (∫ m, T n q m • R (u m) v ∂μK) =
      Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • ∫ m, T n q m • R (u m) v ∂μK := by
  have hint : Integrable (fun m => T n q m • R (u m) v) μK :=
    KT.integrable_of_continuous ((T_cont n q).smul ((R.continuous_orbit v).comp hc))
  rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← integral_smul,
    ← integral_mul_left_K (fun m => Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) •
      T n q m • R (u m) v) (tC t t)]
  congr 1
  funext m
  have h := T_shift n q t (tC t t * m)
  rw [inv_mul_cancel_left] at h
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← hu, smul_smul, ← h]

private theorem occ_abs (hu : ∀ a b, u (a * b) = u a * u b) (hc : Continuous u)
    (hz : ∀ t g, Commute (u (tC t t)) g) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, R g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, R g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    {n n' : ℕ} {q q' : ℤ} {w w' : H} (hw : w ∈ τ) (hw' : w' ∈ τ) (hw0 : w ≠ 0) (hw0' : w' ≠ 0)
    (e : ∀ t : ℝ, R (u (tC t t)) w = Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • w)
    (e' : ∀ t : ℝ, R (u (tC t t)) w' = Complex.exp (Complex.I * ((((n' : ℤ) + 2 * q' : ℤ) : ℂ) * t)) • w') :
    (n' : ℤ) + 2 * q' = n + 2 * q := by
  let c : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t))
  let ρ : Submodule ℂ H :=
    { carrier := {x | x ∈ τ ∧ ∀ t : ℝ, R (u (tC t t)) x = c t • x}
      add_mem' := fun {x y} hx hy => ⟨τ.add_mem hx.1 hy.1, fun t => by rw [map_add, hx.2, hy.2, smul_add]⟩
      zero_mem' := ⟨τ.zero_mem, fun t => by simp⟩
      smul_mem' := fun a x hx => ⟨τ.smul_mem a hx.1, fun t => by rw [map_smul, hx.2, smul_comm]⟩ }
  have hρτ : ρ ≤ τ := fun x hx => hx.1
  have hρcl : IsClosed (ρ : Set H) := by
    have e₀ : (ρ : Set H) = (τ : Set H) ∩ ⋂ t : ℝ, {x | R (u (tC t t)) x = c t • x} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [e₀]
    exact hcl.inter (isClosed_iInter fun t =>
      isClosed_eq (ContinuousLinearMap.continuous _) (continuous_const_smul _))
  have hρinv : ∀ g, ∀ x ∈ ρ, R g x ∈ ρ := by
    intro g x hx
    refine ⟨hinv g x hx.1, fun t => ?_⟩
    rw [← UnitaryRep.map_mul_apply, (hz t g).eq, UnitaryRep.map_mul_apply, hx.2, map_smul]
  have hwρ : w ∈ ρ := ⟨hw, e⟩
  rcases hirr ρ hρτ hρcl hρinv with h0 | h1
  · rw [h0] at hwρ
    exact absurd ((Submodule.mem_bot ℂ).1 hwρ) hw0
  · have hwρ' : w' ∈ ρ := h1 ▸ hw'
    refine exp_inj_int fun t => ?_
    have e1 := hwρ'.2 t
    rw [e' t] at e1
    exact smul_left_injective ℂ hw0' e1

end Abstract

section

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι] (C : Co K ι)

private theorem un_central (i : ι) (t : ℝ) (g : G1 K 2) : Commute (C.un i (tC t t)) g := by
  obtain ⟨-, -, hun, -, hmul, -, -, hdec, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  obtain ⟨a, h, rfl, hh⟩ := hdec i g
  rw [hun]
  refine Commute.mul_right ?_ (hh _).symm
  show _ * _ = _ * _
  rw [← hmul, ← hmul, (scal_comm t a).eq]

private theorem un_mul (i : ι) (a b : U2) : C.un i (a * b) = C.un i a * C.un i b := by
  obtain ⟨-, -, hun, -, hmul, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  rw [hun, hun, hun, map_mul]
  exact hmul i _ _

private theorem un_cont (i : ι) : Continuous (C.un i) := by
  obtain ⟨-, -, hun, hc, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws K ι C
  have h : C.un i = fun m => C.gl i (kC m : GL2C) := funext (hun i)
  rw [h]
  exact (hc i).comp (continuous_subtype_val.comp continuous_kC)

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minEx :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ i, ∃ n q, C.MinAt μ τ i n q := by
  intro K _ _ _ ι _ C μ _ τ hτ i
  obtain ⟨hP, -, -, hall⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.piLaws K ι C μ
  have hmem : ∀ (n : ℕ) (q : ℤ) (v : LL μ), v ∈ τ → C.Pi μ i n q v ∈ τ := by
    intro n q v hv
    obtain ⟨P, h1, -, -, -, -, h2⟩ := hP i n q
    rw [← h1]
    exact h2 τ hτ v hv
  have heig : ∀ (n : ℕ) (q : ℤ) (v : LL μ) (t : ℝ), rightRegularRep (Gam K 2) μ (C.un i (tC t t)) (C.Pi μ i n q v) =
      Complex.exp (Complex.I * ((((n : ℤ) + 2 * q : ℤ) : ℂ) * t)) • C.Pi μ i n q v := fun n q v t =>
    eig_abs (rightRegularRep (Gam K 2) μ) (C.un i) (un_mul C i) (un_cont C i) n q t v
  have hex : ∃ n : ℕ, ∃ (q : ℤ) (v : LL μ), v ∈ τ ∧ C.Pi μ i n q v ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hτ.ne
    by_contra hno
    push_neg at hno
    exact hv0 (hall i v fun n q g => hno n q _ (hτ.inv g v hv))
  obtain ⟨q, v, hv, hne⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, q, ⟨v, hv, hne⟩, fun n' q' hab w hw => ?_⟩
  by_contra hw0
  exact hab ⟨Nat.find_min' hex ⟨q', w, hw, hw0⟩,
    occ_abs (rightRegularRep (Gam K 2) μ) (C.un i) (un_mul C i) (un_cont C i) (un_central C i) τ hτ.closed hτ.inv hτ.irr
      (hmem _ _ _ hv) (hmem _ _ _ hw) hne hw0 (heig _ _ _) (heig _ _ _)⟩
