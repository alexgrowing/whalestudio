import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd
open UpperTheory.GalN.V

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.toIsDomain

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

private theorem cong_refl (a : (Qbar l)ˣ) : Cong a a := by simp [Cong]

private theorem cong_symm {a b : (Qbar l)ˣ} (h : Cong a b) : Cong b a := by
  unfold Cong at *; rwa [norm_sub_rev]

private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')

private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]

private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h

private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb

private theorem norm_inv_one {b : (Qbar l)ˣ} (hb : ‖(b : Qbar l)‖ = 1) : ‖((b⁻¹ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_inv_eq_inv_val, norm_inv, hb, inv_one]

private theorem norm_mul_one {a b : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hb : ‖(b : Qbar l)‖ = 1) :
    ‖((a * b : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_mul, norm_mul, ha, hb, mul_one]

private theorem norm_pow_one {a : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (n : ℕ) :
    ‖((a ^ n : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow, ha, one_pow]

private theorem cong_inv {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : Cong a⁻¹ b⁻¹ := by
  have := cong_mul_right (cong_symm h) (a⁻¹ * b⁻¹) (norm_mul_one (norm_inv_one (cong_norm h hb)) (norm_inv_one hb))
  rwa [mul_inv_cancel_left, mul_comm a⁻¹ b⁻¹, mul_inv_cancel_left] at this

private theorem cong_pow {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) (n : ℕ) : Cong (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using cong_refl 1
  | succ n ih => rw [pow_succ, pow_succ]; exact cong_mul ih h (norm_pow_one hb n) hb

private theorem norm_of_finOrder {Γ : Type} [Group Γ] {φ : Γ →* (Qbar l)ˣ} (h : IsOfFinOrder φ) (s : Γ) :
    ‖(φ s : Qbar l)‖ = 1 := by
  obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 : φ s ^ n = 1 := by rw [← MonoidHom.pow_apply, h1]; rfl
  have h3 : ‖(φ s : Qbar l)‖ ^ n = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

private theorem cyc_val (s : G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl

private theorem norm_cyc (s : G F Ω) : ‖((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [cyc_val, norm_algebraMap']
  exact PadicInt.norm_units _

private theorem cong_cyc (s : G F Ω) : Cong (cycBar F Ω l s ^ (l - 1)) 1 := by
  unfold Cong
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val, cyc_val]; simp
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

private theorem cong_cyc_pow (s : G F Ω) (j t : ℕ) : Cong (cycBar F Ω l s ^ (j + (l - 1) * t)) (cycBar F Ω l s ^ j) := by
  rw [pow_add, pow_mul]
  have := cong_mul (cong_refl (cycBar F Ω l s ^ j)) (cong_pow (cong_cyc (l := l) s) (by simp) t)
    (norm_pow_one (norm_cyc s) j) (by simp)
  simpa using this

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem finOrder_of_kills {C : Type} [CommGroup C] {N : ℕ} (hN : 0 < N) {φ : G ℚ Ω →* C} (h : KillsMu N φ) :
    IsOfFinOrder φ := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  refine h _ fun ζ hζ => ?_
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h1 := hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one] at h1
  rw [map_pow, ← h1]

omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (h : IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj]; simp

omit [IsAlgClosure ℚ Ω] in
private theorem cc_not_mem (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω] {c : G ℚ Ω} (h : IsCC c) :
    c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := h
  intro hc
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, hc x]

private theorem sq_mem_galOf (K : Type) [Field K] [NumberField K] [Algebra K Ω] (h : Module.finrank ℚ K = 2) (s : G ℚ Ω) :
    s * s ∈ galOf ℚ K Ω := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  haveI : IsGalois ℚ K := inferInstance
  have h1 : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h]
  have h2 : AlgEquiv.restrictNormalHom K (s * s) = 1 := by
    rw [map_mul, ← sq, ← h1, pow_card_eq_one']
  intro x
  have := AlgEquiv.restrictNormal_commutes (s * s) K x
  rw [← this]
  change algebraMap K Ω (AlgEquiv.restrictNormalHom K (s * s) x) = _
  rw [h2]; rfl

private theorem algClosure (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem ordAt_change {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ ψ' : Fin n → G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (h' : ∀ i s, Cong (ψ' i s) (ψ i s)) : OrdAt r m ψ' A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  exact ⟨κ, h1, h2, fun i s => cong_trans (h3 i s) (cong_symm (h' i s))⟩

private theorem order_at_adjoint_zero {ρ : G F Ω →* GL (Fin 2) (Qbar l)} {m : ℤ} {Φ : G F Ω →* (Qbar l)ˣ} (hΦ : ∀ s, ‖(Φ s : Qbar l)‖ = 1)
    {A : ValuationSubring Ω} (h : OrdAt ρ ![m, 0] ![Φ, 1] A) : OrdAt (ad0 ρ) ![m, 0, -m] ![Φ, 1, Φ⁻¹] A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  have h4 : ∀ s : ↥(Dec (F := F) A), Cong ((κ 0 / κ 1) s) (Φ s) := fun s => by
    have := cong_mul (h3 0 s) (cong_inv (h3 1 s) (by simp)) (hΦ s) (by simp)
    simpa [div_eq_mul_inv] using this
  refine ⟨_, (ad0Facts l _ ρ).2.2.2.1 _ κ h1, fun i s hs => ?_, fun i s => ?_⟩
  · have a0 := h2 0 s hs
    have a1 := h2 1 s hs
    fin_cases i <;> simp [a0, a1]
  · fin_cases i
    · exact h4 s
    · exact cong_refl _
    · have := cong_inv (h4 s) (hΦ s)
      simpa using this

private theorem exists_symmetric_pairing_adjoint_zero {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) {c : Γ} (hc : c * c = 1) :
    ∃ P : GL (Fin 3) (Qbar l), (P.val)ᵀ = P ∧ ∀ s,
      (ad0 ρ s).valᵀ * (P.val) *
        (ad0 ρ (c * s * c⁻¹)).val = P := by
  obtain ⟨P, h1, h2⟩ := (ad0Facts l _ ρ).2.1
  have e : (ad0 ρ c).val * (ad0 ρ c).val = 1 := by
    rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
  have e' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  refine ⟨P * ad0 ρ c, ?_, fun s => ?_⟩
  · rw [Units.val_mul, Matrix.transpose_mul, h1]
    conv_rhs => rw [← h2 c]
    rw [Matrix.mul_assoc _ _ (ad0 ρ c).val, e, Matrix.mul_one]
  · rw [e', map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul]
    conv_rhs => rw [← h2 s]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ad0 ρ c).val (ad0 ρ c).val, e,
      Matrix.one_mul]

private theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (κ : Γ →* kˣ) : ad0 (tw ρ κ) = ad0 ρ := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hk : (κ s : k) ≠ 0 := (κ s).ne_zero
  have hd : (ρ s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero
  have e1 : ∀ (r : Γ →* GL (Fin 2) k), (ad0 r s : Matrix (Fin 3) (Fin 3) k) =
      ((r s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (r s : Matrix (Fin 2) (Fin 2) k) := fun r => by
    rw [ad0, tw_val]; simp
  have e2 : ∀ (a : k) (g : Matrix (Fin 2) (Fin 2) k), symSquareMatrixHom k (a • g) = (a ^ 2) • symSquareMatrixHom k g := fun a g => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring
  rw [e1, e1, tw_val, e2, Matrix.det_smul, smul_smul]
  congr 1
  simp only [Fintype.card_fin]
  field_simp

end Shape

end UpperTheory.V.Sd
