import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProdStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD

theorem pure_step {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) :
    ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
      (y : MvPolynomial (Fin N × Fin N) O) = evalPol O N Φ (x τ : MvPolynomial (Fin N × Fin N) O) ∧
      evalE O N lam P (FreeAlgebra.lift O Fab Φ) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro x
    refine ⟨r • x τ, ?_, ?_⟩
    · rw [AlgHom.commutes, Module.algebraMap_end_apply]; rfl
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, MultilinearMap.map_update_smul,
        Function.update_eq_self]
  | grade1 p =>
    intro x
    obtain ⟨y, hy, he⟩ := hF p x
    refine ⟨y, ?_, ?_⟩
    · rw [hy]; simp [evalPol]
    · rw [FreeAlgebra.lift_ι_apply]; exact he
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ (Function.update x τ y₂)
    refine ⟨y₁, ?_, ?_⟩
    · rw [hy₁, Function.update_self, hy₂, map_mul, Module.End.mul_apply]
    · rw [map_mul, map_mul, Module.End.mul_apply, he₂, he₁, Function.update_idem]
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [Submodule.coe_add, hy₁, hy₂, map_add, LinearMap.add_apply]
    · rw [map_add, map_add, LinearMap.add_apply, he₁, he₂, MultilinearMap.map_update_add]

theorem scalar_of {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) (c : O)
    (hΦ : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), evalPol O N Φ f = c • f) :
    evalE O N lam P (FreeAlgebra.lift O Fab Φ) = c • (1 : Module.End O (NablaT O N lam)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  obtain ⟨y, hy, he⟩ := pure_step τ lam P Fab hF Φ x
  have hyc : y = c • x τ := Subtype.ext (by rw [hy, hΦ _ (x τ).2]; rfl)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, he, hyc,
    MultilinearMap.map_update_smul, Function.update_eq_self]
  simp

def evalA (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] alg O N lam :=
  FreeAlgebra.lift O (Sum.elim (grpA O N lam) fun p =>
    ⟨P p.1 p.2, Algebra.subset_adjoin (Or.inr ⟨p.1, p.2, hP p.1 p.2⟩)⟩)

theorem evalA_coe (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ((evalA O N lam P hP Φ : alg O N lam) : Module.End O (NablaT O N lam)) = evalE O N lam P Φ := by
  have h : (alg O N lam).val.comp (evalA O N lam P hP) = evalE O N lam P := by
    apply FreeAlgebra.hom_ext
    funext p
    rcases p with g | p
    · simp [evalA, evalE, grpA]
    · simp [evalA, evalE]
  exact DFunLike.congr_fun h Φ

theorem compat {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam mu : ι → ℕ → ℕ} {ϖ : O}
    {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Q : ι → (Fin N → ℕ) → Module.End O (NablaT O N mu)) (hQ : ∀ σ w, IsProj O N mu σ w (Q σ w))
    (ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))))
    (h2 : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z)
    (h3 : ∀ g z y, ψ z = Submodule.Quotient.mk y →
      ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y))
    (h4 : ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a →
      IsProj O N mu τ w a' → ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ∀ z y, ψ z = Submodule.Quotient.mk y →
      ψ (evalA O N lam P hP Φ • z) = Submodule.Quotient.mk (evalE O N mu Q Φ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro z y h
    rw [AlgHom.commutes, AlgHom.commutes, h2, h, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
  | grade1 p =>
    intro z y h
    rcases p with g | ⟨σ, w⟩
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inl]; exact h3 g z y h
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      exact h4 σ w _ (Q σ w) (hP σ w) (hQ σ w) z y h
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_mul, map_mul, mul_smul, Module.End.mul_apply]
    exact h₁ _ _ (h₂ z y h)
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_add, map_add, add_smul, map_add, LinearMap.add_apply, h₁ z y h, h₂ z y h, Submodule.Quotient.mk_add]

theorem dvd_of_smul_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type}
    [AddCommGroup V] [Module O V] {ϖ : O} (hϖ : Irreducible ϖ) (d : O) (y : V)
    (hne : (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) ≠ 0)
    (h0 : d • (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) = 0) : ϖ ∣ d := by
  by_contra hd
  have hu : IsUnit d := by
    by_contra hnu
    have hm : d ∈ IsLocalRing.maximalIdeal O := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
    exact hd hm
  obtain ⟨u, rfl⟩ := hu
  apply hne
  have h1 := congrArg (fun q => (↑u⁻¹ : O) • q) h0
  simpa [smul_smul] using h1

theorem int_dvd_of {O : Type} [CommRing O] {ϖ : O} (hϖ : ¬ IsUnit ϖ) {l : ℕ} (hl : l.Prime)
    (hϖl : ϖ ∣ (l : O)) (d : ℤ) (hd : ϖ ∣ (d : O)) : (l : ℤ) ∣ d := by
  by_contra h
  have hc : IsCoprime (l : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h' : Nat.Coprime l d.natAbs := (Nat.Prime.coprime_iff_not_dvd hl).2 (fun h' => h (Int.natCast_dvd.2 h'))
    simpa [Int.gcd] using h'
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ϖ ∣ ((u * l + v * d : ℤ) : O) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖl _) (dvd_mul_of_dvd_right hd _)
  rw [huv, Int.cast_one] at h1
  exact hϖ (isUnit_of_dvd_one h1)

set_option synthInstance.maxHeartbeats 400000 in

theorem linkage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ →
    ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) →
    ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm →
    Embeds O N lam mu ϖ Gm → ∀ τ,
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  intro O _ _ _ _ N ι _ _ lam mu l ϖ hl hϖ hϖl hlam hmu Gm _ _ _ hSub hEmb τ
  obtain ⟨U, π, hπ, -⟩ := hSub
  obtain ⟨ψ, hψ, h2, h3, h4⟩ := hEmb
  choose P hP _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam σ w
  choose Q hQ _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι mu σ w
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ c : Fin N, lam τ c + ∑ c : Fin N, mu τ c := ⟨_, rfl⟩
  choose Fab hFab using fun p : Fin N × Fin N => GlobalTheory.T.polarisationOperator_formula_groupAndProjectors O N ι τ M p.1 p.2
  obtain ⟨Fk, hFk⟩ := GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod O N
  have hscal : ∀ (nu : ι → ℕ → ℕ) (R : ι → (Fin N → ℕ) → Module.End O (NablaT O N nu)),
      (∀ σ, Antitone (res N (nu σ))) → (∀ σ w, IsProj O N nu σ w (R σ w)) → ∑ c : Fin N, nu τ c ≤ M → ∀ k,
      evalE O N nu R (FreeAlgebra.lift O Fab (Fk k)) =
        (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • 1 := by
    intro nu R hnu hR hb k
    apply scalar_of τ nu R Fab (fun p x => hFab p nu R hnu hR hb x)
    intro f hf
    exact hFk (res N (nu τ)) (hnu τ) f hf k
  obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
  obtain ⟨u, rfl⟩ := hπ z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (ψ (π u))
  have hne : (Submodule.Quotient.mk y : NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))) ≠ 0 := by
    rw [hy]; intro h; apply hz; apply hψ; rw [h, map_zero]
  have key : ∀ k, ϖ ∣ ((((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k -
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ)) : O) := by
    intro k
    apply dvd_of_smul_eq_zero hϖ _ y hne
    have hL := hscal lam P hlam hP (by omega) k
    have hMu := hscal mu Q hmu hQ (by omega) k
    have hc := compat P hP Q hQ ψ h2 h3 h4 (FreeAlgebra.lift O Fab (Fk k)) (π u) y hy.symm
    have hA : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • π u =
        algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • π u := by
      have hu' : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • u =
          algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • u := by
        apply Subtype.ext
        change ((evalA O N lam P hP _ : alg O N lam) : Module.End O _) (u : NablaT O N lam) =
          ((algebraMap O (alg O N lam) _ : alg O N lam) : Module.End O _) (u : NablaT O N lam)
        rw [evalA_coe, hL, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
          Module.algebraMap_end_apply]
      rw [← π.map_smul, hu', π.map_smul]
    rw [hA, h2, hMu, ← hy] at hc
    rw [Int.cast_sub, sub_smul, sub_eq_zero, hc]
    simp [Submodule.Quotient.mk_smul]
  have hmap : ∀ nu : ι → ℕ → ℕ,
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
        (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).map (Int.castRingHom (ZMod l)) := by
    intro nu; simp [Polynomial.map_prod]
  rw [hmap lam, hmap mu]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub]
  exact dvd_neg.2 (int_dvd_of hϖ.not_isUnit hl hϖl _ (key k))

end GlobalTheory.CapelliLink

end
