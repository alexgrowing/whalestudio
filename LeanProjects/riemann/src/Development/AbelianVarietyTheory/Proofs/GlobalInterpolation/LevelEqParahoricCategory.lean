import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.level_eq_parahoric_category

theorem cbe_mul {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {ρ h r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hρ : ρ ∈ Loc.R1 k n c) (hr : r ∈ Loc.Cbe J (ρ * h)) :
    ρ⁻¹ * r * ρ ∈ Loc.Cbe J h := by
  have hr1 : r ∈ Loc.R1 k n c := hr.1
  refine ⟨(mul_mem (mul_mem (inv_mem hρ) hr1) hρ : ρ⁻¹ * r * ρ ∈ Loc.R1 k n c), ?_⟩
  have h2 : (ρ * h)⁻¹ * r * (ρ * h)⁻¹⁻¹ ∈ J := hr.2
  show h⁻¹ * (ρ⁻¹ * r * ρ) * h⁻¹⁻¹ ∈ J
  convert h2 using 1
  group

theorem conj_res {k : Type} [CommRing k] {n c : ℕ} {ρ r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    {γ g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hγ : ∀ x, ρ (Loc.inX k n c x) = Loc.inX k n c (γ x))
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (x : Fin n → k) :
    (ρ⁻¹ * r * ρ) (Loc.inX k n c x) = Loc.inX k n c ((γ⁻¹ * g * γ) x) := by
  show ρ.symm (r (ρ _)) = Loc.inX k n c (γ.symm (g (γ x)))
  rw [hγ, hg, LinearEquiv.symm_apply_eq, hγ, LinearEquiv.apply_symm_apply]

theorem n1Arg_conj_eq {F : Type} [Field F] {n c : ℕ} {ρ r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hρ : ρ ∈ Loc.R1 F n c) (hr : r ∈ Loc.R1 F n c) : Loc.n1Arg (ρ⁻¹ * r * ρ) = Loc.n1Arg r := by
  have h1 := unipotentCharacterArgument_mul_stabilizer hρ.1 (mul_mem (mul_mem (inv_mem hρ) hr) hρ).1
  have h2 := unipotentCharacterArgument_mul_stabilizer hr.1 hρ.1
  have e : ρ * (ρ⁻¹ * r * ρ) = r * ρ := by group
  rw [e, h2] at h1
  linear_combination -h1

theorem main : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h ρ : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1) → (∀ (g : ↥lev.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r) → ∃ lev' : LevI X.E X.K (R.N j) P.1, lev'.H = (prCat (Pr := Pr) cst.sharp j P.1 (ρ * h)).subgroupOf (GLint X.E (R.N j) P.1) ∧ (∀ (g : ↥lev'.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (ρ * h) → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev'.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P (ρ * h) r) := by
  intro X Pr R Ch sel S mu cst j P h ρ lev hρ hle hH hlam
  obtain ⟨γ, hγ⟩ := exists_res hρ
  set H' := (prCat (Pr := Pr) cst.sharp j P.1 (ρ * h)).subgroupOf (GLint X.E (R.N j) P.1) with hH'
  have hmem : ∀ g : H', γ⁻¹ * g.1.1 * γ ∈ prCat (Pr := Pr) cst.sharp j P.1 h := by
    intro g
    obtain ⟨r, hr, hg⟩ := Subgroup.mem_subgroupOf.1 g.2
    exact ⟨_, cbe_mul _ hρ hr, conj_res hγ hg⟩
  have hmem2 : ∀ g : H', (⟨γ⁻¹ * g.1.1 * γ, hle (hmem g)⟩ : GLint X.E (R.N j) P.1) ∈ lev.H := by
    intro g
    rw [hH]
    exact Subgroup.mem_subgroupOf.2 (hmem g)
  let φ : H' →* lev.H := MonoidHom.mk' (fun g => ⟨⟨γ⁻¹ * g.1.1 * γ, hle (hmem g)⟩, hmem2 g⟩) (by
    intro a b
    refine Subtype.ext (Subtype.ext ?_)
    show γ⁻¹ * (a.1.1 * b.1.1) * γ = (γ⁻¹ * a.1.1 * γ) * (γ⁻¹ * b.1.1 * γ)
    group)
  refine ⟨⟨H', lev.lam.comp φ⟩, rfl, fun g r hr hg => ?_⟩
  have h1 := hlam (φ g) (ρ⁻¹ * r * ρ) (cbe_mul _ hρ hr) (conj_res hγ hg)
  refine h1.trans ?_
  have e : h⁻¹ * (ρ⁻¹ * r * ρ) * h = (ρ * h)⁻¹ * r * (ρ * h) := by group
  unfold chiInv
  rw [n1Arg_conj_eq hρ hr.1, e]

end GlobalTheory.Proof.level_eq_parahoric_category
