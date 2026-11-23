import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumnsStatement

set_option autoImplicit false

namespace GlobalTheory.FactorDepthProd

section General

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {κ : Type} [Fintype κ] {d : κ → ℕ}
  (G : ∀ b, LogFGL v (d b)) {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C)

omit [Fintype κ] in

theorem constantCoeff_expAlong (x : Σ b, Fin (d b)) : constantCoeff (expAlong G u x) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by simp)) (by simp) ((isExp_expOf _).1 _)

theorem derivAt0_one_subst (f : MvPowerSeries (Σ b, Fin (d b)) C) :
    derivAt0 1 (subst (expAlong G u) f) = constantCoeff f := by
  classical
  have hs : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have h0 : constantCoeff (subst (expAlong G u) (f - (constantCoeff f) • 1)) = 0 :=
    constantCoeff_subst_eq_zero hs (constantCoeff_expAlong G u) (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  unfold derivAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simpa [mfact, sub_eq_zero] using h0

theorem depth_one : depth G u 1 = 0 := by
  classical
  unfold depth
  refine le_antisymm (iInf_le_of_le ⟨1, fun α => ?_⟩ ?_) (le_iInf fun f => ?_)
  · unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  · rw [derivAt0_one_subst, map_one, AddValuation.map_one]; rfl
  · rw [derivAt0_one_subst]
    have h : (0 : WithTop ℝ) ≤ v (constantCoeff f.1) := f.2 0
    exact WithBot.coe_le_coe.2 h

theorem depth_prod [CharZero C] [DecidableEq κ] [∀ b, DecidableEq (ι b)] {F : Type} (col : κ → F)
    (P : F → MvPolynomial (Σ b, ι b) C) (hP : ∀ f, ∀ x ∈ (P f).vars, col x.1 = f) (s : Finset F) :
    depth G u (∏ f ∈ s, P f) = ∑ f ∈ s, depth G u (P f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using depth_one G u
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    refine GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns C v κ d G ι u {b | col b = a} _ _ (hP a) fun x hx h => ?_
    obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hx)
    exact ha ((show col x.1 = a from h) ▸ hP f x hxf ▸ hf)

theorem depth_prod_detPow [CharZero C] {n : ℕ} (G₀ : LogFGL v n) {F : Type} [Fintype F] (r : F → ℕ)
    (w : ∀ f, Fin (r f) → Fin n → C) (cx : F → ℕ) :
    depth (fun _ : (Σ f : F, Fin (r f)) => G₀) (fun b => w b.1)
      (∏ f : F, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (r f), Fin (r f)) =>
        (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : F, Fin (r f)), Fin (r b.1))) (detPow C (r f) (cx f))) =
      ∑ f : F, detDepth G₀ (w f) (cx f) := by
  classical
  rw [depth_prod _ _ (fun b : (Σ f : F, Fin (r f)) => b.1)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have h := GlobalTheory.T.differentialOperatorDepth_restrict_columns C v (Σ f : F, Fin (r f)) (fun _ => n) (fun _ => G₀)
      (fun b => Fin (r b.1)) (fun b => w b.1) (Fin (r f)) ⟨fun b => ⟨f, b⟩, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩
      (detPow C (r f) (cx f))
    unfold detDepth
    refine Eq.trans ?_ (h.trans ?_)
    · congr 1
    · congr 1
  · intro f x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hx)
    rfl

end General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem nuProdC_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X cx
  exact depth_prod_detPow (fgl Ch X) rk (frame Ch X) cx

end GlobalTheory.FactorDepthProd
