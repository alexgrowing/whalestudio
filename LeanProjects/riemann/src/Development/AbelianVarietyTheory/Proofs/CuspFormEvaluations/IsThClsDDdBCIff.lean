import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValAtBc
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelCoverLargerCoeffFieldLyingOverStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumFieldChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_incF (a : c.F) :
    ((ddBC hle d).eF (incF c c' hle a) : (covCoeff hle d).F) =
      incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (d.eF a) := Subtype.ext rfl

theorem exists_algOver (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] :
    ∃ _ : Algebra c'.F k, AlgOver c c' hle k := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  let φ : c'.F →ₐ[c.F] k := IsAlgClosed.lift
  exact ⟨φ.toRingHom.toAlgebra, fun a => φ.commutes a⟩

theorem thLa_iff (w : (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (k : Type) [CommRing k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k]
    (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (v : k) :
    thLaValAt d.Xo₂ (covCoeff hle d) (nabBC (le_covCoeff hle d) d.nab₂)
        (fun q => (ddBC hle d).eF (incF c c' hle (w q))) La N
        (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P)) y₂ v ↔
      thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (y₂.res (le_covCoeff hle d) h₂) v := by
  have h := GlobalTheory.FieldBC.shortValAt_bc E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.nab₂ n
    (fun q => d.eF (w q)) La 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) k h₂ y₂ v
  have e : (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P) :
      MvPolynomial (LtN Dw n) (covCoeff hle d).F) =
      MvPolynomial.map (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d))
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => eF_incF hle d a)
  rw [map_one] at h
  unfold thLaValAt
  rw [e]
  exact h

theorem isThClsD_ddBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (Vs' : Type) [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (x : Cl → Vs) (x' : Cl → Vs'), (∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k))) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a m, (IsThClsD Xo c' (ddBC hle d) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol) (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) ↔ IsThClsD Xo c d w La Nc gam vol ep io x f) := by
  intro E _ _ _ H Dw l Xo c c' hle n d Cl _ w La Nc gam vol ep Vs _ _ io Vs' _ _ io' x x' hio hδ a m f hf
  have hcoef : ∀ (k : Type) [Field k] [Algebra c.F k] [Algebra c'.F k], AlgOver c c' hle k → ∀ cl,
      algebraMap c'.F k (incF c c' hle vol * ((gam cl : c'.F))⁻¹ * incF c c' hle (ep cl)) =
        algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) := by
    intro k _ _ _ h cl
    rw [← h, map_mul (incF c c' hle), map_mul (incF c c' hle), map_inv₀, map_natCast]
  have hf' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a m f hf).2
  have hδ' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ hδ).2
  have hov := (GlobalTheory.T.levelCover_larger_coeffField_lying_over E H Dw l Xo c c' hle n d).1
  constructor
  · intro H' k _ _ _ _ hk y y₂ hy
    obtain ⟨A, h⟩ := exists_algOver hle k
    letI A₂ : Algebra (covCoeff hle d).F k := A
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun b => by
      obtain ⟨b, rfl⟩ := d.eF.surjective b
      rw [hk, ← h b]
      rfl
    obtain ⟨vc, hv, he⟩ := @H' k _ _ A A₂ (fun _ => rfl) (y.ext hle h) (y₂.ext (le_covCoeff hle d) h₂)
      ((hov k h h₂ _ _).2 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · have := hv cl
      rw [hio] at this
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ _ _).1 this
    · have e1 := hf' k h (y.ext hle h)
      have e2 := hδ' k h₂ (y₂.ext (le_covCoeff hle d) h₂)
      simp only [hcoef k h] at he
      rw [e1] at he
      exact he.trans (congrArg (· * _) e2)
  · intro H' k _ _ A A₂ hk y y₂ hy
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI := resAlg hle k
    letI := resAlg (le_covCoeff hle d) k
    have h : AlgOver c c' hle k := fun _ => rfl
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun _ => rfl
    obtain ⟨vc, hv, he⟩ := H' k (fun b => hk (incF c c' hle b)) (y.res hle h)
      (FrPt.res (c' := covCoeff hle d) (le_covCoeff hle d) h₂ y₂) ((hov k h h₂ y₂ y).1 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · rw [hio]
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ y₂ _).2 (hv cl)
    · have e1 := hf' k h y
      have e2 := hδ' k h₂ y₂
      simp only [hcoef k h]
      rw [e1]
      exact he.trans (congrArg (· * _) e2.symm)

end GlobalTheory.ClassSumFieldChange
