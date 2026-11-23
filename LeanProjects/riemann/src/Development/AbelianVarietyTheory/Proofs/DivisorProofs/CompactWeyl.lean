import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPowStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
open GlobalTheory.TrEll

noncomputable section
namespace GlobalTheory.RealSigns

def weylSub {n : ℕ} (ε : Fin n → Bool) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ε ∘ ⇑w = ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    ext i; simp

theorem mem_weylSub {n : ℕ} (ε : Fin n → Bool) (w : Equiv.Perm (Fin n)) :
    w ∈ weylSub ε ↔ w ∈ GlobalTheory.HCChar.compactWeyl ε := by
  simp [weylSub, GlobalTheory.HCChar.compactWeyl]

theorem of_cosets (hR : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i)) : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  intro D V S M ρ P hc
  have hR' := hR D V S M P ρ hc (weylSub (M.ε ρ)) (mem_weylSub (M.ε ρ))
  obtain ⟨T, b, hbij, hconj⟩ := hR'
  have hfin : (XSet P (placeOf D ρ).Completion V.gram).Finite :=
    Set.finite_coe_iff.1 (Finite.of_equiv _ b.symm)
  have h1 := @GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow D.host.F D.host.E _ _ _ _ _ D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank P
    (placeOf D ρ) (embOverOf D ρ)
  have hnorm : ∀ i, ‖cxRoots (embOverOf D ρ).1 P i‖ = 1 := by
    obtain ⟨Ψ, h3⟩ := h1 (by convert hc using 0)
    exact h3.2.2.2.2.2
  have hexp : ∀ z : ℂ, ‖z‖ = 1 → Complex.exp (Complex.arg z * Complex.I) = z := fun z hz => by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rwa [hz, Complex.ofReal_one, one_mul] at h
  refine ⟨hfin, fun q => (b q : Equiv.Perm (Fin V.rank)),
    fun q a => Complex.arg (cxRoots (embOverOf D ρ).1 P (((b q : Equiv.Perm (Fin V.rank)))⁻¹ a)), ?_,
    fun q a => hexp _ (hnorm _), ?_⟩
  · let e : GlobalTheory.HCChar.compactWeyl (M.ε ρ) ≃ weylSub (M.ε ρ) :=
      { toFun := fun w => ⟨w.1, (mem_weylSub _ _).2 w.2⟩, invFun := fun w => ⟨w.1, (mem_weylSub _ _).1 w.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact hbij.comp (Equiv.prodCongr e b).bijective
  · intro q
    have hq : HasCls P (placeOf D ρ).Completion V.gram (gam q.2.choose_spec.choose_spec.2) q.1 :=
      ⟨_, _, q.2.choose_spec.choose_spec.2, q.2.choose_spec.choose_spec.1, rfl⟩
    have hc2 := hconj q (gam q.2.choose_spec.choose_spec.2) hq
    obtain ⟨g, hg⟩ := hc2
    refine ⟨g⁻¹, (congrArg (fun h => frameMat M ρ (h * gam q.2.choose_spec.choose_spec.2 * g⁻¹)) (inv_inv g)).trans (hg.trans ?_)⟩
    exact congrArg Matrix.diagonal (funext fun a => (hexp _ (hnorm _)).symm)

end GlobalTheory.RealSigns
