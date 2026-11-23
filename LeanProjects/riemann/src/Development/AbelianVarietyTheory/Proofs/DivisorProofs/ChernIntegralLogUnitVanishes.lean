import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

open GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ArInt

theorem chInt_logSq_unit_eq_zero : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (a : Γ(X, ⊤)ˣ) (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (fun y => CxPts.logSq y ⊤ a)) ∧
        chInt (comb L n) D (fun σ y => CxPts.logSq y ⊤ a) = 0 := by
  intro H k _ X _ p D hX a ι _ L n
  let u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun σ y => CxPts.logSq y ⊤ a
  have hu : ∀ σ y, CxPts.CInfAt (u σ) y := by
    intro σ y
    have hy : y ∈ ptsIn p σ (⊤ : X.Opens) := mem_ptsIn_top
    have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
    refine ⟨⊤, Unit, inferInstance, fun _ => a.val, fun v => Real.log (‖v ()‖ ^ 2),
      {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const, ?_,
      hs.contDiffOn.log fun _ h => h, Filter.Eventually.of_forall fun _ => rfl⟩
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (ev_ne_zero hy a.isUnit))
  have hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ')) := by
    intro σ σ' i y y' h _
    change CxPts.logSq y' ⊤ a = CxPts.logSq y ⊤ a
    simp only [CxPts.logSq, CxPts.ev_conj h mem_ptsIn_top, RCLike.norm_conj]
  have hiso : (HermLB.triv p).Isometric (fnB u hu hc) := by
    refine isometric_of_local (fun _ : PUnit => (⊤ : X.Opens)) (fun _ => ⟨PUnit.unit, trivial⟩)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => a)
      (fun x j j' _ _ => ?_) (fun σ j y _ => ?_)
    · change _ = gm (𝟙 X) x _ (1 : Γ(X, ⊤ ⊓ ⊤)ˣ) * (gm (𝟙 X) x _ (1 : Γ(X, ⊤ ⊓ ⊤)ˣ))⁻¹ * _
      rw [map_one, inv_one, mul_one, one_mul]
    · change CxPts.logSq y ⊤ a = 0 + CxPts.logSq y ⊤ a
      rw [zero_add]
  have h0 : HermLB.triv p = fnB (fun _ _ => 0) (fun _ y => cInfAt_const 0 y) (fun _ _ _ _ _ _ _ => rfl) := rfl
  obtain ⟨Φ, hΦ⟩ := ((H.arExists k X p D hX).2 (Option ι) fun o => o.elim (HermLB.triv p) L).1
  have hΦ' : IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ :=
    ((H.arIso k X p D hX).2 _ _ Φ hΦ).2.1 _ fun o => by
      cases o with
      | none => exact hiso
      | some i => exact HermLB.Isometric.refl _
  rw [h0] at hΦ
  obtain ⟨h₁, h₂⟩ := H.arMix.fnB H.arExists hX hΦ' n
  have h₃ := (H.arMix.fnB H.arExists hX hΦ n).2
  refine ⟨h₁, ?_⟩
  have hz : chInt (comb L n) D (fun _ _ => (0 : ℝ)) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    simp [Weight.chernInt]
  rw [hz] at h₃
  change chInt (comb L n) D u = 0
  linarith

end GlobalTheory.ArInt
