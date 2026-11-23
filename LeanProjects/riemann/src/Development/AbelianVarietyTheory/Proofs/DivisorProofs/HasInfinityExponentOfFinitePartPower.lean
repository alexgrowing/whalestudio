import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact.InfExp

open IsDedekindDomain

theorem finAdEquiv_one_tmul (D : D7) (k : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) =
      GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D k) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp only [GlobalTheory.BotFormula.toFinE, Formalism.MainNotions.StandardLatticesGL3.inc, Formalism.UG.inclE, RingEquiv.trans_apply,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.comm_tmul]
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp

theorem eq_inf {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ)
    (hf : HasFinPart χ c e) (k : D.host.Eˣ) (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y)
    (hy : infPart D (y : AE D) = 1) (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((χ x : Circle) : ℂ) =
      ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
  have hfin : ((χ y : Circle) : ℂ) = ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) ^ e : ℂˣ) : ℂ) :=
    hf y _ ⟨hy, by rw [hy']; exact finAdEquiv_one_tmul D k⟩
  have h5 : ((χ x : Circle) : ℂ) * ((χ y : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← map_mul, ← hxy, hχ.2 k, Circle.coe_one]
  have haut := c.aut k
  set F : ℂ := ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) : ℂˣ) : ℂ) with hF
  have hF0 : F ≠ 0 := (c.f _).ne_zero
  have hP : ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (c.n τ) = F⁻¹ :=
    eq_inv_of_mul_eq_one_right haut
  rw [Units.val_zpow_eq_zpow_val, ← hF] at hfin
  rw [hfin] at h5
  have hx : ((χ x : Circle) : ℂ) = (F ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h5
  rw [hx, ← inv_zpow, ← hP, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]

set_option maxHeartbeats 1000000 in
open Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in

theorem hasInfExp_of_hasFinPart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    HasFinPart χ c e → ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  intro D N c e χ hχ hf τ₀
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  refine ⟨e * c.n τ₀, by push_cast; ring, ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩, fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨τ₀⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((χ (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
    intro z
    refine (denseRange_units (tauE D) hd).induction_on z (isClosed_eq
      (continuous_subtype_val.comp (hχ.1.comp Tc)) (continuous_finset_prod _ fun τ _ => ?_)) fun k => ?_
    · have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h2 : ∀ z : D.what₂.Tau → ℂˣ, ((‖(z τ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
        Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (z τ).ne_zero)
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h2).zpow₀ _ fun z =>
        Or.inl (div_ne_zero (z τ).ne_zero (h2 z))
    · refine Eq.trans ?_ (GlobalTheory.NormExact.InfExp.eq_inf c e χ hχ hf k _ _ (hab _) (hb _).1 (hb _).2)
      rw [hT _ (ha (Units.map (incA D).toMonoidHom k)).2]
      congr 3
      funext τ
      exact Units.ext ((congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)).symm
  intro x hx hx'
  refine (congrArg (fun u => ((χ u : Circle) : ℂ)) (hT x hx)).trans ((key _).trans ?_)
  refine Finset.prod_eq_single τ₀ (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom x : ℂˣ) : ℂ) = 1 := hx' τ hτ
  rw [this, norm_one, Complex.ofReal_one, div_one, one_zpow]

end GlobalTheory.NormExact.InfExp
