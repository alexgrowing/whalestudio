import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in

theorem hasInfQ_of_hasInfExp (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : D.what₂.Tau → ℚ)
    (hc : ChrEq c χ) (h : ∀ τ, HasInfExp D c τ (e τ)) : χ.HasInfQ (tauE D) e := by
  classical
  choose n hn hx using h
  refine ⟨n, hn, fun k => ?_⟩
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θ, hθ⟩ : ∃ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ := ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
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
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro z
    have h1 : c (T.toHomUnits z) = ∏ τ, c (T.toHomUnits (Pi.mulSingle τ (z τ))) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle z]
      rw [map_prod, map_prod]
    have h2 := congrArg Circle.coeHom h1
    rw [map_prod] at h2
    refine h2.trans (Finset.prod_congr rfl fun τ _ => ?_)
    have h3 := (hx τ).2 θ hθ (T.toHomUnits (Pi.mulSingle τ (z τ))) (tf _) fun τ' hτ' =>
      (ti _ τ').trans (by rw [Pi.mulSingle_eq_of_ne hτ', Units.val_one])
    have h4 : θ τ (infPart D ((T.toHomUnits (Pi.mulSingle τ (z τ)) : (AE D)ˣ) : AE D)) = z τ :=
      (ti _ τ).trans (by rw [Pi.mulSingle_eq_same])
    rw [h4] at h3
    exact h3
  rw [← eq_inf D c χ hc k _ _ (hab _) (hb _).1 (hb _).2, hT _ (ha (Units.map (incA D).toMonoidHom k)).2, key]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h5 : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom (a (Units.map (incA D).toMonoidHom k)) : ℂˣ) : ℂ) =
      tauE D τ (k : D.host.E) :=
    (congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)
  rw [h5]

theorem hasInfExp_iff_hasInfQ : ∀ (D : D7) (c : GlobalTheory.Mem.Th.IdC D) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ),
    Formalism.IndefR.Links.ChrEq c χ → ((∀ τ, HasInfExp D c τ (a τ)) ↔ χ.HasInfQ (Formalism.L2.Host.embTau D) a) :=
  fun D c χ a hc => ⟨hasInfQ_of_hasInfExp D c χ a hc, hasInfExp_of_chrEq D c χ a hc⟩

end GlobalTheory.HeckeInfExp
