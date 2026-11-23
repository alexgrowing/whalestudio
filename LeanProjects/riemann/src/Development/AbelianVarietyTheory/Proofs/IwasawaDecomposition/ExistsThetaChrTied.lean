import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (ChrEq)
open Formalism.L2.Host (HChar)
open scoped TensorProduct

namespace GlobalTheory.TowerCharRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

theorem exists_thetaChrTied (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (X : ThetaX D) (T : ThetaTied D X) (hR : ChrRead T C Tp.xi) :
    ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, ChrEq (T.eChr c) (H.eChr c) := by
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.ChrEqUnique.chrEq_unique D
  have hc : ∀ c, IsHeckeChar D (T.eChr c) ∧ ∀ τ, ∃ a, HasInfExp D (T.eChr c) τ a := fun c => by
    have : T.eChr c ∈ Set.range T.eChr := ⟨c, rfl⟩
    rwa [T.eChr_range] at this
  choose e he using fun c => GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D (T.eChr c) (hc c).1
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    u1 _ _ _ (he (a * b)) (by rw [map_mul]; exact chrEq_mul (he a) (he b))
  have hinf : ∀ c, (e c).HasInfQ (Formalism.L2.Host.embTau D) (X.infTy c) := fun c =>
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ (he c)).1 (T.infTy c)
  refine ⟨⟨MonoidHom.mk' e hmul, fun a b hab => T.eChr_inj (u2 _ _ _ (he a) ?_), fun χ => ⟨?_, ?_⟩, hinf,
    fun μ j => u1 _ _ _ (he _) (hR.chr μ j), u1 _ _ _ (he _) hR.eta⟩, he⟩
  · have hab' : e a = e b := hab
    rw [hab']
    exact he b
  · rintro ⟨c, rfl⟩
    exact ⟨u3 _ _ (he c), _, hinf c⟩
  · rintro ⟨hu, a, ha⟩
    obtain ⟨c, hcχ⟩ := GlobalTheory.CharTransport.exists_chrEq D χ hu
    have hm : c ∈ Set.range T.eChr := by
      rw [T.eChr_range]
      exact ⟨hcχ.1, fun τ => ⟨a τ, (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ hcχ).2 ha τ⟩⟩
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, u1 _ _ _ (he x) hcχ⟩

end GlobalTheory.TowerCharRead

end
