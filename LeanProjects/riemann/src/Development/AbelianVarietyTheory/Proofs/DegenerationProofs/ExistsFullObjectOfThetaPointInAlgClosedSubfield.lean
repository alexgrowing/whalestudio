import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ThetaDescent

theorem exists_full_of_theta_in_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  intro hv h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K κ _ _ _ _ _ i m ρ z v o' hm _ hρ hz hth
  haveI := c.fin
  have hr : H.rt0 ∈ c.F := c.le (baseKA l).ρ.2
  have hζ : zeta l.A ∈ c.F := c.le (baseKA l).ζ.2
  obtain ⟨b, hb⟩ := exists_embedding H c.F hr ρ (i.injective (by rw [map_pow, ← hρ, o'.ρ_sq, map_neg, map_natCast]))
  have hp : IsPrimitiveRoot (i (b ⟨_, hζ⟩)) l.A :=
    ((IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (ζ := ⟨_, hζ⟩)
      (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective).map_of_injective
        b.injective).map_of_injective i.injective
  obtain ⟨I, hI⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l κ _ _ _ o'.I l.A _ l.A_pos hp
  obtain ⟨y, ⟨hy, φ, h₁, h₂, h₃, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hv h6 hU hX hT hE hA E H D l Xo c W₀ Y κ (i.comp b)).1
    { o' with I := I } (fun r h => by
      obtain rfl : r = ⟨_, hr⟩ := Subtype.ext h
      exact hρ.trans (congrArg i hb.symm)) (fun r h => by
      obtain rfl : r = ⟨_, hζ⟩ := Subtype.ext h
      exact hI)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨o, h₄, h₅⟩ := exists_full hv.1.1 hv.1.2.1.secBaseChangeAny (pullback.snd _ _)
    (IntermediateField.inclusion c.le).toRingHom pullback.condition Y.oF b i y hy o' φ h₁ h₂ h₃ m hm z v hz hth
  exact ⟨o, h₄.trans hb, h₅⟩

end GlobalTheory.Ex.ThetaDescent
