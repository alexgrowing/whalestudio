import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

open GlobalTheory.CuspRep.ParLaws in

theorem hasSatake_of_repEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv π')
    (hirr : π'.IsIrreducible) {α : Fin n → ℂˣ} (h : HasSatake π α) : HasSatake π' α :=
  ⟨hirr, fixed_ne_bot_of_equiv φ h.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open GlobalTheory.CuspRep.ParLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem locParT_eq_locComp [IsTotallyComplex E] (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem locRecT_sat (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) (σ : IrrRep (GL (Fin a) (w.adicCompletion E)))
    {α : Fin a → ℂˣ} (hα : HasSatake σ.ρ α) : locRecT hT h (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨b, hb, H⟩ := isRecT_locRecT hT h
  exact GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff b hb _).2 H) (cls σ) α
    (hasSatake_of_repEquiv (equivRep σ) (IrrRep.irr _) hα)

theorem exists_hasSatake_of_unrT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w)
    {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} (hu : (locRecT hT h (cls σ)).unr) : ∃ α, HasSatake σ.ρ α := by
  obtain ⟨b, hb, H⟩ := isRecT_locRecT hT h
  have hs := (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h b hb _ ((GlobalTheory.RecT.lawsT_iff b hb _).2 H) (cls σ)).2 hu
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) a
    ⟨(cls σ).2.rep.V, (cls σ).2.rep.ρ, (cls σ).2.rep.smooth, (cls σ).2.rep.irr⟩ hs
  exact ⟨α, hasSatake_of_repEquiv (equivRep σ).symm σ.irr hα⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open GlobalTheory.CuspRep.ParLaws

theorem csd_unrT : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (a : ℕ) (π : CG L a), π.IsCsd → ∀ (w w' : HeightOneSpectrum (𝓞 L)), ConjPl (IsCMField.complexConj L).toRingEquiv w w' → ∀ (A A' : ValuationSubring Ω) (h : IsPlaceOver A w) (h' : IsPlaceOver A' w'), (locParT hT π h).unr → (locParT hT π h').unr ∧ (locParT hT π h').frobEig = (locParT hT π h).frobEig.map (·⁻¹) := by
  intro hT hF L Ω _ _ _ _ _ _ a π hπ w w' hc A A' h h' hu
  obtain rfl : w' = conjSrc (IsCMField.complexConj L).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hc (IsCMField.complexConj L x)).symm
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF L a π w
  have e : locParT hT (Quotient.mk _ π) h = _ := locParT_eq_locComp hT hσ h
  have e' : locParT hT (Quotient.mk _ π) h' = _ := locParT_eq_locComp hT (isLocComp_flip hπ hσ) h'
  rw [e] at hu
  obtain ⟨α, hα⟩ := exists_hasSatake_of_unrT hT h hu
  rw [e, e', locRecT_sat hT h _ hα, locRecT_sat hT h' _ (hasSatake_flip_conjLoc _ w hα),
    WD.frobEig_diag, WD.frobEig_diag, Multiset.map_map]
  refine ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), ?_⟩
  conv_rhs => rw [← Finset.map_univ_equiv Fin.revPerm, Finset.map_val, Multiset.map_map]
  simp

end GlobalTheory.CuspRep.ParLawsT

end
