import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem frobPoly_of_rec_twist : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) {l : ℕ} [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ) {m : ℕ} {r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)}, Continuous r → ∀ {rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h}, GlobalTheory.LocLanglands.IsRec h rc → ∀ {σ : GlobalTheory.SmGL.IrrRep (GL (Fin m) (w.adicCompletion E))} {α : Fin m → ℂˣ}, GlobalTheory.SmGL.HasSatake σ.ρ α → GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (m : ℝ)) / 2) → ∀ {g : Formalism.ConjugateSelfDual.G E Ω}, Formalism.ConjugateSelfDual.IsFrob (F := E) A (Formalism.ConjugateSelfDual.normV w) g → ((r g⁻¹ : GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = GlobalTheory.SphPar.frobPoly (Formalism.ConjugateSelfDual.normV w) m ((Finset.univ.val.map α).map fun b : ℂˣ => (b : ℂ)) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι m r hr rc hrc σ α hα hwd g hg
  have hr' : Continuous fun x => (r x : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have hgW : g ∈ GlobalTheory.WeilDeligne.Weil h := GlobalTheory.WeilDeligne.mem_Weil_of_isFrob h hg
  have hd : GlobalTheory.WeilDeligne.deg (⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h) = 1 :=
    GlobalTheory.WeilDeligne.deg_eq_one_iff.mpr hg
  have e1 := GlobalTheory.WeilDeligne.charPol_wdOf hl ι hr' (⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h)⁻¹
  rw [hwd, GlobalTheory.CuspRep.ParLaws.rec_eq_diag hrc hα, GlobalTheory.WeilDeligne.WD.lpTw_mk,
    GlobalTheory.WeilDeligne.WD.charPol_mk, GlobalTheory.WeilDeligne.WDRep.tw_ρ,
    GlobalTheory.WeilDeligne.WDRep.diag_ρ, GlobalTheory.WeilDeligne.deg_inv, hd] at e1
  have e2 : ∀ (a : ℂ) (d : Fin m → ℂ), a • GlobalTheory.WeilDeligne.diagEnd d =
      GlobalTheory.WeilDeligne.diagEnd fun i => a * d i := fun a d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [e2, GlobalTheory.WeilDeligne.charpoly_diagEnd] at e1
  change ((r ((⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h)⁻¹ : GlobalTheory.WeilDeligne.Weil h) :
    GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
      ι.toRingHom = _
  rw [← e1, GlobalTheory.SphPar.frobPoly, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 2
  rw [zpow_neg_one, zpow_neg_one, Units.val_inv_eq_inv_val, inv_inv, mul_comm, ← Complex.cpow_neg,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  congr 2
  push_cast
  ring

end GlobalTheory
