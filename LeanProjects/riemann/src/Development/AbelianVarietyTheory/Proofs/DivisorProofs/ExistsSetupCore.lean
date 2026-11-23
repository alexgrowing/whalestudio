import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyPolarizationDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundaryOfTorusDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyToroidalBoundaryDataOfSnc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingCompatHeq
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

theorem GlobalTheory.Mean4.exists_setup_core : ∀ D : D7, (∀ (O : Setup D) (x : ToroidalCompactificationData O.s), ∃ P h, (O.withCore x P h).CoreWith x P) ∧ ∀ (A : Amb D) (N j : ℕ) (h : 1 ≤ j ∧ j < N) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (Φ : s.Flag) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)), ∃ (ng : NgPkg) (k : Kit s L (cxSt D.what₂.LL) jC ng) (adm : AdmSt D N j jC) (met : MetIn k.Φ), k.Φ = Φ ∧ (Setup.ofKit h k adm met).Core := by
  intro D
  refine ⟨fun O x => ?_, fun A N j h S κ s L Φ jC => ?_⟩
  · obtain ⟨P⟩ := GlobalTheory.T.nonempty_polarization_data D _ _ _ _ _ O.s O.Φ (metsOf x O.Φ) (refMet x O.Φ)
    exact ⟨P, GlobalTheory.T.exists_boundary_of_torus_data D _ _ _ _ _ O.s O.L x, O.coreWith_withCore x P _⟩
  · obtain ⟨x⟩ : Nonempty (ToroidalCompactificationData s) := nonempty_toroidal_boundary_data _ _ _ _ _ _ _ _ s.T.Z s.T.snc
    obtain ⟨P⟩ := GlobalTheory.T.nonempty_polarization_data D _ _ _ _ _ s Φ (metsOf x Φ) (refMet x Φ)
    obtain ⟨B, hB⟩ := GlobalTheory.T.exists_boundary_of_torus_data D _ _ _ _ _ s L x
    let pad := AsmCheck.padAny N j h.2.le s.Comp jC
    let k := KitEx.kitOf s L (cxSt D.what₂.LL) Φ (KitEx.key_nonempty s).some pad
    exact ⟨_, { k with B := B, fl := flBetti s Φ L, Mb := mbarOf P }, .ofPkg pad, metTrue x Φ P, rfl, x, P,
      Setup.coreWith_ofKit h _ _ hB rfl rfl⟩
