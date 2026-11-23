import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPresentationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelFrobeniusNoEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoEmbeddingExtensionClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KilledPresentationExtensionFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosedStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.FrobFilt

namespace GlobalTheory.FrobFilt

theorem exists_frob_filtration : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ (r : ℕ) (Qs : Fin (r + 1) → Pres B) (Rs : Fin r → Pres B), IsZero (Qs 0).mod → (∀ i, (Rs i).r = 1) → (∀ i, Kills g (Qs i).mod) → (∀ i, Kills g (Rs i).mod) → (∀ i : Fin r, IsExt (Qs i.castSucc).mod (Qs i.succ).mod (Rs i).mod) → ∃ (Ss : Fin (r + 1) → Pres B) (Rs' : Fin r → Pres B), IsZero (Ss 0).mod ∧ (∀ i, IsFrob p (Qs i).mod (Ss i).mod) ∧ (∀ i, IsFrob p (Rs i).mod (Rs' i).mod) ∧ ∀ i : Fin r, IsExt (Ss i.castSucc).mod (Ss i.succ).mod (Rs' i).mod := by
  intro O _ _ _ p _ _ _ B hN g hg r Qs Rs h0 hr hQ hR hE
  have hRs : ∀ i, ∃ R' : Pres B, IsFrob p (Rs i).mod R'.mod :=
    fun i => GlobalTheory.T.frobenius_presentation_exists O p B g hg (Rs i) (hr i) (hR i)
  choose Rs' hRs' using hRs
  have hstep : ∀ i : Fin r, NoEmb B ((frob p B).obj (Qs i.castSucc).mod) →
      ∃ S : ShortComplex B.X.Modules, S.ShortExact ∧ Nonempty (S.X₁ ≅ (Qs i.castSucc).mod) ∧
        Nonempty (S.X₂ ≅ (Qs i.succ).mod) ∧ Nonempty (S.X₃ ≅ (Rs i).mod) ∧
        (S.map (frob p B)).ShortExact ∧ NoEmb B ((frob p B).obj S.X₂) := by
    intro i hne
    obtain ⟨S, hS, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩⟩ := hE i
    have k1 := kills_of_iso (hQ i.castSucc) e1.symm
    have k2 := kills_of_iso (hQ i.succ) e2.symm
    have k3 := kills_of_iso (hR i) e3.symm
    have hne1 : NoEmb B ((frob p B).obj S.X₁) := hne.of_iso ((frob p B).mapIso e1.symm)
    have hex := GlobalTheory.T.killed_presentation_extension_frobenius O p B hN g hg S hS ⟨Qs i.castSucc, ⟨e1⟩⟩ ⟨Qs i.succ, ⟨e2⟩⟩ ⟨Rs i, ⟨e3⟩⟩
      k1 k2 k3 hne1
    have hne3 : NoEmb B ((frob p B).obj S.X₃) :=
      (GlobalTheory.T.normal_model_frobenius_no_embedding O p B hN g hg (Rs i) (hr i) (hR i)).of_iso ((frob p B).mapIso e3.symm)
    exact ⟨S, hS, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩, hex, GlobalTheory.T.no_embedding_extension_closed O B (S.map (frob p B)) hex hne1 hne3⟩
  have key : ∀ i : Fin (r + 1), (∃ S : Pres B, IsFrob p (Qs i).mod S.mod) ∧
      NoEmb B ((frob p B).obj (Qs i).mod) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have hz := isZero_frob_obj p (B := B) h0
      refine ⟨⟨presZero B, isFrob_iff.2 ⟨isZero_presZero_mod.iso hz⟩⟩, ?_⟩
      intro U V h _ s t _
      have h1 : ∀ u : Γ((frob p B).obj (Qs 0).mod, U), u = 0 := fun u => by
        have := congrArg (fun φ => φ.app U u) (hz.eq_of_src (𝟙 _) 0)
        simpa using this
      rw [h1 s, h1 t]
    | succ i ih =>
      obtain ⟨⟨S0, hS0⟩, hne⟩ := ih
      obtain ⟨S, -, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩, hex, hne2⟩ := hstep i hne
      obtain ⟨f0⟩ := isFrob_iff.1 hS0
      obtain ⟨f3⟩ := isFrob_iff.1 (hRs' i)
      obtain ⟨P, ⟨eP⟩⟩ := GlobalTheory.T.presentation_extension_closed O p B (S.map (frob p B)) hex
        ⟨S0, ⟨(frob p B).mapIso e1 ≪≫ f0.symm⟩⟩ ⟨Rs' i, ⟨(frob p B).mapIso e3 ≪≫ f3.symm⟩⟩
      exact ⟨⟨P, isFrob_iff.2 ⟨eP.symm ≪≫ (frob p B).mapIso e2⟩⟩, hne2.of_iso ((frob p B).mapIso e2)⟩
  choose Ss hSs using fun i => (key i).1
  refine ⟨Ss, Rs', ?_, hSs, hRs', fun i => ?_⟩
  · obtain ⟨f⟩ := isFrob_iff.1 (hSs 0)
    exact (isZero_frob_obj p (B := B) h0).of_iso f
  · obtain ⟨S, -, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩, hex, -⟩ := hstep i (key i.castSucc).2
    obtain ⟨f1⟩ := isFrob_iff.1 (hSs i.castSucc)
    obtain ⟨f2⟩ := isFrob_iff.1 (hSs i.succ)
    obtain ⟨f3⟩ := isFrob_iff.1 (hRs' i)
    exact ⟨S.map (frob p B), hex, ⟨(frob p B).mapIso e1 ≪≫ f1.symm⟩, ⟨(frob p B).mapIso e2 ≪≫ f2.symm⟩,
      ⟨(frob p B).mapIso e3 ≪≫ f3.symm⟩⟩

end GlobalTheory.FrobFilt
