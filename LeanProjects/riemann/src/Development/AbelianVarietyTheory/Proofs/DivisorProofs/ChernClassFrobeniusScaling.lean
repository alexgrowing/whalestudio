import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkPresentationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationFlagFiltrationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationChernClassAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusChernClassScalingStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagFrob

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime]
  [CharZero O] [CharP (ResidueField O) p] {B : GlobalTheory.Vert.Model O}

theorem nonempty_iso_of_isFrob {F F' G G' : B.X.Modules} (h : IsFrob p F G) (h' : IsFrob p F' G')
    (e : Nonempty (F ≅ F')) : Nonempty (G ≅ G') := by
  obtain ⟨hp, ⟨a⟩⟩ := h
  obtain ⟨hp', ⟨b⟩⟩ := h'
  obtain ⟨e⟩ := e
  exact ⟨a ≪≫ (Scheme.Modules.pushforward _).mapIso ((Scheme.Modules.pullback _).mapIso e) ≪≫ b.symm⟩

theorem ck_eq_zero_of_isZero (hB : GlobalTheory.IsNormalScheme B.X) (T : Pres B) (hT : IsZero T.mod) (k : ℕ) :
    T.ck p k = 0 := by
  have hE : IsExt T.mod T.mod T.mod :=
    ⟨ShortComplex.mk (0 : T.mod ⟶ T.mod) (0 : T.mod ⟶ T.mod) (by simp),
      { exact := ShortComplex.exact_of_isZero_X₂ _ hT, mono_f := hT.mono _, epi_g := hT.epi _ },
      ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  have h := congrArg (· - T.ck p k) (GlobalTheory.T.ck_additive_extension O p B hB T T T hE k)
  simpa using h.symm

theorem ck_last_eq_sum (hB : GlobalTheory.IsNormalScheme B.X) (r : ℕ) (T : Fin (r + 1) → Pres B) (U : Fin r → Pres B)
    (h0 : IsZero (T 0).mod) (hE : ∀ i : Fin r, IsExt (T i.castSucc).mod (T i.succ).mod (U i).mod) (k : ℕ) :
    (T (Fin.last r)).ck p k = ∑ i, (U i).ck p k := by
  have key : ∀ j : ℕ, (hj : j ≤ r) →
      (T ⟨j, by omega⟩).ck p k = ∑ i : Fin r, if (i : ℕ) < j then (U i).ck p k else 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using ck_eq_zero_of_isZero hB (T 0) h0 k
    | succ j ih =>
      intro hj
      have h := GlobalTheory.T.ck_additive_extension O p B hB _ _ _ (hE ⟨j, by omega⟩) k
      simp only [Fin.succ_mk, Fin.castSucc_mk] at h
      rw [h, ih (by omega)]
      have hs : (∑ i : Fin r, if (i : ℕ) < j + 1 then (U i).ck p k else 0) =
          (∑ i : Fin r, if (i : ℕ) < j then (U i).ck p k else 0) +
            ∑ i : Fin r, if (⟨j, by omega⟩ : Fin r) = i then (U i).ck p k else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Fin.ext_iff]
        split_ifs <;> first | omega | simp
      rw [hs, Finset.sum_ite_eq]
      simp
  refine (key r le_rfl).trans ?_
  simp

end

theorem ck_frob_of_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P P' : Pres B) (g : Γ(B.X, ⊤)), IsRootOfP p g p → Kills g P.mod → IsFrob p P.mod P'.mod → (haveI := P.iso; Nonempty (GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r)) → ∀ k : ℕ, P'.ck p k = ((p : ℚ) ^ k) • P.ck p k := by
  intro O _ _ _ p _ _ _ B hB P P' g hg hK hF hFP k
  obtain ⟨Qs, Rs, h0, ⟨eQ⟩, hr, hKQ, hKR, hE⟩ := GlobalTheory.T.presentation_flag_filtration_exists O p B hB P g hK hFP
  obtain ⟨Ss, Rs', h0', hFS, hFR, hE'⟩ := GlobalTheory.T.filtration_chern_class_additive O p B hB g hg P.r Qs Rs h0 hr hKQ hKR hE
  obtain ⟨eS⟩ := nonempty_iso_of_isFrob (hFS (Fin.last _)) hF ⟨eQ⟩
  rw [GlobalTheory.T.ck_presentation_invariant O p B hB P' (Ss (Fin.last _)) ⟨eS.symm⟩ k,
    GlobalTheory.T.ck_presentation_invariant O p B hB P (Qs (Fin.last _)) ⟨eQ.symm⟩ k,
    ck_last_eq_sum hB _ Ss Rs' h0' hE' k, ck_last_eq_sum hB _ Qs Rs h0 hE k, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.T.frobenius_chern_class_scaling O p B hB (Rs i) (Rs' i) g hg (hr i) (hKR i) (hFR i) k

end GlobalTheory.FlagFrob

end
