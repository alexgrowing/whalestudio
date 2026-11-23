import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocBrOfAutSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

set_option maxHeartbeats 2000000 in

theorem locAll_exists : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (AutSpec A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  intro hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi hO hBU big
  obtain ⟨X, T, ⟨Sp⟩⟩ := GlobalTheory.T.side_rational_eigen_data hGAR GlobalTheory.HeckeStdFacts.heckeStdPlain D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hO hpsi big
  obtain ⟨Y, Cb, ⟨aut⟩⟩ := GlobalTheory.T.side_rational_level_data hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi big X T Sp
  obtain ⟨Br, -⟩ := locBr_of_autSpec D cf jE A M C tp.tup big X T Sp Y Cb aut
  have hchi := GlobalTheory.T.side_rational_character_data hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  have hMt := MtIndep.typeV_iSup_indep D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  obtain ⟨Z, hbc, hrb, hmt, hss⟩ := locTy_exists D A.row A.pl X Y hBU hCheb aut.locW aut.iotaQC aut.kFbar Sp.heckeLoc_gamma_places hchi hMt
  exact ⟨{ X := X, T := T, Y := Y, C := Cb, Z := Z, B := Br, bc_tie := hbc, rbar_tie := hrb, mtpar_tie := hmt }, Sp, ⟨aut⟩, hss⟩

end GlobalTheory.HeightCounting

end
