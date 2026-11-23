import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverPStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeNotStable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhereStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationInverseHalfDifferentEqOneUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffPrimeKernelLatticesOfAgreeAwayStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdeleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAwayStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.AwayInd

set_option maxHeartbeats 4000000 in

theorem away_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → S.Pos → S.Pair → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hK hPos hPair
  intro v j hj
  have hgood := J.one.good
  have hint := J.one.int
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  obtain ⟨hcop, hSS, -, -⟩ := GlobalTheory.T.level_badPrimes_coprime_residueChar S hDict hSpl
  obtain ⟨P, hPof, happ, hpP, hpP2⟩ := GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP _ _ _ _ _ (A0 J) hint hSpl.1 v
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.XcSplit.prime_not_stable _ _ (sigD D) _ _ _ (A0 J) _ hgood hint hSpl.1 v P hPof
  have hpC : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, map_natCast]; exact hpP
  have hcopE : IsCoprime (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) := by
    have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
    simpa using h
  have hlev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hpQ hlQ
    obtain ⟨x, y, hxy⟩ := hcopE
    have h1 : (1 : 𝓞 D.host.E) ∈ Q.asIdeal := hxy ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left x hlQ) (Q.asIdeal.mul_mem_left y hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hab' : (b : D.host.E) = D.host.conj (a : D.host.E) := by
    rw [hab]
    first | exact Formalism.L2.PairingIndexBounds.F.sig_conj D _ | exact Formalism.L2.Fam.sig_eq_conj D.host D.sp.cm _ | exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  refine ⟨P, ⟨a, b, hab', ha, hb⟩, GlobalTheory.T.localisation_inverseHalfDifferent_eq_one_unramified D _ hp P hpP hpP2, fun h => hSS P h hpP, fun h => hSS _ h hpC,
    hlev P hpP, hlev _ hpC, hPof, happ, ?_⟩
  by_cases hc : Nonempty ((sysS H X std).Lv.comp j) ∧ Nonempty ((sysS H X std).Lv.comp (j + 1))
  · obtain ⟨⟨c⟩, ⟨c'⟩⟩ := hc
    obtain ⟨π, hπU, hoff, hord⟩ := GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere _ _ (sigD D) _ _ _ (A0 J) _ hgood v
    have hU : IsUnifAt J v π := ⟨hπU, hoff, hord⟩
    obtain ⟨x, y, hx0, hy0, hx, hy⟩ := GlobalTheory.T.two_units_at_place_uniformizing_idele S hDict hSpl hK hPos v π hU j hj c c'
    refine ⟨x, y, hx0, hy0, ?_⟩
    intro La Lb La' Lb' h1 h2 h3 h4 haw
    have e1 : La.1 = Lb.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.1) haw
    have e2 : Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.2) haw
    have e3 : La'.1 = Lb'.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.1) haw
    have e4 : Function.update La'.2 ((sysS H X std).vJ (j + 1) v) ⊥ = Function.update Lb'.2 ((sysS H X std).vJ (j + 1) v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.2) haw
    have hA : SameAway (hT := hT) (H := H) (X := X) std v j La Lb := ⟨h1, h3, e1, e2⟩
    have hA' : SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' := ⟨h2, h4, e3, e4⟩
    refine ⟨GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof j hj.le La Lb hA, GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof (j + 1) hj La' Lb' hA', ?_, ?_,
      GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway S hDict hSpl v j hj La Lb La' Lb' hA hA', GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace S hDict hSpl hPair v π hU j hj x y hx hy La Lb La' Lb' hA hA'⟩
    · have hLb : Lb = (La.1, Lb.2) := Prod.ext e1.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl j La.1 La.2 Lb.2
    · have hLb : Lb' = (La'.1, Lb'.2) := Prod.ext e3.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl (j + 1) La'.1 La'.2 Lb'.2
  · have h1 : (sysS H X std).vEqK 1 0 := GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb 1 (by simp)
    refine ⟨1, 1, h1, h1, ?_⟩
    intro La Lb La' Lb'
    exact absurd ⟨⟨La.1⟩, ⟨La'.1⟩⟩ hc

end GlobalTheory.TwV.Xc.AwayInd
