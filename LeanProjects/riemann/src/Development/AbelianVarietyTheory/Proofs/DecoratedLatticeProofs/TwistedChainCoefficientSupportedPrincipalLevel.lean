import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

noncomputable section

namespace GlobalTheory.TwSuppLev

theorem isSBHalf_twDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Q Z e hS hT _ _ he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hS.1 hT.1 βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem eq_of_under_eq {D : D7} {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) {PP PP' : Pl D.host.E}
    (hP : PP ∈ Z) (hP' : PP' ∈ Z) (hu : PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)) : PP' = PP := by
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h1 | h1
  · exact h1
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1) (GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hP PP' hP')

theorem gAt_mem_levG_of_supp : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → (∀ PP' ∈ L.Q, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F)) → gAt S (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG S βS L := by
  intro D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq hQu
  obtain ⟨hSt, hB, hR⟩ := GlobalTheory.T.principalPlace_component_stabilises_lattice_twisted D S T ΛS βS βT L χ ξ e hsd hfr hrk he hP g x hx hx' PP hPP huniq
  exact GlobalTheory.T.principalPlace_component_mem_level_of_reduction D S βS L hP g PP hPP (fun PP' hP' hu => huniq PP' (Finset.mem_union_left _ hP') hu) hQu hSt hB hR

theorem supp_at_principal : ∀ D : D7, ForStepQ D fun c w _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ P (g : GA D s.V), coefW p.ω m X (p.pt P) g ≠ 0 → ∀ v ∈ w.S₀, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L := by
  intro D _hgap c w hw k _hk s s' hs hs' p hp m X hX φ g hne v hv
  obtain ⟨hr, hL, hfl⟩ := hs
  obtain ⟨hr', hL', hfl'⟩ := hs'
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  have hfr' : Formalism.L2.DIV.IsFrame s'.β s'.Λ := hfl'.frame
  have hrank : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hfl.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h1, h2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : s.L.Q = w.Q := by rw [hL]; rfl
  have hPg : s.L.Pg = w.Pg := by rw [hL]; rfl
  have hPH : s.L.P.H = ⊥ := by rw [hL]; rfl
  simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
  obtain ⟨PP, hPP, rfl⟩ := hv
  by_contra hnot
  have hsupp := fun x hx => by_contra fun h => hnot
    (gAt_mem_levG_of_supp D s.V s'.V s.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ e hsd hfr hrank (hQ ▸ he) hPH g x
      (by rw [hQ]; exact hx) (by rw [hQ]; exact h) PP (hPg ▸ hPP)
      (fun PP' hP' hu => eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (hQ ▸ hP') hu)
      fun PP' hP' hu => Finset.disjoint_left.1 hw.disj hPP (by
        have hP'' : PP' ∈ w.Q := hQ ▸ hP'
        have := eq_of_under_eq he (Finset.mem_union_left _ (hPg ▸ hPP)) (Finset.mem_union_right _ hP'') hu
        subst this
        exact hP''))
  have hsb := isSBHalf_twDatum D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (w.chi (k + 1)) w.ξ w.Q (s.L.Pg ∪ w.Q) e hsd hsd' hfr hfr' he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hw.com.std s.Λ s'.Λ hsd hsd'
    (s.L.Pg ∪ w.Q) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hw.com.std hw.com.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact hne (GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2)

end GlobalTheory.TwSuppLev

end
