import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemicharaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumRead

theorem reads_datum_eq_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT f₀ Φ f Ξ hV hSB hTh hΦ hΞ1 hΞ2
  classical
  obtain ⟨ΛS, hΛS, hΛS'⟩ := id hdS
  obtain ⟨ΛT, hΛT, hΛT'⟩ := id hdT
  obtain ⟨hRX, hRA, hRB⟩ := GlobalTheory.T.periodLatticeHalves_reps_finite_index D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa
  set SX := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSXd
  set SA := repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)
    (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSAd
  set SB := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSBd
  set MA := halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  set MB := halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  have hpx : ∀ x ∈ SX, ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x := fun x hx => by
    obtain ⟨x', hx', h⟩ := AddSubgroup.mem_map.1 (hRX.1 x hx)
    exact ⟨x', hx', h⟩
  have hpy : ∀ y ∈ SB, ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y := fun y hy => by
    obtain ⟨y', hy', h⟩ := AddSubgroup.mem_map.1 (hRB.1 y hy)
    exact ⟨y', hy', h⟩
  let px : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun x =>
    if h : ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x then h.choose else 0
  let py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun y =>
    if h : ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y then h.choose else 0
  have hpx' : ∀ x ∈ SX, px x ∈ MA ∧ embH (tauE D) δ (px x) = x := fun x hx => by
    simp only [px, dif_pos (hpx x hx)]; exact (hpx x hx).choose_spec
  have hpy' : ∀ y ∈ SB, py y ∈ MB ∧ embH (tauE D) δ (py y) = y := fun y hy => by
    simp only [py, dif_pos (hpy y hy)]; exact (hpy y hy).choose_spec
  let mt : Formalism.L2.Col.HomE D.host.E a b → Matrix (Fin T.rank) (Fin S.rank) D.host.E := fun x =>
    (LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)
  have hmt : ∀ x, toHom S T hS hT (mt x) = x := fun x => by
    simp only [mt]
    unfold toHom
    have h : ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)).reindex (finCongr hT) (finCongr hS) =
        LinearMap.toMatrix' x := by
      ext i j; simp [Matrix.reindex_apply]
    rw [h, Matrix.toLin'_toMatrix']
  let K : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - p.1) * (brk (HV sc) p.2 s)⁻¹
  have hF := GlobalTheory.T.finite_fourier_expansion_half_split_places D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx' hpy'
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hf1 : f = ∑ p ∈ SX ×ˢ SB, K p • heisO ψ S T ((mt (px p.1)).map fun r => e * incA D r)
      (heisO ψ S T ((mt (py p.2)).map fun r => cA D e * incA D r) f₀) := by
    refine GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates D ψ S T e _ f₀ Φ f _ (SX ×ˢ SB) K (fun p => (mt (px p.1)).map fun r => e * incA D r)
      (fun p => (mt (py p.2)).map fun r => cA D e * incA D r) c hc hTh ?_ ?_ ?_ ?_
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, hee]
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
    · intro p hp u hu
      exact GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT (py p.2) (hpy' _ (Finset.mem_product.1 hp).2).1 u hu
    · intro t
      rw [hF t, Finset.sum_product]

  have hV' := hV
  obtain ⟨hstd, hvac⟩ := hV'
  have h0 : IsThetaFunO ψ S T f₀ := hvac.theta
  have hψ : IsCharAF D.host.F ψ := hstd.1
  set G : VV D.what₂.Tau a b × VV D.what₂.Tau a b → WO S T := fun p =>
    GlobalTheory.VacUnique.finRat S T (mt (px p.1)) + GlobalTheory.VacUnique.finRat S T (mt (py p.2)) with hG
  set C : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    K p * (alV D.host.d sc p.1 * alV D.host.d sc p.2) with hC
  have hf2 : f = ∑ p ∈ SX ×ˢ SB, C p • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) := by
    rw [hf1]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
    rw [GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (py p.2) (hpy' _ h2').1,
      GlobalTheory.LatVac.heisO_smul,
      GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (px p.1) (hpx' _ h1).1 (py p.2) (hpy' _ h2').1,
      (hpx' _ h1).2, (hpy' _ h2').2, smul_smul, smul_smul, hC]
    congr 1
    ring
  have hf3 : f = ∑ p ∈ SX ×ˢ SB, (C p * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (GlobalTheory.VacUnique.finRat S T (mt (py p.2))))) • heisO ψ S T (G p) f₀ := by
    rw [hf2]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LatVac.heisO_heisO, smul_smul]
  have hGi : ∀ p ∈ SX ×ˢ SB, (G p).map (infPart D) = 0 := fun p _ => by
    simp only [hG, ← map_add]
    exact GlobalTheory.VacUnique.finRat_inf S T _
  refine ⟨⟨?_, fun τ => ?_⟩, ?_⟩
  · rw [hf3]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ h0 _ _ G _ hGi
  · rw [hf3]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ hP.inf f₀ h0 τ _ (hvac.fock τ) _ _ G _ hGi
  · have hread : ∀ p ∈ SX ×ˢ SB, xiN θ S T hS hT δ sc (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) =
        Formalism.L2.Th1.H.opU (HV sc) p.1 (Formalism.L2.Th1.H.opU (HV sc) p.2 (xiN θ S T hS hT δ sc f₀)) := by
      intro p hp
      obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
      have hfin : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.VacUnique.finRat S T γ) := fun γ =>
        ⟨GlobalTheory.VacUnique.finRat_inf S T γ, GlobalTheory.VacUnique.finRat_fin S T γ⟩
      have ht1 : IsThetaFunO ψ S T (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) :=
        GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.VacUnique.finRat_inf S T _) h0
      rw [GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ ht1 _ _ (hfin _), GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ h0 _ _ (hfin _),
        hmt, hmt, (hpx' _ h1).2, (hpy' _ h2').2]
    funext z
    have hlin : xiN θ S T hS hT δ sc f z = ∑ p ∈ SX ×ˢ SB, C p * xiN θ S T hS hT δ sc
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
          (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) z := by
      rw [hf2]
      simp only [xiN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hlin]
    rw [Finset.sum_congr rfl fun p hp => by rw [hread p hp]]
    show _ = xiL (HV sc) (alV D.host.d sc) 1 SX SA SB (onV (tauE D) δ Ξ) (xiN θ S T hS hT δ sc f₀) z
    rw [GlobalTheory.ThetaCosetSum.xiL_eq_kernel, Finset.sum_product]
    simp only [hC, K, Formalism.L2.Th1.H.opU, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
    ring

end GlobalTheory.AdForm.DatumRead
