import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemPeriodLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImageStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.SeamKer

open Formalism.L2.Th1.H

variable {D : D7} {X : Fields}

def seamT (s : Seam D X) (a b : ℕ) : VV D.what₂.Tau a b ≃+ VV X.Tau a b where
  toFun v := fun τ => v (s.iT τ)
  invFun w := fun τ => w (s.iT.symm τ)
  left_inv v := by funext τ; simp
  right_inv w := by funext τ; simp
  map_add' _ _ := rfl

theorem HV_seamT (s : Seam D X) {a b : ℕ} (sc : ℝ) (x y : VV D.what₂.Tau a b) :
    HV sc (seamT s a b x) (seamT s a b y) = HV sc x y := by
  show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, x (s.iT τ) i j * (starRingEnd ℂ) (y (s.iT τ) i j)) =
    (sc : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT (fun τ' => ∑ i, ∑ j, x τ' i j * (starRingEnd ℂ) (y τ' i j))]

theorem alV_seamT (s : Seam D X) {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV D.what₂.Tau a b) :
    alV d sc (seamT s a b x) = alV d sc x := by
  have h := HV_seamT s sc x x
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf, h]

theorem seam_kerTh : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  intro D X s hs cc δ B χ cD a b SS cl N N' Ξ hcc hδ hδ0 hVec hcl hSS hA hDat
  classical
  have hyp := KerMove.split_of_adm _ cl (s.lat N) (s.lat N') B hcc hδ hδ0 hA hcl hSS
  have hI := KerMove.finIdx_of_adm (cc := cc) (δ := δ) (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') hA hcl
  have hθ := KerMove.eNat_fixed (s.lat N) (s.lat N') B χ hcc hδ hVec hA
  have := KerMove.tau_nonempty D
  have hΦ := hDat.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
  have hper := GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff s hs B χ cD SS cl N N'
  have hemb := GlobalTheory.T.complexCoordinates_columnFieldIdentification s hs δ (a := a) (b := b)
  have hexp := GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism s hs SS
  have hΛ := hemb.2.2.1 _ _ hper
  have hAh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (fun Q => -expS SS Q)
    (fun Q => -expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) Q)
    (fun P => by simp only [hexp]))
  have hBh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (expS SS)
    (expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) hexp)
  have hdat : onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) = fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v) :=
    funext fun v => (hemb.2.2.2 hδ0 Ξ v).symm
  have hvec : B.eNat χ a b (s.lat N) (s.lat N') = fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v) := by
    funext v
    show B.eNat χ a b (s.lat N) (s.lat N') v = B.eNat χ a b (s.lat N) (s.lat N') (fun τ => v (s.iT (s.iT.symm τ)))
    simp only [Equiv.apply_symm_apply]
  have hθ' : (fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v)) ∈ fixedBy _ _ _ := hvec ▸ hθ
  have hΦ' : InvOn _ _ (fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v)) := hdat ▸ hΦ
  funext z
  unfold Seam.push kerTh thC xiV
  rw [hdat, hvec]
  exact GlobalTheory.T.xiL_two_alt _ _ _ _ (seamT s a b) (HV_seamT s _) (alV_seamT s _ _) _ _ _ _ _ _ hyp hΛ hAh hBh
    ⟨_, repsOf_spec _ _ hI.1⟩ ⟨_, repsOf_spec _ _ hI.2.1⟩ ⟨_, repsOf_spec _ _ hI.2.2⟩ 1 _ _ hθ' hΦ' z

end GlobalTheory.TwU.SeamKer
