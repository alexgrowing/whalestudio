import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSiegelI
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivStep
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchange
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DHol
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilH

instance fcGR (n : ℕ) : FirstCountableTopology (GR n) := by
  have h1 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
  have h2 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph.symm.isInducing).firstCountableTopology
  exact (Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal).firstCountableTopology

theorem iteratedDeriv_mul_const (f : ℂ → ℂ) (k : ℂ) (r : ℕ) :
    iteratedDeriv r (fun w => f w * k) = fun w => iteratedDeriv r f w * k := by
  induction r with
  | zero => simp
  | succ r ih => rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]; exact deriv_mul_const_field' k

theorem isSiegel_Ir {n : ℕ} {r : ℝ} (hr : 0 < r) :
    IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
      IsSiegel (((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by
  have hc : ((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (Complex.I * r) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_neg, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal]
    ring_nf
  rw [hc]
  have : IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul, smul_smul]
    have e : -(Complex.I / 2) * (Complex.I * r - star (Complex.I * r)) = (r : ℂ) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring_nf; rw [Complex.I_sq]; ring
    rw [e]
    exact Matrix.PosDef.one.smul (by exact_mod_cast hr)
  exact ⟨this, this⟩

end PositivityTheory.Rg.Sw.Glob.DilH

namespace PositivityTheory.Rg.Sw.Glob

attribute [local irreducible] famC

set_option maxHeartbeats 1000000 in
open DilAH DilCH DilEH DilH in
theorem gIdil_of' (hWTC : GlobalTheory.Published.WeilThetaConvergence) (hDecA : DecompAway) (hAway : AwayAct) (hLF : LocFact)
    (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) (hSF : SchFP) (hLNe : LNe) (hDC : DCalc) : GIdil := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨA g X a ha
  have hl0 : ∀ τ', l τ' ≠ 0 := hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hc : 0 < cLoc l τ := cLoc_pos (hl0 τ)
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hfr : IsUnit fr.det := hcx.hfr.1
  have hΨ : AwayCls θ τ fr Ψ := hAI D n V θ l s τ ε fr hcx.hθ hcx.hs hcx.hfr hl0 Ψ hΨA
  obtain ⟨L, hL⟩ := hLF D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨e, hG⟩ := hGL D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨x, y₀, hxt, hg, -⟩ := hDecA D n θ τ ι hcx.hθ hcx.hι g
  obtain ⟨A, hA⟩ := hAway D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx x hxt
  obtain ⟨hAΨ, hAact⟩ := hA Ψ hΨ
  have hsch1 : ∀ P : PX V.rank n, IsSch (fP (cLoc l τ) P) := fun P => hSF _ _ _ hc P
  obtain ⟨hB1, hB2, hB3⟩ := dBound V.rank n ε (tLoc l τ) (cLoc l τ) e X hc htc
  have hfam : ∀ (y : GR n) (z : ℂ), z ∈ stripS X → IsSch (famC ε (tLoc l τ) (cLoc l τ) e y X z) := by
    intro y z hz
    obtain ⟨h1, h2, -, -⟩ := dSieg n y X z hz
    unfold famC
    exact SchwartzDifferenceQuotient.isSch_smul _ (gCSch V.rank n ε _ _ hc htc _ _ h1 h2)
  have hphi : ∀ P : PX V.rank n, phiS θ τ fr (cLoc l τ) Ψ P = ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ := by
    intro P; unfold phiS; rw [dif_pos (hΨ.2 _ (hsch1 P))]
  have hω : ∀ (y : GR n) (P : PX V.rank n), (ω (g * ι y) (phiS θ τ fr (cLoc l τ) Ψ P)).1 =
      tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) (A Ψ) := by
    intro y P
    have h1 : ω (ι (y₀ * y)) ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ =
        ⟨tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) Ψ, hΨ.2 _ (hL.1 _ _ (hsch1 P))⟩ :=
      Subtype.ext (hL.2 _ Ψ hΨ _ (hsch1 P))
    rw [hg, mul_assoc, ← map_mul ι, map_mul ω, Module.End.mul_apply, hphi, h1]
    exact hAact _ (hL.1 _ _ (hsch1 P))
  have hbase : ∀ (y : GR n) (s' : ℝ), L (y * a s') (fP (cLoc l τ) 1) = famC ε (tLoc l τ) (cLoc l τ) e y X s' := by
    intro y s'
    rw [fP_one ε (tLoc l τ) _ hc, hG _ _ isSiegel_I, dReal _ _ ε _ _ e y X a ha s']
  have hR : ∀ s' : ℝ, (s' : ℂ) ∈ stripS X := fun s' j => by simp [div_pos Real.pi_pos]
  have hAc : Continuous (A Ψ) := FTH.cont_of_away hcx.hθ hAΨ
  set φ : GR n → ℂ → Mx D V.rank n → ℂ := fun y z xx => tens θ τ fr (famC ε (tLoc l τ) (cLoc l τ) e (y₀ * y) X z) (A Ψ) xx
    with hφ
  have hs1 : ∀ y z, z ∈ stripS X → φ y z ∈ schwartzA θ V.rank n := fun y z hz => hAΨ.2 _ (hfam _ z hz)
  have hs2 : ∀ y xx, DifferentiableOn ℂ (fun z => φ y z xx) (stripS X) := fun y xx =>
    (hB1 (y₀ * y) _).mul_const _
  have hcu : Continuous fun xx : Mx D V.rank n => fr⁻¹ * compAt θ τ xx :=
    continuous_const.matrix_mul (GlobalTheory.RealWeil.continuous_compAt hcx.hθ τ V.rank n)
  have hs3 : ∀ xx, ContinuousOn (fun p : GR n × ℂ => φ p.1 p.2 xx) (Set.univ ×ˢ stripS X) := by
    intro xx
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2, fr⁻¹ * compAt θ τ xx) := by fun_prop
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.2, Set.mem_univ _⟩) continuousOn_const
  have hs4 : ∀ y, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ y zx.1 zx.2) (stripS X ×ˢ Set.univ) := by
    intro y
    have hm : Continuous fun zx : ℂ × Mx D V.rank n => (y₀ * y, zx.1, fr⁻¹ * compAt θ τ zx.2) :=
      continuous_const.prodMk (continuous_fst.prodMk (hcu.comp continuous_snd))
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.1, Set.mem_univ _⟩)
      (hAc.comp continuous_snd).continuousOn
  have hs5 : ∀ (p₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      M ∈ schwartzA θ V.rank n ∧ ∀ pz ∈ N, pz.2 ∈ stripS X → ∀ xx, ‖φ pz.1 pz.2 xx‖ ≤ ‖M xx‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N', δ, C, hN', hδ, hbd⟩ := hB3 (y₀ * p₀) z₀ hz₀
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2) := by fun_prop
    have hdc : 0 < δ / cLoc l τ := div_pos hδ hc
    obtain ⟨hS1, hS2⟩ := isSiegel_Ir (n := n) hdc
    have hgs := gCSch V.rank n ε _ _ hc htc _ _ hS1 hS2
    refine ⟨(fun p : GR n × ℂ => (y₀ * p.1, p.2)) ⁻¹' N', tens θ τ fr (fun u => ((max C 0 : ℝ) : ℂ) *
      gC ε (tLoc l τ) (cLoc l τ) ((Complex.I * ((δ / cLoc l τ : ℝ) : ℂ)) • 1) ((-(Complex.I * ((δ / cLoc l τ : ℝ) : ℂ))) • 1) u) (A Ψ),
      hm.continuousAt.preimage_mem_nhds hN', hAΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul _ hgs), fun pz hpz hz xx => ?_⟩
    have hb := hbd _ hpz hz (fr⁻¹ * compAt θ τ xx)
    simp only [hφ, tens, norm_mul]
    have hgg := gC_gauss ε (tLoc l τ) (cLoc l τ) hc δ (fr⁻¹ * compAt θ τ xx)
    rw [hgg]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)]
    have he : ∀ r : ℝ, ‖Complex.exp (-(r : ℂ))‖ = Real.exp (-r) := fun r => by
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le))
      (norm_nonneg _)
  obtain ⟨hcont, hdiff, hiter⟩ := dHol hWTC D n V hcx.hn hcx.hr.2.2 θ hcx.hθ ν hcx.hν (GR n) (stripS X)
    (DBoundBH.isOpen_stripS X) φ hs1 hs2 hs3 hs4 hs5
  refine ⟨stripS X, fun y z => ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν,
    DBoundBH.isOpen_stripS X, hR, hcont, fun y => ⟨hdiff y, fun t' => ?_, fun r => ?_⟩⟩
  ·
    have hfun : (ω (g * ι (y * a t')) (phiS θ τ fr (cLoc l τ) Ψ 1)).1 = φ y t' := by
      rw [hω, ← mul_assoc, hbase]
    have key : (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ 1) (g * ι (y * a t')) := by
      funext h; unfold theta; rw [hfun]; rfl
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) = _
    rw [key]; rfl
  ·
    rw [hiter y r 0 (hR 0)]
    have hpt : ∀ xx : Mx D V.rank n, iteratedDeriv r (fun w => φ y w xx) 0 =
        tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) ((dil (cLoc l τ) X ^ r) 1))) (A Ψ) xx := by
      intro xx
      simp only [hφ, tens]
      rw [iteratedDeriv_mul_const]
      beta_reduce
      by_cases hz : ∃ x₀, Ψ x₀ ≠ 0
      · obtain ⟨x₀, hx₀⟩ := hz
        obtain ⟨κ, hκ, hκL⟩ := hLL2 D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL (y₀ * y)
        have hofR := congrFun (iteratedDeriv_ofReal (DBoundBH.isOpen_stripS X)
          (hB1 (y₀ * y) (fr⁻¹ * compAt θ τ xx)) hR r) 0
        simp only [Complex.ofReal_zero] at hofR
        rw [← hofR, exch dReal dBound hDC dL2 contDeriv schScale hSF hL hcx.hθ hfr hΨ hx₀ hc htc hG ha (y₀ * y) hκ hκL r]
      · push_neg at hz
        have hΨ0 : Ψ = 0 := funext hz
        have h0 : tens θ τ fr (fP (cLoc l τ) 1) (A Ψ) = 0 := by
          rw [← hAact _ (hsch1 1)]
          have : (⟨tens θ τ fr (fP (cLoc l τ) 1) Ψ, hΨ.2 _ (hsch1 1)⟩ : schwartzA θ V.rank n) = 0 :=
            Subtype.ext (by funext x'; simp [tens, hΨ0])
          rw [this, map_zero]; rfl
        have hAx : A Ψ xx = 0 := by
          have := congrFun h0 xx
          simp only [tens, Pi.zero_apply] at this
          refine (mul_eq_zero.1 this).resolve_left ?_
          simp [fP, evX, gs, Complex.exp_ne_zero]
        rw [hAx, mul_zero, mul_zero]
    have key : (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ ((dil (cLoc l τ) X ^ r) 1)) (g * ι y) := by
      funext h; unfold theta; rw [hω]
      congr 1; funext ξ; exact hpt _
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) q
      ∂autMeasure V ν) = _
    rw [key]; rfl

theorem gIdil_of (hWTC : GlobalTheory.Published.WeilThetaConvergence) (_hGZ : GZSch) (hDecA : DecompAway) (hAway : AwayAct)
    (hLF : LocFact) (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) : GIdil :=
  gIdil_of' hWTC hDecA hAway hLF hGL hAI hLL2 schFP lNe dCalc

end PositivityTheory.Rg.Sw.Glob
