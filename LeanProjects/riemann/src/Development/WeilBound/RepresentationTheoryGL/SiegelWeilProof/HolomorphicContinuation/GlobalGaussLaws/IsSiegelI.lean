import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DilDSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilEH

attribute [local irreducible] famC

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have e : (-(Complex.I / 2)) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, ← sub_smul, smul_smul]
    have : -(Complex.I / 2) * (Complex.I - -Complex.I) = 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, one_smul]
  rw [e]; exact Matrix.PosDef.one

set_option maxHeartbeats 800000 in
theorem exch (hDR : DReal) (hDB : DBound) (hDC : DCalc) (hDL : DifferenceQuotientIsometryExchange) (hCD : ContDeriv) (hSS : SchScale) (hSF : SchFP)
    (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {ε : Fin V.rank → Bool} {t c : ℝ} (hc : 0 < c)
    (htc : |t| = c) {e : ℤ}
    (hG : ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε t c Z) = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y Z * gZf ε t c (actZ y Z) u)
    {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y'' : GR n) {κ : ℝ} (hκ : 0 < κ)
    (hL2 : ∀ f, IsSch f → ∫ u, ‖L y'' f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) (r : ℕ) :
    L y'' (fP c ((dil c X ^ r) 1)) = fun u => iteratedDeriv r (fun s : ℝ => famC ε t c e y'' X s u) 0 := by
  have hg0 : gZf ε t c (Complex.I • 1) = fP c (1 : PX V.rank n) := (DilAH.fP_one ε t c hc).symm
  have hg0s : IsSch (gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) : (Fin V.rank → Fin n → ℂ) → ℂ) := by
    rw [hg0]; exact hSF _ _ c hc 1
  have hbase : ∀ (y : GR n) (s : ℝ), L (y * a s) (gZf ε t c (Complex.I • 1)) = famC ε t c e y X s := by
    intro y s
    rw [hG _ _ isSiegel_I, hDR _ _ ε t c e y X a ha s]
  set Gf : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ := fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s
    with hGf
  set Ef : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ :=
    fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e y'' X s' u) s with hEf
  obtain ⟨hC1, hC2⟩ := hDC V.rank n ε t c e X hc htc
  obtain ⟨hB1, hB2, -⟩ := hDB V.rank n ε t c e X hc htc
  have hGs : ∀ r s, IsSch (Gf r s) := by
    intro r s
    have : Gf r s = fun u => (Real.exp (s * (V.rank : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j)) := by
      funext u; exact hC1 s r u
    rw [this]
    exact hSS _ _ _ s X _ (hSF _ _ c hc _)
  have hstrip : IsOpen (stripS X) := DBoundBH.isOpen_stripS X
  have hR : ∀ s : ℝ, (s : ℂ) ∈ stripS X := fun s j => by simp [div_pos Real.pi_pos]

  set F : ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun z u => famC ε t c e y'' X z u with hF
  have hFd : ∀ u, DifferentiableOn ℂ (fun z => F z u) (stripS X) := fun u => hB1 y'' u
  have hFc : ContinuousOn (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => F p.1 p.2) (stripS X ×ˢ Set.univ) := by
    have hcont : Continuous (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => ((y'', p) : GR n × (ℂ × (Fin V.rank → Fin n → ℂ)))) :=
      continuous_const.prodMk continuous_id
    exact hB2.comp hcont.continuousOn fun p hp => ⟨Set.mem_univ _, hp⟩
  have hEr : ∀ r u, (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F s' u) s) = fun s : ℝ => iteratedDeriv r (fun z => F z u) s :=
    fun r u => DilCH.iteratedDeriv_ofReal hstrip (hFd u) hR r
  have key : ∀ r s, L y'' (Gf r s) = Ef r s := by
    intro r
    induction r with
    | zero =>
      intro s
      have e1 : Gf 0 s = L (a s) (gZf ε t c (Complex.I • 1)) := by
        funext u; rw [← one_mul (a s), hbase]; simp [hGf]
      have e2 : Ef 0 s = famC ε t c e y'' X s := by funext u; simp [hEf]
      rw [e1, e2, ← DilCH.L_mul hL hθ hfr hΨ hx₀ y'' (a s) hg0s, hbase]
    | succ r ih =>
      intro s
      refine hDL V.rank n (L y'') κ hκ (fun f hf => hL.1 y'' f hf)
        (fun f g hf hg => DilCH.L_sub hL hθ hfr hΨ hx₀ y'' hf hg)
        (fun a' f hf => DilCH.L_smul hL hθ hfr hΨ hx₀ y'' a' hf) hL2 (Gf r) (Gf (r + 1) s) (Ef (r + 1) s) s
        (hGs r) (hGs (r + 1) s) ?_ (hC2 r s) ?_
      ·
        have hcd := hCD V.rank n (stripS X) hstrip F hFc hFd (r + 1)
        have : Ef (r + 1) s = fun u => iteratedDeriv (r + 1) (fun z => F z u) (s : ℂ) := by
          funext u; simp only [hEf]; rw [show (fun s' : ℝ => famC ε t c e y'' X s' u) = fun s' : ℝ => F s' u from rfl,
            congrFun (hEr (r + 1) u) s]
        rw [this]
        exact hcd.comp_continuous (f := fun u : Fin V.rank → Fin n → ℂ => ((s : ℂ), u))
          (continuous_const.prodMk continuous_id) fun u => ⟨hR s, Set.mem_univ _⟩
      · intro u
        simp only [ih]
        have hd : HasDerivAt (fun s' : ℝ => Ef r s' u) (Ef (r + 1) s u) s := by
          have e3 : (fun s' : ℝ => Ef r s' u) = fun s' : ℝ => iteratedDeriv r (fun z => F z u) s' := hEr r u
          have e4 : Ef (r + 1) s u = iteratedDeriv (r + 1) (fun z => F z u) s := congrFun (hEr (r + 1) u) s
          rw [e3, e4, iteratedDeriv_succ]
          exact ((DilCH.diffOn_iteratedDeriv hstrip (hFd u) r).differentiableAt
            (hstrip.mem_nhds (hR s))).hasDerivAt.comp_ofReal
        have := hd.tendsto_slope_zero
        refine this.congr fun h => ?_
        simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]
  have e0 : Gf r 0 = fP c ((dil c X ^ r) 1) := by
    funext u; rw [show Gf r 0 u = _ from hC1 0 r u]; simp
  rw [← e0, key r 0]

end PositivityTheory.Rg.Sw.Glob.DilEH
