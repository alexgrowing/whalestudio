import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermCocompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {n : ℕ}

def SplitTauP : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι →
    ∀ g : G D n, ∃ (y : GR n) (x : G D n), g = ι y * x ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def NbTauP : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n),
    IsCharAF D.host.F ψ → IsInfFam θ → IsPlaceEmb θ τ ι → ∀ (nb : hermA D n → G D n), PositivityTheory.PfSWUS.IsNMap nb →
    ∀ (nb' : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb' x) = nU (herm x)) →
      (∀ x, ∃ b : hermA D n, ι (nb' x) = nb b) ∧
      ∀ β : HermE D n, ∃ β' : Matrix (Fin n) (Fin n) ℂ, β'.IsHermitian ∧ (β.1.det = 0 → β'.det = 0) ∧
        ∀ x (b : hermA D n), ι (nb' x) = nb b →
          ψ (halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) = eTr β' x

def ChiPer : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (β : HermE D n), ∀ l ∈ ratHerm D n,
    ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) l.1 : Mx D n n))) = 1

namespace LamSingH

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.one_mul]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

def toGR (M : M2 n) (hM : InG M) : GR n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by
      intro h0
      have e := congrArg Matrix.det hM
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
      have hJ : (JJ n).det ≠ 0 := by
        intro hJ0
        have h1 : JJ n * JJ n = -1 := by
          rw [JJ, Matrix.fromBlocks_multiply]
          simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
            Matrix.one_mul]
          rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
        have := congrArg Matrix.det h1
        rw [Matrix.det_mul, hJ0, zero_mul] at this
        simp [Matrix.det_neg] at this
      exact hJ e.symm), hM⟩

theorem mR_toGR (M : M2 n) (hM : InG M) : mR (toGR M hM) = M := rfl

theorem toGR_mR (y : GR n) : toGR (mR y) y.2 = y := by
  apply Subtype.ext; apply Units.ext; rfl

theorem mR_mul (y y' : GR n) : mR (y * y') = mR y * mR y' := rfl

end LamSingH

open LamSingH

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem gLsing_core (hFZ : FourierZeroN) (hTS : TwoSided) (hD : DenseTau) (hCD : PositivityTheory.PfSWUS.CoefDataExists)
    (hNb : NbFacts) (hCh : CharFacts) (hCo : HermCocompact) (hSp : SplitTauP) (hNt : NbTauP) (hPer : ChiPer) :
    GLsing := by
  classical
  intro D n ψ θ τ ι hψ hθ hι F hFc hF hΛ ψ₀ hψ₀ nb' hnb' g a b
  obtain ⟨nb, lam, 𝓖, hcd⟩ := hCD D n
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hcd
  obtain ⟨hcont, hadd, hrat⟩ := hNb D n nb hnb
  obtain ⟨hbx0, hchar⟩ := hNt D n ψ θ τ ι hψ hθ hι nb hnb nb' hnb'
  choose bx hbx using hbx0
  obtain ⟨K, hK, hKc⟩ := hCo D n
  obtain ⟨hψ₀c, hψ₀s, hψ₀F⟩ := hψ₀
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin n) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin n → Fin n → D.host.E))
  have hmem : ∀ q : ratHerm D n, q.1.1 ∈ ratMx D n n := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D n) := by
    choose g hg using fun q : ratHerm D n => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hlam
  have hιc : Continuous ι := hι.1

  have hnb'c : Continuous nb' := by
    have hv : Continuous fun x => ((nb' x : GL (Fin n ⊕ Fin n) ℂ) : M2 n) := by
      have e : (fun x => ((nb' x : GL (Fin n ⊕ Fin n) ℂ) : M2 n)) = fun x => nU (herm x) := funext hnb'
      rw [e]
      refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [herm]
      fun_prop
    have hinv : ∀ x, (((nb' x : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = nU (-herm x) := by
      intro x
      apply Units.inv_eq_of_mul_eq_one_right
      change mR (nb' x) * nU (-herm x) = 1
      rw [hnb' x, nU, nU, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul, zero_add, Matrix.mul_neg,
        add_neg_cancel, neg_add_cancel, neg_zero]
      exact (Matrix.fromBlocks_one : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = (1 : M2 n))
    have hi : Continuous fun x => (((nb' x : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) := by
      rw [funext hinv]
      refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [herm, Pi.neg_apply, Matrix.neg_apply]
      fun_prop
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨hv, hi⟩) _
  have hcomm : ∀ x c, ι (nb' x) * nb c = nb c * ι (nb' x) := by
    intro x c
    rw [hbx x, ← hadd, ← hadd, add_comm]
  have hper : ∀ (g' : G D n) (c : hermA D n), ∃ k ∈ K, F (nb c * g') = F (nb k * g') := by
    intro g' c
    obtain ⟨l, hl, hcl⟩ := hKc c
    refine ⟨c - l, hcl, ?_⟩
    have e : nb c = nb l * nb (c - l) := by rw [← hadd, add_sub_cancel]
    rw [e, mul_assoc, hF _ (hrat l hl)]

  have hA : ∀ g' : G D n, ∫ x, F (ι (nb' x) * g') * ψ₀ x = 0 := by
    set h : G D n → ℂ := fun g' => ∫ x, F (ι (nb' x) * g') * ψ₀ x with hdef
    have hΦc : Continuous fun z : G D n × (Fin n → Fin n → ℝ) => F (ι (nb' z.2) * z.1) :=
      hFc.comp ((hιc.comp (hnb'c.comp continuous_snd)).mul continuous_fst)
    have hint : ∀ g', Integrable (fun x => F (ι (nb' x) * g') * ψ₀ x) := fun g' =>
      (((hFc.comp ((hιc.comp hnb'c).mul continuous_const))).mul hψ₀c).integrable_of_hasCompactSupport
        (hψ₀s.mul_left)
    have hhc : Continuous h := by
      rw [continuous_iff_continuousAt]
      intro g0
      rw [Metric.continuousAt_iff']
      intro ε hε
      set c1 : ℝ := ∫ x, ‖ψ₀ x‖ with hc1
      have h0 : 0 ≤ c1 := integral_nonneg fun x => norm_nonneg _
      set c0 : ℝ := c1 + 1 with hc0
      have hc0p : 0 < c0 := by linarith
      set δ := ε / c0
      have hδ : 0 < δ := div_pos hε hc0p
      have hev : ∀ᶠ g' in nhds g0, ∀ x ∈ tsupport ψ₀, ‖F (ι (nb' x) * g') - F (ι (nb' x) * g0)‖ < δ := by
        refine hψ₀s.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
        have h1 := (hΦc.tendsto (g0, x)).eventually (Metric.ball_mem_nhds _ (half_pos hδ))
        have h2 := ((hΦc.comp (Continuous.prodMk continuous_const continuous_snd : Continuous
          fun z : G D n × (Fin n → Fin n → ℝ) => (g0, z.2))).tendsto (g0, x)).eventually
            (Metric.ball_mem_nhds _ (half_pos hδ))
        filter_upwards [h1, h2] with z hz1 hz2
        simp only [Metric.mem_ball, dist_eq_norm, Function.comp] at hz1 hz2
        calc ‖F (ι (nb' z.2) * z.1) - F (ι (nb' z.2) * g0)‖
            ≤ ‖F (ι (nb' z.2) * z.1) - F (ι (nb' x) * g0)‖ + ‖F (ι (nb' x) * g0) - F (ι (nb' z.2) * g0)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add hz1 (by rw [norm_sub_rev]; exact hz2)
          _ = δ := add_halves δ
      filter_upwards [hev] with g' hg'
      rw [dist_eq_norm]
      simp only [hdef]
      rw [← integral_sub (hint g') (hint g0)]
      have hbd : ∀ x, ‖F (ι (nb' x) * g') * ψ₀ x - F (ι (nb' x) * g0) * ψ₀ x‖ ≤ δ * ‖ψ₀ x‖ := by
        intro x
        rw [← sub_mul, norm_mul]
        by_cases hx : x ∈ tsupport ψ₀
        · exact mul_le_mul_of_nonneg_right (hg' x hx).le (norm_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]
      calc ‖∫ x, (F (ι (nb' x) * g') * ψ₀ x - F (ι (nb' x) * g0) * ψ₀ x)‖
          ≤ ∫ x, δ * ‖ψ₀ x‖ := norm_integral_le_of_norm_le ((hψ₀c.norm.integrable_of_hasCompactSupport
              hψ₀s.norm).const_mul δ) (Filter.Eventually.of_forall hbd)
        _ = δ * ∫ x, ‖ψ₀ x‖ := integral_const_mul _ _
        _ < δ * c0 := mul_lt_mul_of_pos_left (by linarith) hδ
        _ = ε := div_mul_cancel₀ ε hc0p.ne'
    have hinv : ∀ b0 : hermA D n, (∃ β : HermE D n, b0.1 = β.1.map (incA D)) → ∀ g', h (nb b0 * g') = h g' := by
      rintro b0 ⟨β, hβ⟩ g'
      have hb0 : b0 ∈ ratHerm D n := ⟨β.1, hβ.symm⟩
      simp only [hdef]
      congr 1
      funext x
      rw [← mul_assoc, hcomm x b0, mul_assoc, hF _ (hrat b0 hb0)]
    have hcoef : ∀ β g', PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb h β g' = 0 := by
      intro β g'
      obtain ⟨β'', hβh, hβdet, hβchar⟩ := hchar β
      obtain ⟨hχc, hχn⟩ := hCh D n ψ hψ β
      set χ : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))
        with hχ
      have hχadd : ∀ u v, χ (u + v) = χ u * χ v := by
        intro u v
        simp only [hχ, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, halfTr, map_add, mul_add, neg_add]
        exact AddChar.map_add_eq_mul ψ _ _
      have hχper : ∀ l ∈ ratHerm D n, ∀ b, χ (l + b) = χ b := by
        intro l hl b
        have h1 : χ l = 1 := hPer D n ψ hψ β l hl
        rw [hχadd, h1, one_mul]
      have hχneg : ∀ x, χ (-(bx x)) = eTr β'' x := by
        intro x
        rw [← hβchar x (bx x) (hbx x)]
        simp only [hχ, AddSubgroup.coe_neg, Matrix.mul_neg, Matrix.trace_neg, halfTr, map_neg, mul_neg, neg_neg]
      obtain ⟨M, hM⟩ : ∃ M, ∀ c : hermA D n, ‖F (nb c * g')‖ ≤ M := by
        obtain ⟨M, hM⟩ := (hK.image (hcont.mul continuous_const : Continuous fun c => nb c * g')).exists_bound_of_continuousOn
          hFc.continuousOn
        refine ⟨M, fun c => ?_⟩
        obtain ⟨k, hk, e⟩ := hper g' c
        rw [e]
        exact hM _ ⟨k, hk, rfl⟩
      haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
        ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
      have hG : Integrable (fun p : hermA D n × (Fin n → Fin n → ℝ) => F (ι (nb' p.2) * (nb p.1 * g')) * ψ₀ p.2 * χ p.1)
          ((lam.restrict 𝓖).prod volume) := by
        refine Integrable.mono' ((integrable_const M).mul_prod (hψ₀c.norm.integrable_of_hasCompactSupport hψ₀s.norm)) ?_ ?_
        · exact (((hFc.comp ((hιc.comp (hnb'c.comp continuous_snd)).mul ((hcont.comp continuous_fst).mul
            continuous_const))).mul (hψ₀c.comp continuous_snd)).mul (hχc.comp continuous_fst)).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun p => ?_
          rw [norm_mul, norm_mul, hχn, mul_one]
          have e : ι (nb' p.2) * (nb p.1 * g') = nb (bx p.2 + p.1) * g' := by rw [← mul_assoc, hbx, hadd]
          rw [e]
          exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      have step3 : ∀ x, ∫ b in 𝓖, F (ι (nb' x) * (nb b * g')) * ψ₀ x * χ b ∂lam =
          PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb F β g' * (ψ₀ x * eTr β'' x) := by
        intro x
        have e1 : ∀ b, F (ι (nb' x) * (nb b * g')) * ψ₀ x * χ b =
            (F (nb (b + bx x) * g') * χ (b + bx x)) * (χ (-(bx x)) * ψ₀ x) := by
          intro b
          have e2 : χ b = χ (b + bx x) * χ (-(bx x)) := by rw [← hχadd, add_neg_cancel_right]
          rw [← mul_assoc, hbx, ← hadd, add_comm (bx x) b, e2]
          ring
        simp_rw [e1]
        rw [integral_mul_const]
        have htr := Formalism.IndefR.Tow.fd_setIntegral_add hfd (f := fun b => F (nb b * g') * χ b)
          (fun l hl b => by rw [hadd, mul_assoc, hF _ (hrat l hl), hχper l hl b]) (bx x)
        rw [htr, hχneg]
        rw [show PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb F β g' = ∫ b in 𝓖, F (nb b * g') * χ b ∂lam from rfl]
        ring
      have hfc : PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb h β g' =
          PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb F β g' * ∫ x, ψ₀ x * eTr β'' x := by
        have step1 : PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb h β g' =
            ∫ b in 𝓖, ∫ x, F (ι (nb' x) * (nb b * g')) * ψ₀ x * χ b ∂volume ∂lam := by
          simp only [PositivityTheory.PfSWUS.fc, hdef, hχ]
          congr 1
          funext b
          rw [← integral_mul_const]
        rw [step1, integral_integral_swap hG]
        simp_rw [step3]
        rw [integral_const_mul]
      rw [hfc]
      by_cases hdet : β.1.det = 0
      · rw [hψ₀F β'' hβh (hβdet hdet), mul_zero]
      · rw [show PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb F β g' = 0 from
          hΛ _ ⟨nb, lam, 𝓖, β, g', ⟨hnb, hlam, hfd, hvol⟩, hdet, rfl⟩, zero_mul]
    intro g'
    exact congrFun (hFZ D n ψ hψ nb lam 𝓖 ⟨hnb, hlam, hfd, hvol⟩ h hhc hinv hcoef) g'

  have hmRc : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val
  let Fam : G D n → M2 n → ℂ := fun h M => if hM : InG M then F (ι (toGR M hM) * h) else 0
  have hFam : ∀ h M (hM : InG M), Fam h M = F (ι (toGR M hM) * h) := fun h M hM => dif_pos hM
  let Γ : Set (M2 n) := {M | ∃ hM : InG M, ∃ γ ∈ GF D n, ∃ x : G D n, γ = x * ι (toGR M hM) ∧
    ∀ y'' : GR n, x * ι y'' = ι y'' * x}
  have hFamc : ∀ h, ContinuousOn (Fam h) {M | InG M} := by
    intro h
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous fun M : ({M | InG M} : Set (M2 n)) => toGR M.1 M.2 := by
      apply Continuous.subtype_mk
      refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
      have hinv : ∀ M : ({M | InG M} : Set (M2 n)), (((toGR M.1 M.2 : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) =
          -(JJ n * M.1ᴴ * JJ n) := by
        intro M
        apply Units.inv_eq_of_mul_eq_one_left
        show -(JJ n * M.1ᴴ * JJ n) * M.1 = 1
        have h2 : M.1ᴴ * JJ n * M.1 = JJ n := M.2
        rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc M.1ᴴ, h2, JJ_sq, neg_neg]
      exact (((continuous_const.mul (continuous_subtype_val.matrix_conjTranspose)).mul continuous_const).neg).congr
        fun M => (hinv M).symm
    exact (hFc.comp ((hιc.comp hc).mul continuous_const)).congr fun M => (hFam h M.1 M.2).symm
  have hΓ2 : {M | InG M} ⊆ closure Γ := by
    intro M hM
    rw [mem_closure_iff]
    intro U hU hMU
    obtain ⟨γ, hγ, y', hy'O, x, hγx, hxc⟩ :=
      hD D n θ τ ι hθ hι (toGR M hM) {y | mR y ∈ U} (hU.preimage hmRc) hMU
    refine ⟨mR y', hy'O, y'.2, γ, hγ, x, ?_, hxc⟩
    rw [toGR_mR]
    exact hγx
  have hΓ3 : ∀ γM ∈ Γ, ∀ h, ∃ h', ∀ M, InG M → Fam h (γM * M) = Fam h' M := by
    rintro γM ⟨hγM, γ, hγ, x, hγx, hxc⟩ h
    refine ⟨x⁻¹ * h, fun M hM => ?_⟩
    have hprod : InG (γM * M) := (toGR γM hγM * toGR M hM).2
    rw [hFam _ _ hprod, hFam _ _ hM]
    have e : toGR (γM * M) hprod = toGR γM hγM * toGR M hM := by
      apply Subtype.ext; apply Units.ext; rfl
    have hy0 : ι (toGR γM hγM) = γ * x⁻¹ := by rw [hγx, hxc, mul_inv_cancel_right]
    have hxc' : x⁻¹ * ι (toGR M hM) = ι (toGR M hM) * x⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxc, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, map_mul, hy0]
    simp only [mul_assoc]
    rw [hF _ hγ, ← mul_assoc, hxc', mul_assoc]
  have hB0 : ∀ h M, InG M → ∫ x, Fam h (nU (herm x) * M) * ψ₀ x = 0 := by
    intro h M hM
    have e : ∀ x, Fam h (nU (herm x) * M) = F (ι (nb' x) * (ι (toGR M hM) * h)) := by
      intro x
      have hp : InG (nU (herm x) * M) := by
        have h2 : InG (mR (nb' x * toGR M hM)) := (nb' x * toGR M hM).2
        rwa [mR_mul, hnb', mR_toGR] at h2
      rw [hFam _ _ hp]
      have e2 : toGR (nU (herm x) * M) hp = nb' x * toGR M hM := by
        apply Subtype.ext; apply Units.ext
        show nU (herm x) * M = mR (nb' x) * M
        rw [hnb']
      rw [e2, map_mul, mul_assoc]
    simp_rw [e]
    exact hA _
  have hB := hTS n (G D n) Fam Γ hFamc (fun γ hγ => hγ.1) hΓ2 hΓ3 ψ₀ hψ₀c hψ₀s hB0
  obtain ⟨y, x0, hg, hx0⟩ := hSp D n θ τ ι hθ hι g
  have key : ∀ u : GR n, g * ι u = ι (y * u * y⁻¹) * g := by
    intro u
    calc g * ι u = ι y * (x0 * ι u) := by rw [hg, mul_assoc]
      _ = ι y * (ι u * x0) := by rw [hx0]
      _ = ι (y * u) * x0 := by rw [map_mul, mul_assoc]
      _ = ι (y * u * y⁻¹) * (ι y * x0) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
      _ = ι (y * u * y⁻¹) * g := by rw [hg]
  have e : ∀ x, F (g * ι (a * nb' x * b)) = Fam g (mR (y * a) * nU (herm x) * mR (b * y⁻¹)) := by
    intro x
    have hp : InG (mR (y * a) * nU (herm x) * mR (b * y⁻¹)) := by
      have h2 : InG (mR (y * a * nb' x * (b * y⁻¹))) := (y * a * nb' x * (b * y⁻¹)).2
      rwa [mR_mul, mR_mul, mR_mul, hnb'] at h2
    have e3 : toGR (mR (y * a) * nU (herm x) * mR (b * y⁻¹)) hp = y * (a * nb' x * b) * y⁻¹ := by
      apply Subtype.ext; apply Units.ext
      show mR (y * a) * nU (herm x) * mR (b * y⁻¹) = mR (y * (a * nb' x * b) * y⁻¹)
      simp only [mR_mul, hnb', Matrix.mul_assoc]
    rw [hFam _ _ hp, key, e3]
  simp_rw [e]
  exact hB g _ _ (y * a).2 (b * y⁻¹).2

end PositivityTheory.Rg.Sw.Glob
