import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefiniteStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GaussSeriesVacuum

open GlobalTheory.HeisenbergGaussianSeries GlobalTheory.SplitScalar GlobalTheory.VacuumO

theorem series_inv_scalar {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (a : V) (u : G) (hu : p u = 0) (c : ℂ) (hχ : ∀ x, c * (β x u * χ (x + u)) = χ x) (w : G) :
    c * (β w u * series p ι β om J Γ χ a (w + u)) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) u = 1 := by
    have := swap_mul β hl hr hd (ι a) u
    rw [hβ u a, hu] at this
    simpa using this
  rw [← hχ (g + w), ← add_assoc (g : G) w u, hr (ι a) (g + w) u, h1, hr g w u, hl g w u,
    map_add p w u, hu, add_zero]
  ring

theorem series_regular {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ)
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ)
    (hpc : Continuous p) (hιc : Continuous ι) (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (hn : ∀ x y, ‖β x y‖ = 1) (hβc : Continuous fun q : G × G => β q.1 q.2)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hJ : ∀ v, J (J v) = -v) (hsym : ∀ x y, om x (J y) = om y (J x)) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0) (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hχι : ∀ x v, χ (x + ι v) = χ x)
    (hU : IsOpen (U : Set G)) (hUinv : ∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) (a : V) :
    Continuous (series p ι β om J Γ χ a) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v)) ∧
      ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z))) 0 +
        Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * series p ι β om J Γ χ a (w + ι (t • J z))) 0 = 0 := by
  obtain ⟨M, hM⟩ := exists_exponent om J
  have hexp := fun w : G => GlobalTheory.expSeries_contDiff_and_hasDerivAt V Γ
    (fun g => β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ)))
    (fun g => M (p g + (a + p w)))
    (summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun g => β g w * β (ι a) (g + w))
      (fun g => by rw [norm_mul, hn, hn, one_mul]) w (a + p w) M)
  have hexpand := series_expand (Γ := Γ) hp hl hr hβ hsym hχι (fun y v => M y v) hM a
  have hne : ∀ x y, β x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have hgauss : ContDiff ℝ ∞ fun v : V => Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_bilin om J))).cexp
  have hsmooth : ∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v) := by
    intro w
    have h1 : ContDiff ℝ ∞ fun v : V => Complex.exp (Real.pi * Complex.I * (om (p w) v : ℝ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (LinearMap.toContinuousLinearMap (om (p w))).contDiff)).cexp
    have h2 := h1.mul (hgauss.mul (hexp w).1)
    refine (congrArg (ContDiff ℝ ∞) (funext fun v => ?_)).mp h2
    rw [← hexpand w v, hβ, ← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨?_, hsmooth, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hc1 : Continuous fun x : G => p (x - w) := hpc.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun x : G => β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))) :=
      hβc.comp (f := fun x : G => (w + ι (p (x - w)), (x - w) - ι (p (x - w))))
        ((continuous_const.add (hιc.comp hc1)).prodMk
          ((continuous_id.sub continuous_const).sub (hιc.comp hc1)))
    have hc3 : Continuous fun x : G => (β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))))⁻¹ *
        series p ι β om J Γ χ a (w + ι (p (x - w))) :=
      (hc2.inv₀ fun x => hne _ _).mul ((hsmooth w).continuous.comp hc1)
    refine hc3.continuousAt.congr ?_
    have hnhds : ∀ᶠ x in nhds w, x - w ∈ U := by
      have : IsOpen {x : G | x - w ∈ U} := hU.preimage (continuous_id.sub continuous_const)
      exact this.mem_nhds (by simp)
    filter_upwards [hnhds] with x hx
    have h := series_inv (Γ := Γ) (J := J) hl hr hd hβ a ((x - w) - ι (p (x - w)))
      (by rw [map_sub p, hp, sub_self]) (hUinv _ hx) (w + ι (p (x - w)))
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hne _ _), one_mul]
    congr 1; abel
  · intro w z
    have hder : ∀ z : V, HasDerivAt
        (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z)))
        (∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          M (p g + (a + p w)) z) 0 := by
      intro z
      have g1 : HasDerivAt (fun t : ℝ =>
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (t • z) (J (t • z)) : ℝ))) 0 0 := by
        have g0 : HasDerivAt (fun t : ℝ => om (t • z) (J (t • z))) 0 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (om z (J z))
          refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun t => ?_)
          simp [mul_assoc]
        exact (g0.ofReal_comp.const_mul (-(Real.pi / 2 : ℂ))).cexp.congr_deriv (by simp)
      have g2 := g1.mul ((hexp w).2 z).2
      simp only [hexpand]
      exact g2.congr_deriv (by simp)
    rw [(hder z).deriv, (hder (J z)).deriv, ← tsum_mul_left,
      ← ((hexp w).2 z).1.tsum_add (((hexp w).2 (J z)).1.mul_left Complex.I)]
    refine (tsum_congr fun g => ?_).trans tsum_zero
    rw [hM, hM, hJ, map_neg]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          (om (p g + (a + p w)) (J z) : ℝ)) * Complex.I_mul_I

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem fin_smul_of_real {v : WO S T} (hv : v.map (finPart D) = 0) : (1 - realIdem D) • v = 0 := by
  rw [sub_smul, one_smul, sub_eq_zero]
  exact Matrix.ext fun i j => (realIdem_mul_of_real (congrFun (congrFun hv i) j)).symm

theorem fin_smul_of_fin {u : WO S T} (hu : u.map (infPart D) = 0) : (1 - realIdem D) • u = u := by
  rw [sub_smul, one_smul, mem_finSub_iff.1 hu, sub_zero]

theorem chiLat_add_real (w : 𝓞 D.host.E) (x : WO S T) {v : WO S T} (hv : v.map (finPart D) = 0) :
    chiLat ψ S T LS LT w (x + v) = chiLat ψ S T LS LT w x := by
  have e : (1 - realIdem D) • (x + v) = (1 - realIdem D) • x := by rw [smul_add, fin_smul_of_real hv, add_zero]
  rw [chiLat, chiLat, e]

theorem quad_identity {w : 𝓞 D.host.E} (hw : w + GlobalTheory.FinWeil.sgO D w = 1) (y u : WO S T) :
    -symplOH S T (intA D w • u) u + (symplOH S T y u + symplOH S T (intA D w • (y + u)) (y + u)) =
      symplOH S T (intA D w • y) y + symplO S T (intA D w • y) u := by
  have h1 : intA D w • y + cA D (intA D w) • y = y := by
    rw [← add_smul, cA_intA, ← RingHom.map_add, hw, RingHom.map_one, one_smul]
  have h2 := congrArg (fun z => symplOH S T z u) h1
  simp only [symplOH_add_left] at h2
  have h3 := symplOH_smul (intA D w) u y
  rw [symplOH_skew S T (cA D (intA D w) • y) u] at h3
  rw [smul_add (intA D w) y u, symplOH_add_left, symplOH_add_right, symplOH_add_right, ← symplOH_add_self]
  linear_combination h3 - h2

theorem chiLat_add_lat (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) {w : 𝓞 D.host.E}
    (hw : w + GlobalTheory.FinWeil.sgO D w = 1) {u : XF S T} (hu : u ∈ latF S T LS LT) (x : WO S T) :
    phase ψ w u * (ψ (symplOH S T x u) * chiLat ψ S T LS LT w (x + u)) = chiLat ψ S T LS LT w x := by
  have e : (1 - realIdem D) • (x + (u : WO S T)) = (1 - realIdem D) • x + u := by
    rw [smul_add, fin_smul_of_fin u.fin]
  have e2 : symplOH S T x u = symplOH S T ((1 - realIdem D) • x) u := by
    have hdec : x = realIdem D • x + (1 - realIdem D) • x := by rw [← add_smul, add_sub_cancel, one_smul]
    conv_lhs => rw [hdec]
    rw [symplOH_add_left, symplOH, symplO_real_fin S T (real_smul_real x) u.fin, mul_zero, zero_add]
  rw [chiLat, chiLat, e, e2]
  have hy := fin_smul_fin x
  generalize (1 - realIdem D) • x = y at hy ⊢
  by_cases h : y ∈ latO S T LS LT fun _ => True
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : ψ (symplO S T (intA D w • y) u) = 1 :=
      (hA _).1 ((latF S T LS LT).smul_mem w (show XF.mk y hy ∈ latF S T LS LT from h)) u hu
    rw [phase, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_identity hw, AddChar.map_add_eq_mul, h0,
      mul_one]
  · have h2 : y + (u : WO S T) ∉ latO S T LS LT fun _ => True := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]

theorem series_theta_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ a : RW T S, ∃ hf : IsThetaFunO ψ S T (serO ψ θ σ S T sS sT ΛS ΛT w a), Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) (⟨serO ψ θ σ S T sS sT ΛS ΛT w a, hf⟩ : thetaSub ψ S T) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (serO ψ θ σ S T sS sT ΛS ΛT w a) := by
  classical
  intro D ψ hψ θ σ hσ S T sS sT hS hT ΛS ΛT dS dT w hw a
  have hθ := hσ.inf
  obtain ⟨hJJ, hskew, hinvJ, hneg⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  obtain ⟨aL, aR, a0, -, acont, arat, -, -, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ dS dT).1
  have htop : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
  have hl : ∀ x y z : WO S T, ψ (symplOH S T (x + y) z) = ψ (symplOH S T x z) * ψ (symplOH S T y z) :=
    fun x y z => by rw [aL, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WO S T, ψ (symplOH S T x (y + z)) = ψ (symplOH S T x y) * ψ (symplOH S T x z) :=
    fun x y z => by rw [aR, AddChar.map_add_eq_mul]
  have hd : ∀ x : WO S T, ψ (symplOH S T x x) = 1 := fun x => by rw [a0, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WO S T) (v : RW T S), ψ (symplOH S T x (iotaW σ T S v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) v : ℝ)) := fun x v => by
    have e := GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ hθ hψ S T x (iotaW σ T S v) (Or.inr (hσ.real_iota T S v))
    rw [hσ.pi_iota] at e
    exact e
  have fl : ∀ u ∈ latF S T ΛS ΛT, ∀ x : WO S T, phase ψ w u * (ψ (symplOH S T x u) *
      serO ψ θ σ S T sS sT ΛS ΛT w a (x + u)) = serO ψ θ σ S T sS sT ΛS ΛT w a x := fun u hu x =>
    series_inv_scalar (G := WO S T) (β := fun x y => ψ (symplOH S T x y)) hl hr hd hβ a u (piW_of_inf θ u.fin) _
      (chiLat_add_lat hA hw hu) x
  set Λ : AddSubgroup (WO S T) := latO S T ΛS ΛT fun _ => True with hΛ
  have hlev : ∀ u ∈ thick Λ 2, ∃ l ∈ latF S T ΛS ΛT, u - iotaW σ T S (piW θ T S u) = ((2 • l : XF S T) : WO S T) := by
    rintro u ⟨l, hl, hu⟩
    refine ⟨XF.mk l (latO_fin hl), hl, ?_⟩
    have e := hσ.iota_pi (V := T) (W := S) (x := u - 2 • l) hu
    rw [map_sub, map_nsmul, piW_of_inf θ (latO_fin hl), smul_zero, sub_zero] at e
    rw [e, XF.coe_nsmul, XF.coe_mk]
    abel
  obtain ⟨fc, fs, fv⟩ := series_regular (G := WO S T) (piW θ T S) (iotaW σ T S)
    (fun x y => ψ (symplOH S T x y)) (omO S T) (jO S T sS sT) (ratL T S)
    (Λ.comap (AddMonoidHom.mk' (fun x : WO S T => (1 - realIdem D) • x) (smul_add _))) (thick Λ 2)
    (chiLat ψ S T ΛS ΛT w) (continuous_pi' hθ T S) (hσ.continuous_iota T S) (hσ.pi_iota T S) hl hr hd
    (fun x y => hψ.1.2.1 _) (hψ.1.1.comp acont) hβ hJJ
    (fun x y => by rw [← hinvJ x, hJJ, map_neg, ← hskew])
    (fun v hv => by rw [hskew]; exact neg_pos.2 (hneg v hv))
    (by
      rintro _ ⟨g, rfl⟩ h
      have : g = 0 := by
        funext i j
        have e : θ (D.eTau.symm 1) (infPart D (incA D (g i j))) = 0 :=
          congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
        rw [comp_incA hθ] at e
        exact (tauE D _).injective (e.trans (RingHom.map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((GlobalTheory.T.finite_rational_points_completed_lattice D S T ΛS ΛT dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨g, rfl⟩, h1, h2⟩
      refine ⟨g, ⟨⟨_, h1, ?_⟩, fun τ i j => ?_⟩, rfl⟩
      · have e : (ratW T S g : WO S T) - (1 - realIdem D) • (ratW T S g : WO S T) =
            realIdem D • (ratW T S g : WO S T) := by rw [sub_smul, one_smul, sub_sub_cancel]
        exact (congrArg (fun z : WO S T => z.map (finPart D)) e).trans (real_smul_real _)
      · rw [← comp_incA hθ]
        let y : RW T S := piW θ T S (ratW T S g)
        exact ((norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))).trans h2)
    (fun x hx => if_neg hx)
    (fun x => by
      rw [chiLat]
      split_ifs
      · exact (hψ.1.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => chiLat_add_real w x (hσ.real_iota T S v))
    (GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos)
    (fun u hu x => by
      obtain ⟨l, hl, e⟩ := hlev u hu
      have e2 := chiLat_add_lat hA hw (nsmul_mem hl 2) x
      rw [phase_two hA w hl, one_mul] at e2
      rw [e]
      exact e2) a
  refine ⟨⟨fun g x => ?_, ⟨thick Λ 2, GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos, fun u hu h => ?_⟩, fc,
    fun k L hL hL0 x => ?_⟩, fun u hu => Subtype.ext (funext fun x => fl u hu x), fun τ z => ?_⟩
  · have e : ψ (symplOH S T (ratW T S g) x) * serO ψ θ σ S T sS sT ΛS ΛT w a (ratW T S g + x) =
        serO ψ θ σ S T sS sT ΛS ΛT w a x :=
      series_quasi (G := WO S T) (Γ := ratL T S) (β := fun x y => ψ (symplOH S T x y)) hl hr (fun g hg g' hg' => by
        obtain ⟨b, hb⟩ := arat g hg g' hg'
        simp only [hb]
        exact hψ.1.2.2.1 b) a (ratW T S g) ⟨g, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨l, hl, e⟩ := hlev u hu
    rw [piW_of_inf θ h, map_zero, sub_zero] at e
    funext x
    have e2 := fl _ (nsmul_mem hl 2) x
    rw [phase_two hA w hl, one_mul, ← e] at e2
    exact e2
  · exact ((smooth_iff_sm_and_real_lines D θ σ hσ T S).1 _).2 fs k L hL hL0 x
  · funext x
    let v : RW T S := Pi.single τ z
    have v1 : v τ = z := Pi.single_eq_same _ _
    have v2 : ∀ τ', τ' ≠ τ → v τ' = 0 := fun τ' h => Pi.single_eq_of_ne h _
    have l1 := lineAt_eq hσ S T τ z v v1 v2
    have l2 := lineAt_eq hσ S T τ (cplxO (sS τ) (sT τ) z) (jO S T sS sT v) (by rw [jO_apply, v1]) (fun τ' h => by
      rw [jO_apply, v2 τ' h]
      have : cplxO (sS τ') (sT τ') (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by simp [cplxO]
      exact this)
    show deriv (fun t : ℝ => ψ (symplOH S T x (lineAt θ τ z t)) *
        serO ψ θ σ S T sS sT ΛS ΛT w a (x + lineAt θ τ z t)) 0 +
      Complex.I * deriv (fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) *
        serO ψ θ σ S T sS sT ΛS ΛT w a (x + lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) 0 = 0
    simp only [l1, l2]
    exact fv x v

end GlobalTheory.GaussSeriesVacuum

end
