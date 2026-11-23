import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicClassicalVacuumFactorEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmulStatement

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacFamily

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem compAt_fin {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h1 : infHom V k = 1 := hk
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V k) = ((infHom V k).val).map (θ τ) := rfl
  rw [h2, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem frMove_mul_fin {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank)
    (u : GA D W) {k : GA D W} (hk : k ∈ GfC W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * k) x = frMove θ W rfl X u x := by
  funext τ
  have e : realM θ (Formalism.L2.Theta.mt W (u * k)) τ.1 = realM θ (Formalism.L2.Theta.mt W u) τ.1 := by
    unfold realM
    split_ifs with h
    · rw [GlobalTheory.UnitaryChar.compAt_mt_mul, compAt_fin θ W hk, Matrix.mul_one]
    · rfl
  unfold frMove
  rw [e]

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (u : GA D W) {x : Frame X.Ψ W.rank} (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X u x) := by
  intro τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have hG : X.Gm = -(W.gram)ᵀ := by rw [hX.model.1]; simp
  have e : mat (frMove θ W rfl X u x) τ = compAt θ hτ.choose (Formalism.L2.Theta.mt W u) * mat x τ := by
    show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) = _
    unfold realM
    rw [dif_pos hτ]
    simp
  have hu : (compAt θ hτ.choose (Formalism.L2.Theta.mt W u))ᴴ * gramAt D W hτ.choose *
      compAt θ hτ.choose (Formalism.L2.Theta.mt W u) = gramAt D W hτ.choose :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u _
  have hg : gramAt D W hτ.choose = W.gram.map τ.1 := by
    conv_rhs => rw [hτ.choose_spec]
    rfl
  rw [hg] at hu
  rw [← hx τ, e, hG, GlobalTheory.FrameCplx.gram_eq, GlobalTheory.FrameCplx.gram_eq, Matrix.conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

abbrev twist {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}

theorem latO_le {D : D7} (V W : HSp D) (LV : Set (Fin V.rank → D.host.E))
    {L L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (h : twist L ≤ twist L') :
    latO V W LV (L : Set (Fin W.rank → D.host.E)) (fun _ => True) ≤
      latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have key : ∀ w ∈ twist L', ∀ b : 𝓞 D.host.E,
      (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((b • w) i * ∑ k, star (s k) * V.gram k j) : WO V W) ∈
        latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a', ha', t', ht', rfl⟩ := hw
      intro b
      refine AddSubgroup.subset_closure ⟨α, hα, hP, b • a', (D.host.AA.coeToSubmodule).smul_mem b ha',
        s, hs, t', ht', ?_⟩
      ext i j
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, smul_mul_assoc]
    | zero =>
      intro b
      convert (latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True).zero_mem
      ext i j
      simp
    | add w w' _ _ h1 h2 =>
      intro b
      convert add_mem (h1 b) (h2 b)
      ext i j
      simp only [Matrix.of_apply, smul_add, Pi.add_apply, add_mul, TensorProduct.tmul_add, Matrix.add_apply]
    | smul c w _ h1 =>
      intro b
      rw [smul_smul]
      exact h1 _
  have := key (a • t) (h (Submodule.subset_span ⟨a, ha, t, ht, rfl⟩)) 1
  rw [one_smul] at this
  exact this

theorem actO_mul {D : D7} (V W : HSp D) (h h' : GA D W) (u : WO V W) :
    actO V W 1 (h * h') u = actO V W 1 h (actO V W 1 h' u) := by
  have e1 : Formalism.L2.Theta.mt V 1⁻¹ = 1 := by rw [inv_one]; rfl
  have e2 : Formalism.L2.Theta.mt W (h * h') = Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h' := rfl
  unfold actO
  rw [e1, e2]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem actO_one {D : D7} (V W : HSp D) (u : WO V W) : actO V W 1 1 u = u := by
  have e1 : Formalism.L2.Theta.mt V 1⁻¹ = 1 := by rw [inv_one]; rfl
  have e2 : Formalism.L2.Theta.mt W 1 = 1 := rfl
  unfold actO
  rw [e1, e2]
  simp only [Matrix.mul_one, Matrix.one_mul]

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) : latR rfl L = L := by
  have : LinearMap.funLeft (𝓞 E) E (Fin.cast (rfl : m = m).symm) = LinearMap.id := rfl
  unfold latR
  rw [this, Submodule.map_id]

theorem latG_mul {D : D7} (W : HSp D) {u : GA D W} (hu : u ∈ GinfC W) (k : GA D W) :
    Formalism.L2.Pj.latG W (u * k) = Formalism.L2.Pj.latG W k := by
  have h : finHom W u = 1 := hu
  unfold Formalism.L2.Pj.latG Formalism.L2.Pj.gLat
  rw [map_mul, h, one_mul]

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, map_ofNat] at this
    exact this
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs, map_neg, map_natCast]
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at hre him
    have h0 : (τ (H.rt : E)).re = 0 := by
      by_contra h
      have h5 : (τ (H.rt : E)).im = 0 := mul_left_cancel₀ h (by linarith)
      rw [h5] at hre
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [h0]
  have h3 : (2 : E) * cc (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add, map_one, map_ofNat] at this
    rw [sub_eq_add_neg, ← hc]
    exact this
  linear_combination (h2 + h3) / 2

theorem mem_stdL {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Fin n → E) :
    w ∈ stdL E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = w j := by
  rw [stdL, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    choose c hc using h
    refine ⟨c, funext fun j => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ← hc]

theorem exists_vacuum_multiplier : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → SelfD X X.Λ → ∀ (x₀ : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x₀ → IsInvOf W hr X x₀ s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) ∧ ∀ k : GA D W, latR hr (Formalism.L2.Pj.latG W k) = X.Λ → IsONFr X (frMove θ W hr X k x₀) ∧ Reads θ V W hr X bas idx (om (1, k) f) ((κ * mu k) • v) (frMove θ W hr X k x₀) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS H hH ΛV ΛW hV0 hΛV hΛW hsV hsW hstdV hsd x₀ s hx hinv f hf v hv
  subst hr
  have hstd := hP.weil.std
  by_cases hex : ∃ k : GA D W, latR rfl (Formalism.L2.Pj.latG W k) = X.Λ
  swap
  · obtain ⟨ρ, hρ, h⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq D.host.E W.rank X g bas idx V.rank hS hP.even _
      H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) X.Λ hsd v hv
    refine ⟨ρ, by exact_mod_cast hρ.ne', fun x' hx' hu ϑ κ' h1 h2 h3 => ?_, fun k hk => absurd ⟨k, hk⟩ hex⟩
    rw [h x' hx' hu ϑ κ' h1 h2 h3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hsplit := (GlobalTheory.UnitarySplit.real_finite_split D W).1
  have hfin1 : Formalism.IndefR.FWT.fin V 1 = 1 := map_one _
  have hmv := fun k => GlobalTheory.MovedLat.moved_lattices D V W ΛV ΛW hΛV hΛW hsV hsW 1 k
  have hV1 : Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1) = ΛV := by rw [hfin1]; exact (hmv 1).2.2.2.2.1
  simp only [hV1] at hmv
  obtain ⟨k₁, hk₁⟩ := hex
  obtain ⟨u₁, hu₁, k₀, hk₀, rfl⟩ := hsplit k₁
  rw [latR_rfl, latG_mul W hu₁] at hk₁
  obtain ⟨-, hs₀, hl₀, ht₀, -, -⟩ := hmv k₀
  set L₀ := Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k₀) with hL₀
  have hf₀ : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (L₀ : Set (Fin W.rank → D.host.E))
      (om (1, k₀) f) :=
    GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χV χW om hP.weil hP.inf _ _ s s _ _ _ _ 1 k₀
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [compAt_fin θ W hk₀, Matrix.one_mul, Matrix.mul_one]) hl₀ f hf
  have hL : ∀ L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L = twist L₀ → X.Λ = latR rfl L := fun L h => by
    rw [latR_rfl, h, ← hk₁, ht₀]
  have hconj : ∀ w : Fin V.rank → D.host.E, w ∈ stdL D.host.E V.rank ↔ (fun j => star (w j)) ∈ ΛV := by
    intro w
    have hb : ∀ b : 𝓞 D.host.E, ((H.bar b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := fun b => H.bar_eq b
    rw [mem_stdL, ← SetLike.mem_coe, hstdV, SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
    refine forall_congr' fun j => ⟨?_, fun h => ?_⟩
    · rintro ⟨b, e⟩ -
      exact Submodule.mem_one.2 ⟨H.bar b, by rw [← e]; exact hb b⟩
    · obtain ⟨b, e⟩ := Submodule.mem_one.1 (h (Set.mem_univ _))
      refine ⟨H.bar b, ?_⟩
      rw [hb, show (b : D.host.E) = star (w j) from e, star_star]
  obtain ⟨κ₀, hκ₀, hR₀⟩ := GlobalTheory.T.adelicVacuum_reads_multiple_classicalVacuum D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS H hH ΛV L₀
    _ X.Λ hP.sigV hP.sigW hsV hs₀ hconj hL x₀ s hx hinv _ hf₀ v hv
  have hN := GlobalTheory.T.norm_adelicClassicalVacuumFactor_eq D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS H hH ΛV L₀
    hsV hs₀ hstdV hL x₀ s hx _ hf₀ v hv κ₀ hR₀
  have hmu0 : mu k₀ ≠ 0 := fun h => by
    have := hmu.norm k₀
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x₀ s
    hx hinv).1
  refine ⟨κ₀ / mu k₀, div_ne_zero hκ₀ hmu0, fun x' hx' hu ϑ κ' h1 h2 h3 => ?_, fun k hk => ?_⟩
  · rw [hN x' hx' hu ϑ κ' h1 h2 h3, norm_div, hmu.norm, div_one]
  refine ⟨isONFr_frMove hP.inf W X hX k hx, ?_⟩
  obtain ⟨u, hu, c, hc, rfl⟩ := hsplit k
  rw [latR_rfl, latG_mul W hu] at hk
  obtain ⟨-, -, hl, ht, -, -⟩ := hmv c
  have htw : twist (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W c)) = twist L₀ :=
    ht.symm.trans (hk.trans (hk₁.symm.trans ht₀))
  have hlat := le_antisymm (latO_le V W ΛV htw.le) (latO_le V W ΛV htw.ge)
  rw [hlat] at hl
  have hk' : c * k₀⁻¹ ∈ GfC W := mul_mem hc (inv_mem hk₀)
  have hfix := GlobalTheory.T.weilRep_lattice_stabilizer_vacuum_eq_det_char_smul D ψ θ V W χV χW om hP mu hmu H ΛV L₀ hV0 hsV hs₀ s hcart _ hf₀ _ hk' (fun w => by
    rw [hl₀ w, hl]
    constructor
    · rintro ⟨w₀, hw₀, rfl⟩
      exact ⟨w₀, hw₀, by rw [← actO_mul, inv_mul_cancel_right]⟩
    · rintro ⟨w₀, hw₀, e⟩
      refine ⟨w₀, hw₀, ?_⟩
      have := congrArg (actO V W 1 (k₀ * c⁻¹)) e
      rw [← actO_mul, ← actO_mul, inv_mul_cancel_right] at this
      rw [← this, show k₀ * c⁻¹ * (c * k₀⁻¹) = 1 by group, actO_one])
  have hth : IsThetaFunO ψ V W (om (1, c * k₀⁻¹) (om (1, k₀) f)) := hP.weil.om_pres _ _ hf₀.2.theta
  have hR := (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x₀ hx
    _ _ _ _ hR₀ hR₀).1 (mu (c * k₀⁻¹)) 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hfix] at hR
  have hR' := GlobalTheory.T.weilRepresentation_real_moves_frame_detChar D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x₀ hx _ _ hth hR u hu
  have e1 : om (1, u) (om (1, c * k₀⁻¹) (om (1, k₀) f)) = om (1, u * c) f := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk]
    simp only [mul_one, mul_assoc, inv_mul_cancel]
  have e2 : κ₀ / mu k₀ * mu (u * c) = mu u * (mu (c * k₀⁻¹) * κ₀) := by
    have : mu c = mu (c * k₀⁻¹) * mu k₀ := by rw [← muVal_mul hmu, inv_mul_cancel_right]
    rw [muVal_mul hmu, this]
    field_simp
  rw [e1, smul_smul, smul_smul, mul_assoc, ← e2] at hR'
  rw [frMove_mul_fin θ W X u hc]
  exact hR'

end GlobalTheory.VacFamily
