import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WhitAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.IwaAd

variable {D : D7} {n : ℕ}

theorem par_ne_zero {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) : ∀ τ, l τ ≠ 0 := by
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 hμ ω hS.hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hS.hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hS.hθ l l' hS.hl hl''
  subst hleq
  intro τ h0
  have h := habs τ
  rw [h0, abs_zero] at h
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have h2 : tauE D τ μ' ≠ 0 := (map_ne_zero _).2 hsk.1
  exact (div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)) h.symm

theorem temperate_poly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (MvPolynomial.C a) (fun τ => Matrix.of (z τ))) =
        fun _ => a := by
      funext z; simp [evalPoly]
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        fun z => evalPoly p (fun τ => Matrix.of (z τ)) + evalPoly q (fun τ => Matrix.of (z τ)) := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    obtain ⟨τ, i, j, e⟩ := k
    let L0 : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))
    let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      if e then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp L0 else L0
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
          evalPoly (p * MvPolynomial.X (τ, i, j, e)) (fun τ => Matrix.of (z τ))) =
        fun z => evalPoly p (fun τ => Matrix.of (z τ)) * L z := by
      funext z
      cases e <;> simp [evalPoly, L, L0]
    rw [this]; exact hp.mul L.hasTemperateGrowth

theorem exists_schwartz_polyGauss (V : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z,
      f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  obtain ⟨f0, hf0⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (temperate_poly p) f0, fun z => ?_⟩
  rw [SchwartzMap.bilinLeftCLM_apply]
  simp [hf0, mul_comm]

section Pure
open NumberField IsDedekindDomain GlobalTheory.PureFinite PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n' M : ℕ}

theorem isLocallyConstant_finprod
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n' → Fin M → Fv F v ⊗[F] E) → ℂ) (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    IsLocallyConstant (fun X : Fin n' → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n' → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n' → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hev : ∀ Y ∈ U, (∏ᶠ v, Φv v (projV v Y)) = ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    intro Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  have hP : IsLocallyConstant (fun Y : Fin n' → Fin M → Af F ⊗[F] E => ∏ v ∈ hS.toFinset, Φv v (projV v Y)) := by
    refine Finset.induction_on hS.toFinset ?_ ?_
    · simp only [Finset.prod_empty]; exact IsLocallyConstant.const _
    · intro a t ha ih
      simp only [Finset.prod_insert ha]
      exact ((hSB a).1.comp_continuous (continuous_projV_fin b a)).mul ih
  filter_upwards [hUo.mem_nhds hXU, (IsLocallyConstant.iff_eventually_eq _).1 hP X] with Y hY hPY
  rw [hev Y hY, hPY, hev X hXU]

end Pure

theorem sb_of_pure {m d : ℕ} {bs : Module.Basis (Fin d) D.host.F D.host.E}
    {g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    {gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ}
    (h : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv) :
    g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_basis bs
  obtain ⟨hSB, hae, hprod⟩ := h
  let f : (Fin n → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => ∏ᶠ v, gv v (projV v X)
  have hlc : IsLocallyConstant f := isLocallyConstant_finprod bs gv hSB hae
  have hcs : HasCompactSupport f := GlobalTheory.PureFinite.hasCompactSupport_finprod bs gv hSB hae
  let e : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin n → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X j i => X i j
      invFun := fun X i j => X j i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j) }
  have hg : g = f ∘ e := funext fun X => hprod (e X)
  rw [hg]
  exact ⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩

theorem mem_of_mono {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) {φ : Mx D V.rank n → ℂ}
    (h : IsMonoFock θ V l s φ) : φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  have hg := sb_of_pure hp
  obtain ⟨f, hf⟩ := exists_schwartz_polyGauss V l (par_ne_zero hS) s hS.hs (MvPolynomial.monomial e c)
  refine ⟨Submodule.subset_span ⟨f, g, hg, ?_⟩, Submodule.subset_span ⟨_, g, hg, rfl⟩⟩
  funext x
  rw [hf]
  rfl

theorem continuous_height {H : G D n → ℝ≥0} (hH : IsHeight H) : Continuous H := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  rw [PolesModel.height_eq hH]
  exact PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP
    GlobalTheory.StdUnn.Model.isCompact_K

theorem height_pos {H : G D n → ℝ≥0} (hH : IsHeight H) (x : G D n) : 0 < H x := by
  rw [PolesModel.height_eq hH]
  exact iwAbs_pos _ _ x

theorem height_ratio {H : G D n → ℝ≥0} (hH : IsHeight H) (g : G D n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, (H (x * g) : ℝ) ≤ C * H x ∧ (H x : ℝ) ≤ C * H (x * g) := by
  have hc := continuous_height hH
  have hK : IsCompact (K D n : Set (G D n)) := GlobalTheory.StdUnn.Model.isCompact_K
  have h1 : Continuous fun k : G D n => (H (k * g) : ℝ) :=
    NNReal.continuous_coe.comp (hc.comp (continuous_id.mul continuous_const))
  have h2 : Continuous fun k : G D n => (H (k * g) : ℝ)⁻¹ :=
    h1.inv₀ fun k => (NNReal.coe_pos.2 (height_pos hH _)).ne'
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn h2.continuousOn
  refine ⟨max 1 (max C₁ C₂), le_max_left _ _, fun x => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := PolesModel.isIwasawa.1 x
  have hkH : H k = 1 := by
    rw [PolesModel.height_eq hH]; exact PolesModel.isIwasawa.iwAbs_of_mem hk
  have e1 : H ((p : G D n) * k) = PolesModel.modP p := by
    rw [PolesModel.height_eq hH]; exact PolesModel.isIwasawa.iwAbs_mul p hk
  have e2 : H ((p : G D n) * k * g) = PolesModel.modP p * H (k * g) := by
    rw [PolesModel.height_eq hH, mul_assoc]; exact PolesModel.isIwasawa.iwAbs_left p _
  have hp0 : (0 : ℝ) ≤ PolesModel.modP p := NNReal.coe_nonneg _
  have hk0 : (0 : ℝ) < H (k * g) := NNReal.coe_pos.2 (height_pos hH _)
  have b1 : (H (k * g) : ℝ) ≤ max 1 (max C₁ C₂) := by
    have := hC₁ k hk
    rw [Real.norm_of_nonneg hk0.le] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  have b2 : (H (k * g) : ℝ)⁻¹ ≤ max 1 (max C₁ C₂) := by
    have := hC₂ k hk
    rw [Real.norm_of_nonneg (inv_nonneg.2 hk0.le)] at this
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
  rw [e1, e2, NNReal.coe_mul]
  constructor
  · calc (PolesModel.modP p : ℝ) * H (k * g) ≤ PolesModel.modP p * max 1 (max C₁ C₂) :=
          mul_le_mul_of_nonneg_left b1 hp0
      _ = _ := mul_comm _ _
  · calc (PolesModel.modP p : ℝ) = (H (k * g) : ℝ)⁻¹ * (PolesModel.modP p * H (k * g)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right b2 (mul_nonneg hp0 hk0.le)

theorem norm_npow_le {H : G D n → ℝ≥0} (hH : IsHeight H) (g : G D n) (t : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖npow (H (x * g)) t‖ ≤ M * ‖npow (H x) t‖ := by
  obtain ⟨C, hC, hb⟩ := height_ratio hH g
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  refine ⟨C ^ |t.re|, (Real.rpow_pos_of_pos hC0 _).le, fun x => ?_⟩
  have ha : (0 : ℝ) < H (x * g) := NNReal.coe_pos.2 (height_pos hH _)
  have hx : (0 : ℝ) < H x := NNReal.coe_pos.2 (height_pos hH _)
  rw [norm_npow (height_pos hH _), norm_npow (height_pos hH _)]
  obtain ⟨h1, h2⟩ := hb x
  rcases le_total 0 t.re with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow hC0.le hx.le]
    exact Real.rpow_le_rpow ha.le h1 h
  · rw [abs_of_nonpos h]
    have h3 : (H x : ℝ) * C⁻¹ ≤ H (x * g) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hC0]; linarith
    have h4 : (H (x * g) : ℝ) ^ t.re ≤ ((H x : ℝ) * C⁻¹) ^ t.re :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos h (Set.mem_Ioi.2 (mul_pos hx (inv_pos.2 hC0))) (Set.mem_Ioi.2 ha) h3
    rw [Real.mul_rpow hx.le (inv_pos.2 hC0).le, Real.inv_rpow hC0.le, ← Real.rpow_neg hC0.le] at h4
    linarith [h4, mul_comm ((H x : ℝ) ^ t.re) (C ^ (-t.re))]

theorem jt_eq {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {nb : hermA D n → G D n}
    (hNb : IsNMap nb) (Φ : schwartzA θ V.rank n) (b : hermA D n) :
    Jt ψ V μ Φ.1 b = (ω (w * nb b) Φ).1 0 := by
  have h := GlobalTheory.CompanionTheory.SWGlue.weil_cell_zero hω hw b (hNb b) Φ 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  exact h.symm

theorem integrable_term {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) (hR : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hC : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0) (g : G D n)
    (T : Mx D n n) {z : ℂ} (hz : (n : ℝ) / 2 < z.re) :
    Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ Φ.1 b *
      ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n)))) lam := by
  have hJ : ∀ b, Jt ψ V μ Φ.1 b = (ω (w * nb b) Φ).1 0 := jt_eq hS.hω hw hC.1 Φ
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  have hsec := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 hμ ω hS.hω l hS.hl
    s hS.hs Φ hS.hΦ
  have hcn := GlobalTheory.CompanionTheory.SwUnf.nb_continuous hC.1
  have hI := (GlobalTheory.CompanionTheory.SwUnf.unfold D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz 1).1
  obtain ⟨M, hM0, hM⟩ := norm_npow_le hS.hH g (z - s0 V n)
  have hcJ : Continuous fun b : hermA D n => Jt ψ V μ Φ.1 b := by
    simp only [hJ]
    exact hsec.2.1.comp (continuous_const.mul hcn)
  have hcH : Continuous fun b : hermA D n => npow (H (w * nb b * g)) (z - s0 V n) := by
    have e : (fun b : hermA D n => npow (H (w * nb b * g)) (z - s0 V n)) = fun b =>
        Complex.exp (((Real.log (H (w * nb b * g)) : ℝ) : ℂ) * (z - s0 V n)) :=
      funext fun b => npow_eq_exp (height_pos hS.hH _) _
    rw [e]
    refine Continuous.cexp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    exact (NNReal.continuous_coe.comp ((continuous_height hS.hH).comp
      ((continuous_const.mul hcn).mul continuous_const))).log
      fun b => (NNReal.coe_pos.2 (height_pos hS.hH _)).ne'
  have hcχ : Continuous fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) :=
    (GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hS.hψ (-T)).congr fun b => GlobalTheory.CompanionTheory.HermPoisson.chi_neg_left ψ _ b
  refine (hI.norm.const_mul M).mono' ((hcH.mul hcJ).mul hcχ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => ?_)
  have e : sect ω H Φ z (w * nb b * 1) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
    rw [hJ, mul_one, sect]
  rw [norm_mul, norm_mul, hS.hψ.2.1, mul_one, e, norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem whitTAdd : PositivityTheory.PfSWUS.WhitTAdd := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a g N φs hφ
  refine ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  have hmem : ∀ j, φs j ∈ schwartzA θ V.rank n ∧ φs j ∈ fockA θ V n l s := fun j => mem_of_mono hS (hφ j)
  let Ψ : Fin N → schwartzA θ V.rank n := fun j => ⟨φs j, (hmem j).1⟩
  have hS' : ∀ j, Std D n V ψ χ θ μ ω H l s ν (Ψ j) := fun j =>
    ⟨hS.hψ, hS.hχ, hS.hη, hS.hθ, hS.hμ, hS.hω, hS.hH, hS.hl, hS.hs, hS.hν, (hmem j).2⟩
  have hI := fun j => integrable_term (hS' j) hR hC hw hβ g (adj a.1 * β.1.map (incA D) * a.1) hz
  have hsum : (∑ j, φs j) = (∑ j, Ψ j : schwartzA θ V.rank n).1 := by
    rw [AddSubmonoidClass.coe_finset_sum]
  have hJ : ∀ b, Jt ψ V μ (∑ j, φs j) b = ∑ j, Jt ψ V μ (φs j) b := fun b => by
    rw [hsum, jt_eq hS.hω hw hC.1, map_sum, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => (jt_eq hS.hω hw hC.1 (Ψ j) b).symm
  simp only [whitT]
  rw [← integral_finset_sum _ fun j _ => hI j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [hJ, Finset.mul_sum, Finset.sum_mul]
  rfl

end GlobalTheory.CompanionTheory.WhitAdd
end
