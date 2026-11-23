import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorCR

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Weil

variable {G : Type} [Group G] [MeasurableSpace G]

theorem weil_bruhat [MeasurableMul G] {μG μS ν : Measure G} (K : Set G) (hK : μS Kᶜ = 0)
    (hW : ∀ F : G → ℝ≥0∞, Measurable F → ∫⁻ x, F x ∂μG = ∫⁻ x, ∫⁻ s, F (s * x) ∂μS ∂ν)
    {β : G → ℝ≥0∞} (hβm : Measurable β) (hβ1 : ∀ x, ∫⁻ s, β (s * x) ∂μS = 1)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hinv : ∀ s ∈ K, ∀ x, F (s * x) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, F x * β x ∂μG := by
  have hKae : ∀ᵐ s ∂μS, s ∈ K := MeasureTheory.mem_ae_iff.mpr hK
  have key : ∀ x, ∫⁻ s, F (s * x) * β (s * x) ∂μS = F x := by
    intro x
    have hae : (fun s => F (s * x) * β (s * x)) =ᵐ[μS] fun s => F x * β (s * x) := by
      filter_upwards [hKae] with s hs
      rw [hinv s hs x]
    rw [lintegral_congr_ae hae, lintegral_const_mul _ (show Measurable fun s => β (s * x) from hβm.comp (measurable_mul_const x)), hβ1 x, mul_one]
  rw [hW (fun x => F x * β x) (hF.mul hβm)]
  refine lintegral_congr fun x => ?_
  exact (key x).symm

end Weil

section Tr

open Classical Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem exists_const_l2SG_transport_eq_mul_lintegral {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) {z : Fin (2 * r + k + 1) → ℂ}
    (K : Set (Formalism.REAL.UJ ε)) (hKc : IsClosed K) (hKg : QPK.IsGrp K)
    (hd : ∀ γ : Formalism.REAL.UJ ε, Formalism.L2.SG.RealObj.trG Q Qi γ ∈ Formalism.QuantumDeterminants.Sset k r z ↔ γ ∈ K)
    (hSsub : Formalism.QuantumDeterminants.Sset k r z ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μSB νB : Measure (Formalism.QuantumDeterminants.Mt k r)} (hSB : IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μSB)
    (hQB : IsQuotMeas ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) μSB νB)
    {μS νl : Measure (Formalism.REAL.UJ ε)} (hS : QPK.InvOn μS K)
    (hWl : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, ∫⁻ s, F (s * x) ∂μS ∂νl)
    {β : Formalism.REAL.UJ ε → ℝ≥0∞} (hβm : Measurable β) (hβ1 : ∀ x, ∫⁻ s, β (s * x) ∂μS = 1)
    {V : Type} [NormedAddCommGroup V] (f : Formalism.REAL.UJ ε → V) (hf : Continuous f)
    (hfK : ∀ s ∈ K, ∀ x, ‖f (s * x)‖ = ‖f x‖) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ l2SG νB (wTg Q Qi f) = c * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂νl := by
  subst hn
  have hmapG : (fun γ : Formalism.REAL.UJ ε => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)) = cM Qi Q := rfl
  rw [hmapG] at hQB
  set e : Formalism.REAL.UJ ε → Formalism.QuantumDeterminants.Mt k r := cM Qi Q with he_def
  have he : MeasurableEmbedding e := cM_measEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2
  have hqi := qiHqi ε h2 hg

  have emul : ∀ a b : Formalism.REAL.UJ ε, (Matrix.of (e (a * b)) : Matrix _ _ ℂ) =
      (Matrix.of (e a) : Matrix _ _ ℂ) * Matrix.of (e b) := by
    intro a b
    show Qi * uMat (a * b) * Q = (Qi * uMat a * Q) * (Qi * uMat b * Q)
    rw [Formalism.L2.SG.WuDecayPf.uMat_mul']
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi * uMat a) Q Qi, h2, Matrix.mul_one]
  have eUH : ∀ x : Formalism.REAL.UJ ε, (Matrix.of (e x) : Matrix _ _ ℂ) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro x
    show (Qi * uMat x * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * uMat x * Q) = Formalism.QuantumDeterminants.Hpk k r
    have hx : (uMat x)ᴴ * Formalism.REAL.Jm ε * uMat x = Formalism.REAL.Jm ε := x.2
    calc (Qi * uMat x * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * uMat x * Q)
        = Qᴴ * ((uMat x)ᴴ * (Qiᴴ * Formalism.QuantumDeterminants.Hpk k r * Qi) * uMat x) * Q := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hqi, hx, hg]
  have hrange : ∀ y : Formalism.QuantumDeterminants.Mt k r, y ∈ Set.range e ↔ (Matrix.of y : Matrix _ _ ℂ) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩; exact eUH x
    · intro hy
      refine ⟨toUJn (Q * Matrix.of y * Qi) (cond_tr h2 hg hy), ?_⟩
      show Qi * (Q * Matrix.of y * Qi) * Q = y
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
      rw [Matrix.mul_assoc, h1, Matrix.mul_one]; rfl
  have hlm : ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := fun a => WlocSk.HM.lmul_meas a
  have hmulP : Measurable (WlocSk.mulP (k := k) (r := r)) := WlocSk.HM.mulP_meas
  haveI := hSB.1

  have lint_range : ∀ (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞), Measurable g →
      (∀ y, y ∉ Set.range e → g y = 0) → ∫⁻ y, g y ∂ν = ∫⁻ x, g (e x) ∂(ν.comap e) := by
    intro ν g hg hg0
    have h3 : g = (Set.range e).indicator g := by
      funext y
      by_cases hy : y ∈ Set.range e
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hg0 y hy]
    rw [h3, lintegral_indicator he.measurableSet_range, ← he.map_comap, he.lintegral_map]
    refine lintegral_congr fun x => ?_
    rw [Set.indicator_of_mem (Set.mem_range_self x)]
  set μSU := μSB.comap e with hμSU
  set νU := νB.comap e with hνU
  have hmapS : μSU.map e = μSB := by
    rw [hμSU, he.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    have h0 : μSB {x | (Matrix.of x : Matrix _ _ ℂ) ∉ Formalism.QuantumDeterminants.Sset k r z} = 0 := hSB.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    rw [hrange]
    simp only [Set.mem_setOf_eq, not_not] at hy
    exact hSsub hy
  have hInvU : QPK.InvOn μSU K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI := hSB.1
      exact SigmaFinite.of_map μSU he.measurable.aemeasurable (by rw [hmapS]; infer_instance)
    · intro h0; apply hSB.2.1; rw [← hmapS, h0, Measure.map_zero]
    · rw [hμSU, he.comap_apply]
      refine measure_mono_null ?_ hSB.2.2.1
      rintro _ ⟨x, hx, rfl⟩
      intro hxS
      exact hx ((hd x).1 hxS)
    · intro s hs
      have key : (μSU.map (fun x => s * x)).map e = μSU.map e := by
        rw [Measure.map_map he.measurable (measurable_const_mul s)]
        have hc : e ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (Matrix.of (e s)) ∘ e := by
          funext x
          simp only [Function.comp_apply, Formalism.QuantumDeterminants.lmulM]
          exact emul s x
        have hsS : (Matrix.of (e s) : Matrix _ _ ℂ) ∈ Formalism.QuantumDeterminants.Sset k r z := (hd s).2 hs
        rw [hc, ← Measure.map_map (hlm _) he.measurable, hmapS, hSB.2.2.2 _ hsS]
      have := congrArg (Measure.comap e) key
      rwa [he.comap_map, he.comap_map] at this

  have hWU : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, ∫⁻ s, F (s * x) ∂μSU ∂νU := by
    intro F hF
    set Ft := Function.extend e F 0 with hFtdef
    have hFt : Measurable Ft := he.measurable_extend hF measurable_const
    have hFte : ∀ x, Ft (e x) = F x := fun x => he.injective.extend_apply F 0 x
    have hFt0 : ∀ y, y ∉ Set.range e → Ft y = 0 := fun y hy => by
      rw [hFtdef, Function.extend_apply' F (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) y (by simpa using hy)]; rfl
    have e1 : ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ y, Ft y ∂((Formalism.REAL.muG ε).map e) := by
      rw [he.lintegral_map]; simp only [hFte]
    rw [e1, hQB Ft hFt]
    set I : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun y => ∫⁻ s, Ft (fun i j => (Matrix.of s * Matrix.of y) i j) ∂μSB with hIdef
    have hIm : Measurable I := by
      show Measurable fun y => ∫⁻ s, (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Ft (WlocSk.mulP p)) (s, y) ∂μSB
      exact Measurable.lintegral_prod_left' (hFt.comp hmulP)
    have hI0 : ∀ y, y ∉ Set.range e → I y = 0 := by
      intro y hy
      apply (lintegral_eq_zero_iff' ((hFt.comp hmulP).comp (measurable_id.prodMk measurable_const)).aemeasurable).2
      have h0 : μSB {x | (Matrix.of x : Matrix _ _ ℂ) ∉ Formalism.QuantumDeterminants.Sset k r z} = 0 := hSB.2.2.1
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
      simp only [Set.mem_setOf_eq, not_not] at hs
      apply hFt0
      intro hmem
      apply hy
      rw [hrange] at hmem ⊢
      have hsU := hSsub hs
      have hu := WlocSk.HM.isUnit_of_uh hsU
      have : (Matrix.of y : Matrix _ _ ℂ) = (Matrix.of s)⁻¹ * ((Matrix.of s) * Matrix.of y) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      rw [this]
      exact WlocSk.HM.uh_mul (WlocSk.HM.uh_inv hsU) hmem
    have hIe : ∀ x, I (e x) = ∫⁻ s, F (s * x) ∂μSU := by
      intro x
      rw [hIdef]
      simp only []
      rw [← hmapS, he.lintegral_map]
      · refine lintegral_congr fun s => ?_
        have : (fun i j => ((Matrix.of (e s) : Matrix _ _ ℂ) * Matrix.of (e x)) i j) = e (s * x) := by
          rw [← emul]; rfl
        rw [this, hFte]
    rw [lint_range νB I hIm hI0]
    simp only [hIe]
    rfl
  obtain ⟨c, hc0, hct, hμ⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ ε) K hKc hKg μSU μS hInvU hS
  have hWc : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, ∫⁻ s, F (s * x) ∂μS ∂(c • νU) := by
    intro F hF
    rw [hWU F hF, hμ, lintegral_smul_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hct]
  set F0 : Formalism.REAL.UJ ε → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ 2 with hF0
  have hF0m : Measurable F0 := hf.enorm.measurable.pow_const 2
  have hF0K : ∀ s ∈ K, ∀ x, F0 (s * x) = F0 x := by
    intro s hs x
    simp only [hF0]
    rw [← enorm_norm (f (s * x)), hfK s hs x, enorm_norm]
  have h_l := weil_bruhat K hS.2.2.1 hWl hβm hβ1 F0 hF0m hF0K
  have h_u := weil_bruhat K hS.2.2.1 hWc hβm hβ1 F0 hF0m hF0K
  rw [← h_l, lintegral_smul_measure, smul_eq_mul] at h_u

  have hwT : ∀ y : Formalism.QuantumDeterminants.Mt k r, ((‖wTg Q Qi f (Matrix.of y)‖₊ : ℝ≥0∞)) ^ 2 = Function.extend e F0 0 y := by
    intro y
    by_cases hy : y ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hy
      rw [he.injective.extend_apply F0 0 x]
      have : wTg Q Qi f (Matrix.of (e x)) = f x := by
        refine wTg_eq f x ?_
        show uMat x = Q * (Qi * uMat x * Q) * Qi
        simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
        rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      rw [this]; rfl
    · rw [Function.extend_apply' F0 (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) y (by simpa using hy)]
      have : wTg Q Qi f (Matrix.of y) = 0 := by
        unfold wTg
        rw [dif_neg]
        rintro ⟨γ, hγ⟩
        apply hy
        refine ⟨γ, ?_⟩
        show Qi * uMat γ * Q = y
        rw [hγ]
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rw [Matrix.mul_assoc, h1, Matrix.mul_one]; rfl
      rw [this]; simp
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.2 hct, ENNReal.inv_ne_top.2 hc0, ?_⟩
  unfold l2SG
  simp only [hwT]
  have hz0 : ∀ y, y ∉ Set.range e → Function.extend e F0 (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) y = 0 := fun y hy => by
    rw [Function.extend_apply' F0 (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) y (by simpa using hy)]; rfl
  rw [lint_range νB (Function.extend e F0 (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)) (he.measurable_extend hF0m measurable_const) hz0]
  have hext : ∀ x, Function.extend e F0 (0 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (e x) = F0 x :=
    fun x => he.injective.extend_apply F0 0 x
  simp only [hext]
  show ∫⁻ x, F0 x ∂νU = c⁻¹ * ∫⁻ x, F0 x ∂νl
  rw [← h_u, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end Tr

section L2Step

open Classical Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.WuDec

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def SDict (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
    Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) ↔
      γ ∈ NHloc X u (vOf X τ)

def SDictAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) u τ, SDict C u τ

theorem sset_sub_UH {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.Sset k r z ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  intro g hg
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  simp only [Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hh hm ⊢
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * hᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = mᴴ * (hᴴ * Formalism.QuantumDeterminants.Hpk k r * h) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hh.1, hm.1]

theorem bruhat_loc (X : HidaSetting D) (u : D.what₂.Word) {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {Cc : ℝ≥0∞}
    (hQ : QuotWit X u μS νl Cc) (v : InfinitePlace X.B.I.F) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧ ∀ x, ∫⁻ s, β (s * x) ∂(μS v) = 1 := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := place_facts X u v
  obtain ⟨-, -, hloc, -⟩ := hQ
  obtain ⟨hSv, -⟩ := hloc v
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v)
    (Hfix X u v) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  have hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v)) := by
    rw [← NHloc_eq]; exact hSv
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM
  refine ⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun x => ?_⟩
  rw [hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
    smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]

theorem local_l2_all_of_dictionary (hD : SDictAll) : L2ConditionAllChoices := by
  intro D hG X θ C u τ
  obtain ⟨μS, νl, Cc, hQ⟩ := quotAll_of Formalism.L2.SG.Closed.QuotProdK_holds Formalism.L2.SG.Pf.WFL.locHNProps_holds
    Formalism.L2.SG.Closed.NUnimodLoc_holds D X u
  obtain ⟨hL0, hLt⟩ := localRepresentationL2 X u hQ (vOf X τ)
  obtain ⟨β, hβm, hβ1⟩ := bruhat_loc X u hQ (vOf X τ)
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, -⟩ := place_facts X u (vOf X τ)
  have hKc : IsClosed (NHloc X u (vOf X τ)) := by rw [NHloc_eq]; exact QPK.prodSet_isClosed hNc hHc
  have hKg : QPK.IsGrp (NHloc X u (vOf X τ)) := by rw [NHloc_eq]; exact QPK.prodSet_isGrp hNg hHg hnorm
  have hQ' := hQ
  obtain ⟨-, -, hloc, -⟩ := hQ'
  obtain ⟨hSv, hWv⟩ := hloc (vOf X τ)
  have hfK : ∀ s ∈ NHloc X u (vOf X τ), ∀ x, ‖X.Wloc u (vOf X τ) (s * x)‖ = ‖X.Wloc u (vOf X τ) x‖ := by
    rintro s ⟨m, hm, h, hh, rfl⟩ x
    exact norm_Wloc_inv X u (vOf X τ) (mul_mem_Sloc X u _ (Nloc_sub X u _ hm) (Hloc_sub X u _ hh)) x
  obtain ⟨c, hc0, hct, heq⟩ := exists_const_l2SG_transport_eq_mul_lintegral (n_eq' X) (X.B.I.ε (vOf X τ)) (C.isT τ).1 (C.isT τ).2.1 (C.isT τ).2.2.1
    (NHloc X u (vOf X τ)) hKc hKg (hD D X θ C u τ) (sset_sub_UH _) (muS_haar C u τ) (C.nuS_q u τ) hSv hWv hβm hβ1
    (X.Wloc u (vOf X τ)) (X.Wloc_cont u _) hfK
  have e : l2SG (C.nuS u τ) (wT C u τ) = c * ∫⁻ x, ‖X.Wloc u (vOf X τ) x‖ₑ ^ 2 ∂(νl (vOf X τ)) := heq
  rw [e]
  exact ⟨mul_ne_zero hc0 hL0, ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (lt_top_iff_ne_top.2 hLt)⟩

end L2Step

end Formalism.L2.SG.Pf.LocF
