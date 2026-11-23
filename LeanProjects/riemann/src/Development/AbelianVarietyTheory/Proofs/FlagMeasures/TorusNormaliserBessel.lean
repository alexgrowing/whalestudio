import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselMove

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

abbrev MM (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem inv_mem {g : MM k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).2.1

theorem mul_mem' {g h : MM k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).2.2 h hh

theorem unit_of {g : MM k r} (hg : g ∈ GG k r) : IsUnit g :=
  (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1

theorem mul_inv' {g : MM k r} (hg : g ∈ GG k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of hg))

theorem inv_mul' {g : MM k r} (hg : g ∈ GG k r) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of hg))

theorem mic {g : MM k r} (hg : g ∈ GG k r) (x : MM k r) : g * (g⁻¹ * x) = x := by
  rw [← Matrix.mul_assoc, mul_inv' hg, Matrix.one_mul]

theorem imc {g : MM k r} (hg : g ∈ GG k r) (x : MM k r) : g⁻¹ * (g * x) = x := by
  rw [← Matrix.mul_assoc, inv_mul' hg, Matrix.one_mul]

section rep

variable {R : Rep k r}

theorem sig_mul (hR : IsURepOn (GG k r) R.σ) {a b : MM k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) (v : R.H) :
    R.σ (a * b) v = R.σ a (R.σ b v) := by
  rw [hR.1.2 a ha b hb]; rfl

theorem sig_one (hR : IsURepOn (GG k r) R.σ) (v : R.H) : R.σ 1 v = v := by
  rw [hR.1.1]; rfl

theorem sig_sm (hR : IsURepOn (GG k r) R.σ) {c : MM k r} (hc : c ∈ GG k r) {v : R.H} (hv : v ∈ R.sm) :
    R.σ c v ∈ R.sm := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hag⟩ := hv (g₀ * c) (mul_mem' (g := g₀) hg₀ hc)
  let L := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c)
  have hL : ∀ x, L x = x * c := fun x => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, hgU,
    hF.comp L.contDiff.contDiffOn (fun x hx => hx), fun x hx hxH => ?_⟩
  have e := hag (x * c) hx (mul_mem' (g := x) hxH hc)
  show R.σ x (R.σ c v) = F (x * c)
  rw [← e]
  exact (sig_mul hR (a := x) hxH hc v).symm

def sigEquiv (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) : R.H ≃L[ℝ] R.H :=
  ContinuousLinearEquiv.equivOfInverse ((R.σ g).restrictScalars ℝ) ((R.σ g⁻¹).restrictScalars ℝ)
    (fun v => by
      show R.σ g⁻¹ (R.σ g v) = v
      rw [← sig_mul hR (inv_mem hg) hg, inv_mul' hg, sig_one hR])
    (fun v => by
      show R.σ g (R.σ g⁻¹ v) = v
      rw [← sig_mul hR hg (inv_mem hg), mul_inv' hg, sig_one hR])

theorem dsig_sigma (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) {X : MM k r}
    (hX : PI.UpqRep.InLieHpk k r X) (v : R.H) :
    PI.UpqRep.dsig (k := k) (r := r) R.σ X (R.σ g v) =
      R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ (g⁻¹ * X * g) v) := by
  unfold PI.UpqRep.dsig
  have e : (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (R.σ g v)) =
      (sigEquiv hR hg) ∘ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • (g⁻¹ * X * g))) v) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • X) ∈ GG k r :=
      CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t)
    show _ = R.σ g (R.σ (NormedSpace.exp ((t : ℂ) • (g⁻¹ * X * g))) v)
    have e1 : (t : ℂ) • (g⁻¹ * X * g) = g⁻¹ * ((t : ℂ) • X) * g := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_conj' _ _ (unit_of hg), ← sig_mul hR hm hg,
      ← sig_mul hR hg (mul_mem' (mul_mem' (inv_mem hg) hm) hg), Matrix.mul_assoc, mic hg]
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem dsigW_sigma (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) (W : List (MM k r))
    (hW : ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) (v : R.H) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, PI.UpqRep.InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show PI.UpqRep.dsig R.σ X (PI.UpqRep.dsigW R.σ W (R.σ g v)) =
      R.σ g (PI.UpqRep.dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', dsig_sigma hR hg (hW X List.mem_cons_self)]

theorem smMap_sigma (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) where
  mem v hv := sig_sm hR hg hv
  add v _ w _ := map_add _ _ _
  smul a v _ := map_smul _ _ _
  cont W hW := by
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact GlobalTheory.SmMapAct.inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hR hg W hW v, hR.2.1 g hg]

theorem sig_TK (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) {v : R.H} (hv : v ∈ R.TK) :
    R.σ g v ∈ R.TK := by
  unfold Rep.TK at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, v₀, hv₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨g * a, mul_mem' hg ha, v₀, hv₀, (sig_mul hR hg ha v₀).symm⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem sig_inner (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) (v w : R.H) :
    ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (LinearIsometry.mk (R.σ g : R.H →ₗ[ℂ] R.H) (hR.2.1 g hg)).inner_map_map v w

theorem bessel_transport (hR : IsURepOn (GG k r) R.σ) {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : MM k r → (Wp →L[ℂ] Wp)} {ψ ψ' : MM k r → ℂ} {t : MM k r}
    (ht : t ∈ GG k r) (hN : ∀ n ∈ Nset k r, t * n * t⁻¹ ∈ Nset k r) (hc : ∀ h ∈ UWset k r z, t * h = h * t)
    (hψ : ∀ n ∈ Nset k r, ψ' n = ψ (t * n * t⁻¹)) {B : R.H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ R.σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ' R.σ π (fun v => B (R.σ t v)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h hh m hm v hv => ?_,
    GlobalTheory.SmMapAct.cw_comp (smMap_sigma hR ht) h4⟩
  · show B (R.σ t (v + w)) = _
    rw [map_add, h1 _ (sig_sm hR ht hv) _ (sig_sm hR ht hw)]
  · show B (R.σ t (a • v)) = _
    rw [map_smul, h2 _ _ (sig_sm hR ht hv)]
  · show B (R.σ t (R.σ (h * m) v)) = _
    rw [hψ m hm, ← h3 h hh _ (hN m hm) _ (sig_sm hR ht hv),
      ← sig_mul hR ht (mul_mem' hh.1 hm.1), ← sig_mul hR (mul_mem' hh.1 (hN m hm).1) ht]
    congr 3
    simp only [Matrix.mul_assoc, inv_mul' ht, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hc h hh, Matrix.mul_assoc]

end rep

def conjE {t : MM k r} (ht : t ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (t⁻¹ * Matrix.of x * t) i j
  invFun x := fun i j => (t * Matrix.of x * t⁻¹) i j
  left_inv x := by
    show t * (t⁻¹ * Matrix.of x * t) * t⁻¹ = Matrix.of x
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  right_inv x := by
    show t⁻¹ * (t * Matrix.of x * t⁻¹) * t = Matrix.of x
    simp only [Matrix.mul_assoc, inv_mul' ht, Matrix.mul_one, imc ht]
  measurable_toFun := by
    apply Continuous.measurable
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def leftE {t : MM k r} (ht : t ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (t⁻¹ * Matrix.of x) i j
  invFun x := fun i j => (t * Matrix.of x) i j
  left_inv x := by
    show t * (t⁻¹ * Matrix.of x) = Matrix.of x
    exact mic ht _
  right_inv x := by
    show t⁻¹ * (t * Matrix.of x) = Matrix.of x
    exact imc ht _
  measurable_toFun := by
    apply Continuous.measurable
    exact continuous_const.matrix_mul continuous_id
  measurable_invFun := by
    apply Continuous.measurable
    exact continuous_const.matrix_mul continuous_id

theorem meas_lmul (a : MM k r) : Measurable (lmulM a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  exact continuous_const.matrix_mul continuous_id

theorem meas_mul : Measurable (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r)) := by
  apply Continuous.measurable
  exact continuous_fst.matrix_mul continuous_snd

theorem haar_conj {t : MM k r} (ht : t ∈ GG k r) {S : Set (MM k r)} (hN : ∀ n, n ∈ S ↔ t * n * t⁻¹ ∈ S)
    {μ : Measure (Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn S μ) :
    PI.BesselPeriodGGP.IsHaarOn S (μ.map (conjE ht)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  refine ⟨(conjE ht).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h
    exact h2 ((Measure.map_eq_zero_iff (conjE ht).measurable.aemeasurable).mp h)
  · rw [MeasurableEquiv.map_apply]
    convert h3 using 2
    ext x
    show t⁻¹ * Matrix.of x * t ∉ S ↔ Matrix.of x ∉ S
    rw [hN]
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  · rw [Measure.map_map (meas_lmul s) (conjE ht).measurable]
    conv_rhs => rw [← h4 _ ((hN s).mp hs)]
    rw [Measure.map_map (conjE ht).measurable (meas_lmul _)]
    congr 1
    funext x
    show s * (t⁻¹ * Matrix.of x * t) = t⁻¹ * (t * s * t⁻¹ * Matrix.of x) * t
    simp only [Matrix.mul_assoc, imc ht]

theorem prod_conj {t : MM k r} (ht : t ∈ GG k r) (μW μN : Measure (Mt k r)) [SFinite μW] [SFinite μN] :
    μW.prod (μN.map (conjE ht)) =
      (μW.prod μN).map (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (conjE ht)) := by
  conv_lhs => rw [← Measure.map_id (μ := μW)]
  rw [Measure.map_prod_map _ _ measurable_id (conjE ht).measurable]
  rfl

theorem ae_prod {S T : Set (MM k r)} {μW μN : Measure (Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn S μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn T μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ S ∧ Matrix.of p.2 ∈ T := by
  haveI := hW.1
  haveI := hN.1
  have a : ∀ᵐ x ∂μW, Matrix.of x ∈ S := hW.2.2.1
  have b : ∀ᵐ x ∂μN, Matrix.of x ∈ T := hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae a).and (Measure.quasiMeasurePreserving_snd.ae b)

theorem muS_conj {t : MM k r} (ht : t ∈ GG k r) {S T : Set (MM k r)} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn S μW) (hN : PI.BesselPeriodGGP.IsHaarOn T μN)
    (hc : ∀ h ∈ S, t * h = h * t) :
    Formalism.FourierDecayAlt.ThreeDimData.muSof μW (μN.map (conjE ht)) = (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN).map (conjE ht) := by
  haveI := hW.1
  haveI := hN.1
  unfold Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [prod_conj ht, Measure.map_map meas_mul (MeasurableEquiv.measurable _),
    Measure.map_map (conjE ht).measurable meas_mul]
  refine Measure.map_congr ?_
  filter_upwards [ae_prod hW hN] with p hp
  show Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t) = t⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * t
  have e : Matrix.of p.1 * t⁻¹ = t⁻¹ * Matrix.of p.1 := by
    calc Matrix.of p.1 * t⁻¹ = t⁻¹ * (t * Matrix.of p.1) * t⁻¹ := by rw [imc ht]
      _ = t⁻¹ * Matrix.of p.1 := by
        rw [hc _ hp.1]; simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
  simp only [← Matrix.mul_assoc, e]

theorem quot_conj {t : MM k r} (ht : t ∈ GG k r) {μG μS ν : Measure (Mt k r)}
    (hG : PI.BesselPeriodGGP.IsHaarOn (GG k r) μG) (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) :
    PI.BesselPeriodGGP.IsQuotMeas μG (μS.map (conjE ht)) (ν.map (leftE ht)) := by
  intro f hf
  have h1 : μG.map (leftE ht) = μG := hG.2.2.2 _ (inv_mem ht)
  conv_lhs => rw [← h1]
  rw [lintegral_map_equiv, lintegral_map_equiv, hq (fun a => f (leftE ht a)) (hf.comp (leftE ht).measurable)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_map_equiv]
  refine lintegral_congr fun s => ?_
  congr 1
  show t⁻¹ * (Matrix.of s * Matrix.of x) = t⁻¹ * Matrix.of s * t * (t⁻¹ * Matrix.of x)
  simp only [Matrix.mul_assoc, mic ht]

theorem bessel_move : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  intro _ k r Wp _ _ _ _ z π u c μW μN μG νq t ht hN hc hψ hS
  obtain ⟨s1, s2, s3, s4, hW, hμN, hG, hq⟩ := hS
  have hti : t⁻¹⁻¹ = t := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of ht))
  have hcan : ∀ n : MM k r, t * (t⁻¹ * n * t) * t⁻¹ = n := fun n => by
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  have hN' : ∀ n ∈ Nset k r, t⁻¹ * n * t ∈ Nset k r := fun n hn => by
    rw [hN, hcan]; exact hn
  have hc' : ∀ h ∈ UWset k r z, t⁻¹ * h = h * t⁻¹ := fun h hh => by
    calc t⁻¹ * h = t⁻¹ * (h * t) * t⁻¹ := by simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      _ = h * t⁻¹ := by rw [← hc h hh, imc ht]
  refine ⟨⟨s1, s2, s3, s4, hW, haar_conj ht hN hμN, hG, ?_⟩, fun R hR => ⟨fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_⟩⟩
  · have := quot_conj ht hG hq
    rw [← muS_conj ht hW hμN hc] at this
    exact this
  · exact bessel_transport hR ht (fun n hn => (hN n).mp hn) hc hψ hB
  · have h := bessel_transport (ψ' := psi k r z c) hR (inv_mem ht) (fun n hn => by rw [hti]; exact hN' n hn) hc'
      (fun n hn => by rw [hti, hψ _ (hN' n hn), hcan]) hB
    have e : (fun v => B (R.σ t (R.σ t⁻¹ v))) = B := by
      funext v
      rw [← sig_mul hR ht (inv_mem ht), mul_inv' ht, sig_one hR]
    rw [e] at h
    exact h
  · intro l₁ hl x hx v hv
    haveI := hW.1
    haveI := hμN.1
    rw [← (hl.2 _ (sig_sm hR (inv_mem ht) hx) _ (sig_TK hR (inv_mem ht) hv)).2]
    show _ = Formalism.FourierDecayAlt.ThreeDimData.be z cStd π R.σ μW (μN.map (conjE ht)) _ _
    unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [prod_conj ht, integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod hW hμN] with p hp
    show (⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) x⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ =
      (⟪R.σ t⁻¹ v, R.σ (Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t)) (R.σ t⁻¹ x)⟫_ℂ *
        star (psi k r z cStd (t⁻¹ * Matrix.of p.2 * t))) • π (Matrix.of p.1)⁻¹
    rw [hψ _ (hN' _ hp.2), hcan, ← sig_inner hR (inv_mem ht) v,
      ← sig_mul hR (inv_mem ht) (mul_mem' hp.1.1 hp.2.1),
      ← sig_mul hR (mul_mem' hp.1.1 (hN' _ hp.2).1) (inv_mem ht)]
    have e : Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t) * t⁻¹ = t⁻¹ * (Matrix.of p.1 * Matrix.of p.2) := by
      simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← hc' _ hp.1, Matrix.mul_assoc]
    rw [e]

end GlobalTheory.BesselMove

end
