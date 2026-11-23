import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralFinsetSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralZeroOfTwistedPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionTwistDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnFinsetLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtSuperconnFibreStatement

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.TorsionFormCover

theorem finite_quotient {g : ℕ} (M M' : Submodule ℤ (Fl g)) (hM : IsLat M) (hM' : IsLat M') (hle : M ≤ M') :
    Finite (M' ⧸ M.submoduleOf M') :=
  GlobalTheory.T.finite_quotient_of_isLat_le' M M' hM hM' hle

theorem setIntegral_eq_smul_of_le {g : ℕ} (M M' : Submodule ℤ (Fl g)) (hM : IsLat M) (hM' : IsLat M') (hle : M ≤ M')
    (D : Set (Fl g)) (hD : IsAddFundamentalDomain M D volume) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
      (ψ : Fl g → V), Continuous ψ → (∀ l ∈ M', ∀ x, ψ (x + l) = ψ x) →
      ∀ D' : Set (Fl g), IsAddFundamentalDomain M' D' volume →
        ∫ x in D, ψ x = c • ∫ x in D', ψ x :=
  GlobalTheory.T.fundamental_domain_integral_ratio M M' hM hM' hle D hD

theorem setIntegral_finset_sum_of_periodic {g : ℕ} (M : Submodule ℤ (Fl g)) (hM : IsLat M) (D : Set (Fl g))
    (hD : IsAddFundamentalDomain M D volume) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {ι : Type} (s : Finset ι) (ψ : ι → Fl g → V)
    (hc : ∀ i ∈ s, Continuous (ψ i)) (hp : ∀ i ∈ s, ∀ l ∈ M, ∀ x, ψ i (x + l) = ψ i x) :
    ∫ x in D, ∑ i ∈ s, ψ i x = ∑ i ∈ s, ∫ x in D, ψ i x :=
  GlobalTheory.T.fundamental_domain_integral_finset_sum M hM D hD V s ψ hc hp

theorem setIntegral_eq_zero_of_twist {g : ℕ} (M : Submodule ℤ (Fl g)) (hM : IsLat M) (D : Set (Fl g))
    (hD : IsAddFundamentalDomain M D volume) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (ψ : Fl g → V) (l₀ : Fl g) (a : ℂ) (hp : ∀ l ∈ M, ∀ x, ψ (x + l) = ψ x)
    (ht : ∀ x, ψ (x + l₀) = a • ψ x) (ha : a ≠ 1) : ∫ x in D, ψ x = 0 :=
  GlobalTheory.T.integral_zero_of_twisted_periodic M hM D hD V ψ l₀ a hp ht ha

theorem exists_twist_decomposition {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {M M' : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    (hj : IsFactor B τ M' j) (hle : M ≤ M') [Finite (M' ⧸ M.submoduleOf M')] (b : E) (hb : b ∈ B)
    (f : (Fin g → ℂ) → Ext m) (hf : IsSec τ M j b f) :
    ∃ F : AddChar (M' ⧸ M.submoduleOf M') ℂ → (Fin g → ℂ) → Ext m,
      (∀ χ, IsSec τ M' (twistFactor M M' χ j) b (F χ)) ∧ ∀ z, ∑ᶠ χ, F χ z = f z :=
  GlobalTheory.T.theta_section_twist_decomposition hj hle b hb f hf

theorem superconn_finset_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) :
    superconn τ h β u (fun Q => ∑ i ∈ s, a i • F i Q) P = ∑ i ∈ s, a i • superconn τ h β u (F i) P :=
  GlobalTheory.T.superconn_finset_linear τ h β u s a F P hF

theorem differentiableAt_superconn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}
    (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P)
    (β : Fin n → E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)) (hf : ContDiff ℝ ∞ f)
    (b : E) (hb : b ∈ B) (z : Fin g → ℂ) :
    DifferentiableAt ℝ (superconn τ h β u fun P => f P.2) (b, z) :=
  GlobalTheory.T.differentiableAt_superconn_fibre hτ hh hpos β u f hf b hb z

theorem per_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x l : Fl g) :
    per τ (x + l) = per τ x + per τ l := by
  funext i; simp [per, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]; ring

theorem continuous_per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Continuous (per τ) := by
  unfold per; fun_prop

theorem continuous_strN {m g : ℕ} : Continuous (strN (m := m) (g := g)) := by
  unfold strN; fun_prop

theorem twistFactor_of_mem' {E : Type} {g : ℕ} {M M' : Submodule ℤ (Fl g)}
    (χ : AddChar (M' ⧸ M.submoduleOf M') ℂ) (j : Fl g → Pt E g → ℂ) {l : Fl g} (hl : l ∈ M')
    (P : Pt E g) : twistFactor M M' χ j l P = χ (Submodule.Quotient.mk ⟨l, hl⟩) * j l P := by
  unfold twistFactor; rw [dif_pos hl]

theorem twistFactor_of_mem {E : Type} {g : ℕ} {M M' : Submodule ℤ (Fl g)} (hle : M ≤ M')
    (χ : AddChar (M' ⧸ M.submoduleOf M') ℂ) (j : Fl g → Pt E g → ℂ) {l : Fl g} (hl : l ∈ M)
    (P : Pt E g) : twistFactor M M' χ j l P = j l P := by
  rw [twistFactor_of_mem' χ j (hle hl)]
  have : (Submodule.Quotient.mk ⟨l, hle hl⟩ : M' ⧸ M.submoduleOf M') = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (by simpa [Submodule.submoduleOf] using hl)
  rw [this, AddChar.map_zero_eq_one, one_mul]

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (χ : AddChar A ℂ) (a : A) : χ a ≠ 0 := by
  intro h0
  have := AddChar.map_add_eq_mul χ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
  exact one_ne_zero this

theorem strN_smul_sum {m g : ℕ} {ι : Type} (s : Finset ι) (a : ℂ)
    (A : ι → Ext (m + g) →L[ℂ] Ext (m + g)) :
    strN (a • ∑ i ∈ s, A i) = a • ∑ i ∈ s, strN (A i) := by
  funext S
  simp only [strN, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I _ => by ring

theorem phi_sum {m : ℕ} {ι : Type} (s : Finset ι) (w : ι → Ext m) :
    phi (∑ i ∈ s, w i) = ∑ i ∈ s, phi (w i) := by
  funext S; simp [phi, Finset.sum_apply, Finset.mul_sum]

theorem isMellinDeriv_zero : IsMellinDeriv (fun _ => 0) 0 :=
  ⟨0, 0, by simp, by simp, by simp⟩

theorem isMellinDeriv_add {F G : ℝ → ℂ} {T U : ℂ} (hF : IsMellinDeriv F T)
    (hG : IsMellinDeriv G U) : IsMellinDeriv (fun u => F u + G u) (T + U) := by
  obtain ⟨C₁, C₀, i1, i2, e⟩ := hF
  obtain ⟨D₁, D₀, j1, j2, e'⟩ := hG
  have k1 : (fun u : ℝ => (F u + G u - (C₁ + D₁) / u - (C₀ + D₀)) / u) =
      fun u => (F u - C₁ / u - C₀) / u + (G u - D₁ / u - D₀) / u := by
    funext u; ring
  have k2 : (fun u : ℝ => (F u + G u) / u) = fun u => F u / u + G u / u := by
    funext u; ring
  refine ⟨C₁ + D₁, C₀ + D₀, ?_, ?_, ?_⟩
  · rw [k1]; exact i1.add j1
  · rw [k2]; exact i2.add j2
  · rw [k1, k2, integral_add i1 j1, integral_add i2 j2, e, e']; ring

theorem isMellinDeriv_sum {ι : Type} (s : Finset ι) (F : ι → ℝ → ℂ) (T : ι → ℂ)
    (hF : ∀ i ∈ s, IsMellinDeriv (F i) (T i)) :
    IsMellinDeriv (fun u => ∑ i ∈ s, F i u) (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMellinDeriv_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact isMellinDeriv_add (hF i (Finset.mem_insert_self _ _))
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

theorem tendstoLocallyUniformly_sum {X V : Type} [TopologicalSpace X] [NormedAddCommGroup V]
    {ι : Type} (s : Finset ι) {F : ι → ℝ → X → V} {f : ι → X → V} {l : Filter ℝ}
    (hF : ∀ i ∈ s, TendstoLocallyUniformly (F i) (f i) l) :
    TendstoLocallyUniformly (fun t x => ∑ i ∈ s, F i t x) (fun x => ∑ i ∈ s, f i x) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu x => ⟨univ, univ_mem, .of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

theorem curv_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}
    (hτ : IsPeriodMap B τ) (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P)
    (β : Fin n → E) (b : E) (hb : b ∈ B) (u : ℝ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (f : ι → (Fin g → ℂ) → Ext (n + n + g)) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (z : Fin g → ℂ) :
    curv τ h β b u (fun y => ∑ i ∈ s, a i • f i y) z = ∑ i ∈ s, a i • curv τ h β b u (f i) z := by
  unfold curv
  have inner : (superconn τ h β u fun P : Pt E g => ∑ i ∈ s, a i • f i P.2) =
      fun P => ∑ i ∈ s, a i • superconn τ h β u (fun Q : Pt E g => f i Q.2) P := by
    funext P
    exact superconn_finset_sum τ h β u s a (fun i Q => f i Q.2) P fun i hi =>
      ((hf i hi).differentiable (by simp)).differentiableAt.comp P differentiableAt_snd
  rw [inner]
  exact superconn_finset_sum τ h β u s a (fun i => superconn τ h β u fun Q : Pt E g => f i Q.2) (b, z)
    fun i hi => differentiableAt_superconn hτ hh hpos β u (f i) (hf i hi) b hb z

theorem coverSum : CoverSum := by
  intro E _ _ _ g n B τ M M' j h hDat hM hle β b hb T hT
  classical
  obtain ⟨hτ, hM', hfac, hmet⟩ := hDat
  haveI : Finite (M' ⧸ M.submoduleOf M') := finite_quotient M M' hM hM' hle
  haveI : Fintype (AddChar (M' ⧸ M.submoduleOf M') ℂ) := Fintype.ofFinite _
  have hT' : ∀ χ, ∃ F, IsHeatTrace τ M' (twistFactor M M' χ j) h β b F ∧
      ∀ S, IsMellinDeriv (fun u => F u S) (T χ S) := hT
  choose F hF hMel using hT'
  have hF' : ∀ χ, ∃ D : Set (Fl g), IsAddFundamentalDomain M' D volume ∧ ∀ u > 0, ∃ K,
      IsHeatKernel τ M' (twistFactor M M' χ j) h β b u D K ∧
        F χ u = phi (∫ x in D, strN (K 1 (per (τ b) x) (per (τ b) x))) := hF
  choose D hD hK using hF'
  choose K hKh hKF using hK
  have hMl : IsLat M := hM
  obtain ⟨hdisc, hzl⟩ := hM
  have hD0 : IsAddFundamentalDomain M (GlobalTheory.latticeDomain M) volume :=
    GlobalTheory.isAddFundamentalDomain_latticeDomain M volume
  obtain ⟨c, hc0, hc⟩ := setIntegral_eq_smul_of_le M M' hMl hM' hle _ hD0
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc0
  have hKc : ∀ χ u (hu : u > 0) t, t > 0 →
      Continuous (fun p : (Fin g → ℂ) × (Fin g → ℂ) => K χ u hu t p.1 p.2) := by
    intro χ u hu t ht
    exact (hKh χ u hu).1.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun p => ⟨ht, mem_univ _⟩)
  have hfacne : ∀ χ (l : Fl g) (hl : l ∈ M') (w : Fin g → ℂ), twistFactor M M' χ j l (b, w) ≠ 0 := by
    intro χ l hl w
    rw [twistFactor_of_mem' χ j hl]
    exact mul_ne_zero (addChar_ne_zero _ _) ((hfac.1 l hl).2 (b, w) ⟨hb, mem_univ _⟩)
  unfold IsTorsionForm IsHeatTrace
  refine ⟨fun u => ∑ χ, F χ u, ⟨GlobalTheory.latticeDomain M, hD0, fun u hu => ?_⟩, fun S => ?_⟩
  swap
  · have e : (∑ᶠ χ, T χ) S = ∑ χ, T χ S := by rw [finsum_eq_sum_of_fintype, Finset.sum_apply]
    rw [e]
    have := isMellinDeriv_sum Finset.univ (fun χ u => F χ u S) (fun χ => T χ S) fun χ _ => hMel χ S
    simp only [Finset.sum_apply]
    exact this
  refine ⟨fun t z z' => ((c : ℂ)⁻¹) • ∑ χ, K χ u hu t z z', ?_, ?_⟩
  · unfold IsHeatKernel
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (ContDiffOn.sum (s := Finset.univ)
        (f := fun χ (a : ℝ × (Fin g → ℂ) × (Fin g → ℂ)) => K χ u hu a.1 a.2.1 a.2.2)
        fun χ _ => (hKh χ u hu).1).const_smul ((c : ℂ)⁻¹)
    · intro t ht l hl z z'
      beta_reduce
      have e1 : ∀ χ, K χ u hu t (z + per (τ b) l) z' = j l (b, z) • K χ u hu t z z' := fun χ => by
        rw [((hKh χ u hu).2.1 t ht l (hle hl) z z').1, twistFactor_of_mem hle χ j hl]
      have e2 : ∀ χ, j l (b, z') • K χ u hu t z (z' + per (τ b) l) = K χ u hu t z z' := fun χ => by
        rw [← twistFactor_of_mem hle χ j hl]; exact ((hKh χ u hu).2.1 t ht l (hle hl) z z').2
      refine ⟨?_, ?_⟩
      · simp only [e1, ← Finset.smul_sum]; rw [smul_comm]
      · rw [smul_comm, Finset.smul_sum]; simp only [e2]
    · intro t ht z z' w
      beta_reduce
      have hd := HasDerivAt.fun_sum (u := Finset.univ) (A := fun χ t' => K χ u hu t' z z' w)
        fun χ _ => (hKh χ u hu).2.2.1 t ht z z' w
      have hd2 := hd.const_smul ((c : ℂ)⁻¹)
      have hsm : ∀ χ, ContDiff ℝ ∞ (fun y => K χ u hu t y z' w) := fun χ =>
        contDiff_iff_contDiffAt.2 fun y => by
          have hA : ContDiffAt ℝ ∞ (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) => K χ u hu a.1 a.2.1 a.2.2)
              (t, y, z') := (hKh χ u hu).1.contDiffAt (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem)
          have hB : ContDiffAt ℝ ∞ (fun y' : Fin g → ℂ => (t, y', z')) y :=
            contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const)
          exact (((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) w).restrictScalars ℝ).contDiff.contDiffAt).comp y
            (ContDiffAt.comp (g := fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) => K χ u hu a.1 a.2.1 a.2.2)
            (f := fun y' : Fin g → ℂ => (t, y', z')) y hA hB)
      have e1 : (fun t' => ((c : ℂ)⁻¹ • ∑ χ, K χ u hu t' z z') w) =
          fun t' => (c : ℂ)⁻¹ • ∑ χ, K χ u hu t' z z' w := by
        funext t'; simp [ContinuousLinearMap.sum_apply]
      have e : (fun y => ((c : ℂ)⁻¹ • ∑ χ, K χ u hu t y z') w) =
          fun y => ∑ χ, (c : ℂ)⁻¹ • K χ u hu t y z' w := by
        funext y; simp [ContinuousLinearMap.sum_apply, Finset.smul_sum]
      rw [e1, e, curv_sum hτ hmet.1 hmet.2.1 β b hb u Finset.univ (fun _ => (c : ℂ)⁻¹) _
        (fun χ _ => hsm χ) z]
      refine hd2.congr_deriv ?_
      simp [Finset.smul_sum]
    · intro f hf
      obtain ⟨Fc, hFc, hsum⟩ := exists_twist_decomposition hfac hle b hb f hf
      have hlim := tendstoLocallyUniformly_sum Finset.univ
        (fun χ _ => (hKh χ u hu).2.2.2 (Fc χ) (hFc χ))
      have hf' : (fun z => ∑ χ, Fc χ z) = f := by
        funext z; rw [← hsum z, finsum_eq_sum_of_fintype]
      rw [hf'] at hlim
      have key : ∀ t > 0, ∀ z, ∫ x in GlobalTheory.latticeDomain M,
          ((c : ℂ)⁻¹ • ∑ χ, K χ u hu t z (per (τ b) x)) (f (per (τ b) x)) =
          ∑ χ, ∫ x in D χ, K χ u hu t z (per (τ b) x) (Fc χ (per (τ b) x)) := by
        intro t ht z
        set ψ : AddChar (M' ⧸ M.submoduleOf M') ℂ → AddChar (M' ⧸ M.submoduleOf M') ℂ →
            Fl g → Ext (n + n + g) :=
          fun χ χ' x => K χ u hu t z (per (τ b) x) (Fc χ' (per (τ b) x)) with hψ
        have hpc := continuous_per (τ b)
        have hψc : ∀ χ χ', Continuous (ψ χ χ') := fun χ χ' =>
          ((hKc χ u hu t ht).comp (continuous_const.prodMk hpc)).clm_apply
            ((hFc χ').1.continuous.comp hpc)
        have hA : ∀ χ χ' (l : Fl g) (hl : l ∈ M') x,
            ψ χ χ' (x + l) = twistFactor M M' χ' j l (b, per (τ b) x) •
              K χ u hu t z (per (τ b) x + per (τ b) l) (Fc χ' (per (τ b) x)) ∧
            ψ χ χ' x = twistFactor M M' χ j l (b, per (τ b) x) •
              K χ u hu t z (per (τ b) x + per (τ b) l) (Fc χ' (per (τ b) x)) := by
          intro χ χ' l hl x
          constructor
          · simp only [hψ, per_add, (hFc χ').2 l hl, map_smul]
          · simp only [hψ]
            rw [← ((hKh χ u hu).2.1 t ht l hl z (per (τ b) x)).2, ContinuousLinearMap.smul_apply]
        have hMper : ∀ χ χ' (l : Fl g), l ∈ M → ∀ x, ψ χ χ' (x + l) = ψ χ χ' x := by
          intro χ χ' l hl x
          obtain ⟨h1, h2⟩ := hA χ χ' l (hle hl) x
          rw [h1, h2, twistFactor_of_mem hle χ' j hl, twistFactor_of_mem hle χ j hl]
        have off : ∀ χ χ', χ' ≠ χ → ∫ x in GlobalTheory.latticeDomain M, ψ χ χ' x = 0 := by
          intro χ χ' hne
          obtain ⟨q, hq⟩ : ∃ q, χ' q ≠ χ q := by
            by_contra hcon; push_neg at hcon; exact hne (DFunLike.ext χ' χ hcon)
          obtain ⟨⟨l, hl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
          refine setIntegral_eq_zero_of_twist M hMl _ hD0 _ (ψ χ χ') l
            (χ' (Submodule.Quotient.mk ⟨l, hl⟩) * (χ (Submodule.Quotient.mk ⟨l, hl⟩))⁻¹)
            (hMper χ χ') (fun x => ?_) ?_
          · obtain ⟨h1, h2⟩ := hA χ χ' l hl x
            rw [h1, h2, smul_smul, twistFactor_of_mem' χ' j hl, twistFactor_of_mem' χ j hl]
            congr 1
            rw [mul_assoc, ← mul_assoc (χ _)⁻¹, inv_mul_cancel₀ (addChar_ne_zero _ _), one_mul]
          · intro h1
            exact hq ((mul_inv_eq_one₀ (addChar_ne_zero _ _)).1 h1)
        have diag : ∀ χ, ∫ x in GlobalTheory.latticeDomain M, ψ χ χ x = c • ∫ x in D χ, ψ χ χ x := by
          intro χ
          refine hc _ (ψ χ χ) (hψc χ χ) (fun l hl x => ?_) (D χ) (hD χ)
          obtain ⟨h1, h2⟩ := hA χ χ l hl x
          rw [h1, h2]
        have hfx : ∀ x, f (per (τ b) x) = ∑ χ', Fc χ' (per (τ b) x) := fun x => by
          rw [← hsum, finsum_eq_sum_of_fintype]
        have e1 : (fun x => ((c : ℂ)⁻¹ • ∑ χ, K χ u hu t z (per (τ b) x)) (f (per (τ b) x))) =
            fun x => (c : ℂ)⁻¹ • ∑ p : AddChar (M' ⧸ M.submoduleOf M') ℂ ×
              AddChar (M' ⧸ M.submoduleOf M') ℂ, ψ p.1 p.2 x := by
          funext x
          rw [hfx x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
            Fintype.sum_prod_type]
          simp only [hψ, map_sum]
        rw [e1, integral_smul, setIntegral_finset_sum_of_periodic M hMl _ hD0 _ Finset.univ (fun (p : AddChar (M' ⧸ M.submoduleOf M') ℂ × AddChar (M' ⧸ M.submoduleOf M') ℂ) x => ψ p.1 p.2 x)
          (fun p _ => hψc _ _) (fun p _ l hl x => hMper p.1 p.2 l hl x), Fintype.sum_prod_type]
        have e4 : ∀ χ, ∑ χ', ∫ x in GlobalTheory.latticeDomain M, ψ χ χ' x =
            ∫ x in GlobalTheory.latticeDomain M, ψ χ χ x :=
          fun χ => Finset.sum_eq_single χ (fun χ' _ hne => off χ χ' hne) (by simp)
        simp only [e4, diag]
        rw [Finset.smul_sum]
        simp only [← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hcC, one_smul, hψ]
      intro U hU x
      obtain ⟨V, hV, hev⟩ := hlim U hU x
      refine ⟨V, hV, ?_⟩
      filter_upwards [hev, self_mem_nhdsWithin] with t h1 h2 y hy
      beta_reduce
      rw [key t h2 y]
      exact h1 y hy
  · beta_reduce
    have hdiagc : ∀ χ, Continuous fun x => strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)) :=
      fun χ => continuous_strN.comp
        ((hKc χ u hu 1 one_pos).comp ((continuous_per _).prodMk (continuous_per _)))
    have hdiagp : ∀ χ, ∀ l ∈ M', ∀ x, strN (K χ u hu 1 (per (τ b) (x + l)) (per (τ b) (x + l))) =
        strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)) := by
      intro χ l hl x
      obtain ⟨k1, -⟩ := (hKh χ u hu).2.1 1 one_pos l hl (per (τ b) x) (per (τ b) x + per (τ b) l)
      obtain ⟨-, k2⟩ := (hKh χ u hu).2.1 1 one_pos l hl (per (τ b) x) (per (τ b) x)
      rw [per_add, k1, k2]
    have e2 : ∀ χ, ∫ x in GlobalTheory.latticeDomain M, strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)) =
        c • ∫ x in D χ, strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)) := fun χ =>
      hc _ _ (hdiagc χ) (hdiagp χ) (D χ) (hD χ)
    have e3 : (fun x => strN ((c : ℂ)⁻¹ • ∑ χ, K χ u hu 1 (per (τ b) x) (per (τ b) x))) =
        fun x => (c : ℂ)⁻¹ • ∑ χ, strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)) := by
      funext x; exact strN_smul_sum _ _ _
    rw [e3, integral_smul, setIntegral_finset_sum_of_periodic M hMl _ hD0 _ Finset.univ
      (fun χ x => strN (K χ u hu 1 (per (τ b) x) (per (τ b) x)))
      (fun χ _ => hdiagc χ) (fun χ _ l hl x => hdiagp χ l (hle hl) x)]
    simp only [e2, ← Complex.coe_smul, Finset.smul_sum, smul_smul, inv_mul_cancel₀ hcC, one_smul,
      phi_sum]
    exact Finset.sum_congr rfl fun χ _ => hKF χ u hu

end GlobalTheory.TorsionFormCover
