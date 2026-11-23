import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricLoc
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricConj

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Generic

variable {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_logSq_ev {W : Y.Opens} (u : Γ(Y, W)ˣ) (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => Real.log (‖ev p σ W u.val z‖ ^ 2)) y := by
  refine ⟨W, Unit, inferInstance, fun _ => u.val, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0}, hy,
    isOpen_ne_fun (continuous_apply ()) continuous_const, ev_ne_zero hy u.isUnit, ?_,
    Filter.EventuallyEq.rfl⟩
  refine ContDiffOn.log ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn ?_
  intro v hv
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

theorem cInfAt_sum {ι : Type} (s : Finset ι) {f : ι → CxPts p σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (0 : ℝ) y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Generic

section Transport

variable {X : Scheme.{0}} {p : X ⟶ Sp k}

private theorem phi_sub_logSq_eq_of_mem_overlap (A : LB X) (hA : A.IsLB) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a a' : L.B.ι) (b : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (ha' : y ∈ ptsIn p σ (L.B.U a')) (hb : y ∈ ptsIn p σ (A.U b)) :
    (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) =
      (L.φ σ).φ a' y - y.logSq (L.B.U a' ⊓ A.U b) (w.s (a', b)) := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a', b)) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ha' hb ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a', b))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have hbb : y.logSq (A.U b ⊓ A.U b) (A.g b b) = 0 := by
    have h0 := congrArg (y.logSq _) (hA.g_self b)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto)] at h0
    exact h0
  have ht := (L.φ σ).trans a a' y ha ha'
  have hl : Real.log (‖gv p σ L.B a a' y‖ ^ 2) = y.logSq (L.B.U a ⊓ L.B.U a') (L.B.g a a') := rfl
  rw [hl] at ht
  rw [hbb] at hg
  linarith

private theorem logSq_inf_eq_add_logSq_transition (A : LB X) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a : L.B.ι) (b b' : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (hb : y ∈ ptsIn p σ (A.U b)) (hb' : y ∈ ptsIn p σ (A.U b')) :
    y.logSq (L.B.U a ⊓ A.U b') (w.s (a, b')) =
      y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) + y.logSq (A.U b ⊓ A.U b') (A.g b b') := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a, b')) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha hb hb' ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a, b'))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have haa : y.logSq (L.B.U a ⊓ L.B.U a) (L.B.g a a) = 0 := by
    have h0 := congrArg (y.logSq _) (L.isLB.g_self a)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto)] at h0
    exact h0
  rw [haa] at hg
  linarith

theorem exists_transport (A : LB X) (hA : A.IsLB) (L : HermLB p) (hL : LBIso A L.B) :
    ∃ (χ : ∀ σ : k →+* ℂ, Weight p σ A) (hc : ∀ σ, (χ σ).IsCInf) (hj : ∀ σ σ', (χ σ).IsConj (χ σ')),
      (⟨A, hA, χ, hc, hj⟩ : HermLB p).Isometric L := by
  obtain ⟨w, hw⟩ := hL
  have hcov : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ a, y ∈ ptsIn p σ (L.B.U a) := by
    intro σ y
    have h : ∀ x : X, ∃ a, x ∈ L.B.U a := by
      intro x
      have hx : x ∈ (⨆ i, L.B.U i) := by
        rw [L.isLB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun a ha => mem_ptsIn.mpr ha
  let F : ∀ σ : k →+* ℂ, A.ι → CxPts p σ → ℝ := fun σ b y =>
    (L.φ σ).φ (hcov σ y).choose y -
      y.logSq (L.B.U (hcov σ y).choose ⊓ A.U b) (w.s ((hcov σ y).choose, b))
  have hF : ∀ (σ : k →+* ℂ) (b : A.ι) (y : CxPts p σ) (a : L.B.ι), y ∈ ptsIn p σ (L.B.U a) →
      y ∈ ptsIn p σ (A.U b) → F σ b y = (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) :=
    fun σ b y a ha hb => phi_sub_logSq_eq_of_mem_overlap A hA L w hw σ _ a b y (hcov σ y).choose_spec ha hb
  have htr : ∀ (σ : k →+* ℂ) (i j : A.ι), ∀ y ∈ ptsIn p σ (A.U i), y ∈ ptsIn p σ (A.U j) →
      F σ j y = F σ i y - Real.log (‖gv p σ A i j y‖ ^ 2) := by
    intro σ i j y hi hj
    obtain ⟨a, ha⟩ := hcov σ y
    rw [hF σ j y a ha hj, hF σ i y a ha hi]
    have h2 := logSq_inf_eq_add_logSq_transition A L w hw σ a i j y ha hi hj
    have hl : Real.log (‖gv p σ A i j y‖ ^ 2) = y.logSq (A.U i ⊓ A.U j) (A.g i j) := rfl
    rw [hl]
    linarith
  let χ : ∀ σ : k →+* ℂ, Weight p σ A := fun σ => ⟨hA, F σ, htr σ⟩
  have hc : ∀ σ, (χ σ).IsCInf := by
    intro σ b y hb
    obtain ⟨a, ha⟩ := hcov σ y
    have hS : ptsIn p σ (L.B.U a) ∩ ptsIn p σ (A.U b) ∈ 𝓝 y :=
      ((isOpen_ptsIn _).inter (isOpen_ptsIn _)).mem_nhds ⟨ha, hb⟩
    have h2 := cInfAt_logSq_ev (W := L.B.U a ⊓ A.U b) (w.s (a, b)) (mem_ptsIn_inf.mpr ⟨ha, hb⟩)
    have h1 : CInfAt (fun z => (L.φ σ).φ a z - z.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))) y :=
      ((L.cInf σ a y ha).add h2.neg).congr (Filter.Eventually.of_forall fun z => sub_eq_add_neg _ _)
    exact h1.congr (Filter.mem_of_superset hS fun z hz => hF σ b z a hz.1 hz.2)
  have hj : ∀ σ σ', (χ σ).IsConj (χ σ') := by
    intro σ σ' b y y' hyy' hb
    obtain ⟨a, ha⟩ := hcov σ y
    have ha' := (mem_ptsIn_iff_of_conj hyy').mpr ha
    have hb' := (mem_ptsIn_iff_of_conj hyy').mpr hb
    show F σ' b y' = F σ b y
    rw [hF σ' b y' a ha' hb', hF σ b y a ha hb, L.conj σ σ' a y y' hyy' ha]
    congr 1
    unfold CxPts.logSq
    rw [ev_conj hyy' (mem_ptsIn_inf.mpr ⟨ha, hb⟩), Complex.norm_conj]
  refine ⟨χ, hc, hj, w, hw, ?_⟩
  intro σ a b y ha hb
  have h3 := hF σ b y a ha hb
  show (L.φ σ).φ a y = F σ b y + y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))
  linarith

end Transport

section Glue

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem mem_ptsIn_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c : B.ι) (x : CxPts p σ)
    (h : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c)) : x ∈ ptsIn p σ ((B.pull i).U fun _ => c) := by
  have h1 := (mem_ptsIn_preimage (m := PtsOver.map i hi (spMap σ)) (fun z => rfl)).mpr h
  rw [mem_ptsIn] at h1 ⊢
  simp only [LB.pull, LB.LinComb]
  rw [← SetLike.mem_coe]
  simpa [LB.wchart] using h1

theorem gv_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c c' : B.ι) (x : CxPts p σ)
    (h : x ∈ ptsIn p σ ((B.pull i).U fun _ => c)) (h' : x ∈ ptsIn p σ ((B.pull i).U fun _ => c')) :
    gv p σ (B.pull i) (fun _ => c) (fun _ => c') x = gv q σ B c c' (PtsOver.map i hi (spMap σ) x) :=
  (gv_linComb (m := fun _ => PtsOver.map i hi (spMap σ) x) (fun _ => rfl) h h').trans (by simp)

private theorem logSq_cocycle {Y : Scheme.{0}} {r : Y ⟶ Sp k} {σ : k →+* ℂ} (B : LB Y)
    (hB : B.IsLB) (c₁ c₂ c₃ : B.ι) (z : CxPts r σ) (h₁ : z ∈ ptsIn r σ (B.U c₁))
    (h₂ : z ∈ ptsIn r σ (B.U c₂)) (h₃ : z ∈ ptsIn r σ (B.U c₃)) :
    z.logSq (B.U c₁ ⊓ B.U c₂) (B.g c₁ c₂) + z.logSq (B.U c₂ ⊓ B.U c₃) (B.g c₂ c₃) =
      z.logSq (B.U c₁ ⊓ B.U c₃) (B.g c₁ c₃) := by
  have h0 := congrArg (z.logSq _) (hB.cocycle c₁ c₂ c₃)
  rw [logSq_mul (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto)] at h0
  exact h0

theorem exists_weight_ext_sigma (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (σ : k →+* ℂ) (χ : Weight p σ (B.pull i)) (hχ : χ.IsCInf) :
    ∃ ψ : Weight q σ B, ψ.IsCInf ∧ ∀ (c : B.ι) (x : CxPts p σ),
      PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) → ψ.φ c (PtsOver.map i hi (spMap σ) x) = χ.φ (fun _ => c) x := by
  haveI : CompactSpace (CxPts q σ) := compactSpace σ hP.isProjOver
  haveI : T2Space (CxPts q σ) := t2Space_cxPts_of_isProjOver σ hP.isProjOver
  obtain ⟨R⟩ := hs σ
  set m := PtsOver.map i hi (spMap σ) with hm
  have hmc : IsClosed (range m) := (PtsOver.isClosedEmbedding_map i hi (spMap σ)).isClosed_range
  have hcov : ∀ y : CxPts q σ, ∃ c, y ∈ ptsIn q σ (B.U c) := by
    intro y
    have h : ∀ x : P, ∃ c, x ∈ B.U c := by
      intro x
      have hx : x ∈ (⨆ c, B.U c) := by
        rw [hB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun c hc => mem_ptsIn.mpr hc
  have loc : ∀ y : CxPts q σ, ∃ (c : B.ι) (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ),
      IsOpen V ∧ y ∈ V ∧ V ⊆ ptsIn q σ (B.U c) ∧ (∀ z ∈ V, CInfAt θ z) ∧
        ∀ x : CxPts p σ, m x ∈ V → θ (m x) = χ.φ (fun _ => c) x := by
    intro y
    obtain ⟨c, hc⟩ := hcov y
    by_cases hy : y ∈ range m
    · obtain ⟨x₀, rfl⟩ := hy
      have hx₀ := mem_ptsIn_pull i hi B c x₀ hc
      obtain ⟨V, θ, hV, hV₀, hθ, heq⟩ := exists_local_ext i hi (χ.φ fun _ => c) x₀ (hχ (fun _ => c) x₀ hx₀)
      exact ⟨c, V ∩ ptsIn q σ (B.U c), θ, hV.inter (isOpen_ptsIn _), ⟨hV₀, hc⟩, inter_subset_right,
        fun z hz => hθ z hz.1, fun x hx => heq x hx.1⟩
    · refine ⟨c, (range m)ᶜ ∩ ptsIn q σ (B.U c), fun _ => 0, hmc.isOpen_compl.inter (isOpen_ptsIn _),
        ⟨hy, hc⟩, inter_subset_right, fun z _ => cInfAt_const 0 z, ?_⟩
      intro x hx
      exact absurd (mem_range_self x) hx.1
  choose cc V θ hVo hyV hVsub hθ hθx using loc
  obtain ⟨n, a, ρ, hρs, hρ0, hρsupp, hρ1⟩ := exists_partition R V hVo (fun y => ⟨y, hyV y⟩)
  have hzero : ∀ t z, ρ t z ≠ 0 → z ∈ V (a t) := fun t z h0 =>
    hρsupp t (subset_tsupport _ (Function.mem_support.mpr h0))
  let Ψ : B.ι → CxPts q σ → ℝ := fun c z =>
    ∑ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))
  have htr : ∀ (c c' : B.ι), ∀ z ∈ ptsIn q σ (B.U c), z ∈ ptsIn q σ (B.U c') →
      Ψ c' z = Ψ c z - Real.log (‖gv q σ B c c' z‖ ^ 2) := by
    intro c c' z hz hz'
    have key : ∀ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c') (B.g (cc (a t)) c')) =
        ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) -
          ρ t z * z.logSq (B.U c ⊓ B.U c') (B.g c c') := by
      intro t
      by_cases h0 : ρ t z = 0
      · simp [h0]
      have hzc := hVsub (a t) (hzero t z h0)
      have h3 := logSq_cocycle B hB (cc (a t)) c c' z hzc hz hz'
      rw [← h3]
      ring
    have hl : Real.log (‖gv q σ B c c' z‖ ^ 2) = z.logSq (B.U c ⊓ B.U c') (B.g c c') := rfl
    show ∑ t : Fin n, _ = ∑ t : Fin n, _ - _
    rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_sub_distrib, ← Finset.sum_mul, hρ1, one_mul, hl]
  refine ⟨⟨hB, Ψ, htr⟩, ?_, ?_⟩
  · intro c z hz
    show CInfAt (fun w => ∑ t : Fin n, ρ t w *
      (θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))) z
    apply cInfAt_sum
    intro t _
    by_cases hzV : z ∈ V (a t)
    · have hzc := hVsub (a t) hzV
      have h2 := cInfAt_logSq_ev (W := B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)
        (mem_ptsIn_inf.mpr ⟨hzc, hz⟩)
      have h1 : CInfAt (fun w => θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) z :=
        ((hθ (a t) z hzV).add h2.neg).congr (Filter.Eventually.of_forall fun w => sub_eq_add_neg _ _)
      exact cInfAt_mul (hρs t z) h1
    · have hns : z ∉ tsupport (ρ t) := fun h => hzV (hρsupp t h)
      have hev := (notMem_tsupport_iff_eventuallyEq.mp hns)
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hev] with w hw
      simp only [Pi.zero_apply] at hw
      simp [hw]
  · intro c x hx
    show ∑ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
      CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = χ.φ (fun _ => c) x
    have key : ∀ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
        CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = ρ t (m x) * χ.φ (fun _ => c) x := by
      intro t
      by_cases h0 : ρ t (m x) = 0
      · simp [h0]
      have hzV := hzero t (m x) h0
      have hzc := hVsub (a t) hzV
      rw [hθx (a t) x hzV]
      have hxa := mem_ptsIn_pull i hi B (cc (a t)) x hzc
      have hxc := mem_ptsIn_pull i hi B c x hx
      have htrχ := χ.trans (fun _ => cc (a t)) (fun _ => c) x hxa hxc
      rw [gv_pull i hi B (cc (a t)) c x hxa hxc] at htrχ
      have hl : Real.log (‖gv q σ B (cc (a t)) c (PtsOver.map i hi (spMap σ) x)‖ ^ 2) =
          CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c) := rfl
      rw [hl] at htrχ
      rw [htrχ]
    rw [Finset.sum_congr rfl (fun t _ => key t), ← Finset.sum_mul, hρ1, one_mul]

end Glue

section Conj

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem cInfAt_conj {σ : k →+* ℂ} {f : CxPts q ((starRingEnd ℂ).comp σ) → ℝ} {y : CxPts q σ}
    (h : CInfAt f (conjPts q rfl y)) : CInfAt (fun z => f (conjPts q rfl z)) y := by
  obtain ⟨W, ι, hι, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hy' : y ∈ ptsIn q σ W := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mp hyW
  have evrel : ∀ z ∈ ptsIn q σ W, ∀ a, ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl z) =
      starRingEnd ℂ (ev q σ W (g a) z) := fun z hz a => ev_conj rfl hz (g a)
  have hc1 : ContDiff ℝ ∞ (fun z : ℂ => starRingEnd ℂ z) := by
    have h0 := Complex.conjCLE.contDiff (n := ∞)
    convert h0 using 1
    funext z
    simp
  let c : (ι → ℂ) → (ι → ℂ) := fun v a => starRingEnd ℂ (v a)
  have hc : ContDiff ℝ ∞ c := contDiff_pi.mpr fun a => hc1.comp (contDiff_apply ℝ ℂ a)
  refine ⟨W, ι, hι, g, fun v => F (c v), c ⁻¹' O, hy', hO.preimage hc.continuous, ?_,
    hF.comp hc.contDiffOn (mapsTo_preimage c O), ?_⟩
  · show (fun a => starRingEnd ℂ (ev q σ W (g a) y)) ∈ O
    have he : (fun a => starRingEnd ℂ (ev q σ W (g a) y)) =
        fun a => ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl y) :=
      funext fun a => (evrel y hy' a).symm
    rw [he]
    exact hmem
  · have h1 := hev.comp_tendsto ((conjPts q rfl).continuous.tendsto y)
    have h2 : ptsIn q σ W ∈ 𝓝 y := (isOpen_ptsIn W).mem_nhds hy'
    filter_upwards [h1, h2] with z hz hzW
    simp only [Function.comp] at hz
    rw [hz]
    show F _ = F _
    congr 1
    funext a
    exact evrel z hzW a

theorem exists_weight_ext (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (χ : ∀ σ : k →+* ℂ, Weight p σ (B.pull i))
    (hχ : ∀ σ, (χ σ).IsCInf) (hχc : ∀ σ σ', (χ σ).IsConj (χ σ')) :
    ∃ ψ : ∀ σ : k →+* ℂ, Weight q σ B, (∀ σ, (ψ σ).IsCInf) ∧ (∀ σ σ', (ψ σ).IsConj (ψ σ')) ∧
      ∀ (σ : k →+* ℂ) (c : B.ι) (x : CxPts p σ), PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) →
        (ψ σ).φ c (PtsOver.map i hi (spMap σ) x) = (χ σ).φ (fun _ => c) x := by
  choose ψ0 hψ0c hψ0e using fun σ => exists_weight_ext_sigma i hi hP hs B hB σ (χ σ) (hχ σ)
  have hcongr : ∀ (c : B.ι) (σ1 σ2 : k →+* ℂ), σ1 = σ2 → ∀ (z1 : CxPts q σ1) (z2 : CxPts q σ2),
      (z1 : Sp ℂ ⟶ P) = z2 → (ψ0 σ1).φ c z1 = (ψ0 σ2).φ c z2 := by
    intro c σ1 σ2 h z1 z2 hz
    subst h
    rw [Subtype.ext hz]
  have hLconj : ∀ (σ : k →+* ℂ) (c c' : B.ι) (y : CxPts q σ), y ∈ ptsIn q σ (B.U c ⊓ B.U c') →
      Real.log (‖gv q ((starRingEnd ℂ).comp σ) B c c' (conjPts q rfl y)‖ ^ 2) =
        Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hy
    unfold CxPts.gv
    rw [ev_conj rfl hy, Complex.norm_conj]
  let Ψ : ∀ σ : k →+* ℂ, B.ι → CxPts q σ → ℝ := fun σ c y =>
    ((ψ0 σ).φ c y + (ψ0 ((starRingEnd ℂ).comp σ)).φ c (conjPts q rfl y)) / 2
  have htr : ∀ (σ : k →+* ℂ) (c c' : B.ι), ∀ y ∈ ptsIn q σ (B.U c), y ∈ ptsIn q σ (B.U c') →
      Ψ σ c' y = Ψ σ c y - Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hc hc'
    have hc2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc
    have hc2' := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc'
    have e1 := (ψ0 σ).trans c c' y hc hc'
    have e2 := (ψ0 ((starRingEnd ℂ).comp σ)).trans c c' _ hc2 hc2'
    rw [hLconj σ c c' y (mem_ptsIn_inf.mpr ⟨hc, hc'⟩)] at e2
    show (_ + _) / 2 = (_ + _) / 2 - _
    rw [e1, e2]
    ring
  refine ⟨fun σ => ⟨hB, Ψ σ, htr σ⟩, ?_, ?_, ?_⟩
  · intro σ c y hy
    have hy2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hy
    have h1 := hψ0c σ c y hy
    have h2 := cInfAt_conj (f := (ψ0 ((starRingEnd ℂ).comp σ)).φ c) (hψ0c _ c _ hy2)
    exact h1.comp₂ h2 (G := fun v => (v.1 + v.2) / 2) (by fun_prop)
  · intro σ σ' c y y' hyy' hy
    have hσ := eq_conj_of_conj hyy'
    subst hσ
    have hy' : y' = conjPts q rfl y := Subtype.ext hyy'
    subst hy'
    show ((ψ0 _).φ c (conjPts q rfl y) + (ψ0 _).φ c (conjPts q rfl (conjPts q rfl y))) / 2 =
      ((ψ0 σ).φ c y + (ψ0 _).φ c (conjPts q rfl y)) / 2
    rw [hcongr c ((starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ)) σ (RingHom.ext fun x => by simp)
      (conjPts q rfl (conjPts q rfl y)) y ((conjHomeomorph P).left_inv _)]
    ring
  · intro σ c x hx
    have hxp := mem_ptsIn_pull i hi B c x hx
    have hmx : conjPts q rfl (PtsOver.map i hi (spMap σ) x) =
        PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) := by
      apply Subtype.ext
      show spMap (starRingEnd ℂ) ≫ ((x : Sp ℂ ⟶ X) ≫ i) = (spMap (starRingEnd ℂ) ≫ (x : Sp ℂ ⟶ X)) ≫ i
      exact (Category.assoc _ _ _).symm
    have hx2 : PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) ∈
        ptsIn q ((starRingEnd ℂ).comp σ) (B.U c) := by
      rw [← hmx]
      exact (mem_ptsIn_iff_of_conj rfl).mpr hx
    show ((ψ0 σ).φ c (PtsOver.map i hi (spMap σ) x) +
      (ψ0 _).φ c (conjPts q rfl (PtsOver.map i hi (spMap σ) x))) / 2 = (χ σ).φ (fun _ => c) x
    rw [hψ0e σ c x hx, hmx, hψ0e _ c (conjPts p rfl x) hx2, hχc σ _ (fun _ => c) x (conjPts p rfl x) rfl hxp]
    ring

end Conj

end GlobalTheory.AmbMetric
