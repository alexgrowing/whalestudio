import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift

section General

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {n : ℕ}

theorem analytic_eval {G : (Fin n → ℂ) → (Σ k, J k) → ℂ} {T : Set (Fin n → ℂ)}
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (f : MRing J) :
    AnalyticOnNhd ℂ (fun w => eval (G w) (map (Int.castRingHom ℂ) f)) T := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticOnNhd_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X]
    exact hp.mul (hG i)

theorem isOpen_forall_ne {A : Type} [Finite A] {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    {f : A → (Fin n → ℂ) → ℂ} (hf : ∀ a, AnalyticOnNhd ℂ (f a) T) :
    IsOpen {w | w ∈ T ∧ ∀ a, f a w ≠ 0} := by
  have e : {w | w ∈ T ∧ ∀ a, f a w ≠ 0} = T ∩ ⋂ a, (T ∩ f a ⁻¹' {0}ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, fun a => ⟨h.1, h.2 a⟩⟩, fun h => ⟨h.1, fun a => (h.2 a).2⟩⟩
  rw [e]
  exact hT.inter (isOpen_iInter_of_finite fun a =>
    (hf a).continuousOn.isOpen_inter_preimage hT isOpen_compl_singleton)

theorem form_notMem_iff (z : (Σ k, J k) → ℂ) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∉ mCoordIdeal z ↔ eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
  rw [Ne, form_mem_mCoordIdeal_iff z hg, aeval_def, algebraMap_int_eq, eval₂_eq_eval_map]

theorem exists_normalised {A : Type} [Finite A] (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (s : A → Ω)
    (G : (Fin n → ℂ) → (Σ k, J k) → ℂ) {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (hmem : ∀ w ∈ T, G w ∈ mcPts (mCoordIdeal x))
    {w₀ : Fin n → ℂ} (hw₀ : w₀ ∈ T) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ mCoordIdeal (G w₀))
    (hreg : ∀ a, RegAt x (mCoordIdeal (G w₀)) (s a)) :
    ∃ (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, J k) → ℂ), V ⊆ T ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
      (∀ a, AnalyticOnNhd ℂ (fun w => valAt x (s a) (bl w)) V) ∧
      ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal x) ∧ (∀ k, bl w ⟨k, c k⟩ = 1) ∧ SameOrbit (G w) (bl w) ∧
        ∀ a, RegAt x (mCoordIdeal (bl w)) (s a) := by
  choose d g h hg hh hnot heq using hreg
  have hX : ∀ (k : K) (i : J k), IsMultiHomog (X ⟨k, i⟩ : MRing J) (fun k' => if k' = k then 1 else 0) := fun k i =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩
  have hx : ∀ a, aeval x (h a) ≠ 0 := fun a e0 => by
    have h1 := (hmem w₀ hw₀).2 _ (mem_mCoordIdeal_of_aeval_eq_zero x (hh a) e0)
    exact (form_notMem_iff _ (hh a)).1 (hnot a) h1
  set bl : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun w p => G w p / G w ⟨p.1, c p.1⟩ with hbl
  set T₁ : Set (Fin n → ℂ) := {w | w ∈ T ∧ ∀ k, G w ⟨k, c k⟩ ≠ 0} with hT₁
  have hT₁o : IsOpen T₁ := isOpen_forall_ne hT fun k => hG ⟨k, c k⟩
  have hT₁T : T₁ ⊆ T := fun w hw => hw.1
  have hblq : ∀ q, AnalyticOnNhd ℂ (fun w => bl w q) T₁ := fun q =>
    ((hG q).mono hT₁T).div ((hG ⟨q.1, c q.1⟩).mono hT₁T) fun w hw => hw.2 q.1
  have hevh : ∀ a, AnalyticOnNhd ℂ (fun w => eval (bl w) (map (Int.castRingHom ℂ) (h a))) T₁ := fun a =>
    analytic_eval hblq (h a)
  have horb : ∀ w ∈ T₁, SameOrbit (G w) (bl w) := fun w hw =>
    ⟨fun k => G w ⟨k, c k⟩, hw.2, funext fun p => by
      have := hw.2 p.1
      simp only [hbl]
      field_simp⟩
  have hw₁ : w₀ ∈ T₁ := ⟨hw₀, fun k e0 => (form_notMem_iff _ (hX k (c k))).1 (hc k) (by simpa using e0)⟩
  refine ⟨{w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0}, bl,
    fun w hw => hw.1.1, isOpen_forall_ne hT₁o hevh, ⟨hw₁, fun a => ?_⟩, fun q => (hblq q).mono fun w hw => hw.1,
    fun a => ?_, fun w hw => ?_⟩
  · rw [← form_notMem_iff _ (hh a), ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit (horb w₀ hw₁)]
    exact hnot a
  · have hV : IsOpen {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} :=
      isOpen_forall_ne hT₁o hevh
    refine AnalyticOnNhd.congr hV (((analytic_eval hblq (g a)).mono fun w hw => hw.1).div
      ((hevh a).mono fun w hw => hw.1) fun w hw => hw.2 a) fun w hw => ?_
    have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact (valAt_eq hz ⟨d a, g a, h a, hg a, hh a, hx a, heq a, hw.2 a, rfl⟩).symm
  · have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact ⟨hz, fun k => div_self (hw.1.2 k), horb w hw.1,
      fun a => ⟨d a, g a, h a, hg a, hh a, (form_notMem_iff _ (hh a)).2 (hw.2 a), heq a⟩⟩

end General

theorem exists_baseChart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X)
    (hgood : M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀))) :
    ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ),
      x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  obtain ⟨kb, hkb⟩ := Rb.A.cover x₀
  have hT : IsOpen ((Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀) :=
    (Rb.A.chart kb).isOpen_inter_preimage_symm (Rb.isOpen_U x₀)
  have hlw : Rb.lift x₀ ((Rb.A.chart kb).symm (Rb.A.chart kb x₀)) = Rb.lift x₀ x₀ := by
    rw [(Rb.A.chart kb).left_inv hkb]
  have hw₀ : Rb.A.chart kb x₀ ∈ (Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀ :=
    ⟨(Rb.A.chart kb).map_source hkb, by
      show (Rb.A.chart kb).symm (Rb.A.chart kb x₀) ∈ Rb.U x₀
      rw [(Rb.A.chart kb).left_inv hkb]
      exact Rb.mem_U x₀⟩
  let s : (((Σ k, ι k) × Finset (Fin N)) ⊕ ((Σ k, ι k) × Finset (Fin N))) ⊕
      ({p : Ψ × Fin N // M.blk p = none} ⊕ {p : Ψ × Fin N // M.blk p = none}) → M.Ω :=
    Sum.elim (Sum.elim (fun a => F.u a.1 a.2) (fun a => F.u' a.2 a.1))
      (Sum.elim (fun p => F.υ p.1) (fun p => (F.υ p.1)⁻¹))
  obtain ⟨V, bl, hVT, hVo, hV₀, hq, hval, hpt⟩ := exists_normalised M.x F.c s
    (fun w => Rb.lift x₀ ((Rb.A.chart kb).symm w)) hT (fun q => Rb.holo x₀ q kb)
    (fun w hw => Rb.mem x₀ _ hw.2) hw₀
    (by simpa only [hlw] using hgood.1)
    (by
      simp only [hlw]
      rintro ((⟨q, I⟩ | ⟨q, I⟩) | (⟨p, hp⟩ | ⟨p, hp⟩))
      · exact (hgood.2.1 q I).1
      · exact (hgood.2.1 q I).2
      · exact (hgood.2.2 p hp).2.1
      · exact (hgood.2.2 p hp).2.2)
  refine ⟨kb, V, bl, hkb, hV₀, hVo, fun w hw => (hVT hw).1, hq,
    fun q I => hval (Sum.inl (Sum.inl (q, I))), fun w hw => ?_⟩
  obtain ⟨hz, h1, hor, hr⟩ := hpt w hw
  refine ⟨hz, h1, ⟨fun k e0 => ?_, fun q I => ⟨hr (Sum.inl (Sum.inl (q, I))), hr (Sum.inl (Sum.inr (q, I)))⟩,
    fun p hp => ⟨(hgood.2.2 p hp).1, hr (Sum.inr (Sum.inl ⟨p, hp⟩)), hr (Sum.inr (Sum.inr ⟨p, hp⟩))⟩⟩,
    orbit_trans (Rb.compat _ x₀ _ ⟨Rb.mem_U _, (hVT hw).2⟩) hor⟩
  have := (form_mem_mCoordIdeal_iff (bl w) (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single
    (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k))).1 e0
  rw [aeval_X, h1 k] at this
  exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift
