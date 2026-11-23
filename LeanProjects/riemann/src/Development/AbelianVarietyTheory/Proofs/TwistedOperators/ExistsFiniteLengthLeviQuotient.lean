import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfFiniteDimensional

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology

namespace GlobalTheory.ThetaGLCover

section Homog

variable {H Y : Type} [Group H] [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]

def orbInd (r : Y → H → Y) (hc : ∀ y, Continuous (r y)) (ho : ∀ y, IsOpenMap (r y)) (y : Y) {K : Subgroup H}
    (h1 : IsOpen (K : Set H)) (h2 : IsCompact (K : Set H)) : SB Y :=
  ⟨(r y '' K).indicator fun _ => 1,
    GlobalTheory.SBExtend.indicator_mem_SB (h2.image (hc y)) ⟨(h2.image (hc y)).isClosed, ho y _ h1⟩⟩

variable {r : Y → H → Y} (hc : ∀ y, Continuous (r y)) (ho : ∀ y, IsOpenMap (r y))
  (h1 : ∀ x, r x 1 = x) (hm : ∀ x g h, r x (g * h) = r (r x g) h)

include h1 hm in

theorem exists_sum_orbInd {K : Subgroup H} (hK1 : IsOpen (K : Set H)) (hK2 : IsCompact (K : Set H)) (Φ : SB Y)
    (hΦ : ∀ y, ∀ x ∈ K, Φ.1 (r y x) = Φ.1 y) :
    ∃ t : Finset Y, (∀ y ∈ t, Φ.1 y ≠ 0) ∧ Φ = ∑ y ∈ t, Φ.1 y • orbInd r hc ho y hK1 hK2 := by
  classical
  obtain ⟨s, hs⟩ := Φ.2.2.isCompact.elim_finite_subcover (fun y => r y '' K) (fun y => ho y _ hK1)
    (fun y _ => Set.mem_iUnion.2 ⟨y, 1, K.one_mem, h1 y⟩)
  have hs' : ∀ z, Φ.1 z ≠ 0 → ∃ y ∈ s, z ∈ r y '' K := fun z hz => by
    simpa using hs (subset_tsupport _ hz)
  clear hs
  induction s using Finset.induction_on generalizing Φ with
  | empty =>
    refine ⟨∅, by simp, Subtype.ext (funext fun z => ?_)⟩
    by_contra hz
    simpa using hs' z hz
  | insert y s _ ih =>
    have hval : ∀ z ∈ r y '' K, Φ.1 z = Φ.1 y := by
      rintro _ ⟨x, hx, rfl⟩
      exact hΦ y x hx
    have hinv : ∀ z, ∀ x ∈ K, (r z x ∈ r y '' K ↔ z ∈ r y '' K) := by
      intro z x hx
      constructor
      · rintro ⟨u, hu, e⟩
        exact ⟨u * x⁻¹, K.mul_mem hu (K.inv_mem hx), by rw [hm, e, ← hm, mul_inv_cancel, h1]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u * x, K.mul_mem hu hx, hm _ _ _⟩
    set Ψ : SB Y := Φ - Φ.1 y • orbInd r hc ho y hK1 hK2 with hΨ
    have hΨv : ∀ z, Ψ.1 z = Φ.1 z - Φ.1 y * (r y '' K).indicator (fun _ => (1 : ℂ)) z := fun _ => rfl
    have hin : ∀ z ∈ r y '' K, Ψ.1 z = 0 := fun z hz => by
      rw [hΨv, Set.indicator_of_mem hz, hval z hz, mul_one, sub_self]
    have hout : ∀ z ∉ r y '' K, Ψ.1 z = Φ.1 z := fun z hz => by
      rw [hΨv, Set.indicator_of_notMem hz, mul_zero, sub_zero]
    obtain ⟨t, ht, e⟩ := ih Ψ (fun z x hx => by
        by_cases hz : z ∈ r y '' K
        · rw [hin z hz, hin _ ((hinv z x hx).2 hz)]
        · rw [hout z hz, hout _ (mt (hinv z x hx).1 hz), hΦ z x hx])
      (fun z hz => by
        have hz' : z ∉ r y '' K := fun h => hz (hin z h)
        obtain ⟨u, hu, h⟩ := hs' z (by rwa [← hout z hz'])
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact absurd h hz'
        · exact ⟨u, hu, h⟩)
    have ht' : ∀ z ∈ t, Ψ.1 z = Φ.1 z := fun z hz => hout z fun h => ht z hz (hin z h)
    have e' : Ψ = ∑ z ∈ t, Φ.1 z • orbInd r hc ho z hK1 hK2 :=
      e.trans (Finset.sum_congr rfl fun z hz => by rw [ht' z hz])
    by_cases hy : Φ.1 y = 0
    · refine ⟨t, fun z hz => ht' z hz ▸ ht z hz, ?_⟩
      rw [← e', hΨ, hy, zero_smul, sub_zero]
    · have hyt : y ∉ t := fun h => ht y h (hin y ⟨1, K.one_mem, h1 y⟩)
      refine ⟨insert y t, fun z hz => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact hy
        · exact ht' z hz ▸ ht z hz
      · rw [Finset.sum_insert hyt, ← e', hΨ, add_sub_cancel]

variable {M : Type} [AddCommGroup M] [Module ℂ M] (c : H →* ℂˣ) (l : SB Y →ₗ[ℂ] M)
  (hl : ∀ h (Φ Φ' : SB Y), (∀ y, Φ'.1 y = (c h : ℂ) * Φ.1 (r y h)) → l Φ' = l Φ)

include h1 hm hl in
theorem map_orbInd_translate (y : Y) (h : H) {K K' : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hK1' : IsOpen (K' : Set H)) (hK2' : IsCompact (K' : Set H))
    (hKK : ∀ x, x ∈ K' ↔ h⁻¹ * x * h ∈ K) :
    l (orbInd r hc ho (r y h) hK1 hK2) = (c h : ℂ) • l (orbInd r hc ho y hK1' hK2') := by
  rw [← map_smul]
  refine (hl h _ _ fun z => ?_).symm
  show (c h : ℂ) * (r y '' K').indicator (fun _ => (1 : ℂ)) z =
    (c h : ℂ) * (r (r y h) '' K).indicator (fun _ => (1 : ℂ)) (r z h)
  have : z ∈ r y '' K' ↔ r z h ∈ r (r y h) '' K := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (hKK u).1 hu, by rw [← hm, ← hm]; congr 1; group⟩
    · rintro ⟨u, hu, e⟩
      refine ⟨h * u * h⁻¹, (hKK _).2 (by simpa [mul_assoc] using hu), ?_⟩
      rw [hm, hm, e, ← hm, mul_inv_cancel, h1]
  by_cases hz : z ∈ r y '' K'
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (this.1 hz)]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (mt this.2 hz)]

include h1 hm hl in
theorem map_orbInd_normal (y : Y) {K J : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hJ1 : IsOpen (J : Set H)) (hJ2 : IsCompact (J : Set H))
    (hKc : ∀ x ∈ K, c x = 1) (hJK : J ≤ K) (hn : ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∃ a : ℂ, a ≠ 0 ∧ l (orbInd r hc ho y hK1 hK2) = a • l (orbInd r hc ho y hJ1 hJ2) := by
  have hv : ∀ z, (orbInd r hc ho y hK1 hK2).1 z = (r y '' K).indicator (fun _ => (1 : ℂ)) z := fun _ => rfl
  obtain ⟨t, ht, e⟩ := exists_sum_orbInd hc ho h1 hm hJ1 hJ2 (orbInd r hc ho y hK1 hK2) (fun z x hx => by
    have : r z x ∈ r y '' K ↔ z ∈ r y '' K := by
      constructor
      · rintro ⟨u, hu, e⟩
        exact ⟨u * x⁻¹, K.mul_mem hu (K.inv_mem (hJK hx)), by rw [hm, e, ← hm, mul_inv_cancel, h1]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u * x, K.mul_mem hu (hJK hx), hm _ _ _⟩
    rw [hv, hv]
    by_cases hz : z ∈ r y '' K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (this.2 hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (mt this.1 hz)])
  refine ⟨t.card, ?_, ?_⟩
  · intro h0
    have : t = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast h0)
    rw [this, Finset.sum_empty] at e
    have h2 := hv y
    rw [e, Set.indicator_of_mem (show y ∈ r y '' K from ⟨1, K.one_mem, h1 y⟩)] at h2
    exact zero_ne_one h2
  · rw [e, map_sum, Finset.sum_congr rfl (g := fun _ => l (orbInd r hc ho y hJ1 hJ2)), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
    intro z hz
    have hz' : z ∈ r y '' K := Set.mem_of_indicator_ne_zero (hv z ▸ ht z hz)
    rw [hv, Set.indicator_of_mem hz', one_smul]
    obtain ⟨u, hu, rfl⟩ := hz'
    rw [map_orbInd_translate hc ho h1 hm c l hl y u hJ1 hJ2 hJ1 hJ2 fun x => ⟨fun hx => by
      simpa using hn _ (K.inv_mem hu) x hx, fun hx => by simpa [mul_assoc] using hn _ hu _ hx⟩, hKc u hu]
    simp

include h1 hm hl in
theorem map_orbInd_le [IsTopologicalGroup H] (y : Y) {K J : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hJ1 : IsOpen (J : Set H)) (hJ2 : IsCompact (J : Set H))
    (hKc : ∀ x ∈ K, c x = 1) (hJK : J ≤ K) :
    ∃ a : ℂ, a ≠ 0 ∧ l (orbInd r hc ho y hK1 hK2) = a • l (orbInd r hc ho y hJ1 hJ2) := by
  let N : Subgroup H :=
    { carrier := {x | ∀ u ∈ K, u * x * u⁻¹ ∈ J}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {x x'} hx hx' u hu => by
        simpa [mul_assoc] using J.mul_mem (hx u hu) (hx' u hu)
      inv_mem' := fun {x} hx u hu => by simpa [mul_assoc] using J.inv_mem (hx u hu) }
  have hNJ : N ≤ J := fun x hx => by simpa using hx 1 K.one_mem
  have hN1 : IsOpen (N : Set H) := by
    refine N.isOpen_of_mem_nhds (g := 1) (hK2.eventually_forall_of_forall_eventually
      (P := fun x u => u * x * u⁻¹ ∈ J) fun u _ => ?_)
    exact (hJ1.preimage (f := fun z : H × H => z.2 * z.1 * z.2⁻¹) (by fun_prop)).mem_nhds (by simp)
  have hN2 : IsCompact (N : Set H) := hJ2.of_isClosed_subset (N.isClosed_of_isOpen hN1) hNJ
  have hn : ∀ x ∈ K, ∀ j ∈ N, x * j * x⁻¹ ∈ N := fun x hx j hj u hu => by
    simpa [mul_assoc] using hj _ (K.mul_mem hu hx)
  obtain ⟨a, ha, e⟩ := map_orbInd_normal hc ho h1 hm c l hl y hK1 hK2 hN1 hN2 hKc (hNJ.trans hJK) hn
  obtain ⟨b, hb, e'⟩ := map_orbInd_normal hc ho h1 hm c l hl y hJ1 hJ2 hN1 hN2 (fun x hx => hKc x (hJK hx)) hNJ
    fun x hx => hn x (hJK hx)
  exact ⟨a / b, div_ne_zero ha hb, by rw [e, e', smul_smul, div_mul_cancel₀ _ hb]⟩

omit hc ho in
include h1 hm hl in

theorem exists_generator [IsTopologicalGroup H] [SigmaCompactSpace H] [LocallyCompactSpace Y]
    (hcc : Continuous fun p : Y × H => r p.1 p.2) (htr : ∀ y y', ∃ h, r y h = y')
    (hb : ∀ U ∈ 𝓝 (1 : H), ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H) ∧ (K : Set H) ⊆ U)
    (hcs : IsSmoothChar c) : ∃ v : M, ∀ Φ, l Φ ∈ Submodule.span ℂ {v} := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · exact ⟨0, fun Φ => by rw [show Φ = 0 from Subtype.ext (funext fun y => hY.elim y), map_zero]; exact zero_mem _⟩
  have hc : ∀ y, Continuous (r y) := fun y => hcc.comp (Continuous.prodMk_right y)
  have ho : ∀ y, IsOpenMap (r y) := by
    letI : MulAction H Y :=
      { smul := fun g y => r y g⁻¹
        one_smul := fun y => by show r y 1⁻¹ = y; rw [inv_one, h1]
        mul_smul := fun g h y => by show r y (g * h)⁻¹ = r (r y h⁻¹) g⁻¹; rw [_root_.mul_inv_rev, hm] }
    haveI : ContinuousSMul H Y := ⟨hcc.comp (continuous_snd.prodMk continuous_fst.inv)⟩
    haveI : MulAction.IsPretransitive H Y := ⟨fun y y' => by
      obtain ⟨h, e⟩ := htr y y'
      exact ⟨h⁻¹, by show r y h⁻¹⁻¹ = y'; rw [inv_inv, e]⟩⟩
    intro y
    have := (isOpenMap_smul_of_sigmaCompact (G := H) y).comp (Homeomorph.inv H).isOpenMap
    convert this using 1
    funext g
    show r y g = r y g⁻¹⁻¹
    rw [inv_inv]
  have hker : (c.ker : Set H) ∈ 𝓝 1 := IsOpen.mem_nhds hcs c.ker.one_mem
  obtain ⟨K₀, a1, a2, a3⟩ := hb _ hker
  refine ⟨l (orbInd r hc ho y₀ a1 a2), fun Φ => ?_⟩
  obtain ⟨K, b1, b2, b3⟩ := hb _ (Filter.inter_mem hker
    (GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action H Y r h1 hm hcc Φ))
  obtain ⟨t, -, e⟩ := exists_sum_orbInd hc ho h1 hm b1 b2 Φ fun y x hx => (b3 hx).2 y
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun y _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨h, rfl⟩ := htr y₀ y
  let φ : H ≃ₜ H := (Homeomorph.mulLeft h⁻¹).trans (Homeomorph.mulRight h)
  let K' : Subgroup H := K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hK' : (K' : Set H) = φ ⁻¹' K := by ext x; simp [K', φ]
  have c1 : IsOpen (K' : Set H) := hK' ▸ b1.preimage φ.continuous
  have c2 : IsCompact (K' : Set H) := hK' ▸ φ.isCompact_preimage.2 b2
  have c3 : ∀ x ∈ K', c x = 1 := fun x hx => by
    have : c (h⁻¹ * x * h) = 1 := (b3 (show h⁻¹ * x * h ∈ K by simpa [K'] using hx)).1
    simpa [mul_comm] using this
  rw [map_orbInd_translate hc ho h1 hm c l hl y₀ h b1 b2 c1 c2 fun x => by simp [K']]
  refine Submodule.smul_mem _ _ ?_
  have d1 : IsOpen ((K' ⊓ K₀ : Subgroup H) : Set H) := c1.inter a1
  have d2 : IsCompact ((K' ⊓ K₀ : Subgroup H) : Set H) :=
    c2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ d1) Set.inter_subset_left
  obtain ⟨a, -, e1⟩ := map_orbInd_le hc ho h1 hm c l hl y₀ c1 c2 d1 d2 c3 inf_le_left
  obtain ⟨b, hb0, e2⟩ := map_orbInd_le hc ho h1 hm c l hl y₀ a1 a2 d1 d2 (fun x hx => a3 hx) inf_le_right
  rw [e1, e2]
  exact Submodule.mem_span_singleton.2 ⟨a / b, by rw [smul_smul, div_mul_cancel₀ _ hb0]⟩

end Homog

section Strata

open GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

theorem continuous_slice {X G : Type} [TopologicalSpace X] [TopologicalSpace G] (r : X → G → X)
    (h : Continuous fun p : X × G => r p.1 p.2) (g : G) : Continuous fun x => r x g :=
  h.comp (Continuous.prodMk_left g)

def embL (e : c ⊕ d ≃ a) : Levi k (Two c d) →* parabLower k (two e) :=
  (leviEmb k (two e)).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem proj_embL (e : c ⊕ d ≃ a) (g : Levi k (Two c d)) : leviProjLower k (two e) (embL e g) = g := by
  funext x
  ext i j
  exact leviEmb_apply_same k (two e) g x i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pAct_embL (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) :
    pAct e s y (embL e (leviProjLower k (two e) p)) = pAct e s y p := by
  rw [← pAct_eq, proj_embL, pAct_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_embL (e : c ⊕ d ≃ a) (p : parabLower k (two e)) :
    GeneralLinearGroup.det (leviEmb k (two e) (leviProjLower k (two e) p)) =
      GeneralLinearGroup.det (p : GL a k) := by
  rw [det_leviEmb]
  exact (det_parab k (opp (two e)) p).symm

variable (k a b) in

def rChar : GL a k →* ℂˣ := (omChar a b 1).comp (MonoidHom.inl _ _)

theorem isSmoothChar_one : IsSmoothChar (1 : kˣ →* ℂˣ) := by unfold IsSmoothChar; simp

theorem isSmoothChar_rChar : IsSmoothChar (rChar k a b) :=
  (isSmoothChar_omChar isSmoothChar_one).comp _ (continuous_id.prodMk continuous_const)

variable (k b) in

def levRep (e : c ⊕ d ≃ a) (s : Set ℕ) : Representation ℂ (Levi k (Two c d)) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (embL e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (deltaHalf k (Two c d) * (rChar k a b).comp (leviEmb k (two e)))

theorem levRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (g : Levi k (Two c d)) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (levRep k b e s g Φ).1 y =
      ((deltaHalf k (Two c d) g * rChar k a b (leviEmb k (two e) g) : ℂˣ) : ℂ) * Φ.1 (pAct e s y (embL e g)) := rfl

theorem isSmooth_levRep (e : c ⊕ d ≃ a) (s : Set ℕ) : IsSmooth (levRep k b e s) := by
  refine isSmooth_twist (isSmooth_of_nhds fun Φ => ?_)
    ((isSmoothChar_deltaHalf k).mul (isSmoothChar_rChar.comp _ (continuous_leviEmb k _)))
  refine (GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action _ (ColZero k b e s)
    (fun y g => pAct e s y (embL e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (((continuous_rAct s).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_leviEmb k (two e)).comp continuous_snd))).subtype_mk _) Φ).mono fun u hu => ?_
  exact Subtype.ext (funext hu)

omit [Fintype d] [DecidableEq d] [DecidableEq c] [Fintype c] [DecidableEq a] [DecidableEq b] in
theorem isClosed_colZero (e : c ⊕ d ≃ a) (s : Set ℕ) :
    IsClosed {x : RankIn k a b s | ∀ i j, x.1 i (e (.inr j)) = 0} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const

theorem exists_indEquiv (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) :
    ∃ E : SB (RankIn k a b {κ}) ≃ₗ[ℂ] IndSpLower (two e) (levRep k b e {κ}),
      ∀ Φ g y, ((E Φ).1.1 g).1 y = (rChar k a b g : ℂ) * Φ.1 (rAct _ y.1 g) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨-, -, -, -, -, -, -, -, hPK⟩ := LeviInt.levi_integral_facts k _ a _ (opp (two e))
  exact GlobalTheory.SBInduced.sb_induced (GL a k) (RankIn k a b {κ}) (ColZero k b e {κ})
    (SB (ColZero k b e {κ})) (rAct {κ}) (rAct_one _) (rAct_mul _) (continuous_rAct _)
    Subtype.val (isClosed_colZero e _).isClosedEmbedding_subtypeVal (parabLower k (two e)) (KO k a)
    SplitFlip.isCompact_KO
    (fun x => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k b c d a e x.1 (x.2.trans hκ)
      obtain ⟨p, hp', w, hw, h⟩ := hPK g⁻¹
      refine ⟨pAct e _ ⟨rAct _ x g, by rwa [rAct_val]⟩ ⟨p, hp'⟩, w, hw, ?_⟩
      show x = rAct _ (rAct _ (rAct _ x g) p) w
      rw [← rAct_mul, ← rAct_mul, ← h, mul_inv_cancel, rAct_one])
    (pAct e _) (fun _ _ => rfl)
    (fun y y' g h => (mem_parabLower_two k).2 fun i j => by
      refine congrFun (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e y.1.1 (y.1.2.trans hκ) y.2
        (fun m => g.val (e (.inl m)) (e (.inr j))) (funext fun l => ?_)) i
      have := y'.2 l j
      rw [← h, rAct_val, mul_apply_of_cols e y.2] at this
      exact this)
    (rChar k a b) isSmoothChar_rChar _ (LinearEquiv.refl ℂ _)
    (fun p w y => by
      show (((deltaHalf k (Two c d) (leviProjLower k (two e) p))⁻¹ : ℂˣ) : ℂ) *
        (((deltaHalf k (Two c d) (leviProjLower k (two e) p) *
          rChar k a b (leviEmb k (two e) (leviProjLower k (two e) p)) : ℂˣ) : ℂ) *
          w.1 (pAct e _ y (embL e (leviProjLower k (two e) p)))) = _ * w.1 (pAct e _ y p)
      have : rChar k a b (leviEmb k (two e) (leviProjLower k (two e) p)) = rChar k a b p := by
        simp only [rChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply, MonoidHom.inl_apply,
          MonoidHom.coe_fst, MonoidHom.coe_snd, det_embL]
      rw [pAct_embL, this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel_left])

def colL (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (h : GL b k) : ColZero k b e s :=
  ⟨lAct s y.1 h, fun i j => by rw [lAct_val, mul_apply]; simp [y.2]⟩

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem continuous_colL (e : c ⊕ d ≃ a) (s : Set ℕ) :
    Continuous fun p : ColZero k b e s × GL b k => colL e s p.1 p.2 :=
  ((continuous_lAct s).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq d] in
theorem colL_transitive (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) (y y' : ColZero k b e {κ}) :
    ∃ h, colL e _ y h = y' := by
  have inj : ∀ z : ColZero k b e {κ},
      Function.Injective (z.1.1.submatrix id fun i => e (.inl i)).mulVecLin := fun z =>
    (injective_iff_map_eq_zero _).2 (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e z.1.1 (z.1.2.trans hκ) z.2)
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.ofInjective _ (inj y)).symm.trans (LinearEquiv.ofInjective _ (inj y')))
  have hφ' : ∀ v, φ ((y.1.1.submatrix id fun i => e (.inl i)) *ᵥ v) =
      (y'.1.1.submatrix id fun i => e (.inl i)) *ᵥ v := fun v => by
    have := hφ (LinearEquiv.ofInjective _ (inj y) v)
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  let g : GL b k := ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨g⁻¹, Subtype.ext (Subtype.ext ?_)⟩
  show (lAct _ y.1 g⁻¹).1 = _
  rw [lAct_val, inv_inv]
  ext i l
  obtain ⟨l | l, rfl⟩ := e.surjective l
  · have h1 := congrFun (hφ' (Pi.single l 1)) i
    rw [← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec] at h1
    simpa [mul_apply, mulVec, dotProduct, g, Pi.single_apply] using h1
  · rw [y'.2, mul_apply]; simp [y.2]

def leftRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Representation ℂ (GL b k) (SB (ColZero k b e s)) :=
  twist (sbRep (colL e s) (fun y => Subtype.ext (lAct_one s y.1))
    (fun y g h => Subtype.ext (lAct_mul s y.1 g h))
    (continuous_slice (colL e s) (continuous_colL e s))) ψ

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem leftRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (leftRep e s ψ h Φ).1 y = (ψ h : ℂ) * Φ.1 (colL e s y h) := rfl

def leftOp (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) :
    (levRep k b e s).IntertwiningMap (levRep k b e s) where
  toLinearMap := leftRep e s ψ h
  isIntertwining' g := LinearMap.ext fun Φ => Subtype.ext (funext fun y => by
    have : pAct e s (colL e s y h) (embL e g) = colL e s (pAct e s y (embL e g)) h :=
      Subtype.ext (Subtype.ext (by
        show (rAct s (lAct s y.1 h) _).1 = (lAct s (rAct s y.1 _) h).1
        rw [rAct_val, lAct_val, lAct_val, rAct_val, Matrix.mul_assoc]))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, leftRep_apply, levRep_apply, levRep_apply, leftRep_apply, this,
      mul_left_comm])

theorem leftOp_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (leftOp e s ψ h Φ).1 y = (ψ h : ℂ) * Φ.1 (colL e s y h) := rfl

def rel (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) : Submodule ℂ (SB (ColZero k b e s)) :=
  Submodule.span ℂ {y | ∃ h z, y = leftOp e s ψ h z - z}

theorem rel_le (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (g : Levi k (Two c d)) :
    rel e s ψ ≤ (rel e s ψ).comap (levRep k b e s g) := Submodule.span_le.2 (by
  rintro _ ⟨h, z, rfl⟩
  refine Submodule.subset_span ⟨h, levRep k b e s g z, ?_⟩
  rw [map_sub, (leftOp e s ψ h).isIntertwining])

def coinvRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Representation ℂ (Levi k (Two c d)) (SB (ColZero k b e s) ⧸ rel e s ψ) :=
  (levRep k b e s).quotient _ (rel_le e s ψ)

def coinvMk (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    (levRep k b e s).IntertwiningMap (coinvRep e s ψ) where
  toLinearMap := (rel e s ψ).mkQ
  isIntertwining' _ := rfl

theorem coinvMk_surjective (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Function.Surjective (coinvMk e s ψ) := (rel e s ψ).mkQ_surjective

theorem mem_rel_of_coinvMk (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (x : SB (ColZero k b e s))
    (hx : coinvMk e s ψ x = 0) : x ∈ Submodule.span ℂ {y | ∃ h z, y = leftOp e s ψ h z - z} :=
  (Submodule.Quotient.mk_eq_zero (rel e s ψ)).1 hx

theorem isSmooth_coinvRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) : IsSmooth (coinvRep e s ψ) :=
  (IsSubquotient.of_surjective (coinvMk e s ψ) (rel e s ψ).mkQ_surjective).isSmooth (isSmooth_levRep e s)

theorem finiteDimensional_coinv (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {ψ : GL b k →* ℂˣ}
    (hψ : IsSmoothChar ψ) : FiniteDimensional ℂ (SB (ColZero k b e {κ}) ⧸ rel e {κ} ψ) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (Matrix b a k) := inferInstanceAs (LocallyCompactSpace (b → a → k))
  have hlc : IsLocallyClosed {x : Matrix b a k | x.rank ∈ ({κ} : Set ℕ)} := by
    refine ⟨_, _, isOpen_le_rank κ, isClosed_rank_lt (κ + 1), Set.ext fun x => ?_⟩
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    omega
  have : LocallyCompactSpace (RankIn k a b {κ}) := hlc.locallyCompactSpace
  have : LocallyCompactSpace (ColZero k b e {κ}) := (isClosed_colZero e _).locallyCompactSpace
  obtain ⟨v, hv⟩ := exists_generator (r := colL e {κ}) (fun y => Subtype.ext (lAct_one _ y.1))
    (fun y g h => Subtype.ext (lAct_mul _ y.1 g h)) ψ (rel e {κ} ψ).mkQ
    (fun h Φ Φ' hΦ => (Submodule.Quotient.eq _).2 (Submodule.subset_span
      ⟨h, Φ, congrArg (· - Φ) (Subtype.ext (funext hΦ))⟩))
    (continuous_colL e _) (colL_transitive e hκ) (fun U hU => by
      obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k b U hU
      exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩) hψ
  have h2 : Submodule.span ℂ {v} = ⊤ := eq_top_iff.2 fun x _ => by
    obtain ⟨Φ, rfl⟩ := (rel e {κ} ψ).mkQ_surjective x
    exact hv Φ
  exact ⟨h2 ▸ Submodule.fg_span_singleton v⟩

theorem exists_indLower_coinv (e : c ⊕ d ≃ a) {V U Γ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] {σ : Representation ℂ (Levi k (Two c d)) V} {τ : Representation ℂ (Levi k (Two c d)) U}
    (hσ : IsSmooth σ) (A : σ.IntertwiningMap τ) (T : Γ → σ.IntertwiningMap σ) (hA : Function.Surjective A)
    (hT : ∀ x, A x = 0 → x ∈ Submodule.span ℂ {y : V | ∃ γ z, y = T γ z - z}) :
    ∃ q : IndSpLower (two e) σ →ₗ[ℂ] IndSpLower (two e) τ, Function.Surjective q ∧
      (∀ g f, q (parIndLower (two e) σ g f) = parIndLower (two e) τ g (q f)) ∧
      ∀ f, q f = 0 → f ∈ Submodule.span ℂ {w : IndSpLower (two e) σ | ∃ (γ : Γ) (z : IndSpLower (two e) σ),
        ∀ x, w.1.1 x = T γ (z.1.1 x) - z.1.1 x} := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := LeviInt.levi_integral_facts k _ a _ (opp (two e))
  obtain ⟨h1, h2⟩ := IndCoinv.smInd_coinvariants (GL a k) (parabLower k (two e)) (KO k a) hP
    SplitFlip.isCompact_KO hPK (exists_open_normalised_subgroup_subset k a) _ _ _ _
    (isSmooth_comp (isSmooth_twist hσ (isSmoothChar_deltaHalf k).inv) (leviProjLower k (two e)) hcont)
    (compMap (twistMap A (deltaHalf k _)⁻¹) (leviProjLower k (two e))) Γ
    (fun h => compMap (twistMap (T h) (deltaHalf k _)⁻¹) (leviProjLower k (two e))) hA hT
  refine ⟨(smIndMap (compMap (twistMap A (deltaHalf k _)⁻¹) (leviProjLower k (two e)))).toLinearMap, h1,
    fun _ _ => rfl, fun f hf => Submodule.span_mono ?_ (h2 f hf)⟩
  rintro _ ⟨γ, z, rfl⟩
  exact ⟨γ, z, fun _ => rfl⟩

theorem exists_coinvMap (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {ψ : GL b k →* ℂˣ}
    (hψ : IsSmoothChar ψ) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (Levi k (Two c d)) W),
      IsSmooth τ ∧ HasFiniteLength τ ∧
    ∃ q : SB (RankIn k a b {κ}) →ₗ[ℂ] IndSpLower (two e) τ, Function.Surjective q ∧
      (∀ g (Φ Φ' : SB (RankIn k a b {κ})), (∀ x, Φ'.1 x = (rChar k a b g : ℂ) * Φ.1 (rAct _ x g)) →
        q Φ' = parIndLower (two e) τ g (q Φ)) ∧
      ∀ Φ, q Φ = 0 → Φ ∈ Submodule.span ℂ {w : SB (RankIn k a b {κ}) | ∃ (h : GL b k)
        (Ψ : SB (RankIn k a b {κ})), ∀ x, w.1 x = (ψ h : ℂ) * Ψ.1 (lAct _ x h) - Ψ.1 x} := by
  haveI := finiteDimensional_coinv e hκ hψ
  refine ⟨_, _, _, coinvRep e {κ} ψ, isSmooth_coinvRep _ _ _,
    FinitenessModel.hasFiniteLength_of_finiteDimensional _, ?_⟩
  refine (exists_indEquiv (k := k) (b := b) e hκ).elim fun E hE => ?_
  refine (exists_indLower_coinv e (isSmooth_levRep (k := k) (b := b) e {κ})
    (coinvMk e {κ} ψ) (leftOp e {κ} ψ) (coinvMk_surjective e {κ} ψ) (mem_rel_of_coinvMk e {κ} ψ)).elim
    fun q hh => ?_
  have h1 := hh.1
  have hq := hh.2.1
  have h2 := hh.2.2
  refine ⟨q ∘ₗ E.toLinearMap, h1.comp E.surjective, fun g Φ Φ' h => ?_, fun Φ hΦ => ?_⟩
  · have : E Φ' = parIndLower (two e) (levRep k b e {κ}) g (E Φ) :=
      Subtype.ext (Subtype.ext (funext fun x => Subtype.ext (funext fun y => by
        rw [parIndLower_apply, hE, hE, h, map_mul, rAct_mul, Units.val_mul, mul_assoc])))
    exact (congrArg q this).trans (hq _ _)
  · have h3 := h2 (E Φ) hΦ
    rw [← E.symm_apply_apply Φ]
    refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ h3 : E Φ ∈ Submodule.comap E.symm.toLinearMap _)
    rintro w ⟨h, z, hw⟩
    obtain ⟨Ψ, rfl⟩ := E.surjective z
    let Ψ' : SB (RankIn k a b {κ}) := twist (sbRep (lAct {κ}) (lAct_one _) (lAct_mul _)
      (continuous_slice (lAct {κ}) (continuous_lAct _))) ψ h Ψ
    have hΨ' : ∀ x, Ψ'.1 x = (ψ h : ℂ) * Ψ.1 (lAct _ x h) := fun _ => rfl
    clear_value Ψ'
    have : w = E (Ψ' - Ψ) :=
      Subtype.ext (Subtype.ext (funext fun x => Subtype.ext (funext fun y => by
        have h4 : rAct _ (colL e {κ} y h).1 x = lAct _ (rAct _ y.1 x) h := Subtype.ext (by
          show (rAct _ (lAct _ y.1 h) _).1 = _
          rw [rAct_val, lAct_val, lAct_val, rAct_val, Matrix.mul_assoc])
        rw [hw, Submodule.coe_sub, Pi.sub_apply, leftOp_apply, hE, hE, hE, Submodule.coe_sub, Pi.sub_apply,
          hΨ', h4]
        ring)))
    refine Submodule.subset_span ⟨h, Ψ, fun x => ?_⟩
    rw [this, LinearEquiv.coe_coe, E.symm_apply_apply, Submodule.coe_sub, Pi.sub_apply, hΨ']

end Strata

section Main

open GlobalTheory.RankStrataProof GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def res (ρ : ℕ) : rkSub k n m ρ →ₗ[ℂ] SB (RankIn k (Fin m) (Fin n) {ρ}) where
  toFun Φ := ⟨fun x => Φ.1 x.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal ⟨Φ.1, Φ.2.1⟩
    (isClosed_rank_lt (ρ + 1)) (fun y => Nat.lt_succ_of_le (le_of_eq y.2)) fun x hx h0 =>
      ⟨⟨x, le_antisymm (Nat.le_of_lt_succ hx) (not_lt.1 fun h => h0 (Φ.2.2 x h))⟩, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_surjective (ρ : ℕ) : Function.Surjective (res k n m ρ) := by
  intro f
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin m) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin m → k))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin m) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin m → k))
  obtain ⟨G, hG, hG0⟩ := GlobalTheory.SBExtend.exists_extension (Matrix (Fin n) (Fin m) k) {x | ρ ≤ x.rank}
    {x | x.rank ∈ ({ρ} : Set ℕ)} (isOpen_le_rank ρ) (fun x hx => le_of_eq (Eq.symm hx)) f
  exact ⟨⟨G.1, G.2, fun x hx => hG0 x (not_le.2 hx)⟩, Subtype.ext (funext hG)⟩

theorem mem_of_res_eq_zero {ρ : ℕ} {Φ : rkSub k n m ρ} (h : res k n m ρ Φ = 0) : Φ.1 ∈ rkSub k n m (ρ + 1) := by
  refine ⟨Φ.2.1, fun x hx => ?_⟩
  by_cases h1 : x.rank < ρ
  · exact Φ.2.2 x h1
  · exact congrFun (congrArg Subtype.val h) ⟨x, le_antisymm (Nat.le_of_lt_succ hx) (not_lt.1 h1)⟩

theorem om_apply (g : GL (Fin m) k) (h : GL (Fin n) k) {Φ : Matrix (Fin n) (Fin m) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin m) k)) (x : Matrix (Fin n) (Fin m) k) :
    om 1 g h Φ x = (omChar (Fin m) (Fin n) 1 (g, h) : ℂ) * Φ (act x (g, h)) := by
  have := congrFun (omega_eq_om 1 g h ⟨Φ, hΦ⟩) x
  rw [inv_one] at this
  exact this.symm

theorem layer_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ (ρ t : ℕ) (h : ρ + t = m),
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (GlobalTheory.SmGL.Two (Fin ρ) (Fin t))) W),
      GlobalTheory.PRep.IsSmooth τ ∧ GlobalTheory.SmGL.HasFiniteLength τ ∧
      ∃ f : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ),
        (∀ (g : GL (Fin m) k) (v : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ),
          f (GlobalTheory.SmGL.parIndLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ g v) -
              GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) (f v) ∈
            GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1)) ∧
        GlobalTheory.ThetaGLRank.rkSub k n m ρ ≤
          GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ⊔ LinearMap.range f := by
  intro k _ _ _ _ n m χ hχ ρ t h
  let ψ : GL (Fin n) k →* ℂˣ := (omChar (Fin m) (Fin n) 1).comp (MonoidHom.inr _ _) * χ⁻¹
  have hψ : IsSmoothChar ψ :=
    ((isSmoothChar_omChar isSmoothChar_one).comp _ (continuous_const.prodMk continuous_id)).mul
      (IsSmoothChar.inv hχ)
  have hρ : ρ = Fintype.card (Fin ρ) := (Fintype.card_fin ρ).symm
  obtain ⟨W, _, _, τ, hτ, hτ', q, hq, hqg, hq0⟩ := exists_coinvMap (stdSum h) hρ hψ
  refine ⟨W, _, _, τ, hτ, hτ', ?_⟩
  set C := aug m χ ⊔ rkSub k n m (ρ + 1)
  have hker : ∀ Φ : rkSub k n m ρ, q (res k n m ρ Φ) = 0 → Φ.1 ∈ C := by
    intro Φ hΦ
    have h1 : res k n m ρ Φ ∈ (C.comap (rkSub k n m ρ).subtype).map (res k n m ρ) := by
      refine Submodule.span_le.2 ?_ (hq0 _ hΦ)
      rintro w ⟨γ, Ψ, hw⟩
      obtain ⟨Ψ, rfl⟩ := res_surjective ρ Ψ
      have h2 : om 1 (1 : GL (Fin m) k) γ Ψ.1 ∈ rkSub k n m ρ :=
        ⟨Model.om_mem_SB 1 1 γ Ψ.2.1, fun x hx => by
          rw [om_apply _ _ Ψ.2.1, Ψ.2.2 _ (by rwa [rank_act]), mul_zero]⟩
      refine ⟨((χ γ)⁻¹ : ℂˣ).val • (⟨_, h2⟩ - (χ γ : ℂ) • Ψ), ?_, Subtype.ext (funext fun x => ?_)⟩
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, Ψ.1, Ψ.2.1, rfl⟩))
      · rw [hw]
        show ((χ γ)⁻¹ : ℂˣ).val * (om 1 (1 : GL (Fin m) k) γ Ψ.1 x.1 - (χ γ : ℂ) * Ψ.1 x.1) =
          ((omChar (Fin m) (Fin n) 1 (1, γ) * (χ γ)⁻¹ : ℂˣ) : ℂ) * Ψ.1 (act x.1 (1, γ)) - Ψ.1 x.1
        rw [om_apply _ _ Ψ.2.1, mul_sub, Units.inv_mul_cancel_left, Units.val_mul]
        ring
    obtain ⟨Ψ, hΨ, e⟩ := h1
    have h3 : (Φ - Ψ).1 ∈ rkSub k n m (ρ + 1) := mem_of_res_eq_zero (by rw [map_sub, e, sub_self])
    simpa using C.add_mem (Submodule.mem_sup_right h3) hΨ
  obtain ⟨S, hS⟩ := LinearMap.exists_rightInverse_of_surjective (q ∘ₗ res k n m ρ)
    (LinearMap.range_eq_top.2 (hq.comp (res_surjective ρ)))
  have hS' : ∀ v, q (res k n m ρ (S v)) = v := fun v => LinearMap.congr_fun hS v
  refine ⟨(rkSub k n m ρ).subtype ∘ₗ S, fun g v => ?_, fun Φ hΦ => ?_⟩
  · refine hker (S (parIndLower _ _ g v) - ⟨_, om_mem_rkSub ρ g (S v).2⟩) ?_
    rw [map_sub, map_sub, hS', hqg g (res k n m ρ (S v)) _ fun x => om_apply g 1 (S v).2.1 x.1, hS', sub_self]
  · have h1 := hker (⟨Φ, hΦ⟩ - S (q (res k n m ρ ⟨Φ, hΦ⟩))) (by rw [map_sub, map_sub, hS', sub_self])
    simpa using Submodule.add_mem_sup h1 (LinearMap.mem_range_self ((rkSub k n m ρ).subtype ∘ₗ S)
      (q (res k n m ρ ⟨Φ, hΦ⟩)))

end Main

end GlobalTheory.ThetaGLCover
