import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgTransfer

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']

theorem isCh_one {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)

def fixSp (K Q : Subgroup G) (π : Q →* G') (c₀ : G → ℂ) (ρ : K →* (W →L[ℂ] W)) : Submodule ℂ W where
  carrier := {w | ∀ r : K, ∀ hr : (r : G) ∈ Q, π ⟨r, hr⟩ = 1 → c₀ r • ρ r w = w}
  add_mem' := fun {a b} ha hb r hr h1 => by rw [map_add, smul_add, ha r hr h1, hb r hr h1]
  zero_mem' := fun r _ _ => by simp
  smul_mem' := fun a w hw r hr h1 => by rw [map_smul, smul_comm, hw r hr h1]

variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}

def kι (hL : IsLevi Γ K Q Γ' K' π ι c₀) : K' →* K :=
  (Q.subtype.comp (ι.comp K'.subtype)).codRestrict K (fun m => hL.ιK m m.2)

@[simp] theorem kι_coe (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : K') : ((kι hL m : K) : G) = ι m := rfl

theorem c₀_mul (hL : IsLevi Γ K Q Γ' K' π ι c₀) (a b : Q) :
    c₀ ((a * b : Q) : G) = c₀ a * c₀ b := hL.par.ch.mul a a.2 b b.2

theorem c₀_inv (hL : IsLevi Γ K Q Γ' K' π ι c₀) (a : Q) : c₀ ((a⁻¹ : Q) : G) = (c₀ a)⁻¹ := by
  have h := c₀_mul hL a⁻¹ a
  rw [inv_mul_cancel] at h
  have h1 : c₀ ((1 : Q) : G) = 1 := isCh_one hL.par.ch
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem c₀_ι_left (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : G') (a : Q) :
    c₀ ((ι m * a : Q) : G) = c₀ a := by
  rw [c₀_mul hL, hL.triv, one_mul]

theorem c₀_ι_right (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : G') (a : Q) :
    c₀ ((a * ι m : Q) : G) = c₀ a := by
  rw [c₀_mul hL, hL.triv, mul_one]

theorem fix_stable (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (m : K') {w : W}
    (hw : w ∈ fixSp K Q π c₀ ρ) : ρ (kι hL m) w ∈ fixSp K Q π c₀ ρ := by
  intro r hr h1
  set u : K := kι hL m with hu
  have hconj : (((u⁻¹ * r * u : K)) : G) ∈ Q := by
    have : (((u⁻¹ * r * u : K)) : G) = (((ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') : Q) : G) := by
      simp [hu]
    rw [this]
    exact Subtype.property _
  have hval : (⟨((u⁻¹ * r * u : K) : G), hconj⟩ : Q) = (ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') := by
    apply Subtype.ext
    simp [hu]
  have hπ : π ⟨((u⁻¹ * r * u : K) : G), hconj⟩ = 1 := by
    rw [hval, map_mul, map_mul, h1, map_inv, hL.sect]
    simp
  have hc : c₀ ((u⁻¹ * r * u : K) : G) = c₀ r := by
    have : c₀ ((u⁻¹ * r * u : K) : G) = c₀ (((ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') : Q) : G) :=
      congrArg c₀ (congrArg Subtype.val hval)
    rw [this, c₀_ι_right hL, ← map_inv, c₀_ι_left hL]
  have h2 := hw (u⁻¹ * r * u) hconj hπ
  rw [hc] at h2
  have h3 : ρ r (ρ u w) = ρ u (ρ (u⁻¹ * r * u) w) := by
    have : r * u = u * (u⁻¹ * r * u) := by group
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, this]
  rw [h3, ← map_smul, h2]

def resRep (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) :
    K' →* (fixSp K Q π c₀ ρ →L[ℂ] fixSp K Q π c₀ ρ) where
  toFun m := ((ρ (kι hL m)).comp (fixSp K Q π c₀ ρ).subtypeL).codRestrict _
    (fun v => fix_stable hL ρ m v.2)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp
    rfl

theorem resRep_coe (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (m : K')
    (v : fixSp K Q π c₀ ρ) : ((resRep hL ρ m v : fixSp K Q π c₀ ρ) : W) = ρ (kι hL m) v := rfl

theorem kι_cont (hL : IsLevi Γ K Q Γ' K' π ι c₀) : Continuous (kι hL) :=
  Continuous.subtype_mk (continuous_subtype_val.comp (hL.contι.comp continuous_subtype_val)) _

theorem resRep_cont [FiniteDimensional ℂ W] (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : Continuous (resRep hL ρ) := by
  rw [continuous_clm_apply]
  intro v
  refine Continuous.subtype_mk ?_ _
  have : Continuous fun m : K' => (ρ (kι hL m)) (v : W) :=
    (continuous_eval_const (v : W)).comp (hρ.comp (kι_cont hL))
  exact this

def am (ρ : K →* (W →L[ℂ] W)) (c₀ : G → ℂ) (π : Q →* G') (q : Q) (k : K) :
    fixSp K Q π c₀ ρ →L[ℂ] W := c₀ q • (ρ k⁻¹).comp (fixSp K Q π c₀ ρ).subtypeL

theorem am_apply (ρ : K →* (W →L[ℂ] W)) (q : Q) (k : K) (v : fixSp K Q π c₀ ρ) :
    am ρ c₀ π q k v = c₀ q • ρ k⁻¹ (v : W) := rfl

theorem am_move (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (q : Q) (k r : K)
    (hr : (r : G) ∈ Q) (v : fixSp K Q π c₀ ρ) :
    am ρ c₀ π (q * ⟨r, hr⟩) (r⁻¹ * k)
      (resRep hL ρ ⟨π ⟨r, hr⟩, hL.πK ⟨r, hr⟩ r.2⟩⁻¹ v) = am ρ c₀ π q k v := by
  set m : K' := ⟨π ⟨r, hr⟩, hL.πK ⟨r, hr⟩ r.2⟩ with hm
  set s : K := r * (kι hL m)⁻¹ with hs
  have hsQ : (s : G) ∈ Q := by
    have : (s : G) = ((⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ : Q) : G) := by
      simp [hs, hm]
    rw [this]
    exact Subtype.property _
  have hsval : (⟨(s : G), hsQ⟩ : Q) = ⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ := by
    apply Subtype.ext
    simp [hs, hm]
  have hsπ : π ⟨s, hsQ⟩ = 1 := by
    rw [hsval, map_mul, map_inv, hL.sect]
    simp
  have hcs : c₀ (s : G) = c₀ r := by
    have : c₀ (s : G) = c₀ ((⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ : Q) : G) :=
      congrArg c₀ (congrArg Subtype.val hsval)
    rw [this, ← map_inv, c₀_ι_right hL]
  have hv := v.2 s hsQ hsπ
  rw [hcs] at hv
  rw [am_apply, am_apply, c₀_mul hL]
  have h1 : ρ (r⁻¹ * k)⁻¹ ((resRep hL ρ m⁻¹ v : fixSp K Q π c₀ ρ) : W) = ρ k⁻¹ (ρ s (v : W)) := by
    rw [resRep_coe, map_inv (kι hL) m, hs]
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h1]
  have h2 : (c₀ (q : G) * c₀ r) • ρ k⁻¹ (ρ s (v : W)) = c₀ (q : G) • ρ k⁻¹ (c₀ r • ρ s (v : W)) := by
    rw [map_smul, smul_smul]
  simp only [Subgroup.coe_mk] at *
  rw [h2, hv]

theorem exists_qk (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : ∃ (q : Q) (k : K), g = q * k := by
  obtain ⟨p, hp, k, hk, h⟩ := hL.par.iwa g
  exact ⟨⟨p, hp⟩, ⟨k, hk⟩, h⟩

def qOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : Q := (exists_qk hL g).choose

def kOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : K := (exists_qk hL g).choose_spec.choose

theorem qk_spec (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : g = qOf hL g * kOf hL g :=
  (exists_qk hL g).choose_spec.choose_spec

section Ext

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def ext (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (F : G' → E →L[ℂ] fixSp K Q π c₀ ρ)
    (g : G) : E →L[ℂ] W :=
  (am ρ c₀ π (qOf hL g) (kOf hL g)).comp (F (π (qOf hL g)))

def Equi (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W))
    (F : G' → E →L[ℂ] fixSp K Q π c₀ ρ) : Prop :=
  ∀ (g : G') (k : K') (x : E), F (g * k) x = resRep hL ρ k⁻¹ (F g x)

theorem ext_eq (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W))
    {F : G' → E →L[ℂ] fixSp K Q π c₀ ρ} (hF : Equi hL ρ F) (q : Q) (k : K) :
    ext hL ρ F ((q : G) * k) = (am ρ c₀ π q k).comp (F (π q)) := by
  set g : G := (q : G) * k with hg
  have hs := qk_spec hL g
  set q₁ := qOf hL g with hq₁
  set k₁ := kOf hL g with hk₁
  set r : K := k * k₁⁻¹ with hr
  have hrv : (r : G) = ((q⁻¹ * q₁ : Q) : G) := by
    have : (q : G) * k = q₁ * k₁ := hs
    simp only [hr, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, this]
    group
  have hrQ : (r : G) ∈ Q := by
    rw [hrv]
    exact Subtype.property _
  have hq₁' : q₁ = q * ⟨r, hrQ⟩ := by
    apply Subtype.ext
    have : (⟨r, hrQ⟩ : Q) = q⁻¹ * q₁ := Subtype.ext hrv
    rw [this]
    simp
  have hk₁' : k₁ = r⁻¹ * k := by
    simp [hr]
  ext x
  show am ρ c₀ π q₁ k₁ (F (π q₁) x) = am ρ c₀ π q k (F (π q) x)
  rw [← am_move hL ρ q k r hrQ (F (π q) x)]
  have := hF (π q) ⟨π ⟨r, hrQ⟩, hL.πK ⟨r, hrQ⟩ r.2⟩ x
  rw [← this, hq₁', ← hk₁', map_mul]

variable [IsTopologicalGroup G]

theorem am_cont (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous fun y : Q × K => am ρ c₀ π y.1 y.2 := by
  have h1 : Continuous fun q : Q => c₀ q :=
    continuousOn_iff_continuous_restrict.1 hL.par.ch.cont
  unfold am
  refine (h1.comp continuous_fst).smul ?_
  exact (hρ.comp (continuous_inv.comp continuous_snd)).clm_comp continuous_const

theorem ext_cont {T : Type} [TopologicalSpace T] (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ} (hF : ∀ t, Equi hL ρ (F t))
    (hc : Continuous fun y : T × G' => F y.1 y.2) :
    Continuous fun y : T × G => ext hL ρ (F y.1) y.2 := by
  have hΦ : Continuous fun y : T × Q × K => (am ρ c₀ π y.2.1 y.2.2).comp (F y.1 (π y.2.1)) := by
    refine ((am_cont hL hρ).comp continuous_snd).clm_comp ?_
    exact hc.comp (continuous_fst.prodMk (hL.contπ.comp (continuous_fst.comp continuous_snd)))
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro U hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨k₁, -, hk₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (U.map fun y : T × G => kOf hL y.2) (by simp)
  have hk : Tendsto (fun y : T × G => kOf hL y.2) U (𝓝 k₁) := hk₁
  have hU' : Tendsto (fun y : T × G => y) U (𝓝 y₀) := hU
  have hqG : Tendsto (fun y : T × G => y.2 * ((kOf hL y.2 : K) : G)⁻¹) U (𝓝 (y₀.2 * (k₁ : G)⁻¹)) :=
    ((continuous_snd.tendsto y₀).comp hU').mul
      (((continuous_subtype_val.tendsto k₁).comp hk).inv)
  have hqe : ∀ y : T × G, y.2 * ((kOf hL y.2 : K) : G)⁻¹ = (qOf hL y.2 : G) := by
    intro y
    exact mul_inv_eq_of_eq_mul (qk_spec hL y.2)
  simp only [hqe] at hqG
  have hmem : y₀.2 * (k₁ : G)⁻¹ ∈ Q :=
    hL.par.closed.mem_of_tendsto hqG (Eventually.of_forall fun y => (qOf hL y.2).2)
  have hq : Tendsto (fun y : T × G => qOf hL y.2) U (𝓝 (⟨_, hmem⟩ : Q)) :=
    tendsto_subtype_rng.2 hqG
  have hlim := (hΦ.tendsto (y₀.1, (⟨_, hmem⟩ : Q), k₁)).comp
    ((((continuous_fst.tendsto y₀).comp hU').prodMk_nhds (hq.prodMk_nhds hk)))
  have hy : ext hL ρ (F y₀.1) y₀.2 = (am ρ c₀ π ⟨_, hmem⟩ k₁).comp (F y₀.1 (π ⟨_, hmem⟩)) := by
    rw [← ext_eq hL ρ (hF y₀.1)]
    simp
  rw [hy]
  exact hlim

theorem am_bound (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : ∃ B : ℝ, ∀ (q : Q) (k : K), ‖am ρ c₀ π q k‖ ≤ B := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨B * ‖(fixSp K Q π c₀ ρ).subtypeL‖, fun q k => ?_⟩
  unfold am
  refine (norm_smul_le _ _).trans ?_
  rw [hL.par.ch.norm q q.2, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hB _ (Set.mem_univ _)) (norm_nonneg _)

theorem ext_bdd [LocallyCompactSpace G] {T : Type} (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) (S : Set T)
    (F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ)
    (hb : ∀ g', ∃ U ∈ 𝓝 g', ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ U, ‖F t x‖ ≤ M) (g : G) :
    ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ t ∈ S, ∀ g' ∈ U, ‖ext hL ρ (F t) g'‖ ≤ M := by
  obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
  refine ⟨C, hCg, ?_⟩
  set C₁ : Set G := (fun a : G × G => a.1 * a.2⁻¹) '' (C ×ˢ (K : Set G)) with hC₁
  have hC₁c : IsCompact C₁ :=
    (hC.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hCq : IsCompact ((↑) ⁻¹' C₁ : Set Q) :=
    hL.par.closed.isClosedEmbedding_subtypeVal.isCompact_preimage hC₁c
  have hC' : IsCompact (π '' ((↑) ⁻¹' C₁ : Set Q)) := hCq.image hL.contπ
  have hM : ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ π '' ((↑) ⁻¹' C₁ : Set Q), ‖F t x‖ ≤ M := by
    refine hC'.induction_on (p := fun s => ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ s, ‖F t x‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨0, fun _ _ _ h => absurd h (Set.notMem_empty _)⟩
    · rintro s u hsu ⟨M, hM⟩
      exact ⟨M, fun t ht x hx => hM t ht x (hsu hx)⟩
    · rintro s u ⟨M, hM⟩ ⟨N, hN⟩
      refine ⟨max M N, fun t ht x hx => ?_⟩
      rcases hx with hx | hx
      · exact (hM t ht x hx).trans (le_max_left _ _)
      · exact (hN t ht x hx).trans (le_max_right _ _)
    · intro x _
      obtain ⟨U, hU, M, hM⟩ := hb x
      exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, M, hM⟩
  obtain ⟨M, hM⟩ := hM
  obtain ⟨B, hB⟩ := am_bound hK hL hρ
  refine ⟨B * M, fun t ht g' hg' => ?_⟩
  have hq : (qOf hL g' : G) ∈ C₁ := by
    refine ⟨(g', kOf hL g'), ⟨hg', (kOf hL g').2⟩, ?_⟩
    exact mul_inv_eq_of_eq_mul (qk_spec hL g')
  have h2 := hM t ht (π (qOf hL g')) ⟨_, hq, rfl⟩
  have h1 := hB (qOf hL g') (kOf hL g')
  unfold ext
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

end Ext

section Pull

variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}

theorem cos_exists (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') :
    ∃ φ : Cos P (Γ ⊓ Q) ≃ Cos P' Γ', ∀ x, ∃ hq : rep x ∈ Q, ∃ γ ∈ Γ', γ ∈ P' ∧
      π ⟨rep x, hq⟩ = γ * rep (φ x) := by
  let f : ↥(Γ ⊓ Q) → ↥Γ' := fun d => ⟨π ⟨d, d.2.2⟩, hL.πΓ _ d.2.1⟩
  have hf : ∀ a b : ↥(Γ ⊓ Q), b * a⁻¹ ∈ P.subgroupOf (Γ ⊓ Q) ↔ f b * (f a)⁻¹ ∈ P'.subgroupOf Γ' := by
    intro a b
    have hπ : ∀ h, π ⟨((b * a⁻¹ : ↥(Γ ⊓ Q)) : G), h⟩ = ((f b * (f a)⁻¹ : ↥Γ') : G') := by
      intro h
      simp only [f, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [← map_inv, ← map_mul]
      rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hP.mem]
    constructor
    · rintro ⟨h, h2⟩
      rwa [hπ h] at h2
    · intro h
      have hq : ((b * a⁻¹ : ↥(Γ ⊓ Q)) : G) ∈ Q := (b * a⁻¹).2.2
      exact ⟨hq, by rwa [hπ hq]⟩
  let φ₀ : Cos P (Γ ⊓ Q) → Cos P' Γ' := Quotient.map' f (fun a b h =>
    QuotientGroup.rightRel_apply.2 ((hf a b).1 (QuotientGroup.rightRel_apply.1 h)))
  have hbij : Function.Bijective φ₀ := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ a => ?_
      induction y using Quotient.inductionOn with | _ b => ?_
      intro h
      have h2 := Quotient.exact h
      exact Quotient.sound (QuotientGroup.rightRel_apply.2
        ((hf a b).2 (QuotientGroup.rightRel_apply.1 h2)))
    · intro y
      induction y using Quotient.inductionOn with | _ m => ?_
      refine ⟨Quotient.mk _ ⟨ι m, hL.ιΓ m m.2, (ι m).2⟩, ?_⟩
      show Quotient.mk _ (f _) = _
      congr 1
      apply Subtype.ext
      exact hL.sect m
  refine ⟨Equiv.ofBijective φ₀ hbij, fun x => ?_⟩
  set d := Quotient.out x with hd
  have hx : Quotient.mk _ d = x := Quotient.out_eq x
  set e := Quotient.out (Equiv.ofBijective φ₀ hbij x) with he
  have he' : Quotient.mk _ e = Equiv.ofBijective φ₀ hbij x := Quotient.out_eq _
  have h1 : Equiv.ofBijective φ₀ hbij x = Quotient.mk _ (f d) :=
    (congrArg (Equiv.ofBijective φ₀ hbij) hx).symm
  have hrel := Quotient.exact (he'.trans h1)
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 hrel)
  refine ⟨d.2.2, ((f d * e⁻¹ : ↥Γ') : G'), (f d * e⁻¹).2, hmem, ?_⟩
  show π ⟨d, d.2.2⟩ = ((f d * e⁻¹ : ↥Γ') : G') * (e : G')
  simp [f]

def Law (K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) : Prop :=
  ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w

theorem sec_left {ρ : K →* (W →L[ℂ] W)} (h : IsPar Γ K P c) (hs : Law K P c ρ) {w : W}
    (hw : w ∈ secSp K P c ρ) {γ : G} (hγ : γ ∈ Γ) (hγP : γ ∈ P) (x : G) :
    sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := h.iwa x
  have h1 := hs w hw (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := hs w hw p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, h.ch.mul _ hγP _ hp, h.ch.rat γ hγ hγP, one_mul]

theorem sec_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') (hiwa : Iwa P' K')
    {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ) (h2 : Law K' P' c' (resRep hL ρ))
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K) :
    sec K P c ρ ((q : G) * k) v = am ρ c₀ π q k (sec K' P' c' (resRep hL ρ) (π q) v) := by
  obtain ⟨p', hp', k', hk', h⟩ := hiwa (π q)
  set m : K' := ⟨k', hk'⟩ with hm
  set p : Q := q * ι k'⁻¹ with hpd
  have hπp : π p = p' := by
    simp [hpd, map_mul, map_inv, hL.sect, h]
  have hpP : (p : G) ∈ P := (hP.mem _).2 ⟨p.2, by
    show π p ∈ P'
    rw [hπp]
    exact hp'⟩
  have hqk : (q : G) * k = p * ((kι hL m * k : K) : G) := by
    simp [hpd, hm]
  have hcp : c p = c₀ q * c' p' := by
    rw [hP.ch p (by rw [hπp]; exact hp'), hπp, hpd, c₀_ι_right hL]
  have hsec' := h2 _ hv p' hp' m
  rw [hqk, h1 _ hv' _ hpP, hcp, h, hsec', am_apply]
  have h3 : ((resRep hL ρ m⁻¹ v : fixSp K Q π c₀ ρ) : W) = ρ (kι hL m)⁻¹ (v : W) := by
    rw [resRep_coe, map_inv]
  have h4 : ρ (kι hL m * k)⁻¹ (v : W) = ρ k⁻¹ (ρ (kι hL m)⁻¹ (v : W)) := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_rev]
  rw [Submodule.coe_smul, h3, h4, map_smul, smul_smul]

theorem rep_mul {x g : G} (hx : x ∈ Q) (q : Q) (k : K) (h : g = (q : G) * k) :
    x * g = ((⟨x, hx⟩ * q : Q) : G) * k := by
  simp [h, mul_assoc]

theorem conv_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') {l : G → ℝ}
    {l' : G' → ℝ} (hl : ∀ (q : Q) (k : K), l ((q : G) * k) = l' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, l' (γ * x) = l' x) (hc : Conv Γ' P' l') :
    Conv (Γ ⊓ Q) P l := by
  obtain ⟨φ, hφ⟩ := cos_exists hL hP
  intro g
  have h1 := hc (π (qOf hL g))
  rw [← φ.summable_iff] at h1
  refine h1.congr (fun x => ?_)
  obtain ⟨hq, γ, hγ, hγP, h⟩ := hφ x
  simp only [Function.comp]
  rw [rep_mul hq _ _ (qk_spec hL g), hl, map_mul, h, mul_assoc, hinv γ hγ hγP]

theorem summable_eis {ρ : K →* (W →L[ℂ] W)} [CompleteSpace W] {M : ℝ}
    (hM : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {Λ : G → ℂ} {l : G → ℝ}
    (hl : ∀ g, (Λ g).re = l g) (hc : Conv Γ P l) (g : G) (w : W) :
    Summable fun y : Cos P Γ => Complex.exp (Λ (rep y * g)) • sec K P c ρ (rep y * g) w := by
  refine Summable.of_norm_bounded ((hc g).mul_right (M * ‖w‖)) (fun y => ?_)
  rw [norm_smul, Complex.norm_exp, hl]
  exact mul_le_mul_of_nonneg_left (hM _ _) (Real.exp_pos _).le

theorem eis_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c')
    (hpar : IsPar Γ' K' P' c') {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ)
    (h2 : Law K' P' c' (resRep hL ρ)) {Λ : G → ℂ} {Λ' : G' → ℂ}
    (hΛ : ∀ (q : Q) (k : K), Λ ((q : G) * k) = Λ' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, Λ' (γ * x) = Λ' x)
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K)
    (hs : Summable fun y : Cos P' Γ' =>
      Complex.exp (Λ' (rep y * π q)) • sec K' P' c' (resRep hL ρ) (rep y * π q) v) :
    eis (Γ ⊓ Q) K P c ρ Λ ((q : G) * k) v = am ρ c₀ π q k (eis Γ' K' P' c' (resRep hL ρ) Λ' (π q) v) := by
  obtain ⟨φ, hφ⟩ := cos_exists hL hP
  unfold eis
  rw [(am ρ c₀ π q k).map_tsum hs, ← φ.tsum_eq]
  refine tsum_congr (fun x => ?_)
  obtain ⟨hq, γ, hγ, hγP, h⟩ := hφ x
  have hrep : rep x ∈ Γ := (Quotient.out x).2.1
  have hcx : c₀ (rep x) = 1 := hL.par.ch.rat _ hrep hq
  rw [rep_mul hq q k rfl, hΛ, sec_pull hL hP hpar.iwa h1 h2 hv hv', map_mul, h, mul_assoc, hinv γ hγ hγP,
    sec_left hpar h2 hv hγ hγP, map_smul]
  congr 2
  simp only [am]
  rw [c₀_mul hL]
  show (c₀ (rep x) * c₀ q) • _ = _
  rw [hcx, one_mul]

theorem mem_secSp_iff (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c')
    (h1 : c' 1 = 1) (ρ : K →* (W →L[ℂ] W)) (w : W) :
    w ∈ secSp K P c ρ ↔ ∃ hw : w ∈ fixSp K Q π c₀ ρ,
      (⟨w, hw⟩ : fixSp K Q π c₀ ρ) ∈ secSp K' P' c' (resRep hL ρ) := by
  constructor
  · intro hw
    have hfix : w ∈ fixSp K Q π c₀ ρ := by
      intro r hr hπ
      have hrP : (r : G) ∈ P := (hP.mem _).2 ⟨hr, by rw [hπ]; exact P'.one_mem⟩
      have h2 := hw r hrP
      rwa [hP.ch ⟨r, hr⟩ (by rw [hπ]; exact P'.one_mem), hπ, h1, mul_one] at h2
    refine ⟨hfix, fun m hm => ?_⟩
    apply Subtype.ext
    have hπ : π ⟨ι m, (ι m).2⟩ = m := hL.sect m
    have hιP : ((kι hL m : K) : G) ∈ P := (hP.mem _).2 ⟨(ι m).2, by
      show π ⟨ι m, (ι m).2⟩ ∈ P'
      rw [hπ]
      exact hm⟩
    have h2 := hw _ hιP
    have h3 : c ((kι hL m : K) : G) = c' m := by
      have := hP.ch (ι m) (by rw [hL.sect]; exact hm)
      rw [hL.sect, hL.triv, one_mul] at this
      exact this
    rw [h3] at h2
    exact h2
  · rintro ⟨hfix, hw⟩ r hr
    obtain ⟨hrQ, hrπ⟩ := (hP.mem _).1 hr
    set m : K' := ⟨π ⟨r, hrQ⟩, hL.πK ⟨r, hrQ⟩ r.2⟩ with hm
    set s : K := r * (kι hL m)⁻¹ with hs
    have hsval : (s : G) = ((⟨r, hrQ⟩ * (ι (π ⟨r, hrQ⟩))⁻¹ : Q) : G) := by
      simp [hs, hm]
    have hsQ : (s : G) ∈ Q := by
      rw [hsval]
      exact Subtype.property _
    have hsπ : π ⟨s, hsQ⟩ = 1 := by
      have : (⟨(s : G), hsQ⟩ : Q) = ⟨r, hrQ⟩ * (ι (π ⟨r, hrQ⟩))⁻¹ := Subtype.ext hsval
      rw [this, map_mul, map_inv, hL.sect]
      simp
    have hcs : c₀ (s : G) = c₀ r := by
      rw [hsval, ← map_inv, c₀_ι_right hL]
    have hfs := hfix s hsQ hsπ
    rw [hcs] at hfs
    have h3 := congrArg Subtype.val (hw m hrπ)
    have h3' : c' m • ρ (kι hL m) w = w := h3
    have h4 : ρ r w = ρ s (ρ (kι hL m) w) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hs]
      simp
    rw [hP.ch ⟨r, hrQ⟩ hrπ, h4, mul_smul]
    have h5 : c' (π ⟨r, hrQ⟩) • ρ s (ρ (kι hL m) w) = ρ s (c' m • ρ (kι hL m) w) := by
      rw [map_smul]
    rw [h5, h3', hfs]

theorem isPar_pull [IsTopologicalGroup G] (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    (hP : IsPull Q P P' π c₀ c c') (h : IsPar Γ' K' P' c') : IsPar (Γ ⊓ Q) K P c := by
  have hPQ : P ≤ Q := fun g hg => ((hP.mem g).1 hg).1
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · have : (P : Set G) = Subtype.val '' (π ⁻¹' (P' : Set G')) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hP.mem g).1 hg
        exact ⟨⟨g, h1⟩, h2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact (hP.mem _).2 ⟨q.2, hq⟩
    rw [this]
    exact hL.par.closed.isClosedEmbedding_subtypeVal.isClosedMap _ (h.closed.preimage hL.contπ)
  · intro g
    obtain ⟨q, k, hg⟩ := exists_qk hL g
    obtain ⟨p', hp', k', hk', hq⟩ := h.iwa (π q)
    set m : K' := ⟨k', hk'⟩ with hm
    refine ⟨((q * ι k'⁻¹ : Q) : G), (hP.mem _).2 ⟨Subtype.property _, ?_⟩, ((kι hL m * k : K) : G),
      Subtype.property _, ?_⟩
    · show π (q * ι k'⁻¹) ∈ P'
      have : π (q * ι k'⁻¹) = p' := by
        simp [map_mul, map_inv, hL.sect, hq]
      rw [this]
      exact hp'
    · simp [hg, hm]
  · intro p hp q hq
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hp
    obtain ⟨hq1, hq2⟩ := (hP.mem _).1 hq
    have h1 := hP.ch ⟨p, hp1⟩ hp2
    have h2 := hP.ch ⟨q, hq1⟩ hq2
    have h3 := hP.ch (⟨p, hp1⟩ * ⟨q, hq1⟩) (by rw [map_mul]; exact P'.mul_mem hp2 hq2)
    have h4 := c₀_mul hL ⟨p, hp1⟩ ⟨q, hq1⟩
    rw [map_mul, h4, h.ch.mul _ hp2 _ hq2] at h3
    simp only [Subgroup.coe_mul] at h3 h1 h2
    rw [h3, h1, h2]
    ring
  · intro p hp
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hp
    have h1 := hP.ch ⟨p, hp1⟩ hp2
    simp only at h1
    rw [h1, norm_mul, hL.par.ch.norm p hp1, h.ch.norm _ hp2, one_mul]
  · intro γ hγ hγP
    obtain ⟨hp1, hp2⟩ := (hP.mem _).1 hγP
    have h1 := hP.ch ⟨γ, hp1⟩ hp2
    simp only at h1
    rw [h1, hL.par.ch.rat γ hγ.1 hp1, h.ch.rat _ (hL.πΓ ⟨γ, hp1⟩ hγ.1) hp2, one_mul]
  · rw [continuousOn_iff_continuous_restrict]
    have hin : Continuous fun p : P => (⟨p, hPQ p.2⟩ : Q) :=
      Continuous.subtype_mk continuous_subtype_val _
    have hc₀ : Continuous fun q : Q => c₀ q :=
      continuousOn_iff_continuous_restrict.1 hL.par.ch.cont
    have hc' : Continuous fun q : P' => c' q :=
      continuousOn_iff_continuous_restrict.1 h.ch.cont
    have hπ : Continuous fun p : P => (⟨π ⟨p, hPQ p.2⟩, ((hP.mem _).1 p.2).2⟩ : P') :=
      Continuous.subtype_mk (hL.contπ.comp hin) _
    refine ((hc₀.comp hin).mul (hc'.comp hπ)).congr (fun p => ?_)
    have := hP.ch ⟨p, hPQ p.2⟩ ((hP.mem _).1 p.2).2
    exact this.symm

end Pull

section Main

def Corr (ρ : K →* (W →L[ℂ] W)) (L : Submodule ℂ W) (L' : Submodule ℂ (fixSp K Q π c₀ ρ)) : Prop :=
  ∀ w, w ∈ L ↔ ∃ hw : w ∈ fixSp K Q π c₀ ρ, (⟨w, hw⟩ : fixSp K Q π c₀ ρ) ∈ L'

def corrE [FiniteDimensional ℂ W] {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W}
    {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (h : Corr ρ L L') : L ≃L[ℂ] L' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w => ⟨⟨w, ((h w).1 w.2).choose⟩, ((h w).1 w.2).choose_spec⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => ⟨v.1.1, (h _).2 ⟨v.1.2, v.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']

def cj (e : A ≃L[ℂ] A') (f : B ≃L[ℂ] B') : (A' →L[ℂ] B') →L[ℂ] (A →L[ℂ] B) :=
  (ContinuousLinearMap.compL ℂ A B' B (f.symm : B' →L[ℂ] B)).comp
    ((ContinuousLinearMap.compL ℂ A A' B').flip (e : A →L[ℂ] A'))

theorem cj_apply (e : A ≃L[ℂ] A') (f : B ≃L[ℂ] B') (T : A' →L[ℂ] B') (x : A) :
    cj e f T x = f.symm (T (e x)) := rfl

theorem leftGood_comp (T : A →L[ℂ] B) {f : ℂ → A} {a : ℝ} (h : LeftGood f a) :
    LeftGood (fun z => T (f z)) a := by
  refine ⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩
  obtain ⟨M, hM⟩ := h.2 b c hc
  refine ⟨‖T‖ * M, fun z h1 h2 => ?_⟩
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))

def hOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) {L' : Type}
    [NormedAddCommGroup L'] [NormedSpace ℂ L'] (e : A ≃L[ℂ] L')
    (H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)) (z : ℂ) (g : G) : A →L[ℂ] W :=
  ext hL ρ (fun g' => (H' z g').comp (e : A →L[ℂ] L')) g

theorem hOf_eq (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) {L' : Type}
    [NormedAddCommGroup L'] [NormedSpace ℂ L'] (e : A ≃L[ℂ] L')
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w))
    (z : ℂ) (q : Q) (k : K) (w : A) :
    hOf hL ρ e H' z ((q : G) * k) w = am ρ c₀ π q k (H' z (π q) (e w)) := by
  have h := ext_eq hL ρ (F := fun g' => (H' z g').comp (e : A →L[ℂ] L'))
    (fun g m x => hE z g m (e x)) q k
  exact congrArg (fun T : A →L[ℂ] W => T w) h

theorem ht_left {P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) {γ : G} (hγ : γ ∈ Γ) (hγP : γ ∈ P)
    (x : G) : η (γ * x) = η x := by
  rw [h.left γ hγP, h.rat γ hγ hγP, zero_add]

variable {P₁ P₂ : Subgroup G} {P₁' P₂' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
  {η₁ η₂ β : G → ℝ} {η₁' η₂' β' : G' → ℝ}

theorem wall_pull [IsTopologicalGroup G] [LocallyCompactSpace G] [FiniteDimensional ℂ W]
    (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) (hP₁ : IsPull Q P₁ P₁' π c₀ c c') (hP₂ : IsPull Q P₂ P₂' π c₀ c c')
    (hpar₁ : IsPar Γ' K' P₁' c') (hpar₂ : IsPar Γ' K' P₂' c')
    (hη₁ : IsHt Γ' K' P₁' η₁') (hη₂ : IsHt Γ' K' P₂' η₂') (hβ : IsHt Γ' K' P₂' β')
    (hp₁ : PullHt K Q π η₁ η₁') (hp₂ : PullHt K Q π η₂ η₂') (hpβ : PullHt K Q π β β')
    (law₁ : Law K P₁ c ρ) (law₂ : Law K P₂ c ρ) (law₁' : Law K' P₁' c' (resRep hL ρ))
    (law₂' : Law K' P₂' c' (resRep hL ρ)) {M₁ M₂ : ℝ}
    (bd₁ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₁' c' (resRep hL ρ) g w‖ ≤ M₁ * ‖w‖)
    (bd₂ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₂' c' (resRep hL ρ) g w‖ ≤ M₂ * ‖w‖)
    {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
    (hC₁ : Corr ρ (secSp K P₁ c ρ) (secSp K' P₁' c' (resRep hL ρ)))
    (hC₂ : Corr ρ (secSp K P₂ c ρ) (secSp K' P₂' c' (resRep hL ρ)))
    {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hw : Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H')
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w)) :
    Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE hC₂) (Op' z))
      (hOf hL ρ (corrE hLL) H') := by
  haveI : CompleteSpace (fixSp K Q π c₀ ρ) := FiniteDimensional.complete ℂ _
  have hle : ∀ w : L, (w : W) ∈ secSp K P₁ c ρ := by
    intro w
    obtain ⟨h1, h2⟩ := (hLL w).1 w.2
    exact (hC₁ w).2 ⟨h1, hw.le h2⟩
  have hpull : ∀ {η : G → ℝ} {η' : G' → ℝ}, PullHt K Q π η η' → ∀ (q : Q) (k : K),
      η ((q : G) * k) = η' (π q) := fun h q k => h q k k.2
  refine ⟨fun w hw' => hle ⟨w, hw'⟩, hw.pos, fun x hx => ?_, fun x hx => ?_, hw.dEnt, hw.dNe, ?_, fun g => ?_, ?_,
    fun b a g => ?_, fun z hz g w => ?_, fun z hz g w => ?_⟩
  · refine conv_pull hL hP₁ (l' := fun g => x * η₁' g) (fun q k => ?_) (fun γ hγ hγP y => ?_)
      (hw.convR x hx)
    · simp only [hpull hp₁ q k]
    · simp only [ht_left hη₁ hγ hγP y]
  · refine conv_pull hL hP₂ (l' := fun g => β' g - x * η₂' g) (fun q k => ?_) (fun γ hγ hγP y => ?_)
      (hw.convL x hx)
    · simp only [hpull hp₂ q k, hpull hpβ q k]
    · simp only [ht_left hη₂ hγ hγP y, ht_left hβ hγ hγP y]
  · exact leftGood_comp (cj (corrE hLL) (corrE hC₂)) hw.op
  · let T : (L' →L[ℂ] fixSp K Q π c₀ ρ) →L[ℂ] (L →L[ℂ] W) :=
      (ContinuousLinearMap.compL ℂ L _ W (am ρ c₀ π (qOf hL g) (kOf hL g))).comp
        ((ContinuousLinearMap.compL ℂ L L' _).flip (corrE hLL : L →L[ℂ] L'))
    exact T.differentiable.comp (hw.hol (π (qOf hL g)))
  · refine ext_cont hK hL hρ (F := fun z g' => (H' z g').comp (corrE hLL : L →L[ℂ] L'))
      (fun z g m x => hE z g m _) ?_
    exact hw.cont.clm_comp continuous_const
  · refine ext_bdd hK hL hρ {z : ℂ | b ≤ z.re ∧ z.re ≤ a}
      (fun z g' => (H' z g').comp (corrE hLL : L →L[ℂ] L')) (fun g' => ?_) g |>.imp ?_
    · obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g'
      refine ⟨U, hU, M * ‖(corrE hLL : L →L[ℂ] L')‖, fun t ht x hx => ?_⟩
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hM t ht.1 ht.2 x hx) (norm_nonneg _)
    · rintro U ⟨hU, M, hM⟩
      exact ⟨hU, M, fun z h1 h2 g' hg' => hM z ⟨h1, h2⟩ g' hg'⟩
  · obtain ⟨q, k, rfl⟩ := exists_qk hL g
    have hv := hw.le (corrE hLL w).2
    have hs := summable_eis (Λ := fun x => z * η₁' x) (l := fun x => z.re * η₁' x) bd₁
      (fun g => by simp) (hw.convR z.re hz) (π q) ((corrE hLL w : L') : fixSp K Q π c₀ ρ)
    have := eis_pull (Λ := fun x => z * η₁ x) (Λ' := fun x => z * η₁' x) hL hP₁ hpar₁ law₁ law₁'
      (fun q k => by simp only [hpull hp₁ q k]) (fun γ hγ hγP y => by simp only [ht_left hη₁ hγ hγP y])
      hv (hle w) q k hs
    rw [hOf_eq hL ρ _ hE, hw.eqR z hz, map_smul]
    exact congrArg (fun u => D z • u) this.symm
  · obtain ⟨q, k, rfl⟩ := exists_qk hL g
    have hv := (Op' z (corrE hLL w)).2
    have hs := summable_eis (Λ := fun x => (β' x : ℂ) - z * η₂' x) (l := fun x => β' x - z.re * η₂' x)
      bd₂ (fun g => by simp) (hw.convL z.re hz) (π q)
      ((Op' z (corrE hLL w) : secSp K' P₂' c' (resRep hL ρ)) : fixSp K Q π c₀ ρ)
    have := eis_pull (Λ := fun x => (β x : ℂ) - z * η₂ x) (Λ' := fun x => (β' x : ℂ) - z * η₂' x) hL hP₂
      hpar₂ law₂ law₂'
      (fun q k => by simp only [hpull hp₂ q k, hpull hpβ q k])
      (fun γ hγ hγP y => by simp only [ht_left hη₂ hγ hγP y, ht_left hβ hγ hγP y])
      hv (cj (corrE hLL) (corrE hC₂) (Op' z) w).2 q k hs
    rw [hOf_eq hL ρ _ hE, hw.eqL z hz]
    exact this.symm

end Main

end GlobalTheory.CompanionTheory.RgTransfer
