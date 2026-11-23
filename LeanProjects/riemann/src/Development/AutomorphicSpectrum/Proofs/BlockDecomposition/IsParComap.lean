import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CorrESymmCoe

noncomputable section

open Filter Topology PositivityTheory.RgEis PositivityTheory.RgEis.So
open GlobalTheory.CompanionTheory.RgTransfer (cj cj_apply leftGood_comp sec_left Law ht_left)

namespace GlobalTheory.CompanionTheory.RgDescendWall

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁]

def kj (j : G₁ →* G) {K₁ : Subgroup G₁} {K : Subgroup G} (h : K₁ ≤ K.comap j) : K₁ →* K :=
  (j.comp K₁.subtype).codRestrict K (fun m => h m.2)

@[simp] theorem kj_coe (j : G₁ →* G) {K₁ : Subgroup G₁} {K : Subgroup G} (h : K₁ ≤ K.comap j) (m : K₁) :
    ((kj j h m : K) : G) = j m := rfl

theorem kj_cont {j : G₁ →* G} (hj : Continuous j) {K₁ : Subgroup G₁} {K : Subgroup G}
    (h : K₁ ≤ K.comap j) : Continuous (kj j h) :=
  Continuous.subtype_mk (hj.comp continuous_subtype_val) _

variable {Γ K P : Subgroup G} {Γ₁ K₁ : Subgroup G₁} {j : G₁ →* G} {c : G → ℂ}

theorem secSp_eq (h : K₁ ≤ K.comap j) {s : P → G₁} (hs : ∀ p, j (s p) = p)
    (hsK : ∀ p : P, (p : G) ∈ K → s p ∈ K₁) (ρ : K →* (W →L[ℂ] W)) :
    secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j h)) = secSp K P c ρ := by
  ext w
  constructor
  · intro hw r hr
    have hm : s ⟨r, hr⟩ ∈ K₁ := hsK ⟨r, hr⟩ r.2
    have h1 := hw ⟨s ⟨r, hr⟩, hm⟩ (by
      show j (s ⟨r, hr⟩) ∈ P
      rw [hs]
      exact hr)
    have h2 : kj j h ⟨s ⟨r, hr⟩, hm⟩ = r := Subtype.ext (hs _)
    have h3 : (c ∘ j) (s ⟨r, hr⟩) = c r := by
      show c (j _) = _
      rw [hs]
    simp only [MonoidHom.comp_apply, h2] at h1
    rwa [h3] at h1
  · intro hw r hr
    exact hw (kj j h r) hr

theorem isPar_comap (hj : Continuous j) (hΓ : Γ₁.map j = Γ) (hi : Iwa (P.comap j) K₁)
    (h : IsPar Γ K P c) : IsPar Γ₁ K₁ (P.comap j) (c ∘ j) := by
  refine ⟨h.closed.preimage hj, hi, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p hp q hq
    simp only [Function.comp, map_mul]
    exact h.ch.mul _ hp _ hq
  · intro p hp
    exact h.ch.norm _ hp
  · intro γ hγ hγP
    exact h.ch.rat _ (hΓ ▸ Subgroup.mem_map_of_mem j hγ) hγP
  · exact h.ch.cont.comp hj.continuousOn (fun _ hx => hx)

theorem sec_eq (hKK : K₁ ≤ K.comap j) (hi : Iwa (P.comap j) K₁) {ρ : K →* (W →L[ℂ] W)}
    (law : Law K P c ρ) (law₁ : Law K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK))) {w : W}
    (hw : w ∈ secSp K P c ρ) (hw₁ : w ∈ secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK))) (x : G₁) :
    sec K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) x w = sec K P c ρ (j x) w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hi x
  have h1 := law₁ w hw₁ p hp ⟨k, hk⟩
  have h2 := law w hw (j p) hp (kj j hKK ⟨k, hk⟩)
  simp only [kj_coe] at h2
  rw [map_mul, h2]
  simpa using h1

theorem cos_exists (hΓ : Γ₁.map j = Γ) :
    ∃ φ : Cos (P.comap j) Γ₁ ≃ Cos P Γ, ∀ x, ∃ γ ∈ Γ, γ ∈ P ∧ j (rep x) = γ * rep (φ x) := by
  have hm : ∀ d : Γ₁, j d ∈ Γ := fun d => hΓ ▸ Subgroup.mem_map_of_mem j d.2
  let f : Γ₁ → Γ := fun d => ⟨j d, hm d⟩
  have hf : ∀ a b : Γ₁, b * a⁻¹ ∈ (P.comap j).subgroupOf Γ₁ ↔ f b * (f a)⁻¹ ∈ P.subgroupOf Γ := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    simp [f]
  let φ₀ : Cos (P.comap j) Γ₁ → Cos P Γ := Quotient.map' f (fun a b h =>
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
      have hmm : (m : G) ∈ Γ₁.map j := hΓ ▸ m.2
      obtain ⟨d, hd, hdm⟩ := hmm
      refine ⟨Quotient.mk _ ⟨d, hd⟩, ?_⟩
      show Quotient.mk _ (f _) = _
      congr 1
      exact Subtype.ext hdm
  refine ⟨Equiv.ofBijective φ₀ hbij, fun x => ?_⟩
  set d := Quotient.out x with hd
  have hx : Quotient.mk _ d = x := Quotient.out_eq x
  set e := Quotient.out (Equiv.ofBijective φ₀ hbij x) with he
  have he' : Quotient.mk _ e = Equiv.ofBijective φ₀ hbij x := Quotient.out_eq _
  have h1 : Equiv.ofBijective φ₀ hbij x = Quotient.mk _ (f d) :=
    (congrArg (Equiv.ofBijective φ₀ hbij) hx).symm
  have hrel := Quotient.exact (he'.trans h1)
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 hrel)
  refine ⟨((f d * e⁻¹ : Γ) : G), (f d * e⁻¹).2, hmem, ?_⟩
  show j d = ((f d * e⁻¹ : Γ) : G) * (e : G)
  simp [f]

theorem conv_desc (hΓ : Γ₁.map j = Γ) (hsurj : ∀ g, ∃ (x : G₁) (k : K), g = j x * k) {l : G → ℝ}
    {l₁ : G₁ → ℝ} (hl₁ : ∀ x, l₁ x = l (j x)) (hinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, l (γ * x) = l x)
    (hr : ∀ g, ∀ k ∈ K, l (g * k) = l g) (hc : Conv Γ₁ (P.comap j) l₁) : Conv Γ P l := by
  obtain ⟨φ, hφ⟩ := cos_exists (P := P) hΓ
  intro g
  obtain ⟨x, k, rfl⟩ := hsurj g
  have h1 := hc x
  rw [← φ.summable_iff]
  refine h1.congr (fun q => ?_)
  obtain ⟨γ, hγ, hγP, h⟩ := hφ q
  simp only [Function.comp]
  rw [hl₁, map_mul, h, mul_assoc, hinv γ hγ hγP, ← mul_assoc, hr _ _ k.2]

theorem sec_right (hi : Iwa P K) {ρ : K →* (W →L[ℂ] W)} (law : Law K P c ρ) {w : W}
    (hw : w ∈ secSp K P c ρ) (g : G) (k : K) :
    sec K P c ρ (g * k) w = ρ k⁻¹ (sec K P c ρ g w) := by
  obtain ⟨p, hp, k₀, hk₀, rfl⟩ := hi g
  have h1 := law w hw p hp (⟨k₀, hk₀⟩ * k)
  have h2 := law w hw p hp ⟨k₀, hk₀⟩
  simp only [Subgroup.coe_mul] at h1 h2
  rw [mul_assoc, h1, h2, map_smul, mul_inv_rev, map_mul]
  rfl

def rhoE (ρ : K →* (W →L[ℂ] W)) (k : K) : W ≃L[ℂ] W :=
  ContinuousLinearEquiv.equivOfInverse (ρ k) (ρ k⁻¹)
    (fun w => by rw [← ContinuousLinearMap.mul_apply, ← map_mul]; simp)
    (fun w => by rw [← ContinuousLinearMap.mul_apply, ← map_mul]; simp)

theorem eis_right (hi : Iwa P K) {ρ : K →* (W →L[ℂ] W)} (law : Law K P c ρ) {w : W}
    (hw : w ∈ secSp K P c ρ) {Λ : G → ℂ} (hr : ∀ g, ∀ k ∈ K, Λ (g * k) = Λ g) (g : G) (k : K) :
    eis Γ K P c ρ Λ (g * k) w = ρ k⁻¹ (eis Γ K P c ρ Λ g w) := by
  unfold eis
  have h : rhoE ρ k⁻¹ (∑' q : Cos P Γ, Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w) =
      ∑' q : Cos P Γ, rhoE ρ k⁻¹ (Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w) :=
    (rhoE ρ k⁻¹).map_tsum
  refine Eq.trans ?_ h.symm
  refine tsum_congr fun q => ?_
  rw [← mul_assoc, hr _ _ k.2, sec_right hi law hw, map_smul]
  rfl

theorem eis_pull (hΓ : Γ₁.map j = Γ) (hpar : IsPar Γ K P c) {ρ : K →* (W →L[ℂ] W)}
    (law : Law K P c ρ) {ρ₁ : K₁ →* (W →L[ℂ] W)} {w : W} (hw : w ∈ secSp K P c ρ)
    (hsec : ∀ x, sec K₁ (P.comap j) (c ∘ j) ρ₁ x w = sec K P c ρ (j x) w) {Λ : G → ℂ} {Λ₁ : G₁ → ℂ}
    (hΛ₁ : ∀ x, Λ₁ x = Λ (j x)) (hinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) (x : G₁) :
    eis Γ₁ K₁ (P.comap j) (c ∘ j) ρ₁ Λ₁ x w = eis Γ K P c ρ Λ (j x) w := by
  obtain ⟨φ, hφ⟩ := cos_exists (P := P) hΓ
  unfold eis
  rw [← φ.tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨γ, hγ, hγP, h⟩ := hφ q
  rw [hΛ₁, hsec, map_mul, h, mul_assoc, hinv γ hγ hγP, sec_left hpar law hw hγ hγP]

section Dec

def pOf (hi : Iwa P K) (g : G) : P := ⟨(hi g).choose, (hi g).choose_spec.1⟩

def kOf (hi : Iwa P K) (g : G) : K :=
  ⟨(hi g).choose_spec.2.choose, (hi g).choose_spec.2.choose_spec.1⟩

theorem pk_spec (hi : Iwa P K) (g : G) : g = pOf hi g * kOf hi g :=
  (hi g).choose_spec.2.choose_spec.2

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def hD (hi : Iwa P K) (ρ : K →* (W →L[ℂ] W)) (s : P → G₁) (F : G₁ → A →L[ℂ] W) (g : G) : A →L[ℂ] W :=
  (ρ (kOf hi g)⁻¹).comp (F (s (pOf hi g)))

def Equi (j : G₁ →* G) (ρ : K →* (W →L[ℂ] W)) (F : G₁ → A →L[ℂ] W) : Prop :=
  ∀ (x y : G₁) (k : K), j y = j x * k → ∀ a, F y a = ρ k⁻¹ (F x a)

theorem hD_eq (hi : Iwa P K) {ρ : K →* (W →L[ℂ] W)} {s : P → G₁} (hs : ∀ p, j (s p) = p)
    {F : G₁ → A →L[ℂ] W} (hF : Equi j ρ F) (x : G₁) (k : K) :
    hD hi ρ s F (j x * k) = (ρ k⁻¹).comp (F x) := by
  have h := pk_spec hi (j x * k)
  ext a
  show ρ (kOf hi (j x * k))⁻¹ (F (s (pOf hi (j x * k))) a) = ρ k⁻¹ (F x a)
  generalize pOf hi (j x * k) = p at h
  generalize kOf hi (j x * k) = k₀ at h
  have h1 : j (s p) = j x * ((k * k₀⁻¹ : K) : G) := by
    rw [hs]
    have : (p : G) = (j x * k) * (k₀ : G)⁻¹ := eq_mul_inv_of_mul_eq h.symm
    rw [this]
    simp [mul_assoc]
  rw [hF x (s p) (k * k₀⁻¹) h1 a, ← ContinuousLinearMap.mul_apply, ← map_mul]
  congr 2
  group

theorem hD_cont [IsTopologicalGroup G] {T : Type} [TopologicalSpace T] (hK : IsCompact (K : Set G))
    (hcl : IsClosed (P : Set G)) (hi : Iwa P K) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {s : P → G₁} (hsc : Continuous s) (hs : ∀ p, j (s p) = p) {F : T → G₁ → A →L[ℂ] W}
    (hF : ∀ t, Equi j ρ (F t)) (hc : Continuous fun y : T × G₁ => F y.1 y.2) :
    Continuous fun y : T × G => hD hi ρ s (F y.1) y.2 := by
  have hΦ : Continuous fun y : T × P × K => (ρ y.2.2⁻¹).comp (F y.1 (s y.2.1)) := by
    refine (hρ.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))).clm_comp ?_
    exact hc.comp (continuous_fst.prodMk (hsc.comp (continuous_fst.comp continuous_snd)))
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro U hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨k₁, -, hk₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (U.map fun y : T × G => kOf hi y.2) (by simp)
  have hk : Tendsto (fun y : T × G => kOf hi y.2) U (𝓝 k₁) := hk₁
  have hU' : Tendsto (fun y : T × G => y) U (𝓝 y₀) := hU
  have hqG : Tendsto (fun y : T × G => y.2 * ((kOf hi y.2 : K) : G)⁻¹) U (𝓝 (y₀.2 * (k₁ : G)⁻¹)) :=
    ((continuous_snd.tendsto y₀).comp hU').mul
      (((continuous_subtype_val.tendsto k₁).comp hk).inv)
  have hqe : ∀ y : T × G, y.2 * ((kOf hi y.2 : K) : G)⁻¹ = (pOf hi y.2 : G) := by
    intro y
    exact mul_inv_eq_of_eq_mul (pk_spec hi y.2)
  simp only [hqe] at hqG
  have hmem : y₀.2 * (k₁ : G)⁻¹ ∈ P :=
    hcl.mem_of_tendsto hqG (Eventually.of_forall fun y => (pOf hi y.2).2)
  have hq : Tendsto (fun y : T × G => pOf hi y.2) U (𝓝 (⟨_, hmem⟩ : P)) :=
    tendsto_subtype_rng.2 hqG
  have hlim := (hΦ.tendsto (y₀.1, (⟨_, hmem⟩ : P), k₁)).comp
    ((((continuous_fst.tendsto y₀).comp hU').prodMk_nhds (hq.prodMk_nhds hk)))
  have hy : hD hi ρ s (F y₀.1) y₀.2 = (ρ k₁⁻¹).comp (F y₀.1 (s ⟨_, hmem⟩)) := by
    rw [← hD_eq hi hs (hF y₀.1), hs]
    simp
  rw [hy]
  exact hlim

theorem hD_bdd [IsTopologicalGroup G] [LocallyCompactSpace G] {T : Type} (hK : IsCompact (K : Set G))
    (hcl : IsClosed (P : Set G)) (hi : Iwa P K) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {s : P → G₁} (hsc : Continuous s) (S : Set T) (F : T → G₁ → A →L[ℂ] W)
    (hb : ∀ x, ∃ U ∈ 𝓝 x, ∃ M : ℝ, ∀ t ∈ S, ∀ y ∈ U, ‖F t y‖ ≤ M) (g : G) :
    ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ t ∈ S, ∀ g' ∈ U, ‖hD hi ρ s (F t) g'‖ ≤ M := by
  obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
  refine ⟨C, hCg, ?_⟩
  set C₁ : Set G := (fun a : G × G => a.1 * a.2⁻¹) '' (C ×ˢ (K : Set G)) with hC₁
  have hC₁c : IsCompact C₁ :=
    (hC.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hCq : IsCompact ((↑) ⁻¹' C₁ : Set P) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC₁c
  have hC' : IsCompact (s '' ((↑) ⁻¹' C₁ : Set P)) := hCq.image hsc
  have hM : ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ s '' ((↑) ⁻¹' C₁ : Set P), ‖F t x‖ ≤ M := by
    refine hC'.induction_on (p := fun u => ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ u, ‖F t x‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨0, fun _ _ _ h => absurd h (Set.notMem_empty _)⟩
    · rintro a b hab ⟨M, hM⟩
      exact ⟨M, fun t ht x hx => hM t ht x (hab hx)⟩
    · rintro a b ⟨M, hM⟩ ⟨N, hN⟩
      refine ⟨max M N, fun t ht x hx => ?_⟩
      rcases hx with hx | hx
      · exact (hM t ht x hx).trans (le_max_left _ _)
      · exact (hN t ht x hx).trans (le_max_right _ _)
    · intro x _
      obtain ⟨U, hU, M, hM⟩ := hb x
      exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, M, hM⟩
  obtain ⟨M, hM⟩ := hM
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨B * M, fun t ht g' hg' => ?_⟩
  have hq : (pOf hi g' : G) ∈ C₁ := by
    refine ⟨(g', kOf hi g'), ⟨hg', (kOf hi g').2⟩, ?_⟩
    exact mul_inv_eq_of_eq_mul (pk_spec hi g')
  have h2 := hM t ht (s (pOf hi g')) ⟨_, hq, rfl⟩
  have h1 := hB (kOf hi g')⁻¹ (Set.mem_univ _)
  unfold hD
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

end Dec

section Main

def eL [FiniteDimensional ℂ W] {L L' : Submodule ℂ W} (h : L = L') : L ≃L[ℂ] L' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w => ⟨w, h ▸ w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => ⟨v, h ▸ v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem eL_coe [FiniteDimensional ℂ W] {L L' : Submodule ℂ W} (h : L = L') (w : L) :
    ((eL h w : L') : W) = w := rfl

def eC [FiniteDimensional ℂ W] {L L' : Submodule ℂ W} (h : L = L') : L →L[ℂ] L' := (eL h : L →L[ℂ] L')

variable {η η' β : G → ℝ}

theorem wall_desc [IsTopologicalGroup G] [LocallyCompactSpace G] [FiniteDimensional ℂ W]
    (hK : IsCompact (K : Set G)) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) (hKK : K₁ ≤ K.comap j)
    (hΓ : Γ₁.map j = Γ) {s : P → G₁} (hsc : Continuous s) (hjs : ∀ p, j (s p) = p)
    (hi₁ : Iwa (P.comap j) K₁) (hpar : IsPar Γ K P c) (hη : IsHt Γ K P η) (hη' : IsHt Γ K P η')
    (hβ : IsHt Γ K P β) (law : Law K P c ρ) (law₁ : Law K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)))
    (hLe : secSp K P c ρ = secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)))
    {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) →L[ℂ]
      secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)))}
    {H₁ : ℂ → G₁ → (secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) →L[ℂ] W)}
    (hw : Wall Γ₁ K₁ (P.comap j) (P.comap j) (c ∘ j) (η ∘ j) (η' ∘ j) (β ∘ j) (ρ.comp (kj j hKK))
      (secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK))) R D Op H₁) :
    Wall Γ K P P c η η' β ρ (secSp K P c ρ) R D (fun z => cj (eL hLe) (eL hLe) (Op z))
      (fun z => hD hpar.iwa ρ s fun x => (H₁ z x).comp (eC hLe)) := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsurj : ∀ g, ∃ (x : G₁) (k : K), g = j x * k := fun g =>
    ⟨s (pOf hpar.iwa g), kOf hpar.iwa g, by rw [hjs]; exact pk_spec _ g⟩
  have hsec : ∀ w ∈ secSp K P c ρ, ∀ x,
      sec K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) x w = sec K P c ρ (j x) w :=
    fun w hv x => sec_eq hKK hi₁ law law₁ hv (hLe.le hv) x
  have hpull : ∀ {Λ : G → ℂ} {Λ₁ : G₁ → ℂ}, (∀ x, Λ₁ x = Λ (j x)) →
      (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) → ∀ w ∈ secSp K P c ρ, ∀ x,
      eis Γ₁ K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) Λ₁ x w = eis Γ K P c ρ Λ (j x) w :=
    fun hΛ hinv w hv x => eis_pull hΓ hpar law hv (hsec w hv) hΛ hinv x
  have hinvR : ∀ z : ℂ, ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => z * (η x : ℂ)) (γ * x) = z * η x :=
    fun z γ hγ hγP x => by simp only [ht_left hη hγ hγP x]
  have hinvL : ∀ z : ℂ, ∀ γ ∈ Γ, γ ∈ P → ∀ x,
      (fun x => (β x : ℂ) - z * (η' x : ℂ)) (γ * x) = (β x : ℂ) - z * η' x :=
    fun z γ hγ hγP x => by simp only [ht_left hη' hγ hγP x, ht_left hβ hγ hγP x]
  have hE : ∀ z, Equi j ρ (fun x => (H₁ z x).comp (eC hLe)) := by
    intro z x y k hxy w
    have hf : Differentiable ℂ fun z => H₁ z y (eL hLe w) :=
      (hw.hol y).clm_apply (differentiable_const _)
    have hg : Differentiable ℂ fun z => ρ k⁻¹ (H₁ z x (eL hLe w)) :=
      (ρ k⁻¹).differentiable.comp ((hw.hol x).clm_apply (differentiable_const _))
    have hev : (fun z => H₁ z y (eL hLe w)) =ᶠ[𝓝 ((R + 1 : ℝ) : ℂ)]
        fun z => ρ k⁻¹ (H₁ z x (eL hLe w)) := by
      have hmem : {z : ℂ | R < z.re} ∈ 𝓝 ((R + 1 : ℝ) : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [hmem] with z hz
      rw [hw.eqR z hz y, hw.eqR z hz x, map_smul]
      congr 1
      have h1 := hpull (Λ := fun x => z * (η x : ℂ)) (Λ₁ := fun x => z * ((η ∘ j) x : ℂ))
        (fun _ => rfl) (hinvR z) w w.2
      rw [eL_coe, h1 y, h1 x, hxy]
      exact eis_right hpar.iwa law w.2 (fun g k hk => by simp only [hη.right g k hk]) _ k
    have := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z)
      (fun z _ => hg.analyticAt z) hev
    exact congrFun this z
  refine ⟨le_refl _, hw.pos, fun x hx => ?_, fun x hx => ?_, hw.dEnt, hw.dNe, ?_, fun g => ?_, ?_,
    fun b a g => ?_, fun z hz g w => ?_, fun z hz g w => ?_⟩
  · exact conv_desc hΓ hsurj (l := fun g => x * η g) (fun _ => rfl)
      (fun γ hγ hγP y => by simp only [ht_left hη hγ hγP y])
      (fun g k hk => by simp only [hη.right g k hk]) (hw.convR x hx)
  · exact conv_desc hΓ hsurj (l := fun g => β g - x * η' g) (fun _ => rfl)
      (fun γ hγ hγP y => by simp only [ht_left hη' hγ hγP y, ht_left hβ hγ hγP y])
      (fun g k hk => by simp only [hη'.right g k hk, hβ.right g k hk]) (hw.convL x hx)
  · exact leftGood_comp (cj (eL hLe) (eL hLe)) hw.op
  · let T : (secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) →L[ℂ] W) →L[ℂ] (secSp K P c ρ →L[ℂ] W) :=
      (ContinuousLinearMap.compL ℂ (secSp K P c ρ) W W (ρ (kOf hpar.iwa g)⁻¹)).comp
        ((ContinuousLinearMap.compL ℂ (secSp K P c ρ) _ W).flip (eC hLe))
    exact T.differentiable.comp (hw.hol (s (pOf hpar.iwa g)))
  · exact hD_cont hK hpar.closed hpar.iwa hρ hsc hjs
      (F := fun z x => (H₁ z x).comp (eC hLe)) hE
      (hw.cont.clm_comp continuous_const)
  · refine hD_bdd hK hpar.closed hpar.iwa hρ hsc {z : ℂ | b ≤ z.re ∧ z.re ≤ a}
      (fun z x => (H₁ z x).comp (eC hLe)) (fun x => ?_) g |>.imp ?_
    · obtain ⟨U, hU, M, hM⟩ := hw.bdd b a x
      refine ⟨U, hU, M * ‖(eC hLe)‖, fun t ht y hy => ?_⟩
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hM t ht.1 ht.2 y hy) (norm_nonneg _)
    · rintro U ⟨hU, M, hM⟩
      exact ⟨hU, M, fun z h1 h2 g' hg' => hM z ⟨h1, h2⟩ g' hg'⟩
  · obtain ⟨x, k, rfl⟩ := hsurj g
    have h1 := hpull (Λ := fun x => z * (η x : ℂ)) (Λ₁ := fun x => z * ((η ∘ j) x : ℂ))
      (fun _ => rfl) (hinvR z) w w.2 x
    have h2 := eis_right (Γ := Γ) hpar.iwa law w.2 (Λ := fun x => z * (η x : ℂ))
      (fun g k hk => by simp only [hη.right g k hk]) (j x) k
    show hD hpar.iwa ρ s (fun x => (H₁ z x).comp (eC hLe)) (j x * k) w = _
    rw [hD_eq hpar.iwa hjs (hE z), h2, ← h1]
    show ρ k⁻¹ (H₁ z x (eL hLe w)) = _
    rw [show H₁ z x (eL hLe w) = _ from hw.eqR z hz x (eL hLe w), map_smul]
    rfl
  · obtain ⟨x, k, rfl⟩ := hsurj g
    have hv : (((Op z (eL hLe w) : secSp K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)))) : W) ∈
        secSp K P c ρ := hLe.ge (Op z (eL hLe w)).2
    have h1 := hpull (Λ := fun x => (β x : ℂ) - z * (η' x : ℂ))
      (Λ₁ := fun x => ((β ∘ j) x : ℂ) - z * ((η' ∘ j) x : ℂ)) (fun _ => rfl) (hinvL z) _ hv x
    have h2 := eis_right (Γ := Γ) hpar.iwa law hv (Λ := fun x => (β x : ℂ) - z * (η' x : ℂ))
      (fun g k hk => by simp only [hη'.right g k hk, hβ.right g k hk]) (j x) k
    show hD hpar.iwa ρ s (fun x => (H₁ z x).comp (eC hLe)) (j x * k) w = _
    rw [hD_eq hpar.iwa hjs (hE z)]
    show ρ k⁻¹ (H₁ z x (eL hLe w)) = _
    rw [hw.eqL z hz x, h1]
    exact h2.symm

end Main

theorem descend2 : SecLaw → Descend2 := by
  intro hSec G _ _ _ _ _ W _ _ _ K ρ hK hρ G₁ _ _ _ _ _ j Γ P Γ₁ K₁ c η η' β s hj hK₁ hKK hΓ hsc hjs hsK
    hi₁ hpar hη hη' hβ hW
  have hcont : Continuous (ρ.comp (kj j hKK)) := hρ.comp (kj_cont hj hKK)
  have hpar₁ := isPar_comap hj hΓ hi₁ hpar
  have law : Law K P c ρ := (hSec G W K ρ hK hρ Γ P c hpar).1
  have law₁ : Law K₁ (P.comap j) (c ∘ j) (ρ.comp (kj j hKK)) :=
    (hSec G₁ W K₁ _ hK₁ hcont Γ₁ _ _ hpar₁).1
  obtain ⟨R, D, Op, H₁, hw⟩ := hW W (ρ.comp (kj j hKK)) hcont
  exact ⟨R, D, _, _, wall_desc hK hρ hKK hΓ hsc hjs hi₁ hpar hη hη' hβ law law₁
    (secSp_eq hKK hjs hsK ρ).symm hw⟩

end GlobalTheory.CompanionTheory.RgDescendWall
