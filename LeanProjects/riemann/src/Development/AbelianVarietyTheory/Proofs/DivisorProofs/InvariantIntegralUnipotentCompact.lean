import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.Uniq

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ncos (N P : Subgroup G) : Set G := {g | ∃ u ∈ N, ∃ c ∈ P, g = u * c}

def dcos (N P : Subgroup G) (x : G) : Set G := {g | ∃ u ∈ N, ∃ p ∈ P, g = u * x * p}

def cj (x : G) (P : Subgroup G) : Subgroup G := P.comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_cj {x y : G} {P : Subgroup G} : y ∈ cj x P ↔ x⁻¹ * y * x ∈ P := by
  simp [cj, MulAut.conj_apply]

theorem indicator_isLocallyConstant {W : Set G} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := fun s => by
  have h := Set.indicator_const_preimage W s c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hW.isOpen, hW.isClosed.isOpen_compl, isOpen_empty]

theorem nhds_of_relOpen {B P : Subgroup G} (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) :
    ∃ U ∈ nhds (1 : G), ∀ y ∈ B, y ∈ U → y ∈ P := by
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp hPo
  have h1 : (⟨1, B.one_mem⟩ : B) ∈ (Subtype.val : B → G) ⁻¹' V := by rw [hVe]; exact P.one_mem
  refine ⟨V, hV.mem_nhds h1, fun y hy hyV => ?_⟩
  have : (⟨y, hy⟩ : B) ∈ (Subtype.val : B → G) ⁻¹' V := hyV
  rw [hVe] at this
  exact this

theorem cj_le {B P : Subgroup G} {x : G} (hx : x ∈ B) (hPB : P ≤ B) : cj x P ≤ B := by
  intro y hy
  rw [mem_cj] at hy
  have := B.mul_mem (B.mul_mem hx (hPB hy)) (B.inv_mem hx)
  rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this

theorem cj_compact {P : Subgroup G} (x : G) (hPc : IsCompact (P : Set G)) :
    IsCompact ((cj x P : Subgroup G) : Set G) := by
  have : ((cj x P : Subgroup G) : Set G) = (fun y => x * y * x⁻¹) '' (P : Set G) := by
    ext y
    simp only [SetLike.mem_coe, mem_cj, Set.mem_image]
    constructor
    · intro h; exact ⟨_, h, by group⟩
    · rintro ⟨z, hz, rfl⟩; rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group]
  rw [this]
  exact hPc.image (by fun_prop)

theorem cj_open {B P : Subgroup G} {x : G} (hx : x ∈ B)
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) :
    IsOpen ((Subtype.val : B → G) ⁻¹' (cj x P)) := by
  have : (Subtype.val : B → G) ⁻¹' (cj x P) =
      (fun b : B => (⟨x, hx⟩ : B)⁻¹ * b * ⟨x, hx⟩) ⁻¹' ((Subtype.val : B → G) ⁻¹' P) := by
    ext b; simp [mem_cj]
  rw [this]
  exact hPo.preimage (by fun_prop)

theorem dcos_eq (N P : Subgroup G) (x : G) :
    dcos N P x = (fun g => g * x⁻¹) ⁻¹' ncos N (cj x P) := by
  ext g
  simp only [dcos, ncos, Set.mem_preimage, Set.mem_setOf_eq, mem_cj]
  constructor
  · rintro ⟨u, hu, p, hp, rfl⟩
    exact ⟨u, hu, x * p * x⁻¹, by rwa [show x⁻¹ * (x * p * x⁻¹) * x = p by group], by group⟩
  · rintro ⟨u, hu, c, hc, h⟩
    refine ⟨u, hu, _, hc, ?_⟩
    calc g = g * x⁻¹ * x := by group
      _ = u * c * x := by rw [h]
      _ = u * x * (x⁻¹ * c * x) := by group

theorem ncos_left {N P : Subgroup G} {u g : G} (hu : u ∈ N) : u * g ∈ ncos N P ↔ g ∈ ncos N P := by
  constructor
  · rintro ⟨v, hv, c, hc, e⟩
    refine ⟨u⁻¹ * v, N.mul_mem (N.inv_mem hu) hv, c, hc, ?_⟩
    calc g = u⁻¹ * (u * g) := by group
      _ = u⁻¹ * (v * c) := by rw [e]
      _ = u⁻¹ * v * c := by group
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact ⟨u * v, N.mul_mem hu hv, c, hc, by group⟩

theorem ncos_right {N P : Subgroup G} {q g : G} (hq : q ∈ P) : g * q ∈ ncos N P ↔ g ∈ ncos N P := by
  constructor
  · rintro ⟨v, hv, c, hc, e⟩
    refine ⟨v, hv, c * q⁻¹, P.mul_mem hc (P.inv_mem hq), ?_⟩
    calc g = g * q * q⁻¹ := by group
      _ = v * c * q⁻¹ := by rw [e]
      _ = v * (c * q⁻¹) := by group
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact ⟨v, hv, c * q, P.mul_mem hc hq, by group⟩

theorem dcos_left {N P : Subgroup G} {x u g : G} (hu : u ∈ N) :
    u * g ∈ dcos N P x ↔ g ∈ dcos N P x := by
  constructor
  · rintro ⟨v, hv, p, hp, e⟩
    refine ⟨u⁻¹ * v, N.mul_mem (N.inv_mem hu) hv, p, hp, ?_⟩
    calc g = u⁻¹ * (u * g) := by group
      _ = u⁻¹ * (v * x * p) := by rw [e]
      _ = u⁻¹ * v * x * p := by group
  · rintro ⟨v, hv, p, hp, rfl⟩
    exact ⟨u * v, N.mul_mem hu hv, p, hp, by group⟩

theorem dcos_sub {N P : Subgroup G} {x y g : G} (hx : g ∈ dcos N P x) (hy : g ∈ dcos N P y) :
    dcos N P x ⊆ dcos N P y := by
  obtain ⟨u, hu, p, hp, e1⟩ := hx
  obtain ⟨v, hv, q, hq, e2⟩ := hy
  have hxe : x = u⁻¹ * v * y * q * p⁻¹ := by
    calc x = u⁻¹ * (u * x * p) * p⁻¹ := by group
      _ = u⁻¹ * (v * y * q) * p⁻¹ := by rw [← e1, e2]
      _ = u⁻¹ * v * y * q * p⁻¹ := by group
  rintro z ⟨w, hw, r, hr, rfl⟩
  refine ⟨w * u⁻¹ * v, N.mul_mem (N.mul_mem hw (N.inv_mem hu)) hv, q * p⁻¹ * r,
    P.mul_mem (P.mul_mem hq (P.inv_mem hp)) hr, ?_⟩
  rw [hxe]; group

theorem dedupe {α β : Type} [DecidableEq α] (D : α → β) (t₀ : Finset α) :
    ∃ t ⊆ t₀, (∀ x ∈ t₀, ∃ y ∈ t, D x = D y) ∧ ∀ x ∈ t, ∀ y ∈ t, D x = D y → x = y := by
  induction t₀ using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t, hts, hcov, hinj⟩ := ih
    by_cases hex : ∃ y ∈ t, D a = D y
    · refine ⟨t, hts.trans (Finset.subset_insert _ _), ?_, hinj⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hex
      · exact hcov x hx
    · push_neg at hex
      refine ⟨insert a t, Finset.insert_subset_insert _ hts, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨x, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨y, hy, e⟩ := hcov x hx
          exact ⟨y, Finset.mem_insert_of_mem hy, e⟩
      · intro x hx y hy e
        rcases Finset.mem_insert.mp hx with hx | hx <;> rcases Finset.mem_insert.mp hy with hy | hy
        · rw [hx, hy]
        · exact absurd (hx ▸ e) (hex y hy)
        · exact absurd (hy ▸ e).symm (hex x hx)
        · exact hinj x hx y hy e

theorem zero_fun_mem {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c) :
    (fun _ => (0 : ℂ)) ∈ T := by
  rw [hT]
  exact ⟨fun _ _ _ => rfl, IsLocallyConstant.const 0, ∅, isCompact_empty, Set.empty_subset _,
    fun g h => absurd rfl h⟩

theorem linear_combination_mem {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    {F F' : G → ℂ} (hF : F ∈ T) (hF' : F' ∈ T) (c c' : ℂ) :
    (fun g => c * F g + c' * F' g) ∈ T := by
  rw [hT] at hF hF' ⊢
  obtain ⟨hN, hL, C, hC, hCB, hs⟩ := hF
  obtain ⟨hN', hL', C', hC', hCB', hs'⟩ := hF'
  refine ⟨fun u hu g => by simp only [hN u hu, hN' u hu], hL.comp₂ hL' (fun a b => c * a + c' * b),
    C ∪ C', hC.union hC', Set.union_subset hCB hCB', fun g hg => ?_⟩
  by_cases h1 : F g = 0
  · have h2 : F' g ≠ 0 := by intro h2; apply hg; simp [h1, h2]
    obtain ⟨u, hu, c, hc, e⟩ := hs' g h2
    exact ⟨u, hu, c, Or.inr hc, e⟩
  · obtain ⟨u, hu, c, hc, e⟩ := hs g h1
    exact ⟨u, hu, c, Or.inl hc, e⟩

theorem right_translate_mem {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    {F : G → ℂ} (hF : F ∈ T) {x : G} (hx : x ∈ B) : (fun g => F (g * x)) ∈ T := by
  rw [hT] at hF ⊢
  obtain ⟨hN, hL, C, hC, hCB, hs⟩ := hF
  refine ⟨fun u hu g => by rw [mul_assoc]; exact hN u hu _, hL.comp_continuous (continuous_mul_right x),
    (fun c => c * x⁻¹) '' C, hC.image (continuous_mul_right _), ?_, fun g hg => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩; exact B.mul_mem (hCB hc) (B.inv_mem hx)
  · obtain ⟨u, hu, c, hc, e⟩ := hs _ hg
    refine ⟨u, hu, c * x⁻¹, ⟨c, hc, rfl⟩, ?_⟩
    calc g = g * x * x⁻¹ := by group
      _ = u * c * x⁻¹ := by rw [e]
      _ = u * (c * x⁻¹) := by group

theorem nonzero_coset_mem_compact {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {P : Subgroup G} (hPB : P ≤ B) (hPc : IsCompact (P : Set G))
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) :
    (ncos N P).indicator (fun _ => (1 : ℂ)) ∈ T := by
  rw [hT]
  refine ⟨fun u hu g => ?_, indicator_isLocallyConstant (h2 P hPB hPc hPo) 1, P, hPc,
    fun x hx => hPB hx, fun g hg => by have := Set.mem_of_indicator_ne_zero hg; exact this⟩
  have := ncos_left (P := P) (g := g) hu
  by_cases h : g ∈ ncos N P
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (this.mp h'))]

theorem indicator_dcos_mem {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {P : Subgroup G} (hPB : P ≤ B) (hPc : IsCompact (P : Set G))
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) {x : G} (hx : x ∈ B) :
    (dcos N P x).indicator (fun _ => (1 : ℂ)) ∈ T := by
  have := right_translate_mem hT
    (nonzero_coset_mem_compact hT h2 (cj_le hx hPB) (cj_compact x hPc) (cj_open hx hPo)) (B.inv_mem hx)
  convert this using 1
  funext g
  rw [dcos_eq]
  first | rfl | simp only [Set.indicator_apply, Set.mem_preimage]

theorem I_dcos {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {I : (G → ℂ) → ℂ} (hinv : ∀ F ∈ T, ∀ x ∈ B, I (fun g => F (g * x)) = I F)
    {P : Subgroup G} (hPB : P ≤ B) (hPc : IsCompact (P : Set G))
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) {x : G} (hx : x ∈ B) :
    I ((dcos N P x).indicator (fun _ => (1 : ℂ))) = I ((ncos N (cj x P)).indicator (fun _ => (1 : ℂ))) := by
  rw [← hinv _ (nonzero_coset_mem_compact hT h2 (cj_le hx hPB) (cj_compact x hPc) (cj_open hx hPo)) _ (B.inv_mem hx)]
  congr 1
  funext g
  rw [dcos_eq]
  first | rfl | simp only [Set.indicator_apply, Set.mem_preimage]

theorem I_sum {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    {I : (G → ℂ) → ℂ}
    (hlin : ∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F')
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → G → ℂ) (hf : ∀ i ∈ s, f i ∈ T) :
    (fun g => ∑ i ∈ s, c i * f i g) ∈ T ∧ I (fun g => ∑ i ∈ s, c i * f i g) = ∑ i ∈ s, c i * I (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz := zero_fun_mem hT
    have h0 := hlin _ hz _ hz 0 0
    simp only [zero_mul, add_zero] at h0
    simpa using ⟨hz, h0⟩
  | @insert a s ha ih =>
    obtain ⟨hm, hI⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    have e : (fun g => ∑ i ∈ insert a s, c i * f i g) =
        fun g => c a * f a g + 1 * (fun g => ∑ i ∈ s, c i * f i g) g := by
      funext g; rw [Finset.sum_insert ha, one_mul]
    rw [e, Finset.sum_insert ha]
    refine ⟨linear_combination_mem hT hfa hm _ _, ?_⟩
    rw [hlin _ hfa _ hm, hI, one_mul]

theorem decomp {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {I : (G → ℂ) → ℂ}
    (hlin : ∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F')
    {P : Subgroup G} (hPB : P ≤ B) (hPc : IsCompact (P : Set G))
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) {F : G → ℂ} (hF : F ∈ T)
    (hFP : ∀ g, ∀ p ∈ P, F (g * p) = F g) {C : Set G} (hC : IsCompact C) (hCB : C ⊆ B)
    (hs : ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c) :
    ∃ t : Finset G, (∀ x ∈ t, x ∈ C) ∧ (∀ c ∈ C, ∃ x ∈ t, c ∈ dcos N P x) ∧
      I F = ∑ x ∈ t, F x * I ((dcos N P x).indicator fun _ => (1 : ℂ)) := by
  classical
  have hFN := ((hT F).mp hF).1
  obtain ⟨V, hV, hVP⟩ := nhds_of_relOpen hPo
  obtain ⟨t₀, ht₀C, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' V)
    (fun x _ => by
      apply (continuous_mul_left x⁻¹).continuousAt.preimage_mem_nhds
      simpa using hV)
  have hcov' : ∀ c ∈ C, ∃ x ∈ t₀, c ∈ dcos N P x := by
    intro c hc
    have := hcov hc
    simp only [Set.mem_iUnion, Set.mem_preimage] at this
    obtain ⟨x, hx, hxV⟩ := this
    have hxB : x ∈ B := hCB (ht₀C x hx)
    have hp : x⁻¹ * c ∈ P := hVP _ (B.mul_mem (B.inv_mem hxB) (hCB hc)) hxV
    exact ⟨x, hx, 1, N.one_mem, x⁻¹ * c, hp, by group⟩
  obtain ⟨t, htt, htcov, hinj⟩ := dedupe (dcos N P) t₀
  have htC : ∀ x ∈ t, x ∈ C := fun x hx => ht₀C x (htt hx)
  have hcovt : ∀ c ∈ C, ∃ x ∈ t, c ∈ dcos N P x := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hcov' c hc
    obtain ⟨y, hy, e⟩ := htcov x hx
    exact ⟨y, hy, e ▸ hcx⟩
  have hval : ∀ x, ∀ g ∈ dcos N P x, F g = F x := by
    rintro x g ⟨u, hu, p, hp, rfl⟩
    rw [mul_assoc, hFN u hu, hFP x p hp]
  have hdec : F = fun g => ∑ x ∈ t, F x * (dcos N P x).indicator (fun _ => (1 : ℂ)) g := by
    funext g
    by_cases hg : ∃ x ∈ t, g ∈ dcos N P x
    · obtain ⟨x, hx, hgx⟩ := hg
      rw [Finset.sum_eq_single x]
      · rw [Set.indicator_of_mem hgx, mul_one, hval x g hgx]
      · intro y hy hyx
        have : g ∉ dcos N P y := by
          intro hgy
          exact hyx (hinj y hy x hx (Set.Subset.antisymm (dcos_sub hgy hgx) (dcos_sub hgx hgy)))
        rw [Set.indicator_of_notMem this, mul_zero]
      · intro h; exact absurd hx h
    · push_neg at hg
      have hF0 : F g = 0 := by
        by_contra h
        obtain ⟨u, hu, c, hc, rfl⟩ := hs g h
        obtain ⟨x, hx, hcx⟩ := hcovt c hc
        exact hg x hx ((dcos_left hu).mpr hcx)
      rw [hF0]
      exact (Finset.sum_eq_zero fun x hx => by rw [Set.indicator_of_notMem (hg x hx), mul_zero]).symm
  refine ⟨t, htC, hcovt, ?_⟩
  have := (I_sum hT hlin t (fun x => F x) (fun x => (dcos N P x).indicator fun _ => (1 : ℂ))
    (fun x hx => indicator_dcos_mem hT h2 hPB hPc hPo (hCB (htC x hx)))).2
  conv_lhs => rw [hdec]
  exact this

theorem mult {N B : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {I : (G → ℂ) → ℂ}
    (hlin : ∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F')
    (hinv : ∀ F ∈ T, ∀ x ∈ B, I (fun g => F (g * x)) = I F)
    {P Q : Subgroup G} (hPQ : P ≤ Q) (hQB : Q ≤ B) (hPc : IsCompact (P : Set G))
    (hPo : IsOpen ((Subtype.val : B → G) ⁻¹' P)) (hQc : IsCompact (Q : Set G))
    (hQo : IsOpen ((Subtype.val : B → G) ⁻¹' Q))
    (hnorm : ∀ x ∈ Q, ∀ y ∈ P, x * y * x⁻¹ ∈ P) :
    I ((ncos N Q).indicator fun _ => (1 : ℂ)) = 0 ↔ I ((ncos N P).indicator fun _ => (1 : ℂ)) = 0 := by
  have hPB := hPQ.trans hQB
  have hF := nonzero_coset_mem_compact hT h2 hQB hQc hQo
  have hFP : ∀ g, ∀ p ∈ P, (ncos N Q).indicator (fun _ => (1 : ℂ)) (g * p) =
      (ncos N Q).indicator (fun _ => (1 : ℂ)) g := by
    intro g p hp
    have := ncos_right (N := N) (g := g) (hPQ hp)
    by_cases h : g ∈ ncos N Q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (this.mp h'))]
  obtain ⟨t, htQ, hcov, hI⟩ := decomp hT h2 hlin hPB hPc hPo hF hFP hQc (fun x hx => hQB hx)
    (fun g hg => by have := Set.mem_of_indicator_ne_zero hg; exact this)
  have hterm : ∀ x ∈ t, (ncos N Q).indicator (fun _ => (1 : ℂ)) x *
      I ((dcos N P x).indicator fun _ => (1 : ℂ)) = I ((ncos N P).indicator fun _ => (1 : ℂ)) := by
    intro x hx
    have hxQ : x ∈ Q := htQ x hx
    have hS : ncos N (cj x P) = ncos N P := by
      ext g
      simp only [ncos, Set.mem_setOf_eq, mem_cj]
      constructor
      · rintro ⟨u, hu, c, hc, rfl⟩
        refine ⟨u, hu, c, ?_, rfl⟩
        have := hnorm x hxQ _ hc
        rwa [show x * (x⁻¹ * c * x) * x⁻¹ = c by group] at this
      · rintro ⟨u, hu, c, hc, rfl⟩
        refine ⟨u, hu, c, ?_, rfl⟩
        have := hnorm x⁻¹ (Q.inv_mem hxQ) c hc
        rwa [inv_inv] at this
    rw [Set.indicator_of_mem (show x ∈ ncos N Q from ⟨1, N.one_mem, x, hxQ, by group⟩), one_mul,
      I_dcos hT h2 hinv hPB hPc hPo (hQB hxQ), hS]
  rw [hI, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hne : (t.card : ℂ) ≠ 0 := by
    obtain ⟨x, hx, _⟩ := hcov 1 Q.one_mem
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hx)
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hne, fun h => by rw [h, mul_zero]⟩

theorem unif_inv {F : G → ℂ} (hL : IsLocallyConstant F) {C : Set G} (hC : IsCompact C) :
    ∃ U ∈ nhds (1 : G), ∀ c ∈ C, ∀ k ∈ U, F (c * k) = F c := by
  classical
  have hW : ∀ c : G, ∃ W ∈ nhds (1 : G), ∀ v ∈ W, ∀ w ∈ W, F (c * (v * w)) = F c := by
    intro c
    have : (fun k => c * k) ⁻¹' {y | F y = F c} ∈ nhds (1 : G) := by
      apply (continuous_mul_left c).continuousAt.preimage_mem_nhds
      show _ ∈ nhds (c * 1)
      rw [mul_one]
      exact (hL.isOpen_fiber (F c)).mem_nhds rfl
    obtain ⟨W, hW, hWW⟩ := exists_nhds_one_split this
    exact ⟨W, hW, fun v hv w hw => hWW v hv w hw⟩
  choose W hW hWW using hW
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover (fun c => (fun y => c⁻¹ * y) ⁻¹' W c)
    (fun c _ => by
      apply (continuous_mul_left c⁻¹).continuousAt.preimage_mem_nhds
      simpa using hW c)
  refine ⟨⋂ c ∈ t, W c, (Filter.biInter_finset_mem t).mpr fun c _ => hW c, ?_⟩
  intro c' hc' k hk
  have := hcov hc'
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨c, hct, hcW⟩ := this
  have hkW : k ∈ W c := Set.mem_iInter₂.mp hk c hct
  have e1 : F (c' * k) = F c := by
    have := hWW c _ hcW k hkW
    rwa [show c * (c⁻¹ * c' * k) = c' * k by group] at this
  have e2 : F c' = F c := by
    have := hWW c _ hcW 1 (mem_of_mem_nhds (hW c))
    rwa [show c * (c⁻¹ * c' * 1) = c' by group] at this
  rw [e1, e2]

theorem conj_zero {N B K₀ : Subgroup G} {T : Set (G → ℂ)}
    (hT : ∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧
      ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c)
    (h2 : ∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) →
      IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c})
    {I : (G → ℂ) → ℂ}
    (hlin : ∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F')
    (hinv : ∀ F ∈ T, ∀ x ∈ B, I (fun g => F (g * x)) = I F)
    (h3 : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, K ≤ K₀ ∧ IsCompact (K : Set G) ∧
      IsOpen ((Subtype.val : B → G) ⁻¹' K) ∧ (K : Set G) ⊆ U ∧ ∀ x ∈ K₀, ∀ y ∈ K, x * y * x⁻¹ ∈ K)
    (hK₀B : K₀ ≤ B) (hK₀c : IsCompact (K₀ : Set G)) (hK₀o : IsOpen ((Subtype.val : B → G) ⁻¹' K₀))
    (h0 : I ((ncos N K₀).indicator fun _ => (1 : ℂ)) = 0)
    {K : Subgroup G} (hKK₀ : K ≤ K₀) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen ((Subtype.val : B → G) ⁻¹' K)) {c : G} (hc : c ∈ B) :
    I ((ncos N (cj c K)).indicator fun _ => (1 : ℂ)) = 0 := by
  have hKB := hKK₀.trans hK₀B
  obtain ⟨V₁, hV₁, hV₁K⟩ := nhds_of_relOpen hKo
  obtain ⟨V₂, hV₂, hV₂K⟩ := nhds_of_relOpen (cj_open (B.inv_mem hc) hKo)
  obtain ⟨K₁, hK₁K₀, hK₁c, hK₁o, hK₁U, hK₁n⟩ := h3 _ (Filter.inter_mem hV₁ hV₂)
  have hK₁B := hK₁K₀.trans hK₀B
  have hK₁K : K₁ ≤ K := fun y hy => hV₁K y (hK₁B hy) (hK₁U hy).1
  have hK₁K' : ∀ y ∈ K₁, c * y * c⁻¹ ∈ K := fun y hy => by
    have := hV₂K y (hK₁B hy) (hK₁U hy).2
    rwa [mem_cj, inv_inv] at this
  have hL₁L : cj c K₁ ≤ cj c K := fun y hy => by
    rw [mem_cj] at hy ⊢; exact hK₁K hy
  have hL₁K : cj c K₁ ≤ K := fun y hy => by
    rw [mem_cj] at hy
    have := hK₁K' _ hy
    rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at this
  have hL₁n : ∀ x ∈ cj c K, ∀ y ∈ cj c K₁, x * y * x⁻¹ ∈ cj c K₁ := by
    intro x hx y hy
    rw [mem_cj] at hx hy ⊢
    have := hK₁n _ (hKK₀ hx) _ hy
    rwa [show c⁻¹ * x * c * (c⁻¹ * y * c) * (c⁻¹ * x * c)⁻¹ = c⁻¹ * (x * y * x⁻¹) * c by group] at this
  obtain ⟨V₃, hV₃, hV₃L⟩ := nhds_of_relOpen (cj_open hc hK₁o)
  obtain ⟨K₂, hK₂K₀, hK₂c, hK₂o, hK₂U, hK₂n⟩ := h3 _ hV₃
  have hK₂B := hK₂K₀.trans hK₀B
  have hK₂L₁ : K₂ ≤ cj c K₁ := fun y hy => hV₃L y (hK₂B hy) (hK₂U hy)
  have e1 := (mult hT h2 hlin hinv hK₂K₀ hK₀B hK₂c hK₂o hK₀c hK₀o hK₂n).mp h0
  have e2 := (mult hT h2 hlin hinv hK₂L₁ (cj_le hc hK₁B) hK₂c hK₂o (cj_compact c hK₁c)
    (cj_open hc hK₁o) (fun x hx y hy => hK₂n x (hKK₀ (hL₁K hx)) y hy)).mpr e1
  exact (mult hT h2 hlin hinv hL₁L (cj_le hc hKB) (cj_compact c hK₁c) (cj_open hc hK₁o)
    (cj_compact c hKc) (cj_open hc hKo) hL₁n).mpr e2

end

theorem invariant_functional_eq_zero :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (N B K₀ : Subgroup G) (T : Set (G → ℂ)), (∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧ ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c) → (∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) → IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c}) → (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, K ≤ K₀ ∧ IsCompact (K : Set G) ∧ IsOpen ((Subtype.val : B → G) ⁻¹' K) ∧ (K : Set G) ⊆ U ∧ ∀ x ∈ K₀, ∀ y ∈ K, x * y * x⁻¹ ∈ K) → K₀ ≤ B → IsCompact (K₀ : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K₀) → ∀ I : (G → ℂ) → ℂ, (∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F') → (∀ F ∈ T, ∀ x ∈ B, I (fun g => F (g * x)) = I F) → I (Set.indicator {g : G | ∃ u ∈ N, ∃ c ∈ K₀, g = u * c} fun _ => (1 : ℂ)) = 0 → ∀ F ∈ T, I F = 0 := by
  intro G _ _ _ _ N B K₀ T hT h2 h3 hK₀B hK₀c hK₀o I hlin hinv h0 F hF
  obtain ⟨hFN, hFL, C, hCc, hCB, hs⟩ := (hT F).mp hF
  obtain ⟨U, hU, hUF⟩ := unif_inv hFL hCc
  obtain ⟨K, hKK₀, hKc, hKo, hKU, -⟩ := h3 U hU
  have hKB := hKK₀.trans hK₀B
  have hFK : ∀ g, ∀ k ∈ K, F (g * k) = F g := by
    intro g k hk
    by_cases hg : F g ≠ 0
    · obtain ⟨u, hu, c, hc, rfl⟩ := hs g hg
      rw [mul_assoc, hFN u hu, hFN u hu, hUF c hc k (hKU hk)]
    · by_cases hgk : F (g * k) = 0
      · push_neg at hg; rw [hgk, hg]
      · obtain ⟨u, hu, c, hc, e⟩ := hs _ hgk
        have hge : g = u * (c * k⁻¹) := by
          calc g = g * k * k⁻¹ := by group
            _ = u * c * k⁻¹ := by rw [e]
            _ = u * (c * k⁻¹) := by group
        have h1 : F g = F c := by
          rw [hge, hFN u hu, hUF c hc k⁻¹ (hKU (K.inv_mem hk))]
        rw [e, hFN u hu, h1]
  obtain ⟨t, htC, -, hI⟩ := decomp hT h2 hlin hKB hKc hKo hF hFK hCc hCB hs
  rw [hI]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [I_dcos hT h2 hinv hKB hKc hKo (hCB (htC x hx)),
    conj_zero hT h2 hlin hinv h3 hK₀B hK₀c hK₀o h0 hKK₀ hKc hKo (hCB (htC x hx)), mul_zero]

end GlobalTheory.GamMul.Uniq
