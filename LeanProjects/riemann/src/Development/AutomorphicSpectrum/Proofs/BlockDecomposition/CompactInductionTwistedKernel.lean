import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport

open GlobalTheory.PRep Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.CIndKer

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem exists_cut (H : Subgroup G)
    (hbasis : ∀ O : Set G, O ∈ 𝓝 (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (σ : Representation ℂ H W) (S : Set G) (hl : ∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S)
    (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G)) (hr : ∀ k ∈ K₀, ∀ g, g * k ∈ S ↔ g ∈ S)
    (v : cIndSpace H σ) : ∃ w : cIndSpace H σ, ∀ g, w.1.1.1 g = S.indicator v.1.1.1 g := by
  classical
  have hvo : IsOpen {g : G | ind H σ g v.1.1 = v.1.1} := v.1.2
  obtain ⟨K₁, hK₁o, -, hK₁⟩ := hbasis _ (hvo.mem_nhds (by simp))
  have hinv : ∀ g, ∀ x ∈ K₁, v.1.1.1 (g * x) = v.1.1.1 g := by
    intro g x hx
    have h : ind H σ x v.1.1 = v.1.1 := hK₁ hx
    exact congrArg (fun u : indSpace H σ => u.1 g) h
  have hind : S.indicator v.1.1.1 ∈ indSpace H σ := by
    intro h g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hl h h.2 g).2 hg), Set.indicator_of_mem hg]
      exact v.1.1.2 h g
    · rw [Set.indicator_of_notMem (fun h' => hg ((hl h h.2 g).1 h')), Set.indicator_of_notMem hg,
        map_zero]
  have hsm : (⟨S.indicator v.1.1.1, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ) (K₀ ⊓ K₁)
      (by rw [Subgroup.coe_inf]; exact hK₀.inter hK₁o) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show S.indicator v.1.1.1 (g * x) = S.indicator v.1.1.1 g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hr x hx.1 g).2 hg), Set.indicator_of_mem hg, hinv g x hx.2]
    · rw [Set.indicator_of_notMem (fun h' => hg ((hr x hx.1 g).1 h')), Set.indicator_of_notMem hg]
  obtain ⟨C, hC, hsupp⟩ := v.2
  refine ⟨⟨⟨⟨S.indicator v.1.1.1, hind⟩, hsm⟩, C, hC, fun g hg => hsupp g fun h0 => hg ?_⟩,
    fun g => rfl⟩
  show S.indicator v.1.1.1 g = 0
  by_cases hgS : g ∈ S
  · rw [Set.indicator_of_mem hgS, h0]
  · rw [Set.indicator_of_notMem hgS]

theorem cut_mem (H U : Subgroup G)
    (hbasis : ∀ O : Set G, O ∈ 𝓝 (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (σ : Representation ℂ H W) (S : Set G) (hl : ∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S)
    (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G)) (hr : ∀ k ∈ K₀, ∀ g, g * k ∈ S ↔ g ∈ S)
    (hu : ∀ u ∈ U, ∀ g, g * u ∈ S ↔ g ∈ S) (y : cIndSpace H σ)
    (hy : y ∈ twKer (cInd H σ) U 1) :
    ∃ z ∈ twKer (cInd H σ) U 1, ∀ g, z.1.1.1 g = S.indicator y.1.1.1 g := by
  classical
  unfold twKer at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, v, rfl⟩ := hy
    obtain ⟨w, hw⟩ := exists_cut H hbasis σ S hl K₀ hK₀ hr v
    refine ⟨cInd H σ (n : G) w - w, Submodule.subset_span ⟨n, w, by simp⟩, fun g => ?_⟩
    have e1 : (cInd H σ (n : G) w - w).1.1.1 g = w.1.1.1 (g * n) - w.1.1.1 g := rfl
    have e2 : (cInd H σ (n : G) v - (((1 : U →* ℂˣ) n : ℂˣ) : ℂ) • v).1.1.1
        = fun x => v.1.1.1 (x * n) - v.1.1.1 x := by
      funext x
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rfl
    rw [e1, e2, hw, hw]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hu n n.2 g).2 hg), Set.indicator_of_mem hg,
        Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem (fun h' => hg ((hu n n.2 g).1 h')), Set.indicator_of_notMem hg,
        Set.indicator_of_notMem hg, sub_zero]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun g => ?_⟩
    show (0 : W) = S.indicator (fun _ => (0 : W)) g
    simp
  | add a b _ _ ha hb =>
    obtain ⟨z₁, h₁, e₁⟩ := ha
    obtain ⟨z₂, h₂, e₂⟩ := hb
    refine ⟨z₁ + z₂, Submodule.add_mem _ h₁ h₂, fun g => ?_⟩
    have e : (z₁ + z₂).1.1.1 g = z₁.1.1.1 g + z₂.1.1.1 g := rfl
    have e' : (a + b).1.1.1 = a.1.1.1 + b.1.1.1 := rfl
    rw [e, e₁, e₂, e']
    by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hg, add_zero]
  | smul t a _ ha =>
    obtain ⟨z, h, e⟩ := ha
    refine ⟨t • z, Submodule.smul_mem _ _ h, fun g => ?_⟩
    have e1 : (t • z).1.1.1 g = t • z.1.1.1 g := rfl
    have e' : (t • a).1.1.1 = t • a.1.1.1 := rfl
    rw [e1, e, e']
    by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hg, smul_zero]

def dc (H K : Subgroup G) (c : G) : Set G := {g | ∃ b : H, ∃ k ∈ K, g = (b : G) * c * k}

theorem dc_left (H K : Subgroup G) (c : G) : ∀ h ∈ H, ∀ g, h * g ∈ dc H K c ↔ g ∈ dc H K c := by
  intro h hh g
  constructor
  · rintro ⟨b, k, hk, e⟩
    refine ⟨⟨h, hh⟩⁻¹ * b, k, hk, ?_⟩
    have : g = h⁻¹ * (h * g) := by group
    rw [this, e]
    push_cast
    group
  · rintro ⟨b, k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * b, k, hk, by push_cast; group⟩

theorem dc_right (H K : Subgroup G) (c : G) : ∀ x ∈ K, ∀ g, g * x ∈ dc H K c ↔ g ∈ dc H K c := by
  intro x hx g
  constructor
  · rintro ⟨b, k, hk, e⟩
    refine ⟨b, k * x⁻¹, mul_mem hk (inv_mem hx), ?_⟩
    have : g = (g * x) * x⁻¹ := by group
    rw [this, e]
    group
  · rintro ⟨b, k, hk, rfl⟩
    exact ⟨b, k * x, mul_mem hk hx, by group⟩

theorem dc_unip (H U K : Subgroup G) [U.Normal] (hUH : U ≤ H) (c : G) :
    ∀ u ∈ U, ∀ g, g * u ∈ dc H K c ↔ g ∈ dc H K c := by
  have key : ∀ u ∈ U, ∀ g, g ∈ dc H K c → g * u ∈ dc H K c := by
    rintro u hu g ⟨b, k, hk, rfl⟩
    have hw : (c * k) * u * (c * k)⁻¹ ∈ U := ‹U.Normal›.conj_mem u hu _
    refine ⟨b * ⟨_, hUH hw⟩, k, hk, ?_⟩
    push_cast
    group
  intro u hu g
  refine ⟨fun h => ?_, key u hu g⟩
  have := key u⁻¹ (inv_mem hu) _ h
  simpa using this

theorem local_gen (H U : Subgroup G) [U.Normal] (hUH : U ≤ H) (σ : Representation ℂ H W)
    (hσ : IsSmooth σ) (c : G) (n : H) (hn : (n : G) ∈ U) (a : W) :
    ∃ O ∈ 𝓝 (1 : G), ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      (K : Set G) ⊆ O → ∃ y ∈ twKer (cInd H σ) U 1,
        (∀ (b : H), ∀ k ∈ K, y.1.1.1 ((b : G) * c * k) = σ b (σ n a - a)) ∧
        ∀ g, g ∉ dc H K c → y.1.1.1 g = 0 := by
  obtain ⟨O₁, hO₁, e⟩ := isOpen_induced_iff.1 (hσ a)
  have fix : ∀ h : H, (h : G) ∈ O₁ → σ h a = a := fun h hh => by
    have h' : h ∈ (Subtype.val ⁻¹' O₁ : Set H) := hh
    rw [e] at h'
    exact h'
  have h1 : (1 : G) ∈ O₁ := by
    have h' : (1 : H) ∈ (Subtype.val ⁻¹' O₁ : Set H) := by
      rw [e]
      simp
    exact h'
  have hc1 : Continuous fun k : G => c * k * c⁻¹ := by fun_prop
  have hc2 : Continuous fun k : G => (n : G)⁻¹ * (c * k * c⁻¹) * n * (c * k * c⁻¹)⁻¹ := by fun_prop
  have m1 : (fun k : G => c * k * c⁻¹) ⁻¹' O₁ ∈ 𝓝 (1 : G) :=
    (hO₁.preimage hc1).mem_nhds (by simpa using h1)
  have m2 : (fun k : G => (n : G)⁻¹ * (c * k * c⁻¹) * n * (c * k * c⁻¹)⁻¹) ⁻¹' O₁ ∈ 𝓝 (1 : G) :=
    (hO₁.preimage hc2).mem_nhds (by simpa using h1)
  refine ⟨_, Filter.inter_mem m1 m2, fun K hKo hKc hKO => ?_⟩
  obtain ⟨B, hB1, hB0⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc c a
    (fun b x hx hb => fix b (by rw [hb]; exact (hKO hx).1))
  have hu : c⁻¹ * (n : G) * c⁻¹⁻¹ ∈ U := ‹U.Normal›.conj_mem _ hn _
  have hu' : c⁻¹ * (n : G) * c ∈ U := by simpa using hu
  refine ⟨cInd H σ (c⁻¹ * (n : G) * c) B - B,
    Submodule.subset_span ⟨⟨_, hu'⟩, B, by simp⟩, fun b k hk => ?_, fun g hg => ?_⟩
  · have e1 : (cInd H σ (c⁻¹ * (n : G) * c) B - B).1.1.1 ((b : G) * c * k)
        = B.1.1.1 ((b : G) * c * k * (c⁻¹ * (n : G) * c)) - B.1.1.1 ((b : G) * c * k) := rfl
    set κ : G := c * k * c⁻¹ with hκ
    have hm : κ * (n : G) * κ⁻¹ ∈ U := ‹U.Normal›.conj_mem _ hn _
    have ht : (n : G)⁻¹ * κ * n * κ⁻¹ ∈ U := by
      have := mul_mem (inv_mem hn) hm
      simpa [mul_assoc] using this
    let m : H := ⟨_, hUH hm⟩
    let t : H := ⟨_, hUH ht⟩
    have hmt : m = n * t := by
      apply Subtype.ext
      show κ * (n : G) * κ⁻¹ = n * ((n : G)⁻¹ * κ * n * κ⁻¹)
      group
    have hfix : σ t a = a := fix t (hKO hk).2
    have e2 : (b : G) * c * k * (c⁻¹ * (n : G) * c) = ((b * m : H) : G) * c * k := by
      show (b : G) * c * k * (c⁻¹ * (n : G) * c) = (b : G) * (κ * (n : G) * κ⁻¹) * c * k
      rw [hκ]
      group
    rw [e1, e2, hB1 _ _ hk, hB1 _ _ hk, hmt, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, hfix, map_sub]
  · have e1 : (cInd H σ (c⁻¹ * (n : G) * c) B - B).1.1.1 g
        = B.1.1.1 (g * (c⁻¹ * (n : G) * c)) - B.1.1.1 g := rfl
    rw [e1, hB0 _ (fun h => hg ?_), hB0 _ hg, sub_zero]
    exact (dc_unip H U K hUH c _ hu' g).1 h

theorem local_all (H U : Subgroup G) [U.Normal] (hUH : U ≤ H) (σ : Representation ℂ H W)
    (hσ : IsSmooth σ) (c : G) (x : W) (hx : x ∈ twKer σ (U.subgroupOf H) 1) :
    ∃ O ∈ 𝓝 (1 : G), ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      (K : Set G) ⊆ O → ∃ y ∈ twKer (cInd H σ) U 1,
        (∀ (b : H), ∀ k ∈ K, y.1.1.1 ((b : G) * c * k) = σ b x) ∧
        ∀ g, g ∉ dc H K c → y.1.1.1 g = 0 := by
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, v, rfl⟩ := hx
    have := local_gen H U hUH σ hσ c n.1 (Subgroup.mem_subgroupOf.1 n.2) v
    simpa using this
  | zero =>
    exact ⟨Set.univ, Filter.univ_mem, fun K _ _ _ => ⟨0, Submodule.zero_mem _,
      fun b k _ => by rw [map_zero]; rfl, fun g _ => rfl⟩⟩
  | add p q _ _ hp hq =>
    obtain ⟨O₁, h₁, P₁⟩ := hp
    obtain ⟨O₂, h₂, P₂⟩ := hq
    refine ⟨O₁ ∩ O₂, Filter.inter_mem h₁ h₂, fun K hKo hKc hKO => ?_⟩
    obtain ⟨y₁, m₁, a₁, b₁⟩ := P₁ K hKo hKc (hKO.trans Set.inter_subset_left)
    obtain ⟨y₂, m₂, a₂, b₂⟩ := P₂ K hKo hKc (hKO.trans Set.inter_subset_right)
    refine ⟨y₁ + y₂, Submodule.add_mem _ m₁ m₂, fun b k hk => ?_, fun g hg => ?_⟩
    · have e : (y₁ + y₂).1.1.1 ((b : G) * c * k)
          = y₁.1.1.1 ((b : G) * c * k) + y₂.1.1.1 ((b : G) * c * k) := rfl
      rw [e, a₁ b k hk, a₂ b k hk, map_add]
    · have e : (y₁ + y₂).1.1.1 g = y₁.1.1.1 g + y₂.1.1.1 g := rfl
      rw [e, b₁ g hg, b₂ g hg, add_zero]
  | smul t p _ hp =>
    obtain ⟨O, h, P⟩ := hp
    refine ⟨O, h, fun K hKo hKc hKO => ?_⟩
    obtain ⟨y, m, a, b⟩ := P K hKo hKc hKO
    refine ⟨t • y, Submodule.smul_mem _ _ m, fun b' k hk => ?_, fun g hg => ?_⟩
    · have e : (t • y).1.1.1 ((b' : G) * c * k) = t • y.1.1.1 ((b' : G) * c * k) := rfl
      rw [e, a b' k hk, map_smul]
    · have e : (t • y).1.1.1 g = t • y.1.1.1 g := rfl
      rw [e, b g hg, smul_zero]

theorem mem_twKer_cInd : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H U : Subgroup G) [U.Normal], U ≤ H →
    (∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (σ : Representation ℂ H W), IsSmooth σ → ∀ f : cIndSpace H σ,
      (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1 := by
  intro G W _ _ _ _ _ H U _ hUH hbasis σ hσ f hf
  classical
  have hfo : IsOpen {g : G | ind H σ g f.1.1 = f.1.1} := f.1.2
  have hloc : ∀ c : G, ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      ∃ y ∈ twKer (cInd H σ) U 1, ∀ g, y.1.1.1 g = (dc H K c).indicator f.1.1.1 g := by
    intro c
    obtain ⟨O, hO, P⟩ := local_all H U hUH σ hσ c _ (hf c)
    obtain ⟨K, hKo, hKc, hKO⟩ := hbasis _ (Filter.inter_mem hO (hfo.mem_nhds (by simp)))
    obtain ⟨y, hy, h1, h0⟩ := P K hKo hKc (hKO.trans Set.inter_subset_left)
    refine ⟨K, hKo, y, hy, fun g => ?_⟩
    by_cases hg : g ∈ dc H K c
    · rw [Set.indicator_of_mem hg]
      obtain ⟨b, k, hk, rfl⟩ := hg
      have hfix : ind H σ k f.1.1 = f.1.1 := (hKO hk).2
      have e : f.1.1.1 (c * k) = f.1.1.1 c := congrArg (fun v : indSpace H σ => v.1 c) hfix
      rw [h1 b k hk, mul_assoc, f.1.1.2 b, e]
    · rw [Set.indicator_of_notMem hg, h0 g hg]
  choose K hKo y hyY hy using hloc
  have key : ∀ t : Finset G, ∃ S : Set G, (∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S) ∧
      (∀ u ∈ U, ∀ g, g * u ∈ S ↔ g ∈ S) ∧
      (∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ ∀ k ∈ K₀, ∀ g, g * k ∈ S ↔ g ∈ S) ∧
      (∀ c ∈ t, ∀ k ∈ K c, c * k ∈ S) ∧
      ∃ z ∈ twKer (cInd H σ) U 1, ∀ g, z.1.1.1 g = S.indicator f.1.1.1 g := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨∅, by simp, by simp, ⟨⊤, by simp, by simp⟩, by simp, 0, Submodule.zero_mem _,
        fun g => by simp⟩
    | insert c t _ ih =>
      obtain ⟨S, hl, hu, ⟨K₀, hK₀, hr⟩, hcov, z, hz, ez⟩ := ih
      obtain ⟨z', hz', ez'⟩ := cut_mem H U hbasis σ S hl K₀ hK₀ hr hu (y c) (hyY c)
      refine ⟨S ∪ dc H (K c) c, fun h hh g => ?_, fun u hu' g => ?_,
        ⟨K₀ ⊓ K c, by rw [Subgroup.coe_inf]; exact hK₀.inter (hKo c), fun k hk g => ?_⟩,
        fun c' hc' k hk => ?_, z + y c - z',
        Submodule.sub_mem _ (Submodule.add_mem _ hz (hyY c)) hz', fun g => ?_⟩
      · simp only [Set.mem_union, hl h hh g, dc_left H (K c) c h hh g]
      · simp only [Set.mem_union, hu u hu' g, dc_unip H U (K c) hUH c u hu' g]
      · simp only [Set.mem_union, hr k hk.1 g, dc_right H (K c) c k hk.2 g]
      · rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact Or.inr ⟨1, k, hk, by simp⟩
        · exact Or.inl (hcov c' hc' k hk)
      · have e : (z + y c - z').1.1.1 g = z.1.1.1 g + (y c).1.1.1 g - z'.1.1.1 g := rfl
        have hyc : (y c).1.1.1 = (dc H (K c) c).indicator f.1.1.1 := funext (hy c)
        rw [e, ez, ez', hyc]
        by_cases h1 : g ∈ S <;> by_cases h2 : g ∈ dc H (K c) c <;>
          simp [Set.indicator, h1, h2]
  obtain ⟨C, hC, hsupp⟩ := f.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K c : Set G))
    (fun c _ => by
      have : (fun x => c⁻¹ * x) ⁻¹' (K c : Set G) ∈ 𝓝 c :=
        ((hKo c).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
      filter_upwards [this] with x hx
      exact ⟨c⁻¹ * x, hx, by group⟩)
  obtain ⟨S, hl, -, -, hcov, z, hz, ez⟩ := key t
  have hfz : f = z := by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    show f.1.1.1 g = z.1.1.1 g
    rw [ez]
    by_cases h0 : f.1.1.1 g = 0
    · rw [h0]
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, h0]
      · rw [Set.indicator_of_notMem hg]
    · obtain ⟨a, ha, c', hc', e⟩ := hsupp g h0
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      have hg : g ∈ S := by
        rw [e]
        exact (hl a ha _).2 (hcov c hc x hx)
      rw [Set.indicator_of_mem hg]
  rw [hfz]
  exact hz

end GlobalTheory.CompanionTheory.PRep.CIndKer
