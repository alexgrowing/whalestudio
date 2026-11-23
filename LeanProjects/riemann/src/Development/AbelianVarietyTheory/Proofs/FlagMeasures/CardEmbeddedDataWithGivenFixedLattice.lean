import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.DatCount

section General

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem exists_fun_span (t : Finset V) {e : ℕ} (hc : t.card ≤ e) :
    ∃ g : Fin e → V, Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
  obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  refine ⟨Function.extend emb (fun x => (x : V)) 0, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : ∃ x, emb x = i
    · obtain ⟨x, rfl⟩ := hi
      simp only [emb.injective.extend_apply]
      exact Submodule.subset_span x.2
    · simp only [Function.extend_apply' _ _ _ hi]
      simp
  · intro x hx
    exact ⟨emb ⟨x, hx⟩, by simp only [emb.injective.extend_apply]⟩

theorem exists_gens_of_map [IsDedekindDomain R] (f : V →ₗ[R] W) (B : Submodule R V) (A : Submodule R W)
    (m : R) (hm : m ≠ 0) (T : Finset W) (hT : ∀ x ∈ T, m • x ∈ A)
    (hB : B.map f ≤ A ⊔ Submodule.span R (T : Set W)) :
    ∃ t : Finset V, t.card ≤ T.card ∧ B = (B ⊓ A.comap f) ⊔ Submodule.span R (t : Set V) := by
  obtain ⟨t', hc, ht'⟩ := GlobalTheory.Mass.LatticeGens.exists_gens_of_between A m hm T hT (A ⊔ B.map f) le_sup_left
    (sup_le le_sup_left hB)
  have h1 : ∀ w ∈ t', ∃ v ∈ B, w - f v ∈ A := by
    intro w hw
    have : w ∈ A ⊔ B.map f := by
      rw [ht']; exact Submodule.mem_sup_right (Submodule.subset_span hw)
    obtain ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨v, hv, by simpa using ha⟩
  choose! φ hφB hφA using h1
  have hsp : Submodule.span R ((t'.image φ : Finset V) : Set V) ≤ B := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact hφB w hw
  refine ⟨t'.image φ, Finset.card_image_le.trans hc, le_antisymm (fun v hv => ?_) (sup_le inf_le_left hsp)⟩
  have h2 : A ⊔ B.map f ≤ A ⊔ (Submodule.span R ((t'.image φ : Finset V) : Set V)).map f := by
    rw [ht']
    refine sup_le le_sup_left (Submodule.span_le.2 fun w hw => ?_)
    have e : w = (w - f (φ w)) + f (φ w) := by abel
    rw [e]
    exact Submodule.add_mem_sup (hφA w hw)
      (Submodule.mem_map_of_mem (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem φ hw))))
  obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, e⟩ :=
    Submodule.mem_sup.1 (h2 (Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)))
  have e' : v = (v - s) + s := by abel
  rw [e']
  refine Submodule.add_mem_sup ⟨B.sub_mem hv (hsp hs), ?_⟩ hs
  change f (v - s) ∈ A
  rw [map_sub, ← e]
  simpa using ha

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem GenBy.trans {A B C : Submodule (𝓞 K) V} {e e' : ℕ} (h1 : GenBy A B e) (h2 : GenBy B C e') :
    GenBy A C (e + e') := by
  obtain ⟨t, hc, rfl⟩ := h1
  obtain ⟨t', hc', rfl⟩ := h2
  refine ⟨t ∪ t', (Finset.card_union_le _ _).trans (by omega), ?_⟩
  rw [Finset.coe_union, Submodule.span_union, sup_assoc, sup_comm (Submodule.span _ (t' : Set V))]

theorem genBy_dual (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule (𝓞 K) V} {e : ℕ} (hg : GenBy Y X e)
    {m : ℕ} (hm : m ≠ 0) (hmY : ∀ y ∈ Y, (m : 𝓞 K) • y ∈ X) :
    GenBy (Formalism.HermitianLatticesTheory.dual h X) (Formalism.HermitianLatticesTheory.dual h Y) e := by
  obtain ⟨t, hc, hY⟩ := hg
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have htY : ∀ s : t, (s : V) ∈ Y := fun s => by
    rw [hY]; exact Submodule.mem_sup_right (Submodule.subset_span s.2)
  let f : V →ₗ[𝓞 K] (t → K) := LinearMap.pi fun s => (h (s : V)).restrictScalars (𝓞 K)
  let A : Submodule (𝓞 K) (t → K) := Submodule.pi Set.univ fun _ => 1
  let T : Finset (t → K) := Finset.univ.image fun s : t => Pi.single s (m : K)⁻¹
  have hsm : ∀ (c : 𝓞 K) (a : K), c • a = (c : K) * a := fun c a => Algebra.smul_def c a
  obtain ⟨t', hc', ht'⟩ := exists_gens_of_map f (Formalism.HermitianLatticesTheory.dual h X) A (m : 𝓞 K) (Nat.cast_ne_zero.2 hm) T
    (by
      intro x hx
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hx
      intro i _
      by_cases hi : i = s
      · subst hi
        refine Submodule.mem_one.2 ⟨1, ?_⟩
        simp [hsm, hmK]
      · simp [hi])
    (by
      rintro _ ⟨v, hv, rfl⟩
      refine Submodule.mem_sup_right ?_
      rw [← Finset.univ_sum_single (f v)]
      refine Submodule.sum_mem _ fun s _ => ?_
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).1 hv _ (hmY _ (htY s)))
      have e1 : (Pi.single s (f v s) : t → K) = c • (Pi.single s (m : K)⁻¹ : t → K) := by
        rw [← Pi.single_smul, hsm]
        congr 1
        have e2 : h ((m : 𝓞 K) • (s : V)) v = (m : K) * h s v := by
          rw [Nat.cast_smul_eq_nsmul, map_nsmul]; simp
        change h s v = algebraMap (𝓞 K) K c * _
        rw [hc, e2]; field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ s)))))
  refine ⟨t', hc'.trans (Finset.card_image_le.trans (by simpa using hc)), ?_⟩
  have : Formalism.HermitianLatticesTheory.dual h X ⊓ A.comap f = Formalism.HermitianLatticesTheory.dual h Y := by
    ext v
    constructor
    · rintro ⟨hv, hv'⟩
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      rw [hY] at hy
      obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      refine add_mem ((Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).1 hv a ha) ?_
      clear hy
      induction hs using Submodule.span_induction with
      | mem s hs => exact hv' ⟨s, hs⟩ trivial
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [Formalism.HermitianLatticesTheory.genusBasic_hsmul_left Formalism.HermitianLatticesTheory.genusCovol_hinj Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range]
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ ha
    · intro hv
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hv
      refine ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).2 fun y hy => hv y ?_, fun s _ => hv _ (htY s)⟩
      rw [hY]; exact Submodule.mem_sup_left hy
  rw [← this]
  exact ht'

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem flip_nondeg (H : HermSpace K V) : H.B.flip.Nondegenerate := by
  refine ⟨fun x hx => H.nondeg x fun y => ?_, fun x hx => H.nondeg x fun y => hx y⟩
  have : H.B y x = 0 := hx y
  rw [← H.herm, this, star_zero]

omit [NumberField K] [IsScalarTower (𝓞 K) K V] in
theorem fixLat_le {H : HermSpace K V} {g : 𝓞 K} {L' L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)}
    (hΓ : IsModIso H g L' L Γ) : fixLat Γ ≤ L' ∧ fixLat Γ ≤ L :=
  ⟨fun _ hx => (hΓ.1 hx).1, fun _ hx => (hΓ.1 hx).2⟩

theorem fixLat_isLattice {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hL' : Submodule.IsLattice K L') (hL : Submodule.IsLattice K L)
    (hΓ : IsModIso H g L' L Γ) : Submodule.IsLattice K (fixLat Γ) := by
  refine ⟨hL.fg.of_le (fixLat_le hΓ).2, ?_⟩
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro y hy
  have hn := GlobalTheory.Mass.DiscOrder.idxN_ne_zero hL' hL.fg
  set n : 𝓞 K := ((GlobalTheory.Mass.idxN L L' : ℕ) : 𝓞 K) with hn'
  have hn0 : n ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : n • y ∈ L' := GlobalTheory.Mass.LatticeGens.idxN_smul_mem L' L hy
  have h2 : (g * n) • y ∈ fixLat Γ := by
    rw [mul_smul]
    exact hΓ.2.1 ⟨⟨_, h1, rfl⟩, ⟨_, L.smul_mem n hy, rfl⟩⟩
  have h3 : algebraMap (𝓞 K) K (g * n) ≠ 0 := by simpa using ⟨hg, hn0⟩
  have h4 : y = (algebraMap (𝓞 K) K (g * n))⁻¹ • ((g * n) • y) := by
    rw [← algebraMap_smul K (g * n) y, smul_smul, inv_mul_cancel₀ h3, one_smul]
  rw [h4]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h2)

omit [NumberField K] in

theorem div_mem_dual {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hΓ : IsModIso H g L' L Γ) {s y : V} (h : (s, y) ∈ Γ) :
    (algebraMap (𝓞 K) K g)⁻¹ • (s - y) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip (fixLat Γ) := by
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro a ha
  obtain ⟨t, ht⟩ := hΓ.2.2.2.2.2.2 (s, y) h (a, a) ha
  have h3 : algebraMap (𝓞 K) K g ≠ 0 := by simpa using hg
  refine Submodule.mem_one.2 ⟨t, ?_⟩
  rw [map_smul, map_sub, smul_eq_mul]
  change _ = _ * (H.B s a - H.B y a)
  rw [ht, map_mul, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]

omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem graph_le {H : HermSpace K V} {g : 𝓞 K} {L' L : Submodule (𝓞 K) V}
    {Γ₁ Γ₂ : Submodule (𝓞 K) (V × V)} (h1 : IsModIso H g L' L Γ₁) (h2 : IsModIso H g L' L Γ₂)
    (hf : fixLat Γ₁ = fixLat Γ₂) {S : Set V} (hS : L' = fixLat Γ₁ ⊔ Submodule.span (𝓞 K) S)
    (hs : ∀ s ∈ S, ∃ y, (s, y) ∈ Γ₁ ∧ (s, y) ∈ Γ₂) : Γ₁ ≤ Γ₂ := by
  have key : L' ≤ (Γ₁ ⊓ Γ₂).map (LinearMap.fst (𝓞 K) V V) := by
    rw [hS]
    refine sup_le (fun a ha => ⟨(a, a), ⟨ha, ?_⟩, rfl⟩) (Submodule.span_le.2 fun s h => ?_)
    · have : a ∈ fixLat Γ₂ := hf ▸ ha
      exact this
    · obtain ⟨y, hy⟩ := hs s h
      exact ⟨(s, y), hy, rfl⟩
  rintro ⟨y', y⟩ hp
  obtain ⟨⟨a, z⟩, ⟨hz1, hz2⟩, rfl⟩ := key (h1.1 hp).1
  have e1 : ((0 : V), y - z) ∈ Γ₁ := by simpa using Γ₁.sub_mem hp hz1
  have e2 : ((0 : V), y - z) ∈ Γ₂ := h2.2.1 ⟨Submodule.zero_mem _, h1.2.2.2.2.1 _ e1⟩
  simpa using Γ₂.add_mem e2 hz2

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (La : Submodule (𝓞 K) V) (x : ℕ), ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) ≤ ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  intro K V _ _ _ _ _ _ _ _ H hK _ L₀ g j D₀ hL₀ hD hcyc hg La x
  set S := {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} with hSdef
  rcases S.eq_empty_or_nonempty with hS | ⟨d₀, hd₀, hd₀'⟩
  · rw [hS]; simp
  have hs := flip_isSymm H
  have hn := flip_nondeg H
  have hg0 : (g : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hgK : algebraMap (𝓞 K) K g ≠ 0 := by simpa using (by omega : g ≠ 0)
  obtain ⟨an, -, -, hint, -⟩ := Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V H.B.flip hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have hLa : Submodule.IsLattice K La := hd₀' ▸ fixLat_isLattice hg0 hd₀.1.1 hL₀.1 hd₀.2.2.1
  have hle : La ≤ L₀ := hd₀' ▸ (fixLat_le hd₀.2.2.1).2
  have hx : GlobalTheory.Mass.idxN L₀ La = x := hd₀' ▸ hd₀.2.2.2.1
  have hgen : GenBy L₀ La j := hd₀' ▸ hd₀.2.2.2.2
  have hx0 : x ≠ 0 := hx ▸ GlobalTheory.Mass.DiscOrder.idxN_ne_zero hLa hL₀.1.fg
  have hD0 : D₀ ≠ 0 := hD ▸ (GlobalTheory.Mass.DiscOrder.main K V H.B.flip hK hs hn L₀ hL₀).1
  have h0d := (hint L₀).1 hL₀.2
  have hdd := an _ _ hle
  set Ld := Formalism.HermitianLatticesTheory.dual H.B.flip La with hLd
  have i1 : GlobalTheory.Mass.idxN Ld L₀ = D₀ * x := by
    rw [← GlobalTheory.Mass.DiscOrder.idxN_mul h0d hdd, GlobalTheory.Mass.DiscOrder.idxN_dual _ hs hn hLa x L₀ hL₀.1 hle hx, ← hD]
    rfl
  have i2 : GlobalTheory.Mass.idxN Ld La = x * (D₀ * x) := by
    rw [← GlobalTheory.Mass.DiscOrder.idxN_mul hle (h0d.trans hdd), hx, i1]
  have g1 : GenBy Ld (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) j :=
    genBy_dual _ hgen hx0 fun y hy => hx ▸ GlobalTheory.Mass.LatticeGens.idxN_smul_mem La L₀ hy
  obtain ⟨t, htc, ht⟩ := GenBy.trans (GenBy.trans g1 hcyc) hgen
  obtain ⟨c1, c2⟩ := (GlobalTheory.Mass.LatticeGens.gens_and_count K V La Ld (hle.trans (h0d.trans hdd))
    (by rw [i2]; positivity)).2 (2 * j + 1) t (by omega) ht
  have c3 : ∀ L : Submodule (𝓞 K) V, La ≤ L ∧ L ≤ Ld → ∃ u : Fin (2 * j + 1) → V,
      L = La ⊔ Submodule.span (𝓞 K) (Set.range u) := by
    intro L hL
    obtain ⟨t', h1, h2⟩ := c2 L hL.1 hL.2
    obtain ⟨u, hu⟩ := exists_fun_span (R := 𝓞 K) t' h1
    exact ⟨u, by rw [hu]; exact h2⟩
  choose! gen hgen' using c3
  have c4 : ∀ d ∈ S, La ≤ d.1 ∧ d.1 ≤ Ld := by
    rintro d ⟨hd, hd'⟩
    have h1 : La ≤ d.1 := hd' ▸ (fixLat_le hd.2.2.1).1
    exact ⟨h1, ((hint _).1 hd.1.2).trans (an _ _ h1)⟩
  have c5 : ∀ d ∈ S, ∀ i, ∃ y, (gen d.1 i, y) ∈ d.2 := by
    intro d hd i
    refine hd.1.2.2.1.2.2.1 _ ?_
    rw [hgen' d.1 (c4 d hd)]
    rw [← hgen' d.1 (c4 d hd)]
    exact (hgen' d.1 (c4 d hd)).ge (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
  choose! ι hι using c5
  let Q : Set (V ⧸ L₀) := Ld.map L₀.mkQ
  have hQ : Q.encard = ((D₀ * x : ℕ) : ℕ∞) := by
    have h1 : Nat.card Q = D₀ * x := (GlobalTheory.Mass.LatticeGens.card_map_mkQ L₀ Ld).trans i1
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [h1]; positivity)
    rw [← h1, Nat.card_coe_set_eq, (Set.toFinite Q).cast_ncard_eq]
  let F : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V) → Submodule (𝓞 K) V × (Fin (2 * j + 1) → V ⧸ L₀) :=
    fun d => (d.1, fun i => L₀.mkQ ((algebraMap (𝓞 K) K g)⁻¹ • (gen d.1 i - ι d i)))
  have hmaps : Set.MapsTo F S ({L | La ≤ L ∧ L ≤ Ld} ×ˢ Set.univ.pi fun _ => Q) := by
    intro d hd
    refine ⟨c4 d hd, fun i _ => Submodule.mem_map_of_mem ?_⟩
    have := div_mem_dual hg0 hd.1.2.2.1 (hι d hd i)
    rwa [hd.2] at this
  have hle' : ∀ d ∈ S, ∀ d' ∈ S, F d = F d' → d.2 ≤ d'.2 := by
    rintro ⟨L', Γ₁⟩ hd ⟨L'', Γ₂⟩ hd' e
    obtain rfl : L' = L'' := congrArg Prod.fst e
    have m1 : IsModIso H (g : 𝓞 K) L' L₀ Γ₁ := hd.1.2.2.1
    have m2 : IsModIso H (g : 𝓞 K) L' L₀ Γ₂ := hd'.1.2.2.1
    have f1 : fixLat Γ₁ = La := hd.2
    have f2 : fixLat Γ₂ = La := hd'.2
    refine graph_le m1 m2 (f1.trans f2.symm) (S := Set.range (gen L')) (by rw [f1]; exact hgen' L' (c4 _ hd)) ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨ι (L', Γ₁) i, hι _ hd i, ?_⟩
    have e1 := (Submodule.Quotient.eq L₀).1 (congrFun (congrArg Prod.snd e) i)
    have e2 : ((0 : V), ι (L', Γ₂) i - ι (L', Γ₁) i) ∈ Γ₂ := by
      refine m2.2.1 ⟨Submodule.zero_mem _, _, e1, ?_⟩
      change (g : 𝓞 K) • (_ : V) = _
      rw [← algebraMap_smul K (g : 𝓞 K), ← smul_sub, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hgK, one_smul]
      simp
    simpa using Γ₂.sub_mem (hι _ hd' i) e2
  have hinj : Set.InjOn F S := fun d hd d' hd' e =>
    Prod.ext (congrArg Prod.fst e :) (le_antisymm (hle' d hd d' hd' e) (hle' d' hd' d hd e.symm))
  have hb := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_prod, Set.encard_pi_eq_prod_encard, hQ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hb
  rw [i2] at c1
  have hnat : (x * (D₀ * x)) ^ (2 * j + 1) * (D₀ * x) ^ (2 * j + 1) ≤ (x * D₀) ^ (3 * (2 * j + 1)) := by
    rw [pow_mul, ← mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    calc x * (D₀ * x) * (D₀ * x) = x ^ 3 * D₀ ^ 2 * 1 := by ring
      _ ≤ x ^ 3 * D₀ ^ 2 * D₀ := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hD0)
      _ = _ := by ring
  have hfin : S.encard ≤ (((x * D₀) ^ (3 * (2 * j + 1)) : ℕ) : ℕ∞) := by
    refine (hb.trans (mul_le_mul_left c1 _)).trans ?_
    exact_mod_cast hnat
  have := ENat.toENNReal_le.2 hfin
  simpa using this

end GlobalTheory.DegCnt.DatCount
