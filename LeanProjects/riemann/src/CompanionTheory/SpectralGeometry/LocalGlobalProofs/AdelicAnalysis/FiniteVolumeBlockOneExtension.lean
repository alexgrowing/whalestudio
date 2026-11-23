import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetRepsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitaryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerateStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Aniso

theorem mean_lt_top {G G₁ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (ι : G₁ →* G) (hι : IsClosedEmbedding ι) (Γ : Subgroup G) [Countable Γ]
    (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕₁ : Set G₁) (hm₁ : MeasurableSet 𝓕₁) (hfin : μ₁ 𝓕₁ < ⊤) (hcov : ∀ u, ∃ γ ∈ Γ₁, γ * u ∈ 𝓕₁)
    (Q : Type) (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ ⊓ ι.range)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    (hinv : ∀ p ∈ ι.range, ∀ x, f (p * x) = f x)
    (C : Set G) (hC : IsCompact C) (hsupp : ∀ x, f x ≠ 0 → ∃ p ∈ ι.range, ∃ c ∈ C, x = p * c) :
    ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ < ⊤ := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hνinv : ∀ p ∈ ι.range, (μ₁.map ι).map (fun g => p * g) = μ₁.map ι := by
    rintro _ ⟨u, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hme.measurable]
    have h : (fun g => ι u * g) ∘ ι = ι ∘ (fun g => u * g) := by
      ext g; simp
    rw [h, ← Measure.map_map hme.measurable (measurable_const_mul _), map_mul_left_eq_self]
  have hνpos : ∀ U ∈ 𝓝 (1 : G), (μ₁.map ι) U ≠ 0 := by
    intro U hU
    have h1 : ι ⁻¹' U ∈ 𝓝 (1 : G₁) :=
      hι.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    have h2 : 0 < μ₁ (ι ⁻¹' U) := μ₁.measure_pos_of_mem_nhds h1
    have h3 : μ₁ (ι ⁻¹' U) ≤ (μ₁.map ι) U := Measure.le_map_apply hme.measurable.aemeasurable U
    exact (h2.trans_le h3).ne'
  obtain ⟨C', K, hC', hK, hcover⟩ := GlobalTheory.T.invariant_measure_compact_cover_bound G μ ι.range (μ₁.map ι) hνinv hνpos C hC
  obtain ⟨𝓕', h𝓕', hunf⟩ := GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps G μ Γ (Γ ⊓ ι.range) inf_le_left 𝓕 h𝓕 Q r hr hQ
  rw [hunf f hf]
  haveI : Countable ↥(Γ ⊓ ι.range) :=
    (Subgroup.inclusion_injective (inf_le_left : Γ ⊓ ι.range ≤ Γ)).countable
  have hae : ∀ᵐ p ∂(μ₁.map ι), ∃ γ ∈ Γ ⊓ ι.range, γ * p ∈ ι '' 𝓕₁ := by
    refine hme.ae_map_iff.2 (Filter.Eventually.of_forall fun u => ?_)
    obtain ⟨γ, hγ, hγu⟩ := hcov u
    exact ⟨ι γ, ⟨hΓ γ hγ, γ, rfl⟩, γ * u, hγu, map_mul ι γ u⟩
  have hb := hcover (Γ ⊓ ι.range) inf_le_right 𝓕' h𝓕' (ι '' 𝓕₁) (hme.measurableSet_image.2 hm₁) hae f
    (fun _ => 1) hf measurable_const (fun γ hγ x => hinv γ hγ.2 x) hsupp (fun p _ c _ => hf1 _)
  have hS : ∫⁻ p in ι '' 𝓕₁, (1 : ℝ≥0∞) ∂(μ₁.map ι) = μ₁ 𝓕₁ := by
    rw [lintegral_one, Measure.restrict_apply_univ, hme.map_apply,
      Set.preimage_image_eq _ hι.injective]
  rw [hS] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top hK hfin)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem bc_mem_HR (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    bc (inclR (F := F) R) g ∈ HR R σ J := by
  have hs : ∀ e : E, sigR R σ (inclR (F := F) R e) = inclR (F := F) R (σ e) := by
    intro e; simp [sigR, inclR]
  have hval : ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := rfl
  have hc : cT (sigR R σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) =
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).map (inclR (F := F) R) := by
    ext i j
    simp [cT, hs]
  have hg' : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  show cT (sigR R σ) ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
    ((bc (inclR (F := F) R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J
  rw [hval, hc]
  unfold JR
  rw [← Matrix.map_mul, ← Matrix.map_mul, hg']

def ratH (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) : HA R σ J :=
  (⟨bc (inclR (F := F) R) g, bc_mem_HR R σ J g hg⟩ : HR R σ J)

theorem mat_ratH (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    HA.mat R σ J (ratH R σ J g hg) = bc (inclR (F := F) R) g := rfl

theorem act_rat (γ : HA R σ J) (g : GL (Fin M) E) (hγ : HA.mat R σ J γ = bc (inclR (F := F) R) g) {n : ℕ}
    (X : Fin n → Fin M → E) :
    actW R σ J γ (ratTup R X) = ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  simp only [actW, actTup, ratTup, hγ]
  show ∑ j, inclR (F := F) R ((g : Matrix (Fin M) (Fin M) E) i j) * inclR (F := F) R (X a j) =
    inclR (F := F) R (∑ j, (g : Matrix (Fin M) (Fin M) E) i j * X a j)
  simp [map_sum]

end Rat

theorem count_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) (𝓕 : Set (HA (AF F) σ (blockOne (algebraMap F E t) J))), IsHaarH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ → IsFDH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsCompact Ω → cntI σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ hvol t ht μ 𝓕 hμ h𝓕 Ω hΩ
  have hJb : IsHermND σ (blockOne (algebraMap F E t) J) := (GlobalTheory.T.hyperbolic_and_block_one_nondegenerate F E σ hσ M J hJ).2 t ht
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := a1
  haveI := a2
  haveI := a3
  haveI : T2Space (AF F ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.1
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  obtain ⟨tg, lc, sc, t2, bs, hact⟩ :=
    GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 1) (blockOne (algebraMap F E t) J) hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨hcont, -, hmul, hgram⟩ := hact 1
  haveI : μ.IsHaarMeasure := hμ

  let e0E : Fin 1 → Fin (M + 1) → E := fun _ => Fin.cons 1 (fun _ => 0)
  let e0 : Fin 1 → Fin (M + 1) → AF F ⊗[F] E := ratTup (AF F) e0E
  have he0 : e0 = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
    funext a i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e0, e0E, ratTup]
    · simp [e0, e0E, ratTup]
  have hg0 : gramE σ (blockOne (algebraMap F E t) J) e0E = fun _ _ => algebraMap F E t := by
    funext a b
    simp [gramE, hE, hform, e0E, Fin.sum_univ_succ, blockOne]
  have hdet : (gramE σ (blockOne (algebraMap F E t) J) e0E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    have h00 : gramE σ (blockOne (algebraMap F E t) J) e0E 0 0 = algebraMap F E t :=
      congrFun (congrFun hg0 0) 0
    rw [h00]
    simpa using ht
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := RingHom.injective _
  have hratinj : Function.Injective
      (ratTup (F := F) (AF F) : (Fin 1 → Fin (M + 1) → E) → (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) := by
    intro X Y h
    funext a i
    exact hinj (congrFun (congrFun h a) i)
  obtain ⟨hgr1, hgr2, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ (M + 1) (blockOne (algebraMap F E t) J) hJb
  obtain ⟨ι, hιc, hιm, hιs, hιr, -⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hσ M J hJ t ht (AF F)
  have hstab : ∀ h, h ∈ ι.range ↔ actW (AF F) σ (blockOne (algebraMap F E t) J) h e0 = e0 := by
    intro h
    rw [he0]
    exact hιs h

  have hinvact : ∀ (h : HA (AF F) σ (blockOne (algebraMap F E t) J)) (Y Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E),
      actW (AF F) σ (blockOne (algebraMap F E t) J) h Y = Z →
      actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ Z = Y := by
    intro h Y Z hYZ
    obtain ⟨-, hone, -, -⟩ := hact 1
    rw [← hYZ, ← hmul, inv_mul_cancel, hone]

  let Q : Set (Fin 1 → Fin (M + 1) → E) :=
    {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t}
  have hrep : ∀ q : Q, ∃ g ∈ UJ (σ : E →+* E) (blockOne (algebraMap F E t) J),
      ∀ a, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ q.1 a = e0E a := by
    intro q
    have hq : gramE σ (blockOne (algebraMap F E t) J) q.1 = gramE σ (blockOne (algebraMap F E t) J) e0E :=
      q.2.trans hg0.symm
    exact GlobalTheory.T.witt_extension_global F E σ hσ (M + 1) _ hJb 1 q.1 e0E hq (hq ▸ hdet)
  choose g hg hgq using hrep
  let r : Q → HA (AF F) σ (blockOne (algebraMap F E t) J) := fun q => ratH (AF F) σ _ (g q) (hg q)
  have hrq : ∀ q : Q, actW (AF F) σ (blockOne (algebraMap F E t) J) (r q) (ratTup (AF F) q.1) = e0 := by
    intro q
    rw [act_rat (AF F) σ _ (r q) (g q) (mat_ratH (AF F) σ _ (g q) (hg q))]
    show ratTup (AF F) _ = ratTup (AF F) e0E
    congr 1
    funext a
    exact hgq q a
  have hrq' : ∀ q : Q, actW (AF F) σ (blockOne (algebraMap F E t) J) (r q)⁻¹ e0 = ratTup (AF F) q.1 :=
    fun q => hinvact _ _ _ (hrq q)

  let f : HA (AF F) σ (blockOne (algebraMap F E t) J) → ℝ≥0∞ := fun h =>
    Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0)
  have hfm : Measurable f := by
    have hc : Continuous fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0 :=
      hcont.comp (continuous_inv.prodMk continuous_const)
    have hcl : IsClosed Ω := hΩ.isClosed
    have : f = Set.indicator ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) (fun _ => (1 : ℝ≥0∞)) := by
      funext h
      by_cases hh : actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0 ∈ Ω
      · simp only [f]
        rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show h ∈ ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) => actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) from hh)]
      · simp only [f]
        rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (show h ∉ ((fun h : HA (AF F) σ (blockOne (algebraMap F E t) J) => actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ e0) ⁻¹' Ω) from hh)]
    rw [this]
    exact measurable_const.indicator (hcl.preimage hc).measurableSet
  have hf1 : ∀ x, f x ≤ 1 := by
    intro x
    simp only [f, Set.indicator]
    split_ifs <;> simp
  have hinv : ∀ p ∈ ι.range, ∀ x, f (p * x) = f x := by
    intro p hp x
    have hp' : p⁻¹ ∈ ι.range := ι.range.inv_mem hp
    have : actW (AF F) σ (blockOne (algebraMap F E t) J) (p * x)⁻¹ e0 =
        actW (AF F) σ (blockOne (algebraMap F E t) J) x⁻¹ e0 := by
      rw [mul_inv_rev, hmul, (hstab _).1 hp']
    simp only [f, this]
  obtain ⟨C₀, hC₀, hC₀p⟩ := GlobalTheory.T.gram_orbit_compact_representative F E σ hσ (M + 1) _ hJb 1 e0E hdet Ω hΩ
  have hsupp : ∀ x, f x ≠ 0 → ∃ p ∈ ι.range, ∃ c ∈ C₀⁻¹, x = p * c := by
    intro x hx
    have hxΩ : actW (AF F) σ (blockOne (algebraMap F E t) J) x⁻¹ e0 ∈ Ω := by
      by_contra hn
      exact hx (Set.indicator_of_notMem hn _)
    obtain ⟨c, hc, hce⟩ := hC₀p _ hxΩ (by rw [hgram]; exact hgr2 1 e0E)
    refine ⟨x * c, (hstab _).2 ?_, c⁻¹, Set.inv_mem_inv.2 hc, by group⟩
    rw [hmul]
    show actW (AF F) σ (blockOne (algebraMap F E t) J) x (actW (AF F) σ (blockOne (algebraMap F E t) J) c (ratTup (AF F) e0E)) = e0
    rw [hce, ← hmul, mul_inv_cancel]
    exact (hact 1).2.1 e0

  let Γ : Subgroup (HA (AF F) σ (blockOne (algebraMap F E t) J)) := HFinIn (AF F) σ (blockOne (algebraMap F E t) J)
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hσ (M + 1) _ hJb).1
  have hmemΓ : ∀ γ : HA (AF F) σ (blockOne (algebraMap F E t) J),
      γ ∈ Γ ↔ HA.mat (AF F) σ _ γ ∈ HFin (AF F) σ (blockOne (algebraMap F E t) J) := fun γ => Iff.rfl
  have hmemΓ₁ : ∀ γ : HA (AF F) σ J, γ ∈ Γ₁ ↔ HA.mat (AF F) σ _ γ ∈ HFin (AF F) σ J := fun γ => Iff.rfl
  have hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ := fun u hu => (hmemΓ _).2 ((hιr u).2 ((hmemΓ₁ u).1 hu))
  have hr : ∀ q, r q ∈ Γ := fun q => (hmemΓ _).2 (Subgroup.mem_map.2 ⟨g q, hg q, rfl⟩)
  have hQ : ∀ γ ∈ Γ, ∃! q : Q, γ * (r q)⁻¹ ∈ Γ ⊓ ι.range := by
    intro γ hγ
    obtain ⟨g₀, hg₀, hγ₀⟩ := Subgroup.mem_map.1 ((hmemΓ γ).1 hγ)
    have hinvm : HA.mat (AF F) σ _ γ⁻¹ = bc (inclR (F := F) (AF F)) g₀⁻¹ := by
      rw [map_inv, hγ₀]
      rfl
    have hX : actW (AF F) σ (blockOne (algebraMap F E t) J) γ⁻¹ e0 =
        ratTup (AF F) (fun a => ((g₀⁻¹ : GL _ E) : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ e0E a) :=
      act_rat (AF F) σ _ γ⁻¹ g₀⁻¹ hinvm e0E
    have hXQ : (fun a => ((g₀⁻¹ : GL _ E) : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *ᵥ e0E a) ∈ Q := by
      show gramE σ _ _ = _
      rw [← hg0]
      have h1 := hgram γ⁻¹ e0
      rw [hX, hgr2] at h1
      have h2 : gramR (AF F) σ (blockOne (algebraMap F E t) J) e0 =
          (gramE σ (blockOne (algebraMap F E t) J) e0E).map (inclR (AF F)) := hgr2 1 e0E
      rw [h2] at h1
      exact Matrix.map_injective hinj h1
    refine ⟨⟨_, hXQ⟩, ?_, ?_⟩
    · refine ⟨Γ.mul_mem hγ (Γ.inv_mem (hr _)), (hstab _).2 ?_⟩
      rw [hmul, hrq', ← hX, ← hmul, mul_inv_cancel]
      exact (hact 1).2.1 e0
    · rintro q ⟨-, hq⟩
      have h1 := (hstab _).1 hq
      rw [hmul, hrq'] at h1
      have h2 := hinvact _ _ _ h1
      rw [hX] at h2
      exact Subtype.ext (hratinj h2).symm

  obtain ⟨⟨μ₁, hμ₁⟩, hall⟩ := hvol
  haveI : μ₁.IsHaarMeasure := hμ₁
  obtain ⟨𝓕₁, hm₁, hFD₁, hcov₁⟩ := ((GlobalTheory.T.haar_fundamental_domain_exists_unitary F E σ hσ M J hJ).2 μ₁ hμ₁).2.1
  have hfin : μ₁ 𝓕₁ < ⊤ := (hall μ₁ hμ₁).2 𝓕₁ hFD₁
  have key := mean_lt_top μ μ₁ ι hιc Γ Γ₁ hΓ 𝓕 h𝓕 𝓕₁ hm₁ hfin
    (fun u => by
      obtain ⟨γ, h1, h2⟩ := hcov₁ u
      exact ⟨γ, (hmemΓ₁ γ).2 h1, h2⟩)
    Q r hr hQ f hfm hf1 hinv C₀⁻¹ hC₀.inv hsupp
  have hrew : ∀ (h : HA (AF F) σ (blockOne (algebraMap F E t) J)) (q : Q), f (r q * h) =
      Set.indicator Ω (fun _ => (1 : ℝ≥0∞))
        (actW (AF F) σ (blockOne (algebraMap F E t) J) h⁻¹ (ratTup (AF F) q.1)) := by
    intro h q
    simp only [f]
    rw [mul_inv_rev, hmul, hrq']
  unfold cntI
  simp only [← hrew]
  exact key

end GlobalTheory.CompanionTheory.SW.Aniso
