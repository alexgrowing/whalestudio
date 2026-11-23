import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

private theorem tendsto_mul_zero_of_tendsto_zero_of_mem_compact {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {L : Set K} (hL : IsCompact L) {f g : ℕ → K}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) (hg : ∀ j, g j ∈ L) :
    Filter.Tendsto (fun j => f j * g j) Filter.atTop (nhds 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.mp hU
  have hsub : ({0} : Set K) ×ˢ L ⊆ (fun q : K × K => q.1 * q.2) ⁻¹' V := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show 0 * y ∈ V
    rw [zero_mul]
    exact h0V
  obtain ⟨u, w, hu, -, h0u, hLw, huw⟩ :=
    generalized_tube_lemma isCompact_singleton hL (hVo.preimage continuous_mul) hsub
  have hev : ∀ᶠ j in Filter.atTop, f j ∈ u := hf (hu.mem_nhds (h0u (Set.mem_singleton 0)))
  filter_upwards [hev] with j hj
  exact hVU (huw (Set.mk_mem_prod hj (hLw (hg j))))

theorem GlobalTheory.CompanionTheory.AvgFree.not_linearIndependent_of_near {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] (S : Finset (Kˣ × K))
    (hS : ∀ p ∈ S, p.2 ≠ 0 ∧ Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : K) ^ j) Filter.atTop (nhds 0))
    {O L : Set K} (hO : IsCompact O) (hL : IsCompact L) {n M : ℕ} (X : Fin n → Fin M → K)
    (hX : ∀ j : ℕ, ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → K), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, ∑ i, X i k * a i ∈ (fun x => (p.1 : K) ^ j * x) '' L) :
    ¬ LinearIndependent K X := by
  classical
  intro hli
  choose p hpS l a haO hal hmem using hX
  choose w hwL hweq using hmem
  obtain ⟨⟨p₀, l₀⟩, hinf⟩ := Finite.exists_infinite_fiber (fun j : ℕ => ((⟨p j, hpS j⟩ : S), l j))
  set J := (fun j : ℕ => ((⟨p j, hpS j⟩ : S), l j)) ⁻¹' {(p₀, l₀)} with hJdef
  have hJ : Set.Infinite J := Set.infinite_coe_iff.mp hinf
  have hJp : ∀ j ∈ J, p j = (p₀ : Kˣ × K) ∧ l j = l₀ := by
    intro j hj
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hj)
    exact ⟨congrArg Subtype.val (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
  haveI hNe : (Filter.atTop ⊓ Filter.principal J).NeBot := by
    have h := Nat.frequently_atTop_iff_infinite.mpr hJ
    exact Filter.frequently_iff_neBot.mp h
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin n => O)) := isCompact_univ_pi (fun _ => hO)
  have hin : Filter.Tendsto a (Filter.atTop ⊓ Filter.principal J)
      (Filter.principal (Set.pi Set.univ (fun _ : Fin n => O))) :=
    Filter.tendsto_principal.mpr (Filter.Eventually.of_forall fun j i _ => haO j i)
  obtain ⟨a₀, -, hclus⟩ := hcomp hin
  have hp₀ := hS _ p₀.2
  have ha₀l : a₀ l₀ = 1 := by
    have hC : IsClosed {x : Fin n → K | x l₀ = 1} := isClosed_eq (continuous_apply l₀) continuous_const
    have hle : Filter.map a (Filter.atTop ⊓ Filter.principal J) ≤ Filter.principal {x : Fin n → K | x l₀ = 1} := by
      refine Filter.tendsto_principal.mpr ?_
      refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun j hj => ?_)
      show a j l₀ = 1
      rw [← (hJp j hj).2]
      exact hal j
    have hcl := hclus.mono hle
    rw [← mem_closure_iff_clusterPt, hC.closure_eq] at hcl
    exact hcl
  have hzero : ∀ k, p₀.1.2 * ∑ i, X i k * a₀ i = 0 := by
    intro k
    have hcont : Continuous (fun x : Fin n → K => p₀.1.2 * ∑ i, X i k * x i) := by
      fun_prop
    have htend : Filter.Tendsto (fun j => p₀.1.2 * ∑ i, X i k * a j i) (Filter.atTop ⊓ Filter.principal J) (nhds 0) := by
      have h0 := (tendsto_mul_zero_of_tendsto_zero_of_mem_compact hL hp₀.2 (fun j => hwL j k)).mono_left
        (inf_le_left : Filter.atTop ⊓ Filter.principal J ≤ Filter.atTop)
      refine h0.congr' ?_
      refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun j hj => ?_)
      show p₀.1.2 * (p₀.1.1 : K) ^ j * w j k = p₀.1.2 * ∑ i, X i k * a j i
      have hw := hweq j k
      simp only at hw
      rw [← hw, (hJp j hj).1, mul_assoc]
    have hcl := hclus.map hcont.continuousAt (Filter.tendsto_map'_iff.mpr htend)
    exact eq_of_nhds_neBot hcl
  have hsum : ∑ i, (p₀.1.2 * a₀ i) • X i = 0 := by
    ext k
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hzero k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h0 := Fintype.linearIndependent_iff.mp hli (fun i => p₀.1.2 * a₀ i) hsum l₀
  rw [ha₀l, mul_one] at h0
  exact hp₀.1 h0

theorem GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hv O S hOrd L hLc hLo n M X hX
  obtain ⟨hXin, hXli⟩ := hX
  by_contra hnot
  simp only [Set.mem_iUnion, not_exists] at hnot
  refine GlobalTheory.CompanionTheory.AvgFree.not_linearIndependent_of_near S
    (fun p hp => ⟨(hOrd.2.2.2.1 p hp).2.1, (hOrd.2.2.2.1 p hp).2.2.2.1⟩) hOrd.1 hLc X ?_ hXli
  intro j
  have hmem : X ∈ ⋃ p ∈ S, nearNF (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : Fv F v ⊗[F] E) j := by
    by_contra h'
    exact hnot j ⟨hXin, h'⟩
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨p, hp, -, l, a, haO, hal, hk⟩ := hmem
  exact ⟨p, hp, l, a, haO, hal, hk⟩
