import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ListProdStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical NNReal

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem trace_congr {p p' : Submodule ℂ V} (h : p = p') (A : V →ₗ[ℂ] V) (h1 : ∀ v ∈ p, A v ∈ p) (h2 : ∀ v ∈ p', A v ∈ p') :
    LinearMap.trace ℂ p (A.restrict h1) = LinearMap.trace ℂ p' (A.restrict h2) := by
  subst h
  rfl

private theorem hasTrace_smul [MeasurableSpace G] {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (c : ℝ≥0)
    (hc : c ≠ 0) (h : HasTrace m ρ f s) : HasTrace (c • m) ρ f (((c : ℝ) : ℂ) * s) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hr : LinearMap.range (((c : ℝ) : ℂ) • A) = LinearMap.range A := LinearMap.range_smul _ _ hc'
  refine ⟨((c : ℝ) : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure_nnreal, ?_⟩, hr ▸ hfin, ?_⟩
  · rw [integral_smul_nnreal_measure, ← (hA v l).2, LinearMap.smul_apply, map_smul]
    rfl
  · rw [trace_congr hr _ _ (fun v _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self A v)), ← smul_eq_mul, ← map_smul]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem vol_pos (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) : 0 < m.real U :=
  ENNReal.toReal_pos (hU.2.measure_pos m ⟨1, one_mem U⟩).ne' hU.1.measure_lt_top.ne

private theorem trace_ind (m : Measure G) [m.IsHaarMeasure] {ρ : Representation ℂ G V} {U : Subgroup G} (hU : CO U) {s : ℂ}
    (h : HasTrace m ρ ((U : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ U) ∧ s = (m.real U : ℂ) * Module.finrank ℂ (fixedVectors ρ U) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hm : MeasurableSet (U : Set G) := hU.2.measurableSet
  have hc : (m.real U : ℂ) ≠ 0 := by exact_mod_cast (vol_pos m hU).ne'
  have h1 : ∀ v, A v ∈ fixedVectors ρ U := fun v => mem_fixedVectors.2 fun a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_mul_left_eq_self (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ U
    · simp [h, mul_mem ha h]
    · have : a * g ∉ U := fun h' => h (by simpa using mul_mem (inv_mem ha) h')
      simp [h, this]
  have h2 : ∀ v ∈ fixedVectors ρ U, A v = (m.real U : ℂ) • v := fun v hv => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul]
    have : (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (U : Set G).indicator fun _ => l v := by
      funext g
      by_cases h : g ∈ U
      · simp [h, mem_fixedVectors.1 hv g h]
      · simp [h]
    rw [this, integral_indicator_const _ hm]
    rfl
  have hr : LinearMap.range A = fixedVectors ρ U := by
    refine le_antisymm (by rintro _ ⟨v, rfl⟩; exact h1 v) fun v hv => ⟨(m.real U : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, h2 v hv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  haveI : FiniteDimensional ℂ (fixedVectors ρ U) := hr ▸ hfin
  refine ⟨this, ?_⟩
  rw [trace_congr hr _ _ (fun v _ => h1 v)]
  have : A.restrict (p := fixedVectors ρ U) (q := fixedVectors ρ U) (fun v _ => h1 v) = (m.real U : ℂ) • LinearMap.id :=
    LinearMap.ext fun v => Subtype.ext (h2 v v.2)
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]

private theorem ex_haar [LocallyCompactSpace G] {U : Subgroup G} (hU : CO U) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  obtain ⟨P, hP⟩ : ∃ P : TopologicalSpace.PositiveCompacts G, (P : Set G) = U :=
    ⟨⟨⟨U, hU.1⟩, by
      change (interior (U : Set G)).Nonempty
      rw [hU.2.interior_eq]
      exact ⟨1, one_mem U⟩⟩, rfl⟩
  exact ⟨Measure.haarMeasure P, inferInstance, hP ▸ Measure.haarMeasure_self⟩

private theorem ex_norm (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) :
    ∃ (c : ℝ≥0) (m' : Measure G), c ≠ 0 ∧ m'.IsHaarMeasure ∧ m' U = 1 ∧ m = c • m' := by
  have h0 : m U ≠ 0 := (hU.2.measure_pos m ⟨1, one_mem U⟩).ne'
  have h1 : m U ≠ ⊤ := hU.1.measure_lt_top.ne
  have hc : (m U).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, h1⟩
  refine ⟨(m U).toNNReal, (m U).toNNReal⁻¹ • m, hc, Measure.IsHaarMeasure.nnreal_smul m (inv_ne_zero hc), ?_, ?_⟩
  · rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_inv hc, ENNReal.coe_toNNReal h1, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 h1]
  · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

end Abs

private theorem amp_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (h1 : 𝔞.ν = ν) :
    𝔞.A = Oinf μ ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) := by
  subst h1
  rfl

private theorem term {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
    {σ : E ≃ₐ[F] E} {n : ℕ} (hn : 0 < n) {μ : Measure (normOneGL F n)} [μ.IsHaarMeasure] {q : Pl F}
    {w₀ : GroundTheory.Global.SemiLocal.PlacesOver E q} {ν : Measure (archGroup F n)} [ν.IsHaarMeasure] {a : TI F n} {L : Loc σ n q w₀}
    {e : Fin n → ℤ} {l : ℕ} {𝔣 : Side (Twist.id μ) l} (he : Antitone e) (hF : IsSideF L ν a e 𝔣)
    (hf : ∀ v ∈ L.S, L.f v = (L.UF v : Set (Gw n v)).indicator 1) {x : ℝ} (hx : 0 < x) (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (hne : eigIn V 𝔣.toAmp.A x ≠ ⊥) :
    ∃ (c : ℝ) (Z : Multiset ℂ), 0 < c ∧ 0 ∉ Z ∧ Z ≠ 0 ∧ ∀ j : ℕ,
      trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = c * (Z.map (· ^ j)).sum := by
  letI : ∀ v : Pl F, MeasurableSpace (Gw n v) := fun v => borel _
  haveI : ∀ v : Pl F, BorelSpace (Gw n v) := fun v => ⟨rfl⟩
  have hK : ∀ v : Pl F, CO (GLnLocal.integralGL (v.adicCompletion F) n) := fun v =>
    (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (GLnLocal.isOpen_integralGL _ _) le_rfl
  choose m hm using fun v : Pl F => ex_haar (hK v)
  haveI := fun v => (hm v).1
  obtain ⟨κ, hκ, H⟩ := termF F E σ n l hn μ ν m hm
  choose τ hτ using fun v : Pl F => (occursBasics F n μ V v (m v) hV).1
  obtain ⟨N, hN, H⟩ := H a q w₀ L.S V τ x hV hx fun v _ => hτ v
  have hlev : levF L.UF = levOn (insert q L.S) L.UF := by
    unfold levOn
    congr 1
    funext v
    split_ifs with h
    · rfl
    · rw [Finset.mem_insert, not_or] at h
      exact (L.off v h.2 h.1).2.2.2
  have hne' := hne
  rw [amp_eq 𝔣.toAmp ν hF.1, hF.2.1, hF.2.2.2.1, hlev, UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed F n hn μ ν V a x _ L.UF hx.ne'] at hne'
  have hN0 : 0 < N := hN.2 (ne_bot_of_le_ne_bot hne' inf_le_left)
  have hCO : ∀ v ∈ insert q L.S, CO (L.UF v) := fun v hv => by
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [L.at_q.2.2.2]
      exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).1
    · exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (L.lev v hv).2.2.1 (L.lev v hv).2.2.2
  have hpos : ∀ v ∈ insert q L.S, FiniteDimensional ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧
      0 < Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧ HasTrace (m v) (τ v).ρ ((L.UF v : Set (Gw n v)).indicator 1)
        ((((m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) : ℝ)) : ℂ) := fun v hv => by
    obtain ⟨-, -, -, s, hs0, hs⟩ := T.unitTrace F n μ V hV v (m v) inferInstance (τ v) (L.UF v) (hτ v) (hCO v hv)
      (ne_bot_of_le_ne_bot hne' (inf_le_inf (inf_le_left.trans inf_le_left) (iInf₂_le v hv)))
    obtain ⟨h1, h2⟩ := trace_ind (m v) (hCO v hv) hs
    refine ⟨h1, Nat.pos_of_ne_zero fun h => hs0 (by rw [h2, h]; simp), ?_⟩
    push_cast
    exact h2 ▸ hs
  obtain ⟨hq1, hq2, -⟩ := hpos q (Finset.mem_insert_self _ _)
  rw [L.at_q.2.2.2] at hq1 hq2
  obtain ⟨c, m', hc, hm', hm1, hme⟩ := ex_norm (m q) (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n q).1
  obtain ⟨Z, hZ0, hZc, hZ⟩ := iwPow F n q m' hm1 (τ q) e he hq1
  let s : Pl F → ℝ := fun v => (m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v))
  have hs : ∀ v ∈ L.S, 0 < s v := fun v hv =>
    mul_pos (vol_pos _ (hCO v (Finset.mem_insert_of_mem hv))) (Nat.cast_pos.2 (hpos v (Finset.mem_insert_of_mem hv)).2.1)
  refine ⟨κ * x * N * c * ∏ v ∈ L.S, s v, Z, ?_, hZ0, ?_, fun j => ?_⟩
  · have h1 : (0 : ℝ) < c := by exact_mod_cast hc.bot_lt
    have h2 : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    have h3 := Finset.prod_pos hs
    positivity
  · rintro rfl
    rw [← hZc] at hq2
    exact lt_irrefl _ hq2
  · have h1 := hasTrace_smul c hc (hZ j)
    rw [← hme] at h1
    rw [H L e 𝔣 rfl he hF j _ (fun v => (s v : ℂ)) h1 fun v hv => by
      rw [hf v hv]
      exact (hpos v (Finset.mem_insert_of_mem hv)).2.2]
    push_cast
    ring

theorem UpperTheory.ConvolutionTheory.T.posSide :
    UpperTheory.ConvolutionTheory.T.PosSide := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n hn μ _ q w₀ ν _ a L e l 𝔣 he hF hf p V x hV hpV hx hne
  have hfin : {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}.Finite :=
    ((T.ampFin F n hn μ 𝔣.toAmp).1 x hx).subset fun W hW => hW.1
  let ι := {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}
  haveI : Fintype ι := hfin.fintype
  choose c Z hc hZ0 hZ hT using fun W : ι => term hn he hF hf hx W.1 W.2.1.1 W.2.1.2
  have htr : ∀ j, 𝔣.tr p x j = ∑ W : ι, (c W : ℂ) * ((Z W).map (· ^ j)).sum := fun j => by
    simp only [← hT]
    rw [Side.tr, ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem (s := ι)
      (f := fun W => trOn (eigIn W 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U))]
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => ⟨⟨h.1, fun hb => hW ?_⟩, h.2.2⟩, fun h => ⟨h.1.1, ?_, h.2⟩⟩
    · beta_reduce
      rw [hb]
      simpa using UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace (LL μ) ⊥ ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) 0 0 inferInstance fun v hv => by
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
    · exact Submodule.map_id W
  intro h
  let V₀ : ι := ⟨V, ⟨hV, hne⟩, hpV⟩
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero (hZ V₀)
  have h0 := powIndep ι (fun W => (c W : ℂ)) Z hZ0 (h.mono fun j hj => by rw [← htr]; exact not_not.1 hj) ζ
  have h1 : ∑ W : ι, c W * ((Multiset.filter (· = ζ) (Z W)).card : ℝ) = 0 := by exact_mod_cast h0
  refine (Finset.sum_pos' (fun W _ => mul_nonneg (hc W).le (Nat.cast_nonneg _)) ⟨V₀, Finset.mem_univ _, mul_pos (hc _) ?_⟩).ne' h1
  exact Nat.cast_pos.2 (Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩)
