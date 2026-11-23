import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlaceStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.SelfDualAE

private theorem integral_indicator_mul_char_eq_indicator_measure {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure] {χ : V → V → ℂ} (L : AddSubgroup V)
    (ho : IsOpen (L : Set V))
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hL : ∀ y, (∀ x ∈ L, χ x y = 1) ↔ y ∈ L) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂ν =
      (L : Set V).indicator (fun _ => ((ν (L : Set V)).toReal : ℂ)) y := by
  classical
  have hmeas : MeasurableSet (L : Set V) := ho.measurableSet
  have hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
      (L : Set V).indicator (fun x => χ x y) := by
    funext x
    by_cases hx : x ∈ (L : Set V) <;> simp [hx]
  rw [hfun]
  by_cases hy : y ∈ L
  · have hone : ∀ x ∈ (L : Set V), χ x y = 1 := fun x hx => (hL y).2 hy x hx
    rw [Set.indicator_of_mem (show y ∈ (L : Set V) from hy), integral_indicator hmeas,
      setIntegral_congr_fun hmeas hone, setIntegral_const]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem (show y ∉ (L : Set V) from hy)]
    have hex : ∃ x0 ∈ L, χ x0 y ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hy ((hL y).1 hcon)
    obtain ⟨x0, hx0, hne⟩ := hex
    set f : V → ℂ := (L : Set V).indicator (fun x => χ x y) with hf
    have hshift : ∀ x, f (x0 + x) = χ x0 y * f x := by
      intro x
      by_cases hx : x ∈ L
      · have hx' : x0 + x ∈ L := L.add_mem hx0 hx
        simp only [hf, Set.indicator_of_mem (show x0 + x ∈ (L : Set V) from hx'),
          Set.indicator_of_mem (show x ∈ (L : Set V) from hx), hadd]
      · have hx' : x0 + x ∉ L := fun h => hx ((L.add_mem_cancel_left hx0).1 h)
        simp only [hf, Set.indicator_of_notMem (show x0 + x ∉ (L : Set V) from hx'),
          Set.indicator_of_notMem (show x ∉ (L : Set V) from hx), mul_zero]
    have hinv : ∫ x, f (x0 + x) ∂ν = ∫ x, f x ∂ν := integral_add_left_eq_self f x0
    simp_rw [hshift] at hinv
    rw [integral_const_mul] at hinv
    have h0 : (χ x0 y - 1) * ∫ x, f x ∂ν = 0 := by rw [sub_mul, hinv, one_mul, sub_self]
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

theorem selfDual_of_lattice {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ₀ μ : Measure V} {χ : V → V → ℂ}
    (h₀ : SelfDual μ₀ χ) (hμ : μ.IsAddHaarMeasure) (L : AddSubgroup V)
    (hc : IsCompact (L : Set V)) (ho : IsOpen (L : Set V))
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hz : ∀ y, χ y 0 = 1)
    (hL : ∀ y, (∀ x ∈ L, χ x y = 1) ↔ y ∈ L) (h1 : μ L = 1) : SelfDual μ χ := by
  classical
  have hcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L ho
  haveI : μ₀.IsAddHaarMeasure := h₀.1
  have hmeas : MeasurableSet (L : Set V) := ho.measurableSet
  have hft := integral_indicator_mul_char_eq_indicator_measure μ₀ L ho hadd hL
  have hfin : μ₀ (L : Set V) ≠ ⊤ := hc.measure_lt_top.ne
  have hΦc : Continuous ((L : Set V).indicator (fun _ => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const
  have hΦs : HasCompactSupport ((L : Set V).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro' hc hcl (fun x hx => Set.indicator_of_notMem hx _)
  have hI : Integrable (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ₀) μ₀ := by
    simp_rw [hft]
    exact (integrable_indicator_iff hmeas).2 (integrableOn_const hfin)
  have key := h₀.2 _ hΦc hΦs hI 0
  simp_rw [hft, hz, mul_one] at key
  rw [integral_indicator hmeas, setIntegral_const, neg_zero,
    Set.indicator_of_mem (show (0 : V) ∈ (L : Set V) from L.zero_mem)] at key
  have hc0 : (μ₀ (L : Set V)).toReal * (μ₀ (L : Set V)).toReal = 1 := by
    have := key
    simp only [Measure.real, Complex.real_smul] at this
    exact_mod_cast this
  have hc1 : (μ₀ (L : Set V)).toReal = 1 := by
    have hnn : 0 ≤ (μ₀ (L : Set V)).toReal := ENNReal.toReal_nonneg
    nlinarith [sq_nonneg ((μ₀ (L : Set V)).toReal - 1)]
  have hμ₀L : μ₀ (L : Set V) = 1 := by
    rw [← ENNReal.ofReal_toReal hfin, hc1, ENNReal.ofReal_one]
  let K : TopologicalSpace.PositiveCompacts V :=
    ⟨⟨(L : Set V), hc⟩, by
      show (interior (L : Set V)).Nonempty
      rw [ho.interior_eq]
      exact ⟨0, L.zero_mem⟩⟩
  have e1 := Measure.addHaarMeasure_unique μ K
  have e2 := Measure.addHaarMeasure_unique μ₀ K
  have hK : ((K : Set V)) = (L : Set V) := rfl
  have heq : μ = μ₀ := by
    rw [e1, e2, hK, h1, hμ₀L]
  rw [heq]
  exact h₀

section Char

variable (F : Type) [Field F] [NumberField F]

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  have h : pairA F 0 (singleV F v 0) = 0 := by
    simp only [pairA, singleV, RestrictedProduct.single_zero]
    rfl
  rw [psiV, h, AddChar.map_zero_eq_one]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  have h : pairA F 0 (singleV F v (x + y)) =
      pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    refine Prod.ext ?_ ?_
    · exact (add_zero (0 : Ainf F)).symm
    · classical
      exact RestrictedProduct.single_add _ _ _ _
  rw [psiV, h, AddChar.map_add_eq_mul]
  rfl

theorem ev_int (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := GlobalTheory.GaugeEx.IntBasis.ev_int a

end Char

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_one_tmul (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext r x
    simp
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem trace_mul_eq (R : Type) [CommRing R] [Algebra F R] (e : E) (y : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (inclR R e * y) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k *
        algebraMap F R (Algebra.trace F E (e * b k)) := by
  conv_lhs => rw [GlobalTheory.GaugeEx.IntBasis.eq_sum b R y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : inclR R e * ((Algebra.TensorProduct.basis R b).repr y k ⊗ₜ[F] b k) =
      (Algebra.TensorProduct.basis R b).repr y k • ((1 : R) ⊗ₜ[F] (e * b k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, LinearMap.map_smul, trace_one_tmul, smul_eq_mul]

theorem trace_dual_mul (R : Type) [CommRing R] [Algebra F R] (k : Fin d) (y : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (inclR R (b.traceDual k) * y) =
      (Algebra.TensorProduct.basis R b).repr y k := by
  rw [trace_mul_eq b R (b.traceDual k) y]
  simp [Module.Basis.trace_traceDual_mul]

theorem ev_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (Fv F v) e ∈ intV b v := by
  filter_upwards [GlobalTheory.GaugeEx.IntBasis.ev_int_coord b e] with v hv
  exact GlobalTheory.GaugeEx.IntBasis.tmul_mem b v (one_mem _) hv

def intGrp (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := intV b v
  zero_mem' := by intro k; simp
  add_mem' := by
    intro x y hx hy k
    rw [map_add]; exact add_mem (hx k) (hy k)
  neg_mem' := by
    intro x hx k
    rw [map_neg]; exact neg_mem (hx k)

def latGrp (v : HeightOneSpectrum (𝓞 F)) (n M : ℕ) : AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => intGrp b v

theorem coe_latGrp (v : HeightOneSpectrum (𝓞 F)) (n M : ℕ) :
    (latGrp b v n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => Set.univ.pi fun _ => intV b v := rfl

theorem mem_latGrp (v : HeightOneSpectrum (𝓞 F)) (n M : ℕ) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latGrp b v n M ↔ ∀ a i, Y a i ∈ intV b v := by
  rw [← SetLike.mem_coe, coe_latGrp]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [NumberField F] [NumberField E] in
theorem BR_add (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X X' Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (X + X') Y = BR R σ J X Y + BR R σ J X' Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [NumberField F] [NumberField E] in
theorem BR_zero (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X 0 = 0 := by
  simp [BR, hR, Formalism.UG.hform]

omit [NumberField F] [NumberField E] in
theorem sigR_smul (R : Type) [CommRing R] [Algebra F R] (t : R) (y : R ⊗[F] E) :
    sigR R σ (t • y) = t • sigR R σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add y₁ y₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]

omit [NumberField F] [NumberField E] in
theorem BR_smul (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (t : R)
    (X Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (t • X) Y = BR R σ J X Y * t := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  rw [← smul_eq_mul, ← LinearMap.map_smul_of_tower]
  congr 1
  simp only [Finset.smul_sum, smul_mul_assoc]

theorem BR_test (hJ : J.det ≠ 0) (j : Fin M) (k : Fin d) : ∃ x : Fin M → E,
    ∀ (R : Type) [CommRing R] [Algebra F R] (Y : Fin 1 → Fin M → R ⊗[F] E),
      BR R σ J (fun _ i => inclR R (x i)) Y = (Algebra.TensorProduct.basis R b).repr (Y 0 j) k := by
  have hsur : Function.Surjective σ := (AlgHom.bijective σ).2
  choose τ hτ using hsur
  have key : ∀ j' : Fin M, (∑ i, b.traceDual k * J⁻¹ j i * J i j') =
      if j = j' then b.traceDual k else 0 := by
    intro j'
    simp only [mul_assoc, ← Finset.mul_sum]
    have h2 : (∑ i, J⁻¹ j i * J i j') = (J⁻¹ * J) j j' := by simp [Matrix.mul_apply]
    rw [h2, Matrix.nonsing_inv_mul J (Ne.isUnit hJ), Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨fun i => τ (b.traceDual k * J⁻¹ j i), ?_⟩
  intro R _ _ Y
  have hs : ∀ i, sigR R σ (inclR R (τ (b.traceDual k * J⁻¹ j i))) =
      inclR R (b.traceDual k * J⁻¹ j i) := by
    intro i
    simp [sigR, inclR, hτ]
  have hrow : ∀ j' : Fin M, (∑ i, inclR R (b.traceDual k * J⁻¹ j i) * inclR R (J i j') * Y 0 j') =
      inclR R (if j = j' then b.traceDual k else 0) * Y 0 j' := by
    intro j'
    rw [← key j', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul]
  have hsum : hR R σ J (fun i => inclR R (τ (b.traceDual k * J⁻¹ j i))) (Y 0) =
      inclR R (b.traceDual k) * Y 0 j := by
    simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, hs]
    rw [Finset.sum_comm]
    simp only [hrow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Ne.symm hj']
    · simp
  simp only [BR, Fin.sum_univ_one]
  rw [hsum, trace_dual_mul]

theorem ev_dual (hJ : J.det ≠ 0) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    ∀ Y, (∀ X ∈ latGrp b v 1 M, BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F) ↔
      Y ∈ latGrp b v 1 M := by
  choose x hx using fun j k => BR_test b σ J hJ j k
  have h1 := (GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.1
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ j k i, inclR (Fv F v) (x j k i) ∈ intV b v := by
    simp only [Filter.eventually_all]; intro j k i; exact ev_incl b (x j k i)
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, inclR (Fv F v) (J i j) ∈ intV b v := by
    simp only [Filter.eventually_all]; intro i j; exact ev_incl b (J i j)
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (1 * b k)) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]; intro k; exact ev_int F _
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  obtain ⟨hone, hmul, hsig⟩ := hv1
  intro Y
  constructor
  · intro h
    rw [mem_latGrp]
    intro a j k
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    have hX : (fun (_ : Fin 1) i => inclR (Fv F v) (x j k i)) ∈ latGrp b v 1 M :=
      (mem_latGrp b v 1 M _).2 fun _ i => hv2 j k i
    have := h _ hX
    rw [hx j k (Fv F v) Y] at this
    exact this
  · intro hY X hX
    rw [mem_latGrp] at hX hY
    have key : ∀ y ∈ intV b v,
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F := by
      intro y hy
      have := trace_mul_eq b (Fv F v) 1 y
      rw [map_one, one_mul] at this
      rw [this]
      exact sum_mem fun k _ => mul_mem (hy k) (hv4 k)
    unfold BR
    refine sum_mem fun a _ => key _ ?_
    unfold hR Formalism.UG.hform
    refine GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun i _ =>
      GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun j _ => ?_
    exact hmul _ (hmul _ (hsig _ (hX a i)) _ (hv3 i j)) _ (hY a j)

end Alg

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, SdR (Fv F v) (psiV F ψ v) (s.nuV v) ∧ SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (tupMeas (s.lamV v) 1 M) := by
  intro F E _ _ _ _ _ σ hCM d b s ψ hψ M J hJ
  haveI : IsTotallyReal F := hCM.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨-, hloc, -⟩ := GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ
  have hex := GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hCM ψ hψ
  filter_upwards [hloc, ev_dual b σ J hJ.2] with v hv hdv
  refine ⟨?_, ?_⟩
  · obtain ⟨ν0, hν0, -⟩ := (hex v).1
    have hc : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := by
      have he : ((v.adicCompletionIntegers F : Set (Fv F v))) = Metric.closedBall 0 1 := by
        ext y
        simp [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
      rw [he]
      exact isCompact_closedBall 0 1
    refine selfDual_of_lattice hν0 (s.haar_nuV v) (v.adicCompletionIntegers F).toSubring.toAddSubgroup
      hc (Valued.isOpen_valuationSubring _) ?_ ?_ ?_ (s.nuV_int v)
    · intro x x' y
      show psiV F ψ v ((x + x') * y) = psiV F ψ v (x * y) * psiV F ψ v (x' * y)
      rw [add_mul, psiV_add]
    · intro y
      show psiV F ψ v (y * 0) = 1
      rw [mul_zero, psiV_zero]
    · intro y
      have hvy := hv y
      constructor
      · intro h
        apply hvy.1
        intro t ht
        rw [mul_comm]
        exact h t ht
      · intro h t ht
        rw [mul_comm]
        exact hvy.2 h t ht
  · obtain ⟨μ0, hμ0, -⟩ := (hex v).2 M J hJ
    haveI := s.haar_lamV v
    haveI hsf : SigmaFinite (s.lamV v) := by infer_instance
    haveI hH1 : (Measure.pi fun _ : Fin M => s.lamV v).IsAddHaarMeasure := by infer_instance
    haveI : SigmaFinite (Measure.pi fun _ : Fin M => s.lamV v) := by infer_instance
    have hH : (tupMeas (s.lamV v) 1 M).IsAddHaarMeasure := by
      unfold tupMeas; infer_instance
    have hsm : ∀ t ∈ v.adicCompletionIntegers F, ∀ X ∈ latGrp b v 1 M, t • X ∈ latGrp b v 1 M := by
      intro t ht X hX
      rw [mem_latGrp] at hX ⊢
      intro a i k
      have := hX a i k
      simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ht this
    refine selfDual_of_lattice hμ0 hH (latGrp b v 1 M) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [coe_latGrp]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        (GlobalTheory.GaugeEx.IntBasis.compact_open b v).1
    · rw [coe_latGrp]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
        (GlobalTheory.GaugeEx.IntBasis.compact_open b v).2
    · intro X X' Y
      show psiV F ψ v (BR (Fv F v) σ J (X + X') Y) =
        psiV F ψ v (BR (Fv F v) σ J X Y) * psiV F ψ v (BR (Fv F v) σ J X' Y)
      rw [BR_add, psiV_add]
    · intro Y
      show psiV F ψ v (BR (Fv F v) σ J Y 0) = 1
      rw [BR_zero, psiV_zero]
    · intro Y
      show (∀ X ∈ latGrp b v 1 M, psiV F ψ v (BR (Fv F v) σ J X Y) = 1) ↔ Y ∈ latGrp b v 1 M
      rw [← hdv Y]
      constructor
      · intro h X hX
        rw [← hv]
        intro t ht
        rw [← BR_smul]
        exact h _ (hsm t ht X hX)
      · intro h X hX
        have := (hv _).2 (h X hX) 1 (one_mem _)
        simpa using this
    · unfold tupMeas
      rw [coe_latGrp, Measure.pi_pi]
      simp [Measure.pi_pi, s.lamV_int v]

end GlobalTheory.GaugeEx.SelfDualAE
