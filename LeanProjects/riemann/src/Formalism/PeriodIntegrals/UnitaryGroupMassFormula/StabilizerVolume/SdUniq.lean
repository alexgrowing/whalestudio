import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabS

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def TestEx {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  ∃ Φ : V → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ ∧ ∃ z, Φ (-z) ≠ 0

theorem eq_of_testEx {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (hT : TestEx μ χ) : μ = ν := by
  obtain ⟨hHμ, hμi⟩ := hμ
  obtain ⟨hHν, hνi⟩ := hν
  haveI := hHμ
  haveI := hHν
  obtain ⟨Φ, hc, hcs, hi, z, hz⟩ := hT
  obtain ⟨c, hνμ⟩ : ∃ c : NNReal, ν = c • μ := by
    first
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩
    | exact ⟨_, Measure.isAddHaarMeasure_eq_smul ν μ⟩
  have e1 := hμi Φ hc hcs hi z
  have hsm : ∀ w : ℂ, c • w = ((c : ℝ) : ℂ) * w := by
    intro w
    first
    | rw [NNReal.smul_def, Complex.real_smul]
    | simp [NNReal.smul_def]
  have hTν : ∀ y, ∫ x, Φ x * χ x y ∂ν = ((c : ℝ) : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [hνμ, integral_smul_nnreal_measure, hsm]
  have hiν : Integrable (fun y => ∫ x, Φ x * χ x y ∂ν) ν := by
    simp_rw [hTν]
    rw [hνμ]
    first
    | exact (hi.const_mul _).smul_measure_nnreal
    | exact (hi.const_mul _).smul_measure ENNReal.coe_ne_top
  have e2 := hνi Φ hc hcs hiν z
  simp_rw [hTν] at e2
  rw [hνμ, integral_smul_nnreal_measure, hsm] at e2
  simp_rw [mul_assoc, integral_const_mul] at e2
  rw [e1] at e2
  have h4 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have h3 : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * Φ (-z) = 0 := by linear_combination e2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hz
  have h5 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h7 : c = 1 := by exact_mod_cast h6
  rw [hνμ, h7, one_smul]

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)

include hχ in

theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ (L : Set V)
  · rw [Set.indicator_of_mem hy]
    have hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ L
      · simp [Set.indicator_apply, hx, hy x hx]
      · simp [Set.indicator_apply, hx]
    rw [hfun, integral_indicator_const _ hLo.measurableSet]
    simp [Measure.real]
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f (x0 + x) ∂μ = ∫ x, f x ∂μ := integral_add_left_eq_self (μ := μ) f x0
    have hshift : ∀ x, f (x0 + x) = χ x0 y * f x := by
      intro x
      simp only [hf]
      rw [hχ x x0 y]
      by_cases hx : x ∈ L
      · have hx' : x0 + x ∈ L := L.add_mem hx0 hx
        simp [Set.indicator_apply, hx, hx']
      · have hx' : x0 + x ∉ L := fun h => hx (by simpa using L.sub_mem h hx0)
        simp [Set.indicator_apply, hx, hx']
    simp_rw [hshift, integral_const_mul] at key
    have h2 : (χ x0 y - 1) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

include hχ in

theorem testEx_of_lattice (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hA : IsClosed (ann χ L)) (K : Set V) (hK : IsCompact K) (hAK : ann χ L ⊆ K) :
    TestEx μ χ := by
  classical
  have hLcl : IsClosed (L : Set V) := hLc.isClosed
  refine ⟨(L : Set V).indicator (fun _ => (1 : ℂ)), ?_, ?_, ?_, ⟨0, ?_⟩⟩
  · first
    | exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const
    | exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn
  · exact HasCompactSupport.intro hLc (fun x hx => by simp [Set.indicator_apply, hx])
  · have hT : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) =
        (ann χ (L : Set V)).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) := by
      funext y
      exact transform_indicator μ χ hχ L hLo y
    rw [hT]
    have hfin : μ (ann χ (L : Set V)) < ⊤ := (measure_mono hAK).trans_lt hK.measure_lt_top
    refine IntegrableOn.integrable_indicator ?_ hA.measurableSet
    first
    | exact integrableOn_const.2 (Or.inr hfin)
    | exact integrableOn_const hfin.ne
    | exact integrableOn_const_iff.2 (Or.inr hfin)
  · simp [Set.indicator_apply, L.zero_mem]

end Lattice

def AnnAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (χ : V → V → ℂ) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsClosed (ann χ L) ∧
    ∃ K, IsCompact K ∧ ann χ L ⊆ K

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

theorem testEx_of_trivial (hχ : ∀ x y, χ x y = 1) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) : TestEx μ χ := by
  classical
  have hLcl : IsClosed (L : Set V) := hLc.isClosed
  have hind : Continuous ((L : Set V).indicator (fun _ => (1 : ℂ))) := by
    first
    | exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const
    | exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hint : Integrable ((L : Set V).indicator (fun _ => (1 : ℂ))) μ := by
    refine IntegrableOn.integrable_indicator ?_ hLo.measurableSet
    first
    | exact integrableOn_const.2 (Or.inr hfin)
    | exact integrableOn_const hfin.ne
    | exact integrableOn_const_iff.2 (Or.inr hfin)
  by_cases hL : ∀ t, t ∈ L
  · haveI : IsFiniteMeasure μ := ⟨(measure_mono (fun x _ => hL x)).trans_lt hfin⟩
    refine ⟨fun _ => 1, continuous_const, HasCompactSupport.intro hLc (fun x hx => absurd (hL x) hx), ?_, ⟨0, one_ne_zero⟩⟩
    simp only [hχ, mul_one]
    exact integrable_const _
  · push_neg at hL
    obtain ⟨t, ht⟩ := hL
    set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg
    have hcg : Continuous fun x => g (-t + x) := hind.comp' (continuous_add_left (-t))
    refine ⟨fun x => g x - g (-t + x), hind.sub hcg, ?_, ?_, ⟨0, ?_⟩⟩
    · refine HasCompactSupport.intro (hLc.union (hLc.image (continuous_add_left t))) ?_
      intro x hx
      have h1 : x ∉ L := fun h => hx (Or.inl h)
      have h2 : -t + x ∉ L := fun h => hx (Or.inr ⟨-t + x, h, by abel⟩)
      simp [hg, Set.indicator_apply, h1, h2]
    · have h0 : ∀ y, ∫ x, (g x - g (-t + x)) * χ x y ∂μ = 0 := by
        intro y
        simp only [hχ, mul_one]
        rw [integral_sub hint (hint.comp_add_left (-t)), integral_add_left_eq_self (μ := μ) g (-t), sub_self]
      simp only [h0]
      exact integrable_zero _ _ _
    · have hn : -t ∉ L := fun h => ht (by simpa using L.neg_mem h)
      simp [hg, Set.indicator_apply, hn, ht, L.zero_mem]

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  have hr0 : r0 ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)
  by_cases ht0 : t = 0
  · exact ⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (t / r0) with h | h
  · refine ⟨t / r0, h, ?_⟩
    show r0 * (t / r0) = t
    field_simp
  · exfalso
    apply h0
    have h1 := ht _ h
    have e : (t / r0)⁻¹ * t = r0 := by field_simp
    rwa [e] at h1

theorem annAt_of_dual {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v)
    (ψ0 : Fv F v → ℂ) (hψ : Continuous ψ0) (hB : ∀ x, Continuous (B x)) (r0 : Fv F v)
    (h0 : ψ0 r0 ≠ 1) (hD : DualAt v B) : AnnAt (fun x y => ψ0 (B x y)) := by
  obtain ⟨L, hLc, hLo, hst, hdual⟩ := hD
  obtain ⟨K, hK, hsub⟩ := hdual r0
  refine ⟨L, hLc, hLo, ?_, K, hK, ?_⟩
  · have hE : ann (fun x y => ψ0 (B x y)) (L : Set V) =
        ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1} := by
      ext y
      simp [ann]
    rw [hE]
    exact isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))
  · intro y hy
    refine hsub (fun x hx => ?_)
    refine mem_of_psi v ψ0 r0 (B x y) h0 (fun s hs => ?_)
    obtain ⟨x', hx', hB'⟩ := hst s hs x hx
    rw [← hB' y]
    exact hy x' hx'

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  unfold singleV
  first
  | exact RestrictedProduct.single_add _ v r s
  | (ext w
     by_cases hw : w = v
     · subst hw; simp [RestrictedProduct.single]
     · simp [RestrictedProduct.single, hw])

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have e : pairA F 0 (singleV F v (r + s)) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [singleV_add]
    rw [show (pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) : AF F) =
      pairA F (0 + 0) (singleV F v r + singleV F v s) from rfl, add_zero]
  show ψ (pairA F 0 (singleV F v (r + s))) =
    ψ (pairA F 0 (singleV F v r)) * ψ (pairA F 0 (singleV F v s))
  rw [e, AddChar.map_add_eq_mul]

theorem psiInf_add (ψ : AddChar (AF F) ℂ) (r s : Ainf F) :
    psiInf F ψ (r + s) = psiInf F ψ r * psiInf F ψ s := by
  have e : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0 := by
    rw [show (pairA F r 0 + pairA F s 0 : AF F) = pairA F (r + s) (0 + 0) from rfl, add_zero]
  show ψ (pairA F (r + s) 0) = ψ (pairA F r 0) * ψ (pairA F s 0)
  rw [e, AddChar.map_add_eq_mul]

theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let s0 : Fv F v → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) := fun y =>
    ⟨Pi.single v y, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have hc : Continuous s0 := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      exact continuous_id.congr fun y => (Pi.single_eq_same _ _).symm
    · exact (continuous_const (y := (0 : Fv F w))).congr fun y => (Pi.single_eq_of_ne hw y).symm
  have e : singleV F v = fun y => RestrictedProduct.inclusion _ _ hS (s0 y) := by
    funext y
    apply RestrictedProduct.ext
    intro j
    rfl
  rw [e]
  exact (RestrictedProduct.continuous_inclusion hS).comp hc

theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  first
  | exact hψ.comp (continuous_const.prodMk (continuous_singleV (F := F) v))
  | exact hψ.comp (continuous_const.prod_mk (continuous_singleV (F := F) v))

variable (R : Type) [CommRing R] [Algebra F R]

theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  first
  | simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  | simp [BR, hR, Formalism.UG.hform, map_add, add_mul, Finset.sum_add_distrib]

theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  first
  | simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]
  | simp [pairHerm, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))
  | exact IsModuleTopology.continuous_of_linearMap _
  | exact LinearMap.continuous_of_finiteDimensional _
  | fun_prop

theorem continuous_BR_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Continuous (BR R σ J X) := by
  have ht := continuous_trace_tens (F := F) (E := E) R
  unfold BR hR Formalism.UG.hform
  first
  | exact continuous_finset_sum _ fun a _ => ht.comp (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))
  | fun_prop

theorem continuous_pairHerm_right (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) :
    Continuous (pairHerm R σ n S) := by
  have ht := continuous_trace_tens (F := F) (E := E) R
  unfold pairHerm
  first
  | exact continuous_const.mul (ht.comp (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      continuous_const.mul ((continuous_apply a).comp ((continuous_apply b).comp continuous_subtype_val))))
  | fun_prop

end ContY

end SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

def SdTestInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ →
      TestEx μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν →
      TestEx ν (fun S T => psiInf F ψ (pairHerm (Ainf F) σ a S T)))

def SdTestV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ →
      TestEx μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν →
      TestEx ν (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)))

def AnnV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    AnnAt (V := Fin a → Fin M → Fv F v ⊗[F] E) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
    AnnAt (V := HermR (Fv F v) σ a) (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T))

def DualLatV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F),
    DualAt v (BR (Fv F v) σ J (n := a)) ∧ DualAt v (pairHerm (Fv F v) σ a)

theorem sdTestV_of_dual (h : DualLatV) : SdTestV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hDW, hDH⟩ := h F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  by_cases hψv : ∃ r, psiV F ψ v r ≠ 1
  · obtain ⟨r0, h0⟩ := hψv
    have hc := continuous_psiV ψ hψ.1 v
    obtain ⟨L, hLc, hLo, hA, K, hK, hAK⟩ :=
      annAt_of_dual v _ _ hc (fun X => continuous_BR_right (Fv F v) σ J X) r0 h0 hDW
    obtain ⟨L', hLc', hLo', hA', K', hK', hAK'⟩ :=
      annAt_of_dual v _ _ hc (fun S => continuous_pairHerm_right (Fv F v) σ a S) r0 h0 hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_lattice μ _ (fun X T Y => by rw [BR_add, psiV_add]) L hLc hLo
        hA K hK hAK
    · have := hν.1
      exact testEx_of_lattice ν _ (fun S T U => by rw [pairHerm_add, psiV_add]) L'
        hLc' hLo' hA' K' hK' hAK'
  · simp only [not_exists, not_not] at hψv
    obtain ⟨L, hLc, hLo, -⟩ := hDW
    obtain ⟨L', hLc', hLo', -⟩ := hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_trivial μ _ (fun _ _ => hψv _) L hLc hLo
    · have := hν.1
      exact testEx_of_trivial ν _ (fun _ _ => hψv _) L' hLc' hLo'

theorem sdUniq_of (hI : SdTestInf) (hV : SdTestV) : SdUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hIW, hIH⟩ := hI F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  refine ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hIW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hIH ν1 e1), fun v => ?_⟩
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hVW, hVH⟩ := hV F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hVW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hVH ν1 e1)⟩

theorem sdUniq_of_dual (hI : SdTestInf) (hD : DualLatV) : SdUniq := sdUniq_of hI (sdTestV_of_dual hD)

end PI.VolStabS
