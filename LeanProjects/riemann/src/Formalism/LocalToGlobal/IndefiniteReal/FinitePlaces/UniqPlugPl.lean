import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SecondCharacterFact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  IsDedekindDomain NumberField Topology Filter Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin.Refl

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : AF F} (h1 : ∀ w, x.1 w = y.1 w) (h2 : ∀ v, x.2 v = y.2 v) : x = y := Prod.ext (funext h1) (by ext v; exact congrArg _ (h2 v))

def piF (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piI (w : InfinitePlace F) : AF F →+* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def jF (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : AF F := pairA F 0 (single v y)

open Classical in

def jI (w : InfinitePlace F) (y : w.Completion) : AF F :=
  pairA F (Pi.single w y : ∀ w : InfinitePlace F, w.Completion) 0

theorem jF_fst (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) (w : InfinitePlace F) : (jF v y).1 w = 0 := rfl
theorem jF_self (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : (jF v y).2 v = y := by
  classical
  show (Pi.single v y : ∀ v' : HeightOneSpectrum (𝓞 F), v'.adicCompletion F) v = y
  exact Pi.single_eq_same v y
theorem jF_ne {v v' : HeightOneSpectrum (𝓞 F)} (y : v.adicCompletion F) (h : v' ≠ v) : (jF v y).2 v' = 0 := by
  classical
  show (Pi.single v y : ∀ v'' : HeightOneSpectrum (𝓞 F), v''.adicCompletion F) v' = 0
  exact Pi.single_eq_of_ne h y
theorem jI_snd (w : InfinitePlace F) (y : w.Completion) (v : HeightOneSpectrum (𝓞 F)) : (jI w y).2 v = 0 := rfl
open Classical in
theorem jI_self (w : InfinitePlace F) (y : w.Completion) : (jI w y).1 w = y := by simp [jI, pairA]
open Classical in
theorem jI_ne {w w' : InfinitePlace F} (y : w.Completion) (h : w' ≠ w) : (jI w y).1 w' = 0 := by simp [jI, pairA, Pi.single_eq_of_ne h]

theorem mul_jF (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (y : v.adicCompletion F) :
    a * jF v y = jF v (piF v a * y) := by
  refine af_ext (fun w => ?_) (fun v' => ?_)
  · show a.1 w * (jF v y).1 w = (jF v (piF v a * y)).1 w
    rw [jF_fst, jF_fst, mul_zero]
  · show a.2 v' * (jF v y).2 v' = (jF v (piF v a * y)).2 v'
    by_cases h : v' = v
    · subst h
      rw [jF_self, jF_self]
      rfl
    · rw [jF_ne _ h, jF_ne _ h, mul_zero]

theorem mul_jI (w : InfinitePlace F) (a : AF F) (y : w.Completion) : a * jI w y = jI w (piI w a * y) := by
  refine af_ext (fun w' => ?_) (fun v => ?_)
  · show a.1 w' * (jI w y).1 w' = (jI w (piI w a * y)).1 w'
    by_cases h : w' = w
    · subst h
      rw [jI_self, jI_self]
      rfl
    · rw [jI_ne _ h, jI_ne _ h, mul_zero]
  · show a.2 v * (jI w y).2 v = (jI w (piI w a * y)).2 v
    rw [jI_snd, jI_snd, mul_zero]

theorem continuous_piF (v : HeightOneSpectrum (𝓞 F)) : Continuous (piF v) := (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_piI (w : InfinitePlace F) : Continuous (piI w) := (continuous_apply w).comp continuous_fst

theorem tendsto_fin {α : Type*} {l : Filter α} (z : α → Af F)
    (h : ∀ N : ℕ, N ≠ 0 → ∀ᶠ t in l, ∀ v, ‖z t v‖ ≤ ‖(N : v.adicCompletion F)‖) : Tendsto z l (𝓝 0) := by
  intro U hU
  obtain ⟨N, hN, hNU⟩ := finNhd U hU
  rw [Filter.mem_map]
  filter_upwards [h N (by omega)] with t ht
  obtain ⟨y, hy, e⟩ := int_of_le (z t) N 1 (by omega) fun v => by rw [Nat.cast_one, norm_one, mul_one]; exact ht v
  show z t ∈ U
  rw [e]; exact hNU y hy

theorem continuous_single (v : HeightOneSpectrum (𝓞 F)) : Continuous (single v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let s' : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal {v}ᶜ) :=
    fun y => RestrictedProduct.mk (Pi.single v y) (by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Set.mem_compl_singleton_iff] at hw
      rw [Pi.single_eq_of_ne hw]
      exact zero_mem _)
  have hs' : Continuous s' := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases h : w = v
    · subst h
      show Continuous (fun y : w.adicCompletion F =>
        (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F) w)
      simp only [Pi.single_eq_same]
      exact continuous_id
    · show Continuous (fun y : v.adicCompletion F =>
        (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F) w)
      simp only [Pi.single_eq_of_ne h]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hs'

theorem continuous_jF (v : HeightOneSpectrum (𝓞 F)) : Continuous (jF v) := continuous_const.prodMk (continuous_single v)

open Classical in
theorem continuous_jI (w : InfinitePlace F) : Continuous (jI w) := (_root_.continuous_single w).prodMk continuous_const

theorem dense_F (v : HeightOneSpectrum (𝓞 F)) : DenseRange fun q : F => piF v (algebraMap F (AF F) q) := by
  have h : (fun q : F => piF v (algebraMap F (AF F) q)) = algebraMap F (v.adicCompletion F) := by
    funext q
    show (algebraMap F (AF F) q).2 v = _
    rw [algebraMap_AF]
    rfl
  rw [h]
  exact HeightOneSpectrum.denseRange_algebraMap F v

theorem dense_I (w : InfinitePlace F) : DenseRange fun q : F => piI w (algebraMap F (AF F) q) := by
  have h : (fun q : F => piI w (algebraMap F (AF F) q)) = fun x : F => ({ toCompletion := ↑x } : w.Completion) := by
    funext q
    show (algebraMap F (AF F) q).1 w = _
    rw [algebraMap_AF]
    rfl
  rw [h]
  have e : Set.range (fun x : F => ({ toCompletion := ↑(WithAbs.toAbs w.1 x) } : w.Completion)) =
      Set.range (fun x : WithAbs w.1 => ({ toCompletion := ↑x } : w.Completion)) :=
    (WithAbs.toAbs_surjective w.1).range_comp (fun x : WithAbs w.1 => ({ toCompletion := ↑x } : w.Completion))
  unfold DenseRange
  erw [e]
  exact InfinitePlace.Completion.denseRange_coe w

def etaS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := ∑ w : InfinitePlace F, jI w 1 + ∑ v ∈ S, jF v 1

theorem etaS_fst (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) : piI w (etaS S) = 1 := by
  rw [etaS, map_add, map_sum, map_sum, Finset.sum_eq_single w]
  · rw [show piI w (jI w 1) = (jI w 1).1 w from rfl, jI_self]
    simp only [show ∀ v, piI w (jF v 1) = (jF v 1).1 w from fun v => rfl, jF_fst, Finset.sum_const_zero, add_zero]
  · intro w' _ hw'
    show (jI w' 1).1 w = 0
    exact jI_ne _ (Ne.symm hw')
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem etaS_in (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    piF v (etaS S) = 1 := by
  rw [etaS, map_add, map_sum, map_sum, Finset.sum_eq_single v]
  · simp only [show ∀ w, piF v (jI w 1) = (jI w 1).2 v from fun w => rfl, jI_snd, Finset.sum_const_zero, zero_add]
    show (jF v 1).2 v = 1
    exact jF_self v 1
  · intro v' _ hv'
    show (jF v' 1).2 v = 0
    exact jF_ne _ (Ne.symm hv')
  · intro h
    exact absurd hv h

theorem etaS_out (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    piF v (etaS S) = 0 := by
  rw [etaS, map_add, map_sum, map_sum]
  simp only [show ∀ w, piF v (jI w 1) = (jI w 1).2 v from fun w => rfl, jI_snd, Finset.sum_const_zero, zero_add]
  refine Finset.sum_eq_zero fun v' hv' => ?_
  show (jF v' 1).2 v = 0
  exact jF_ne _ (fun h => hv (h ▸ hv'))

theorem tendsto_etaS (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => etaS S * a) atTop (𝓝 a) := by
  classical
  have h1 : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (etaS S * a).1 = a.1 := fun S => funext fun w => by
    show piI w (etaS S) * a.1 w = a.1 w
    rw [etaS_fst, one_mul]
  have h2 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (etaS S * a).2 - a.2) atTop (𝓝 0) := by
    refine tendsto_fin _ fun N hN => ?_
    obtain ⟨S1, hS1⟩ := exists_finset_norm_one (N : F) (Nat.cast_ne_zero.2 hN)
    have hfin := Filter.eventually_cofinite.mp a.2.2
    filter_upwards [Filter.eventually_ge_atTop (S1 ∪ hfin.toFinset)] with S hS v
    show ‖piF v (etaS S) * a.2 v - a.2 v‖ ≤ _
    by_cases hv : v ∈ S
    · rw [etaS_in S v hv, one_mul, sub_self, norm_zero]; exact norm_nonneg _
    · have hv1 : v ∉ S1 := fun h => hv (hS (Finset.mem_union_left _ h))
      have hv2 : v ∉ hfin.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
      have hN1 := hS1 v hv1
      rw [map_natCast] at hN1
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv2
      rw [etaS_out S v hv, zero_mul, zero_sub, norm_neg, hN1]
      exact (norm_le_one_iff_int v _).2 hv2
  have h3 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ((a.1, (etaS S * a).2) : Ainf F × Af F)) atTop
      (𝓝 (a.1, a.2)) := tendsto_const_nhds.prodMk_nhds (tendsto_sub_nhds_zero_iff.1 h2)
  have h4 : (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ((a.1, (etaS S * a).2) : Ainf F × Af F)) =
      fun S => etaS S * a := funext fun S => Prod.ext (h1 S).symm rfl
  rw [h4] at h3
  exact h3

theorem not_sq_inf {E : Type} [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] (δ : E) (hδ0 : δ ≠ 0)
    (hδ : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) (Δ : F) (hΔ : algebraMap F E Δ = δ * δ)
    (w : InfinitePlace F) (s : w.Completion) : s * s ≠ algebraMap F w.Completion Δ := by
  intro hs
  let ρ : w.Completion →+* ℝ := InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  let ψ : F →+* ℂ := Complex.ofRealHom.comp (ρ.comp (algebraMap F w.Completion))
  let φ : E →+* ℂ := ComplexEmbedding.lift E ψ
  have h1 : φ δ * φ δ = ((ρ s * ρ s : ℝ) : ℂ) := by
    rw [← map_mul, ← hΔ, ← map_mul, hs]
    exact ComplexEmbedding.lift_algebraMap_apply E ψ Δ
  have h2 : (φ δ).re = 0 := by
    have := congrArg Complex.re (hδ φ)
    rw [Complex.conj_re, Complex.neg_re] at this
    linarith
  have h3 : (φ δ).im = 0 := by
    have := congrArg Complex.re h1
    rw [Complex.mul_re, h2, Complex.ofReal_re] at this
    nlinarith [mul_self_nonneg (ρ s), mul_self_nonneg (φ δ).im]
  exact (map_ne_zero φ).2 hδ0 (Complex.ext h2 h3)

end Formalism.IndefR.Fin.Refl

end
