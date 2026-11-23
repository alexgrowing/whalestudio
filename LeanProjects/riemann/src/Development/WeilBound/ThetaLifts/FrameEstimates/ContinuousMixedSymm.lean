import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (pure tens SInf evI At Rest Acts piW IsStd)
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.ThKEst.W

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Std
variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Std

section ReFi
open NumberField.mixedEmbedding
variable (F : Type) [Field F] [NumberField F]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

def re : mixedSpace F →+ AF F where
  toFun x := pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) 0
  map_zero' := Prod.ext (map_zero _) rfl
  map_add' x y := Prod.ext (map_add _ x y) (add_zero _).symm

def fi : Af F →+ AF F where
  toFun x := pairA F 0 x
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl

variable {F}

theorem re_mul (x y : mixedSpace F) : re F x * re F y = re F (x * y) := Prod.ext (map_mul _ x y).symm (mul_zero _)
theorem fi_mul (x y : Af F) : fi F x * fi F y = fi F (x * y) := Prod.ext (mul_zero _) rfl
theorem re_mul_fi (x : mixedSpace F) (y : Af F) : re F x * fi F y = 0 := Prod.ext (mul_zero _) (zero_mul _)
theorem mul_fi (x : AF F) (y : Af F) : x * fi F y = fi F (x.2 * y) := Prod.ext (mul_zero _) rfl
theorem evI_re (x : mixedSpace F) : evI F (re F x) = x := RingEquiv.apply_symm_apply _ x
theorem evI_fi (x : Af F) : evI F (fi F x) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
theorem evI_add (x y : AF F) : evI F (x + y) = evI F x + evI F y := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
theorem re_add_fi (x : AF F) : re F (evI F x) + fi F x.2 = x :=
  Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)
theorem continuous_re : Continuous (re F) := (continuous_mixedSymm F).prodMk continuous_const

theorem psi_re {ψ : AddChar (AF F) ℂ} (hstd : IsStd ψ) (x : mixedSpace F) :
    ψ (re F x) = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedSpace F) x : ℝ)) := by
  rw [hstd.2.2 (re F x), evI_re]
  intro u hu
  rw [smul_eq_mul, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]

end ReFi

section Tens
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem pure_eq (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    pure f φ = pureA F f (pf φ) := rfl

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem pure_mem (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    pure f φ ∈ schA F κ := Submodule.subset_span ⟨f, pf φ, pf_mem hφ, rfl⟩

end Tens

section Lift
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F))

def off (a : AF F) : AF F := a - atPlace v (evFin F v a)

theorem ev_off (a : AF F) : evFin F v (off v a) = 0 := by simp [off, evFin_atPlace]

theorem off_add (a b : AF F) : off v (a + b) = off v a + off v b := by simp only [off, map_add]; ring

theorem off_mul (a b : AF F) : off v (a * b) = a * off v b := by
  rw [off, off, mul_sub, mul_comm a (atPlace v _), atPlace_mul_right, map_mul, mul_comm (evFin F v a)]

theorem off_off (a : AF F) : off v (off v a) = off v a := by rw [off, ev_off, map_zero, sub_zero]

theorem at_mul_off (t : Fv F v) (a : AF F) : atPlace v t * off v a = 0 := by
  rw [atPlace_mul_right, ev_off, mul_zero, map_zero]

theorem off_add_at (a : AF F) : off v a + atPlace v (evFin F v a) = a := sub_add_cancel _ _

theorem off_dot (x y : κ → AF F) : off v (x ⬝ᵥ y) = x ⬝ᵥ fun i => off v (y i) := by
  simp only [off, dotProduct, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => off_mul v _ _

theorem ev_dot (x y : κ → AF F) : evFin F v (x ⬝ᵥ y) = (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := by
  simp only [dotProduct, map_sum, map_mul]

def Indep (r : (κ → AF F) → ℂ) : Prop := ∀ x (t : κ → Fv F v), r (x + fun i => atPlace v (t i)) = r x

variable {v}

theorem Indep.off {r : (κ → AF F) → ℂ} (h : Indep v r) (x : κ → AF F) : r (fun i => off v (x i)) = r x := by
  rw [← h _ fun i => evFin F v (x i)]
  congr 1
  funext i
  exact off_add_at v _

open Classical in
theorem pure_update (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ}
    (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u) (φ' : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v φ') = tens (evFin F v) φ' (pure f (Function.update φ v 1)) := by
  funext x
  obtain ⟨S, hS⟩ := exists_fin hφ fun i => sndA F (x i)
  have key : ∀ φ'' : (κ → Fv F v) → ℂ, pf (Function.update φ v φ'') (fun i => sndA F (x i)) =
      φ'' (fun i => evFin F v (x i)) * ∏ u ∈ S.erase v, φ u fun i => evFin F u (x i) := fun φ'' => by
    rw [pf_eq_prod (insert v (S.erase v)) _ fun u hu => ?_, Finset.prod_insert (Finset.notMem_erase _ _),
      Function.update_self]
    · congr 1
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
      rfl
    · have h1 : u ≠ v := fun e => hu (e ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne h1]
      exact hS u fun h => hu (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h1, h⟩))
  show f _ * pf _ (fun i => sndA F (x i)) = φ' _ * (f _ * pf _ (fun i => sndA F (x i)))
  rw [key, key, Pi.one_apply]
  ring

open Classical in
theorem indep_pure (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    Indep v (pure f (Function.update φ v 1)) := by
  intro x t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  · congr 1
    funext i
    show _ = evI F (x i)
    unfold evI
    congr 1
    exact add_zero _
  · refine finprod_congr fun u => ?_
    by_cases h : u = v
    · subst h; simp
    · refine congrArg _ (funext fun i => ?_)
      rw [Pi.add_apply, map_add]
      exact add_eq_left.2 (evalV_singleFin_ne h _)

open Classical in
theorem Good.update {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) {φ' : (κ → Fv F v) → ℂ}
    (h : φ' ∈ SB (κ → Fv F v)) : Good (Function.update φ v φ') := by
  refine ⟨fun u => ?_, ?_⟩
  · by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact hφ.1 u
  · filter_upwards [hφ.2, (Set.finite_singleton v).compl_mem_cofinite] with u hu e
    rwa [Function.update_of_ne e]

open Classical in
variable (v) in

def psv (ψ : AddChar (AF F) ℂ) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (atPlace v).toAddMonoidHom

theorem psv_apply (ψ : AddChar (AF F) ℂ) (t : Fv F v) : psv v ψ t = ψ (atPlace v t) := rfl

scoped instance invTwoV : Invertible (2 : Fv F v) :=
  ⟨evFin F v (⅟2), by rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one],
    by rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]⟩

variable (v) in

def evP (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) := (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

variable (v) in

def offP (w : (κ → AF F) × (κ → AF F)) : (κ → AF F) × (κ → AF F) := (fun i => off v (w.1 i), fun i => off v (w.2 i))

theorem schr_tens (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → Fv F v) → ℂ) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : schr ψ w (tens (evFin F v) φ r) =
      tens (evFin F v) (schr (psv v ψ) (evP v w) φ) (schr ψ (offP v w) r) := by
  funext x
  have e1 : r (x + w.1) = r (x + (offP v w).1) := by
    rw [← h (x + (offP v w).1) fun i => evFin F v (w.1 i)]
    congr 1
    funext i
    simp only [Pi.add_apply, offP, add_assoc, off_add_at]
  have e2 : ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      psv v ψ ((fun i => evFin F v (x i)) ⬝ᵥ (evP v w).2 + ⅟(2 : Fv F v) * ((evP v w).1 ⬝ᵥ (evP v w).2)) *
      ψ (x ⬝ᵥ (offP v w).2 + ⅟(2 : AF F) * ((offP v w).1 ⬝ᵥ (offP v w).2)) := by
    rw [psv_apply, ← AddChar.map_add_eq_mul, ← off_add_at v (x ⬝ᵥ w.2 + _), add_comm (off v _)]
    congr 2
    · rw [map_add, map_mul, ev_dot, ev_dot]; rfl
    · rw [off_add, off_mul, off_dot, ← off_off v (w.1 ⬝ᵥ w.2), off_dot v w.1 w.2, dotProduct_comm w.1, off_dot,
        dotProduct_comm (fun i => off v (w.2 i))]
      rfl
  simp only [schr, tens]
  rw [e1, e2]
  simp only [Pi.add_apply, map_add]
  show _ = _ * φ (fun i => evFin F v (x i) + evFin F v (w.1 i)) * _
  ring

theorem Indep.schr (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : Indep v (schr ψ (offP v w) r) := by
  intro x t
  simp only [GlobalTheory.WeilM.schr]
  rw [add_right_comm, h, add_dotProduct]
  congr 3
  refine add_eq_left.2 (Finset.sum_eq_zero fun i _ => at_mul_off v _ _)

theorem schr_zero {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (φ : (κ → R) → ℂ) :
    schr ψ 0 φ = φ := funext fun x => by simp [schr]

theorem schr_mem_SB {ψ : AddChar (Fv F v) ℂ} (hψ : Continuous ψ) (w : (κ → Fv F v) × (κ → Fv F v))
    {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) : schr ψ w φ ∈ SB (κ → Fv F v) := by
  haveI := nonarch_field (Fv F v)
  refine ⟨IsLocallyConstant.mul ((isLocallyConstant_addChar ψ hψ).comp_continuous (by fun_prop))
    (hφ.1.comp_continuous (continuous_add_const _)), HasCompactSupport.mul_left ?_⟩
  exact hφ.2.comp_homeomorph (Homeomorph.addRight _)

end Lift

section Split
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
open GlobalTheory.EmbChart (tensAt compFin_tensAt tensAt_mul_right tensAt_tmul)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)}

theorem hasSig_det {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  have e : (A.submatrix id finSumFinEquiv.symm)ᵀ * M * (A.map star).submatrix id finSumFinEquiv.symm =
      (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  have := congrArg det e
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_neg] at this
  simp only [mul_zero, zero_mul, det_one, one_mul, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

theorem hTens_tr {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem piW_tmul (t : E →ₐ[F] Fv F v) (a : AF F) (x : E) : piW t (a ⊗ₜ[F] x) = evFin F v a * t x := rfl

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x :=
  (piW_tmul t 1 x).trans (by rw [map_one, one_mul])

theorem piW_cA (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add]
  rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem ev_trace (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = piW t z + piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy]; ring
  | tmul a x =>
    rw [trace_tmul, map_mul, AlgHom.commutes, piW_tmul, piW_tmul, ← t.commutes, trace_cm h, map_add, mul_add]
    rfl

variable (v) in

def ep : AF F := atPlace v 1

theorem ep_mul (a : AF F) : ep v * a = atPlace v (evFin F v a) := by rw [ep, atPlace_mul_right, one_mul]

theorem ev_ep : evFin F v (ep v) = 1 := evFin_atPlace v 1

theorem off_eq (a : AF F) : off v a = (1 - ep v) * a := by rw [sub_mul, one_mul, ep_mul]; rfl

theorem ep_smul (z : AE F E) : ep v • z = tensAt E v (compFin F E v z) := by
  have := tensAt_mul_right (E := E) v 1 z
  rw [one_mul] at this
  rw [← this, Algebra.smul_def]
  rfl

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evFin F v) z ↔ ep v • z = z := by
  constructor
  · intro h
    have := h (1 - ep v) (by rw [map_sub, map_one, ev_ep, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro h a ha
    rw [← h, smul_smul, mul_comm, ep_mul, ha, map_zero, zero_smul]

def spM (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) : Matrix m n (AE F E) :=
  of fun i j => tensAt E v ((splitAlgEquiv h t).symm (A i j, B i j))

theorem spM_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (spM h t A B).map (piW t) = A := Matrix.ext fun i j => by
  show splitProj t (compFin F E v (tensAt E v _)) = _
  rw [compFin_tensAt, splitProj_symm]

theorem spM_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (spM h t A B).map (piW (t.comp σ)) = B := Matrix.ext fun i j => by
  show splitProj (t.comp σ) (compFin F E v (tensAt E v _)) = _
  rw [compFin_tensAt, splitProj_comp_symm]

theorem spM_off (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {m n : Type} (A B : Matrix m n (Fv F v)) :
    (1 - ep v) • spM h t A B = 0 := Matrix.ext fun i j => by
  show (1 - ep v) • tensAt E v _ = 0
  rw [sub_smul, one_smul, ep_smul, compFin_tensAt, sub_self]

theorem map_cA_piW (t : E →ₐ[F] Fv F v) {m n : Type} (y : Matrix m n (AE F E)) :
    (y.map (cA σ)).map (piW t) = y.map (piW (t.comp σ)) := Matrix.ext fun _ _ => piW_cA t _

theorem incM_piW (t : E →ₐ[F] Fv F v) {m n : Type} (J : Matrix m n E) : (incM F J).map (piW t) = J.map t :=
  Matrix.ext fun i j => by rw [map_apply, map_apply, incM, map_apply, piW_inc]

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def coB (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Matrix (Fin n) (Fin d) (Fv F v) := -(X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ)

theorem ev_symp (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (hX : ∀ i j, σ (X.J j i) = X.J i j)
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    evFin F v (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w') =
      trace (coB σ X W t w * (-w'.map (piW t))ᵀ) - trace (coB σ X W t w' * (-w.map (piW t))ᵀ) := by
  have a : ∀ t : E →ₐ[F] Fv F v, piW t (hTens (cA σ) (incM F X.J) (incM F W.J) w w') =
      trace ((w.map (piW t))ᵀ * X.J.map t * w'.map (piW (t.comp σ)) * (W.J.map t)ᵀ) := fun t => by
    rw [hTens_tr, AddMonoidHom.map_trace (piW t), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, transpose_map, transpose_map,
      incM_piW, incM_piW, map_cA_piW]
  have b1 : X.J.map (t.comp σ) = (X.J.map t)ᵀ := Matrix.ext fun i j => congrArg t (hX j i)
  have b2 : (W.J.map (t.comp σ))ᵀ = -W.J.map t := Matrix.ext fun i j => (congrArg t (hW i j)).trans (map_neg t _)
  rw [symp, ev_trace h t, map_mul, map_mul, a, a, comp_conj_conj h, b1, b2, coB, coB]
  generalize w.map (piW t) = A
  generalize w'.map (piW t) = A'
  generalize w.map (piW (t.comp σ)) = B
  generalize w'.map (piW (t.comp σ)) = B'
  generalize X.J.map t = P
  generalize W.J.map t = Q
  have c1 : trace (P * B * Qᵀ * A'ᵀ) = trace (Bᵀ * Pᵀ * A' * Q) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
      ← Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have c2 : trace (P * B' * Qᵀ * Aᵀ) = trace (Aᵀ * P * B' * Qᵀ) := by
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, c1, c2, map_neg, map_one, trace_neg]
  ring

end Split

section Gen
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : HeightOneSpectrum (𝓞 F)}

theorem cont_at : Continuous (atPlace (F := F) v) := continuous_const.prodMk (continuous_singleFin v)

theorem cont_evI : Continuous (evI F) :=
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    ((continuous_apply w.1).comp continuous_fst)).prodMk
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
    ((continuous_apply w.1).comp continuous_fst))

end Gen

section PartB
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem offP_eq {κ : Type} (w : (κ → AF F) × (κ → AF F)) : offP v w = (1 - ep v) • w :=
  Prod.ext (funext fun _ => off_eq _) (funext fun _ => off_eq _)

end PartB

end PositivityTheory.ThKEst.W
end
