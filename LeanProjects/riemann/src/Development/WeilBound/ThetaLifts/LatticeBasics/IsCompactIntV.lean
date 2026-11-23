import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open scoped TensorProduct NNReal Matrix SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

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

theorem isOpen_intV (u : HeightOneSpectrum (𝓞 F)) : IsOpen {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (continuous_apply i)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

def intV (κ : Type) [Fintype κ] (u : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (κ → Fv F u) where
  carrier := {x | ∀ i, x i ∈ u.adicCompletionIntegers F}
  add_mem' h h' i := add_mem (h i) (h' i)
  zero_mem' _ := zero_mem _
  neg_mem' h i := neg_mem (h i)
  isOpen' := isOpen_intV u

theorem stdF_mem (u : HeightOneSpectrum (𝓞 F)) : stdF κ u ∈ SB (κ → Fv F u) :=
  GlobalTheory.WeilM.HaarUniq.indicator_mem (intV κ u) (isCompact_intV u)

theorem good_std : Good (stdF (F := F) κ) := ⟨stdF_mem, .of_forall fun _ => rfl⟩

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

def box (K : ∀ u : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (κ → Fv F u)) (h : ∀ᶠ u in cofinite, K u = intV κ u)
    (h' : ∀ u, K u ≤ intV κ u) : OpenAddSubgroup (κ → Af F) where
  carrier := {y | ∀ u, (fun i => evalV F u (y i)) ∈ K u}
  add_mem' {a b} ha hb u := by
    have := add_mem (ha u) (hb u)
    simp only [Pi.add_apply, map_add]
    exact this
  zero_mem' u := by
    simp only [Pi.zero_apply, map_zero]
    exact zero_mem (K u)
  neg_mem' {a} ha u := by
    have := neg_mem (ha u)
    simp only [Pi.neg_apply, map_neg]
    exact this
  isOpen' := by
    have e : {y : κ → Af F | ∀ u, (fun i => evalV F u (y i)) ∈ K u} =
        (⋂ i, {y | ∀ v, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ∩
          ⋂ u ∈ {u | ¬ K u = intV κ u}, {y | (fun i => evalV F u (y i)) ∈ K u} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun H => ⟨fun i v => h' v (H v) i, fun u _ => H u⟩, fun H u => ?_⟩
      by_cases hu : K u = intV κ u
      · rw [hu]; exact fun i => H.1 i u
      · exact H.2 u hu
    rw [e]
    exact (isOpen_iInter_of_finite fun i => isOpen_intAf.preimage (continuous_apply i)).inter
      (Set.Finite.isOpen_biInter h fun u _ => (K u).isOpen.preimage
        (continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)))

theorem exists_box {W : Set (κ → Af F)} (hW : W ∈ 𝓝 0) : ∃ K h h', ((box (F := F) (κ := κ) K h h' : OpenAddSubgroup (κ → Af F)) : Set (κ → Af F)) ⊆ W := by
  classical
  let j : (∀ u : HeightOneSpectrum (𝓞 F), intV κ u) → κ → Af F := fun x i =>
    RestrictedProduct.structureMap (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) cofinite fun u => ⟨(x u).1 i, (x u).2 i⟩
  have hj : Continuous j := continuous_pi fun i => RestrictedProduct.isEmbedding_structureMap.continuous.comp
    (continuous_pi fun u => Continuous.subtype_mk (f := fun x : ∀ u, intV κ u => (x u).1 i) ((continuous_apply i).comp
      ((continuous_subtype_val (p := fun x => x ∈ intV κ u)).comp (continuous_apply (A := fun u => intV κ u) u))) _)
  have h0 : j ⁻¹' W ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (by convert hW; rfl)
  obtain ⟨U, hUW, hUo, hU0⟩ := mem_nhds_iff.1 h0
  obtain ⟨I₀, s₀, hs₀, hs₁⟩ := isOpen_pi_iff.1 hUo 0 hU0
  let I : Set (HeightOneSpectrum (𝓞 F)) := I₀
  have hI : I.Finite := I₀.finite_toSet
  let t : ∀ u : HeightOneSpectrum (𝓞 F), Set (intV κ u) := fun u => if u ∈ I₀ then s₀ u else Set.univ
  have ht : ∀ u, t u ∈ 𝓝 (0 : intV κ u) := fun u => by
    by_cases hu : u ∈ I₀
    · simp only [t, if_pos hu]
      exact (hs₀ u hu).1.mem_nhds (hs₀ u hu).2
    · simp only [t, if_neg hu, univ_mem]
  have hs : I.pi t ⊆ j ⁻¹' W := fun x hx => hUW (hs₁ fun u hu => by
    simpa only [t, if_pos (Finset.mem_coe.1 hu)] using hx u hu)
  have : ∀ u, ∃ K : OpenAddSubgroup (κ → Fv F u), ∀ x : intV κ u, x.1 ∈ K → x ∈ t u := fun u => by
    have := ht u
    rw [nhds_subtype, mem_comap] at this
    obtain ⟨s, hs, hst⟩ := this
    obtain ⟨K, hK⟩ := (nonarch_pi (Fv F u) κ).is_nonarchimedean s hs
    exact ⟨K, fun x hx => hst (hK hx)⟩
  choose K hK using this
  refine ⟨fun u => if u ∈ I then K u ⊓ intV κ u else intV κ u, ?_, fun u => ?_, fun y hy => ?_⟩
  · filter_upwards [hI.compl_mem_cofinite] with u hu using if_neg hu
  · simp only
    split_ifs
    · exact inf_le_right
    · exact le_rfl
  · have h1 : ∀ u, (fun i => evalV F u (y i)) ∈ intV κ u := fun u => by
      have := hy u
      simp only at this
      split_ifs at this
      · exact this.2
      · exact this
    refine hs (a := fun u => ⟨_, h1 u⟩) fun u hu => hK u _ ?_
    have := hy u
    simp only [if_pos hu] at this
    exact this.1

theorem mem_span_pf {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    g ∈ Submodule.span ℂ {h | ∃ φ, Good φ ∧ h = pf φ} := by
  haveI : NonarchimedeanAddGroup (κ → Af F) := ⟨fun W hW => by
    obtain ⟨K, h, h', hs⟩ := exists_box hW
    exact ⟨_, hs⟩⟩
  obtain ⟨K₀, hK₀⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hg
  obtain ⟨K, h, h', hs⟩ := exists_box K₀.mem_nhds_zero
  obtain ⟨S, hS⟩ := GlobalTheory.WeilM.HaarUniq.exists_decomp (box K h h') hg.2 fun k hk => hK₀ k (hs hk)
  rw [hS]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  generalize q.out = a
  have hG : Good fun u x => Set.indicator (K u : Set (κ → Fv F u)) (fun _ => (1 : ℂ)) (x + -fun i => evalV F u (a i)) := by
    constructor
    · intro u
      have := GlobalTheory.WeilM.HaarUniq.indicator_mem (K u) ((isCompact_intV u).of_isClosed_subset (K u).isClosed (h' u))
      exact ⟨this.1.comp_continuous (continuous_add_const _), this.2.comp_homeomorph (Homeomorph.addRight _)⟩
    · filter_upwards [h, ev_int a] with u hu ha
      funext x
      rw [hu]
      have ha' : (-fun i => evalV F u (a i)) ∈ intV κ u := neg_mem (show _ ∈ intV κ u from ha)
      by_cases hx : x ∈ intV κ u
      · rw [Set.indicator_of_mem (add_mem hx ha'), stdF, Set.indicator_of_mem (by exact hx)]; rfl
      · rw [Set.indicator_of_notMem (by rwa [SetLike.mem_coe, add_mem_cancel_right ha']), stdF,
          Set.indicator_of_notMem (by exact hx)]
  refine ⟨_, hG, funext fun y => ?_⟩
  have e : ∀ u, ((fun i => evalV F u (y i)) + -fun i => evalV F u (a i)) = fun i => evalV F u ((y + -a) i) := fun u => by
    funext i; simp
  by_cases hy : y + -a ∈ box K h h'
  · rw [Set.indicator_of_mem (by exact hy), pf, eq_comm]
    refine finprod_eq_one_of_forall_eq_one fun u => ?_
    rw [e, Set.indicator_of_mem (by exact hy u)]
  · rw [Set.indicator_of_notMem (by exact hy)]
    obtain ⟨u, hu⟩ := not_forall.1 hy
    obtain ⟨S, hS⟩ := exists_fin hG.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h), eq_comm]
    refine Finset.prod_eq_zero (Finset.mem_insert_self _ _) ?_
    rw [e, Set.indicator_of_notMem (by exact hu)]

theorem pureA_add (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g h : (κ → Af F) → ℂ) :
    pureA F f (g + h) = pureA F f g + pureA F f h := funext fun _ => mul_add _ _ _

theorem pureA_smul (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f (c • g) = c • pureA F f g := funext fun _ => mul_left_comm _ _ _

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 :=
  funext fun _ => mul_zero _

theorem schA_le : schA F κ ≤ Submodule.span ℂ {Φ | ∃ f φ, Good φ ∧ Φ = pure f φ} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have := mem_span_pf hg
  clear hg
  induction this using Submodule.span_induction with
  | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  | zero => rw [pureA_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [pureA_add]; exact add_mem hx hy
  | smul a x _ hx => rw [pureA_smul]; exact Submodule.smul_mem _ _ hx

end Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hTens_tr {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

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

open mixedEmbedding in
theorem trace_emb (a : F) : Algebra.trace ℝ (mixedSpace F) (mixedEmbedding F a) = (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

end GlobalTheory.ThK.Dbl.Dense

end
