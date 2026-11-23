import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Transport

variable {R : Type} [CommRing R] {ι ι' : Type} {n : ℕ}

theorem md_twist_rename (e : ι → ι') (LL : Letters ι) (LL' : Letters ι') (S : Set ι) (S' : Set ι')
    (hv : ∀ i, LL'.vec (e i) = LL.vec i) (hS : ∀ i, e i ∈ S' ↔ i ∈ S) (jj : Fin n) (G : MvPolynomial (ι × Fin n) R) :
    twistSub LL' S' jj (rename (fun v : ι × Fin n => (e v.1, v.2)) G) =
      rename (fun v : ι × Fin n => (e v.1, v.2)) (twistSub LL S jj G) := by
  have h : (twistSub (R := R) LL' S' jj).comp (rename (fun v : ι × Fin n => (e v.1, v.2))).toRingHom =
      (rename (fun v : ι × Fin n => (e v.1, v.2)) :
        MvPolynomial (ι × Fin n) (GLLaurent R n) →ₐ[GLLaurent R n] _).toRingHom.comp (twistSub (R := R) LL S jj) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [twistSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, hv, hS]
      split_ifs <;> simp
  exact RingHom.congr_fun h G

theorem md_sDegs_rename (e : ι → ι') (he : Function.Injective e) (LL : Letters ι) (LL' : Letters ι') (S : Set ι)
    (S' : Set ι') (hv : ∀ i, LL'.vec (e i) = LL.vec i) (hS : ∀ i, e i ∈ S' ↔ i ∈ S) (jj : Fin n)
    (G : MvPolynomial (ι × Fin n) R) :
    sDegs LL' S' jj (rename (fun v : ι × Fin n => (e v.1, v.2)) G) = sDegs LL S jj G := by
  have hf : Function.Injective (fun v : ι × Fin n => (e v.1, v.2)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (he h.1) h.2
  unfold sDegs
  rw [md_twist_rename e LL LL' S S' hv hS, support_rename_of_injective hf, Finset.image_biUnion]
  refine Finset.biUnion_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain _ hf]

theorem md_sDegs_comp [Fintype ι] (LL : Letters ι) (S : Set ι) (jj : Fin n) (G : MvPolynomial (ι × Fin n) R)
    (d : ι → ℕ) : sDegs LL S jj (multidegreeComponent d G) ⊆ sDegs LL S jj G := by
  intro z hz
  unfold sDegs at hz ⊢
  rw [Finset.mem_biUnion] at hz ⊢
  obtain ⟨m', hm', hz'⟩ := hz
  have hWH : IsWeightedHomogeneous letterWeight (twistSub LL S jj (multidegreeComponent d G)) d := by
    unfold multidegreeComponent
    rw [map_sum]
    apply IsWeightedHomogeneous.sum
    intro m hm
    have h := twist_substitution_weighted_homog LL S jj m (G.coeff m)
    rwa [weight_eq_multidegree_fun, mem_multidegree_filter G d m hm] at h
  have hwt : Finsupp.weight letterWeight m' = d := hWH (mem_support_iff.1 hm')
  have hsplit : G = multidegreeComponent d G +
      ∑ m ∈ G.support.filter (fun m => ¬ (fun i => multideg m i) = d), monomial m (G.coeff m) := by
    unfold multidegreeComponent
    rw [Finset.sum_filter_add_sum_filter_not]
    exact G.support_sum_monomial_coeff.symm
  have key : (twistSub LL S jj (multidegreeComponent d G)).coeff m' = (twistSub LL S jj G).coeff m' := by
    conv_rhs => rw [hsplit]
    rw [map_add, coeff_add, map_sum, coeff_sum, Finset.sum_eq_zero, add_zero]
    intro m hm
    apply (twist_substitution_weighted_homog LL S jj m (G.coeff m)).coeff_eq_zero
    intro h
    apply (Finset.mem_filter.1 hm).2
    rw [← weight_eq_multidegree_fun, ← h, hwt]
  refine ⟨m', ?_, key ▸ hz'⟩
  rw [mem_support_iff] at hm' ⊢
  rwa [← key]

theorem md_val_comp [Fintype ι] [NeZero n] (LL : Letters ι) (S : Set ι) (G : MvPolynomial (ι × Fin n) R) (d : ι → ℕ) :
    valS LL S G ≤ valS LL S (multidegreeComponent d G) := Finset.inf_mono (md_sDegs_comp LL S _ G d)

theorem md_lam_comp [Fintype ι] [NeZero n] (LL : Letters ι) (S : Set ι) (G : MvPolynomial (ι × Fin n) R) (d : ι → ℕ) :
    lam1S LL S (multidegreeComponent d G) ≤ lam1S LL S G := Finset.sup_mono (md_sDegs_comp LL S _ G d)

theorem md_weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (f : σ → τ) (w : τ → M) (m : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f m) = Finsupp.weight (w ∘ f) m := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul])]
  rfl

theorem md_wh_rename {σ τ M : Type*} [AddCommMonoid M] (f : σ → τ) (w : τ → M) {P : MvPolynomial σ R} {d : M}
    (h : IsWeightedHomogeneous (w ∘ f) P d) : IsWeightedHomogeneous w (rename f P) d := by
  rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [md_weight_mapDomain]
  exact h (mem_support_iff.1 hm)

theorem md_pol_iff [Fintype ι] (P : MvPolynomial (ι × Fin n) R) (d : ι → ℕ) :
    P ∈ Pol R n d ↔ IsWeightedHomogeneous letterWeight P d := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    rw [weight_eq_multidegree_fun]
    funext i
    exact h (Finset.mem_coe.2 (mem_support_iff.2 hm)) i
  · intro h m hm i
    have := h (mem_support_iff.1 (Finset.mem_coe.1 hm))
    rw [weight_eq_multidegree_fun] at this
    exact congrFun this i

end Transport

section Main

variable {O : Type} [CommRing O] [IsDomain O] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ)

theorem md_eL_inj : Function.Injective (eL F j) := fun _ _ h => ((F.letters j).orderEmbOfFin rfl).injective h
theorem md_eL_le (a b : Fin (Mj F j)) : eL F j a ≤ eL F j b ↔ a ≤ b := ((F.letters j).orderEmbOfFin rfl).le_iff_le
theorem md_eL_lt (a b : Fin (Mj F j)) : eL F j a < eL F j b ↔ a < b := ((F.letters j).orderEmbOfFin rfl).lt_iff_lt
theorem md_eL_mem (a : Fin (Mj F j)) : eL F j a ∈ F.letters j := Finset.orderEmbOfFin_mem _ _ _
theorem md_eL_surj {x : ℤ} (hx : x ∈ F.letters j) : ∃ i, eL F j i = x := by
  have h := Finset.range_orderEmbOfFin (F.letters j) rfl
  have hx' : x ∈ Set.range ((F.letters j).orderEmbOfFin rfl) := by rw [h]; exact hx
  exact hx'

theorem md_f_inj (n : ℕ) : Function.Injective (fun v : Fin (Mj F j) × Fin n => (eL F j v.1, v.2)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (md_eL_inj F j h.1) h.2

theorem md_val_tr {n : ℕ} [NeZero n] (S' : Set ℤ) (S : Set (Fin (Mj F j))) (hS : ∀ i, eL F j i ∈ S' ↔ i ∈ S)
    (A0 : MvPolynomial (Fin (Mj F j) × Fin n) O) :
    valS LZ S' (rename (fun v : Fin (Mj F j) × Fin n => (eL F j v.1, v.2)) A0) = valS (LLs F j).toLetters S A0 := by
  unfold valS
  rw [md_sDegs_rename (eL F j) (md_eL_inj F j) (LLs F j).toLetters LZ S S' (fun i => rfl) hS]

theorem md_lam_tr {n : ℕ} [NeZero n] (S' : Set ℤ) (S : Set (Fin (Mj F j))) (hS : ∀ i, eL F j i ∈ S' ↔ i ∈ S)
    (A0 : MvPolynomial (Fin (Mj F j) × Fin n) O) :
    lam1S LZ S' (rename (fun v : Fin (Mj F j) × Fin n => (eL F j v.1, v.2)) A0) = lam1S (LLs F j).toLetters S A0 := by
  unfold lam1S
  rw [md_sDegs_rename (eL F j) (md_eL_inj F j) (LLs F j).toLetters LZ S S' (fun i => rfl) hS]

def GenM (m : ℤ) (th : ℤ → ℝ) : Set (MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) :=
  {P | ∃ (A : MvPolynomial (Fin (Mj F j) × Fin r) O) (G : MvPolynomial (Fin (Mj F j) × Fin K) O)
      (Mx : Fin (Mj F j) → ℤ),
     (∀ v ∈ G.vars, ¬ F.IsW j (eL F j v.1)) ∧ CondM F j m A G Mx ∧
     (∀ i, ¬ F.IsW j (eL F j i) → geR (valS (LLs F j).toLetters {y | y < i} A) (th (eL F j i))) ∧
     P = rename (plVar (K := K)) A * rename (tanVar (r := r)) G}

def MGenM (m : ℤ) (th : ℤ → ℝ) (D : Fin (Mj F j) → ℕ) : Set (MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) :=
  {P | ∃ (d' d'' : Fin (Mj F j) → ℕ) (A : MvPolynomial (Fin (Mj F j) × Fin r) O)
      (G : MvPolynomial (Fin (Mj F j) × Fin K) O) (Mx : Fin (Mj F j) → ℤ),
      A ∈ Pol O r d' ∧ G ∈ Pol O K d'' ∧ (∀ i, d' i + d'' i = D i) ∧
      (∀ i, F.IsW j (eL F j i) → d'' i = 0) ∧ CondM F j m A G Mx ∧
      (∀ i, ¬ F.IsW j (eL F j i) → geR (valS (LLs F j).toLetters {y | y < i} A) (th (eL F j i))) ∧
      P = rename (plVar (K := K)) A * rename (tanVar (r := r)) G}

theorem md_geR_mono {v v' : WithTop ℤ} (h : v ≤ v') {t : ℝ} (hv : geR v t) : geR v' t := by
  intro z hz
  subst hz
  cases hv' : v with
  | top => rw [hv'] at h; simp at h
  | coe z' =>
    rw [hv'] at h
    have h1 : z' ≤ z := by exact_mod_cast h
    have h2 := hv z' hv'
    have h3 : (z' : ℝ) ≤ z := by exact_mod_cast h1
    linarith

theorem md_comp_gen (m : ℤ) (th : ℤ → ℝ) (D : Fin (Mj F j) → ℕ) {ζ : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O}
    (hζ : ζ ∈ Submodule.span O (GenM (O := O) (K := K) F j m th)) :
    weightedHomogeneousComponent letterWeight D ζ ∈ Submodule.span O (MGenM (O := O) (K := K) F j m th D) := by
  induction hζ using Submodule.span_induction with
  | mem x h =>
    obtain ⟨A, G, Mx, hW, hC, hR, rfl⟩ := h
    obtain ⟨IA, hIA⟩ : ∃ IA : Finset (Fin (Mj F j) → ℕ), A = ∑ d ∈ IA, multidegreeComponent d A := ⟨_, eq_sum_multidegree_components A⟩
    obtain ⟨IG, hIG, hIGm⟩ : ∃ IG : Finset (Fin (Mj F j) → ℕ), G = ∑ d ∈ IG, multidegreeComponent d G ∧
        ∀ d ∈ IG, ∃ m0 ∈ G.support, (fun i => multideg m0 i) = d :=
      ⟨_, eq_sum_multidegree_components G, fun d hd => by
        exact (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).1 hd⟩
    have e : rename (plVar (K := K)) A * rename (tanVar (r := r)) G =
        ∑ d' ∈ IA, ∑ d'' ∈ IG,
            rename (plVar (K := K)) (multidegreeComponent d' A) * rename (tanVar (r := r)) (multidegreeComponent d'' G) := by
      rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum, ← hIA, ← hIG]
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun d' _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun d'' hd'' => ?_
    have h1 : IsWeightedHomogeneous letterWeight (rename (plVar (K := K)) (multidegreeComponent d' A)) d' :=
      md_wh_rename (plVar (K := K)) letterWeight ((md_pol_iff _ _).1 (homogeneous_component_mem d' A))
    have h2 : IsWeightedHomogeneous letterWeight (rename (tanVar (r := r)) (multidegreeComponent d'' G)) d'' :=
      md_wh_rename (tanVar (r := r)) letterWeight ((md_pol_iff _ _).1 (homogeneous_component_mem d'' G))
    have hwh := h1.mul h2
    by_cases hD : D = d' + d''
    · subst hD
      rw [hwh.weightedHomogeneousComponent_same]
      refine Submodule.subset_span ⟨d', d'', multidegreeComponent d' A, multidegreeComponent d'' G, Mx, homogeneous_component_mem _ _, homogeneous_component_mem _ _,
        fun i => rfl, ?_, ?_, ?_, rfl⟩
      · intro i hi
        obtain ⟨m0, hm0, rfl⟩ := hIGm d'' hd''
        show multideg m0 i = 0
        unfold multideg
        refine Finset.sum_eq_zero fun c _ => ?_
        by_contra hne
        exact hW (i, c) ((mem_vars_iff_mem_support _).2 ⟨m0, hm0, Finsupp.mem_support_iff.2 hne⟩) hi
      · intro i hi
        refine ⟨fun hE => ⟨le_trans (md_lam_comp _ _ _ _) ((hC i hi).1 hE).1,
          le_trans ((hC i hi).1 hE).2 (md_val_comp _ _ _ _)⟩,
          fun hE => ⟨le_trans (md_lam_comp _ _ _ _) ((hC i hi).2 hE).1,
          le_trans ((hC i hi).2 hE).2 (md_val_comp _ _ _ _)⟩⟩
      · intro i hi
        exact md_geR_mono (md_val_comp _ _ _ _) (hR i hi)
    · rw [hwh.weightedHomogeneousComponent_ne D hD]
      exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Main

theorem restModel : RestModel := by
  intro O _ _ n' r K _ _ _ F j m th o dd xi hxi hhom
  unfold XX' at hxi
  have h1 := (Submodule.mem_inf.1 hxi).1
  have h2 : xi ∈ Submodule.map (plnm F j O K).toLinearMap (Submodule.span O (GenM (O := O) (K := K) F j m th)) := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨A, G, M, hA, hG, hC, rfl⟩
    obtain ⟨A0, rfl⟩ := exists_rename_eq_of_vars_subset_range A _ (md_f_inj F j r) (by
      intro v hv
      obtain ⟨i, hi⟩ := md_eL_surj F j ((mem_supported.1 hA) hv)
      exact ⟨(i, v.2), by simp [hi]⟩)
    obtain ⟨G0, rfl⟩ := exists_rename_eq_of_vars_subset_range G _ (md_f_inj F j K) (by
      intro v hv
      obtain ⟨i, hi⟩ := md_eL_surj F j ((mem_supported.1 hG) hv).1
      exact ⟨(i, v.2), by simp [hi]⟩)
    refine ⟨rename (plVar (K := K)) A0 * rename (tanVar (r := r)) G0,
      ⟨A0, G0, fun i => M (eL F j i), ?_, ?_, ?_, rfl⟩, ?_⟩
    · intro v hv
      obtain ⟨m0, hm0, hvm⟩ := (mem_vars_iff_mem_support _).1 hv
      have h3 : (eL F j v.1, v.2) ∈ (rename (fun v : Fin (Mj F j) × Fin K => (eL F j v.1, v.2)) G0).vars := by
        refine (mem_vars_iff_mem_support _).2
          ⟨Finsupp.mapDomain (fun v : Fin (Mj F j) × Fin K => (eL F j v.1, v.2)) m0, ?_, ?_⟩
        · rw [support_rename_of_injective (md_f_inj F j K)]
          exact Finset.mem_image_of_mem _ hm0
        · rw [Finsupp.mem_support_iff]
          have := Finsupp.mapDomain_apply (md_f_inj F j K) m0 v
          rw [this]
          exact Finsupp.mem_support_iff.1 hvm
      exact ((mem_supported.1 hG) h3).2
    · intro i hi
      have hc := hC (eL F j i) (md_eL_mem F j i) hi
      rw [md_lam_tr F j {y | y ≤ eL F j i} {y | y ≤ i} (fun i' => md_eL_le F j i' i),
        md_lam_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i),
        md_val_tr F j {y | y ≤ eL F j i} {y | y ≤ i} (fun i' => md_eL_le F j i' i),
        md_val_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i)] at hc
      exact ⟨hc.1, hc.2.1⟩
    · intro i hi
      have hc := (hC (eL F j i) (md_eL_mem F j i) hi).2.2
      rw [md_val_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i)] at hc
      exact hc
    · show plnm F j O K _ = _
      unfold plnm plEmb nmEmb
      rw [map_mul, rename_rename, rename_rename, rename_rename, rename_rename]
      rfl
  obtain ⟨ξ0, hξ0, rfl⟩ := h2
  have hwh : IsWeightedHomogeneous letterWeight ξ0 (fun i => dd (eL F j i)) := by
    intro m0 hm0
    rw [weight_eq_multidegree_fun]
    funext i
    rw [mem_restrictSupport_iff] at hhom
    have h3 : Finsupp.mapDomain (fun v : Fin (Mj F j) × Fin (r + K) => (eL F j v.1, v.2)) m0 ∈
        ((plnm F j O K).toLinearMap ξ0).support := by
      show _ ∈ (rename _ ξ0).support
      rw [support_rename_of_injective (md_f_inj F j (r + K))]
      exact Finset.mem_image_of_mem _ (mem_support_iff.2 hm0)
    have h4 := hhom (Finset.mem_coe.2 h3) (eL F j i) (md_eL_mem F j i)
    rw [← h4]
    unfold multideg
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (Finsupp.mapDomain_apply (md_f_inj F j (r + K)) m0 (i, c)).symm
  have h5 := md_comp_gen F j m th (fun i => dd (eL F j i)) hξ0
  rw [hwh.weightedHomogeneousComponent_same] at h5
  have h6 := Submodule.mem_map_of_mem (f := (plnm F j O K).toLinearMap) h5
  rw [Submodule.map_span] at h6
  refine Submodule.span_mono ?_ h6
  rintro _ ⟨P0, ⟨d', d'', A, G, Mx, a1, a2, a3, a4, a5, a6, rfl⟩, rfl⟩
  exact ⟨d', d'', A, G, Mx, a1, a2, a3, a4, a5, a6, rfl⟩

end Formalism.MainNotions.G.symbolGeneratorData
