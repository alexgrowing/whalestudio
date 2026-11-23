import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_trace_data (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) :
    ∃ (HP : Submodule ℂ (tfL2n ε)) (w : Fin n → tfL2n ε), IsClosed (HP : Set (tfL2n ε)) ∧
      HP = (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure ∧
      (∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP) ∧
      (∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v)) ∧
      c0 = (((∑ c, ‖w c‖ ^ 2) / d : ℝ) : ℂ) := by
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hdpos : 0 < d := hd.1
  have hst0 := closGen_stable hgap hσ hD hV hc hVK

  set S : Submodule ℂ (tfL2n ε) := Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
    v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} with hS
  set HP : Submodule ℂ (tfL2n ε) := S.topologicalClosure with hHP
  have hHPc : IsClosed (HP : Set (tfL2n ε)) := S.isClosed_topologicalClosure
  have : CompleteSpace HP := hHPc.completeSpace_coe
  have hst : ∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP :=
    tf_closure_stable dual hσ hD hsm hgap hV hc hVK hW hP hEP hyG
  have hSHP : S ≤ HP := S.le_topologicalClosure
  have hPm : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V) := hP.1
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V := fun f hf c =>
    Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  have hmem := fun {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) =>
    tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf

  have hT2 := fun {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V) (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) =>
    tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC hζ hζ' hm hm'

  set Nr : ℝ := ‖(y : H)‖ ^ 2 with hNr
  have hNpos : 0 < Nr := pow_pos (norm_pos_iff.2 hy0) 2
  have hNc : inner ℂ (y : H) (y : H) = (Nr : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hNr, Complex.ofReal_pow]
    rfl
  set κ : ℝ := d / Nr with hκ
  have hκpos : 0 < κ := div_pos hdpos hNpos
  have hsing : ∀ b, (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := fun b => by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  set u : Fin n → tfL2n ε := fun b => tfPh dual ε σ (y : H) (fun c => ((P (Pi.single b y) c : D) : H)) with hu
  have huHP : ∀ b, u b ∈ HP := fun b => hSHP (Submodule.subset_span ⟨_, hsing b, rfl⟩)
  set a : Fin n → tfL2n ε := fun b => HP.starProjection (tfJ ε (u b)) with ha
  set w : Fin n → tfL2n ε := fun b => (κ : ℂ) • a b with hw
  have haHP : ∀ b, a b ∈ HP := fun b => Submodule.starProjection_apply_mem HP _
  have hwHP : ∀ b, w b ∈ HP := fun b => HP.smul_mem _ (haHP b)
  have hPself : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hproj : ∀ x v, v ∈ HP → inner ℂ (HP.starProjection x) v = inner ℂ x v := by
    intro x v hv
    rw [Submodule.inner_starProjection_left_eq_right HP, hPself v hv]
  have hsubι : ∀ f g : Fin n → D, (fun c => (((f - g) c : D) : H)) =
      (fun c => ((f c : D) : H)) - (fun c => ((g c : D) : H)) := by
    intro f g; funext c; simp

  have hA : ∀ η ∈ tensSub (genSub E V), ∀ v ∈ HP,
      inner ℂ (tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H)))) v = 0 := by
    intro η hη
    have hη' : η - P η ∈ tensSub (genSub E V) := Submodule.sub_mem _ hη (hPm η hη)
    set q := tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H))) with hq
    have hle : S ≤ (ℂ ∙ q)ᗮ := by
      rw [hS, Submodule.span_le]
      rintro v ⟨f, hf, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, hq, tfJ_inner,
        hT2 (hcoeC _ hη') (hcoeC _ (hPm f hf)) (hmem hη') (hmem (hPm f hf)), hsubι, tfFormBH_sub_left,
        ← hPB η hη f hf, hPB η hη (P f) (hPm f hf), hPP f hf, ← hPB η hη f hf, sub_self, zero_mul, zero_div]
    intro v hv
    have h2 : v ∈ (ℂ ∙ q)ᗮ := Submodule.topologicalClosure_minimal S hle (Submodule.isClosed_orthogonal _) hv
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2)

  have hcoefS : ∀ (c : Fin n) (ζ : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ),
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ g = tfSgn ε c * inner ℂ (y : H) (tensGrp dual σ g ζ c) := by
    intro c ζ g
    unfold coefMap
    rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left]
    congr 1
    exact tf_star_sgn ε c
  have hformS : ∀ (c : Fin n) (ζ : Fin n → H),
      tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) ζ = tfSgn ε c * inner ℂ (y : H) (ζ c) := by
    intro c ζ
    rw [tf_coe_single', tfFormBH_single_left]

  have htr : ∀ f ∈ tensSub (genSub E V), ∀ g : Formalism.REAL.UJ ε,
      (∀ c, tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H)) c ∈ closGen E V) ∧
      ∀ c, MemLp (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) 2 (Formalism.REAL.muG ε) := by
    intro f hf g
    refine ⟨fun c => ?_, fun c => ?_⟩
    · rw [tf_tensGrp_apply]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (hst0 _ (umat_mem_UJset ε g) _ (hcoeC _ (hPm f hf) d))
    · have h1 := (hmem (hPm f hf) c).comp_measurePreserving (measurePreserving_mul_right ε g)
      have e : (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) =
          (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
            (fun i => ((P f i : D) : H)) (Formalism.MainNotions.S.umat x)) ∘ (fun x => x * g) := by
        funext x
        simp only [Function.comp_apply, coefMap]
        rw [show Formalism.MainNotions.S.umat (x * g) = Formalism.MainNotions.S.umat x * Formalism.MainNotions.S.umat g from rfl,
          tf_tensGrp_mul dual hσ (umat_mem_UJset ε x) (umat_mem_UJset ε g)]
      rw [e]
      exact h1

  have hrepGen : ∀ f ∈ tensSub (genSub E V), ∀ c,
      ((tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)) c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)))) := by
    intro f hf c
    filter_upwards [coe_toL2_ae_eq_of_memLp (hmem (hPm f hf) c)] with g hg
    rw [tfPh_apply, hg]
    obtain ⟨hζC, hζm⟩ := htr f hf g
    have hRv : tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H))) ∈ HP :=
      hst _ (umat_mem_UJset ε g) _ (hSHP (Submodule.subset_span ⟨f, hf, rfl⟩))
    have hs' : Pi.single c y - P (Pi.single c y) ∈ tensSub (genSub E V) :=
      Submodule.sub_mem _ (hsing c) (hPm _ (hsing c))
    have hA1 := hA _ (hsing c) _ hRv
    rw [tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), tfJ_inner,
      hT2 (hcoeC _ hs') hζC (hmem hs') hζm, hsubι, tfFormBH_sub_left] at hA1
    have hA2 : tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) =
        tfFormBH ε (fun i => ((P (Pi.single c y) i : D) : H))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) := by
      have hne : (inner ℂ (y : H) (y : H)) / (d : ℂ) ≠ 0 := by
        rw [hNc]
        exact div_ne_zero (Complex.ofReal_ne_zero.2 hNpos.ne') (Complex.ofReal_ne_zero.2 hdpos.ne')
      rw [mul_div_assoc] at hA1
      exact sub_eq_zero.1 ((mul_eq_zero.1 hA1).resolve_right hne)
    rw [hcoefS, ← hformS, hA2, hw]
    simp only
    rw [inner_smul_left, Complex.conj_ofReal, ha]
    simp only
    rw [hproj _ _ hRv, tfJ_inner, tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing c))) hζC (hmem (hPm _ (hsing c))) hζm, hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hrepS : ∀ v ∈ S, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact hrepGen f hf
    | zero =>
      intro c
      filter_upwards [Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)] with g hg
      rw [map_zero, inner_zero_right]
      exact hg
    | add x x' _ _ hx hx' =>
      intro c
      filter_upwards [Lp.coeFn_add (x c) (x' c), hx c, hx' c] with g h1 h2 h3
      rw [map_add, inner_add_right, ← h2, ← h3, ← Pi.add_apply, ← h1]
      rfl
    | smul r x _ hx =>
      intro c
      filter_upwards [Lp.coeFn_smul r (x c), hx c] with g h1 h2
      rw [map_smul, inner_smul_right, ← h2, ← smul_eq_mul, ← Pi.smul_apply, ← h1]
      rfl
  have hrep : ∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) :=
    tf_rep_closure (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g))
      (fun g x => le_of_eq ((tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) x)) w S hrepS

  have hT1 : c0 * (Nr : ℂ) = ∑ b, tfSgn ε b *
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    have h1 : inner ℂ (y : H) ((ptr P y : D) : H) = c0 * (Nr : ℂ) := by
      rw [hc0 y hyG, Submodule.coe_smul, inner_smul_right, hNc]
    rw [← h1, ptr_apply, Submodule.coe_sum, inner_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [hPB _ (hsing b) _ (hPm _ (hsing b)), hPP _ (hsing b), hformS, ← mul_assoc, tfSgn_mul_self, one_mul]
  have hub : ∀ b, inner ℂ (u b) (w b) =
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    intro b
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← Submodule.inner_starProjection_left_eq_right HP, hPself _ (huHP b), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing b))) (hcoeC _ (hPm _ (hsing b))) (hmem (hPm _ (hsing b)))
      (hmem (hPm _ (hsing b))), hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := (tfRdiag_isURepOn ε).1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    (tfRdiag_isURepOn ε).1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    (tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) v
  have hadj : ∀ (g : Formalism.REAL.UJ ε) (x x' : tfL2n ε), inner ℂ (tfRdiag ε (Formalism.MainNotions.S.umat g) x) x' =
      inner ℂ x (tfRdiag ε (Formalism.MainNotions.S.umat g⁻¹) x') := by
    intro g x x'
    have hs := GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso g
    rw [← hs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hJr : ∀ (x : tfL2n ε) c, tfJ ε x c = (((if ε c then (1 : ℝ) else -1 : ℝ)) : ℂ) • x c := by
    intro x c
    rw [tfJ_apply]
    congr 1
    unfold tfSgn
    split_ifs <;> simp
  have hswap := tf_tr_swap (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hadj (tfJ ε)
    (fun c => if ε c then (1 : ℝ) else -1) hJr (fun g x => tfRdiag_tfJ ε _ x) HP
    (fun g v hv => hst _ (umat_mem_UJset ε g) v hv) κ u w huHP (fun c => rfl) hrep

  have hJu : ∀ c', starRingEnd ℂ (inner ℂ (tfJ ε (u c')) (w c')) =
      ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
    intro c'
    rw [PiLp.inner_apply, map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [tfJ_apply, inner_smul_left, map_mul, Complex.conj_conj]
  have haa : ∀ c', inner ℂ (tfJ ε (u c')) (w c') = (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
    intro c'
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← hproj _ _ (Submodule.starProjection_apply_mem HP (tfJ ε (u c'))), inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow]
    rfl
  set T : ℝ := ∑ c', ‖a c'‖ ^ 2 with hT
  have hTnn : 0 ≤ T := sum_nonneg fun c' _ => sq_nonneg _
  have hmain : c0 * (Nr : ℂ) = ((κ * T : ℝ) : ℂ) := by
    rw [hT1, sum_congr rfl fun b _ => by rw [← hub b]]
    have e1 : ∀ b, tfSgn ε b * inner ℂ (u b) (w b) =
        ∑ c', tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
      intro b
      rw [PiLp.inner_apply, mul_sum]
      exact sum_congr rfl fun c' _ => by rw [hswap b c']
    rw [sum_congr rfl fun b _ => e1 b, sum_comm]
    have e : ∀ c', ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) =
        (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
      intro c'
      rw [← hJu, haa, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [sum_congr rfl fun c' _ => e c', ← mul_sum, hT]
    push_cast
    rfl
  have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
  have hc0eq : c0 = ((κ * T / Nr : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← hmain]
    field_simp
  have hwT : ∑ c', ‖w c'‖ ^ 2 = κ ^ 2 * T := by
    rw [hT, mul_sum]
    refine sum_congr rfl fun c' _ => ?_
    rw [hw]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκpos.le, mul_pow]
  refine ⟨HP, w, hHPc, rfl, hst, hrep, ?_⟩
  rw [hc0eq, hwT]
  congr 1
  rw [hκ]
  field_simp

end ReciprocityTheory.ChartRestriction.DS.G2
