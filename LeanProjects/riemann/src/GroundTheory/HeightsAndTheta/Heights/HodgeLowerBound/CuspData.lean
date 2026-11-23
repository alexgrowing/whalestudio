import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

namespace CuspData

variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]

def scaleLie (Cd : CuspData D O abelian₂) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : CuspData D O abelian₂ where
  rank := Cd.rank
  basis := Cd.basis
  form := Cd.form
  alt := Cd.alt
  unimod := Cd.unimod
  emb := Cd.emb
  normSq := Cd.normSq
  normSq_pos := Cd.normSq_pos
  form_le := Cd.form_le
  lie z τ v c := (ε : ℂ) * Cd.lie z τ v c
  lie_add z τ v w := by funext c; simp [Cd.lie_add, mul_add]
  lie_smul z τ a v := by funext c; simp [Cd.lie_smul]; ring
  lie_le z hz v := by
    have hs : ∑ τ, ∑ c, ‖(ε : ℂ) * Cd.lie z τ v c‖ ^ 2 = ε ^ 2 * ∑ τ, ∑ c, ‖Cd.lie z τ v c‖ ^ 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0, mul_pow, Finset.mul_sum]
    rw [hs]
    have hS : 0 ≤ ∑ τ, ∑ c, ‖Cd.lie z τ v c‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have he : ε ^ 2 ≤ 1 := by nlinarith
    calc ε ^ 2 * ∑ τ, ∑ c, ‖Cd.lie z τ v c‖ ^ 2 ≤ 1 * ∑ τ, ∑ c, ‖Cd.lie z τ v c‖ ^ 2 :=
          mul_le_mul_of_nonneg_right he hS
      _ ≤ Cd.normSq z v := by rw [one_mul]; exact Cd.lie_le z hz v
  inj z hz τ I hI ρ v hv hli := by
    have hne : (ε : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have := (Cd.inj z hz τ I hI ρ v hv hli).units_smul (fun _ => Units.mk0 (ε : ℂ) hne)
    convert this using 1
    funext a c
    simp [Units.smul_def]
  torus z hz c hc := by
    obtain ⟨h1, h2⟩ := Cd.torus z hz c hc
    refine ⟨h1, ?_⟩
    funext τ v c'
    show (ε : ℂ) * Cd.lie (torusSmul c z) τ v c' = (ε : ℂ) * Cd.lie z τ v c'
    rw [h2]

variable (Cd : CuspData D O abelian₂) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1)

end CuspData

namespace Line

open GaussianInt

def planeEquiv : (GaussianInt × GaussianInt) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun v := ![v.1.re, v.1.im, v.2.re, v.2.im]
  invFun f := (⟨f 0, f 1⟩, ⟨f 2, f 3⟩)
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' n v := by
    ext i; fin_cases i <;> simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  left_inv v := by simp
  right_inv f := by ext i; fin_cases i <;> simp

def planeBasis : Module.Basis (Fin 4) ℤ (GaussianInt × GaussianInt) := Module.Basis.ofEquivFun planeEquiv

theorem planeEquiv_symm_apply (f : Fin 4 → ℤ) : planeEquiv.symm f = (⟨f 0, f 1⟩, ⟨f 2, f 3⟩) := rfl

theorem planeBasis_apply (a : Fin 4) : planeBasis a = planeEquiv.symm (Pi.single a 1) := by
  simp [planeBasis, Module.Basis.coe_ofEquivFun]

def planeForm : (GaussianInt × GaussianInt) →ₗ[ℤ] (GaussianInt × GaussianInt) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im)
    (fun v v' w => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)

theorem planeForm_apply (v w : GaussianInt × GaussianInt) :
    planeForm v w = v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im := rfl

def planeLie (v : GaussianInt × GaussianInt) : ℂ := (toComplex v.1 + Complex.I * toComplex v.2) / 2

theorem planeLie_re (v : GaussianInt × GaussianInt) : (planeLie v).re = ((v.1.re : ℝ) - v.2.im) / 2 := by
  rw [planeLie, toComplex_def₂ v.1, toComplex_def₂ v.2, Complex.div_ofNat_re]
  simp [sub_eq_add_neg]

theorem planeLie_im (v : GaussianInt × GaussianInt) : (planeLie v).im = ((v.1.im : ℝ) + v.2.re) / 2 := by
  rw [planeLie, toComplex_def₂ v.1, toComplex_def₂ v.2, Complex.div_ofNat_im]
  simp

theorem planeLie_smul (a : GaussianInt) (v : GaussianInt × GaussianInt) :
    planeLie (a • v) = toComplex a * planeLie v := by
  simp only [planeLie, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
  ring

theorem planeLie_add (v w : GaussianInt × GaussianInt) : planeLie (v + w) = planeLie v + planeLie w := by
  simp only [planeLie, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem planeForm_I (v : GaussianInt × GaussianInt) :
    planeForm v ((⟨0, 1⟩ : GaussianInt) • v) = 2 * (v.1.im * v.2.re - v.1.re * v.2.im) := by
  rw [planeForm_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

theorem eq_zero_of_planeLie {I : Submodule GaussianInt (GaussianInt × GaussianInt)} (hI : IsIsoSub planeForm I)
    {v : GaussianInt × GaussianInt} (hv : v ∈ I) (h : planeLie v = 0) : v = 0 := by
  have hE := hI v hv _ (I.smul_mem ⟨0, 1⟩ hv)
  rw [planeForm_I] at hE
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [planeLie_re, Complex.zero_re] at hre
  rw [planeLie_im, Complex.zero_im] at him
  have h1 : v.1.re = v.2.im := by
    have : ((v.1.re : ℤ) : ℝ) = (v.2.im : ℝ) := by linarith
    exact_mod_cast this
  have h2 : v.1.im = -v.2.re := by
    have : ((v.1.im : ℤ) : ℝ) = -(v.2.re : ℝ) := by linarith
    exact_mod_cast this
  rw [h1, h2] at hE
  have h3 : v.2.re = 0 := by nlinarith [sq_nonneg v.2.re, sq_nonneg v.2.im]
  have h4 : v.2.im = 0 := by nlinarith [sq_nonneg v.2.re, sq_nonneg v.2.im]
  rw [h3, neg_zero] at h2
  rw [h4] at h1
  exact Prod.ext (Zsqrtd.ext h1 h2) (Zsqrtd.ext h3 h4)

theorem not_two_independent {I : Submodule GaussianInt (GaussianInt × GaussianInt)} (hI : IsIsoSub planeForm I)
    {v w : GaussianInt × GaussianInt} (hv : v ∈ I) (hw : w ∈ I)
    (hli : LinearIndependent GaussianInt ![v, w]) : False := by
  rw [LinearIndependent.pair_iff] at hli
  set δ := v.1 * w.2 - v.2 * w.1 with hδ
  have hA : w.2 • v + (-v.2) • w = (δ, 0) := by
    ext <;> simp [hδ] <;> ring
  have hB : (-w.1) • v + v.1 • w = (0, δ) := by
    ext <;> simp [hδ] <;> ring
  have hAI : ((δ, 0) : GaussianInt × GaussianInt) ∈ I := hA ▸ I.add_mem (I.smul_mem _ hv) (I.smul_mem _ hw)
  have hBI : ((0, δ) : GaussianInt × GaussianInt) ∈ I := hB ▸ I.add_mem (I.smul_mem _ hv) (I.smul_mem _ hw)
  have hE := hI _ hAI _ hBI
  rw [planeForm_apply] at hE
  simp only [show (0 : GaussianInt).re = 0 from rfl, show (0 : GaussianInt).im = 0 from rfl, mul_zero,
    sub_zero] at hE
  have hδ0 : δ = 0 := by
    have h1 : δ.re = 0 := by nlinarith [sq_nonneg δ.re, sq_nonneg δ.im]
    have h2 : δ.im = 0 := by nlinarith [sq_nonneg δ.re, sq_nonneg δ.im]
    exact Zsqrtd.ext h1 h2
  have hA0 := hli _ _ (by rw [hA, hδ0]; rfl)
  have hB0 := hli _ _ (by rw [hB, hδ0]; rfl)
  have hv0 : v = 0 := by
    have e1 : v.1 = 0 := hB0.2
    have e2 : v.2 = 0 := neg_eq_zero.mp hA0.2
    exact Prod.ext e1 e2
  have hw0 : w = 0 := by
    have e1 : w.1 = 0 := neg_eq_zero.mp hB0.1
    have e2 : w.2 = 0 := hA0.1
    exact Prod.ext e1 e2
  have := hli 1 0 (by simp [hv0, hw0])
  exact one_ne_zero this.1

theorem pair_of_family {ρ : ℕ} {w : Fin ρ → GaussianInt × GaussianInt} (hli : LinearIndependent GaussianInt w)
    (a b : Fin ρ) (hab : a ≠ b) : LinearIndependent GaussianInt ![w a, w b] := by
  have := hli.comp ![a, b] (by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all [eq_comm])
  rwa [show w ∘ ![a, b] = ![w a, w b] from by funext i; fin_cases i <;> rfl] at this

theorem family_le_one {I : Submodule GaussianInt (GaussianInt × GaussianInt)} (hI : IsIsoSub planeForm I)
    {ρ : ℕ} {w : Fin ρ → GaussianInt × GaussianInt} (hw : ∀ a, w a ∈ I) (hli : LinearIndependent GaussianInt w) :
    ρ ≤ 1 := by
  by_contra h
  exact not_two_independent hI (hw ⟨0, by omega⟩) (hw ⟨1, by omega⟩)
    (pair_of_family hli _ _ (by simp [Fin.ext_iff]))

theorem planeLie_linInd {T : Type} (t : T) {I : Submodule GaussianInt (GaussianInt × GaussianInt)}
    (hI : IsIsoSub planeForm I) (ρ : ℕ) (v : Fin ρ → GaussianInt × GaussianInt) (hv : ∀ a, v a ∈ I)
    (hli : LinearIndependent GaussianInt v) : LinearIndependent ℂ fun a => fun _ : T => planeLie (v a) := by
  have hρ := family_le_one hI hv hli
  interval_cases ρ
  · exact linearIndependent_empty_type
  · rw [linearIndependent_unique_iff]
    intro h
    have h0 : planeLie (v default) = 0 := congrFun h t
    exact hli.ne_zero default (eq_zero_of_planeLie hI (hv default) h0)

def planeCusp (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    CuspData (lineData II hII) GaussianInt (GaussianInt × GaussianInt) where
  rank := 4
  basis := planeBasis
  form := planeForm
  alt v := by rw [planeForm_apply]; ring
  unimod := by
    have hM : (Matrix.of fun a b => planeForm (planeBasis a) (planeBasis b)) =
        !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [planeBasis_apply, planeEquiv_symm_apply, planeForm_apply, Pi.single_apply]
    rw [hM]
    have : (!![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0] : Matrix (Fin 4) (Fin 4) ℤ).det = 1 := by
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      all_goals decide
    rw [this]
    exact isUnit_one
  emb _ := toComplex
  normSq _ v := Complex.normSq (toComplex v.1) + Complex.normSq (toComplex v.2)
  normSq_pos _ _ v hv := by
    rcases eq_or_ne v.1 0 with h | h
    · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h h2)
      have : 0 < Complex.normSq (toComplex v.2) :=
        Complex.normSq_pos.2 fun e => h2 (toComplex_injective (by rw [e, map_zero]))
      linarith [Complex.normSq_nonneg (toComplex v.1)]
    · have : 0 < Complex.normSq (toComplex v.1) :=
        Complex.normSq_pos.2 fun e => h (toComplex_injective (by rw [e, map_zero]))
      linarith [Complex.normSq_nonneg (toComplex v.2)]
  form_le _ _ v w := by
    rw [planeForm_apply, normSq_toComplex, normSq_toComplex, normSq_toComplex, normSq_toComplex]
    push_cast
    nlinarith [sq_nonneg ((v.1.re : ℝ) * w.2.im - v.1.im * w.2.re),
      sq_nonneg ((v.1.re : ℝ) * w.1.re + v.2.re * w.2.re), sq_nonneg ((v.1.re : ℝ) * w.1.im + v.2.im * w.2.re),
      sq_nonneg ((v.1.im : ℝ) * w.1.re + v.2.re * w.2.im), sq_nonneg ((v.1.im : ℝ) * w.1.im + v.2.im * w.2.im),
      sq_nonneg ((v.2.re : ℝ) * w.1.im - v.2.im * w.1.re)]
  lie _ _ v _ := planeLie v
  lie_add _ _ v w := by funext c; exact planeLie_add v w
  lie_smul _ _ a v := by funext c; simp [planeLie_smul]
  lie_le _ _ v := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Complex.sq_norm]
    show ∑ _c : Fin 1, Complex.normSq (planeLie v) ≤ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, Complex.normSq_apply, planeLie_re,
      planeLie_im, normSq_toComplex, normSq_toComplex]
    nlinarith [sq_nonneg ((v.1.re : ℝ) + v.2.im), sq_nonneg ((v.1.im : ℝ) - v.2.re)]
  inj _ _ _ I hI ρ v hv hli := planeLie_linInd (T := Fin 1) ⟨0, by decide⟩ hI ρ v hv hli
  torus _ _ _ _ := ⟨rfl, rfl⟩

def planeLine : Submodule GaussianInt (GaussianInt × GaussianInt) := GaussianInt ∙ ((1, 0) : GaussianInt × GaussianInt)

theorem mem_planeLine {v : GaussianInt × GaussianInt} : v ∈ planeLine ↔ v.2 = 0 := by
  rw [planeLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; simp
  · intro h; exact ⟨v.1, by ext <;> simp [h]⟩

theorem planeLine_isIso : IsIsoSub planeForm planeLine := by
  intro v hv w hw
  rw [mem_planeLine] at hv hw
  rw [planeForm_apply, hv, hw]
  simp

theorem planeLine_ne_bot : planeLine ≠ ⊥ := by
  intro h
  have : ((1, 0) : GaussianInt × GaussianInt) ∈ planeLine := mem_planeLine.2 rfl
  rw [h, Submodule.mem_bot] at this
  exact one_ne_zero (congrArg Prod.fst this)

theorem planeLine_saturated : IsSaturated planeLine := by
  intro v n hn h
  rw [mem_planeLine] at h ⊢
  have : n • v.2 = 0 := by simpa using h
  exact (smul_eq_zero.mp this).resolve_left hn

theorem planeLine_family : ∃ ρ v, IsNzFamily planeLine ρ v := by
  refine ⟨1, ![(1, 0)], le_rfl, fun a => by fin_cases a; exact mem_planeLine.2 rfl, ?_, ?_⟩
  · rw [linearIndependent_unique_iff]; simp
  · have : Submodule.span GaussianInt (Set.range ![((1, 0) : GaussianInt × GaussianInt)]) = planeLine := by
      simp [planeLine]
    rw [this, AddSubgroup.relIndex_self]
    exact one_ne_zero

theorem planeCusp_Nz_pos (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) (z : (Σ _ : Unit, Fin 2) → ℂ) : 0 < (planeCusp II hII).Nz z planeLine := by
  have key : ∀ ρ (w : Fin ρ → GaussianInt × GaussianInt), IsNzFamily planeLine ρ w →
      0 < (∏ τ : Unit, ((planeCusp II hII).gramLie z τ w).det.re) /
        ((Submodule.span GaussianInt (Set.range w)).toAddSubgroup.relIndex planeLine.toAddSubgroup : ℝ) := by
    intro ρ w ⟨h1, hmem, hli, hidx⟩
    have hidx' : (0 : ℝ) < ((Submodule.span GaussianInt (Set.range w)).toAddSubgroup.relIndex
        planeLine.toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hidx
    refine div_pos ?_ hidx'
    have hρ := family_le_one planeLine_isIso hmem hli
    interval_cases ρ
    · simp only [Finset.univ_unique, Finset.prod_singleton, Matrix.det_unique]
      simp only [CuspData.gramLie, planeCusp, Matrix.of_apply]
      have hw0 : planeLie (w default) ≠ 0 :=
        fun h => hli.ne_zero default (eq_zero_of_planeLie planeLine_isIso (hmem default) h)
      show 0 < (∑ _c : Fin 1, starRingEnd ℂ (planeLie (w default)) * planeLie (w default)).re
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, ← Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_re]
      exact Complex.normSq_pos.2 hw0
  unfold CuspData.Nz
  rw [dif_pos planeLine_family]
  exact key _ _ planeLine_family.choose_spec.choose_spec

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
