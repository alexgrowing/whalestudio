import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq

noncomputable section

open Finset
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cOm (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaP n) ∧ ∀ z, z ∉ OmegaP n → F z = 0}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun z hz => by simp [ha.2 z hz, hb.2 z hz]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' := fun c F hF => ⟨hF.1.const_smul c, fun z hz => by simp [hF.2 z hz]⟩

theorem mem_cOm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} :
    F ∈ cOm n ↔ ContDiffOn ℂ ∞ F (OmegaP n) ∧ ∀ z, z ∉ OmegaP n → F z = 0 := Iff.rfl

theorem cOm_smooth (F : cOm n) : ContDiffOn ℂ ∞ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaP n) :=
  (mem_cOm.1 F.2).1

theorem indicator_rhol_mem (X : Matrix (Fin n) (Fin n) ℂ) (F : cOm n) :
    (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) ∈ cOm n := by
  have hF := cOm_smooth F
  have hs : IsOpen (OmegaP n) := isOpen_positiveOmega
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hF).2
  have hg : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z * X) := by
    have h0 := (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ X)).contDiff (n := ∞)
    first
      | exact h0
      | simpa using h0
      | (convert h0 using 1; funext z; rfl)
      | (convert h0 using 1; funext z; simp [LinearMap.mulRight_apply])
  refine mem_cOm.2 ⟨?_, fun z hz => Set.indicator_of_notMem hz _⟩
  refine (hd.clm_apply hg.contDiffOn).congr fun z hz => ?_
  rw [Set.indicator_of_mem hz]
  rfl

def rOm (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (cOm n) where
  toFun F := ⟨(OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)), indicator_rhol_mem X F⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol X ((F + G : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ)) z =
      (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z +
        (OmegaP n).indicator (Rhol X (G : Matrix (Fin n) (Fin n) ℂ → ℂ)) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      show fderiv ℂ ((F : Matrix (Fin n) (Fin n) ℂ → ℂ) + (G : Matrix (Fin n) (Fin n) ℂ → ℂ)) z (z * X) =
        fderiv ℂ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X) + fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X)
      erw [((differentiableAt_of_contDiffOn_omega (cOm_smooth F) hz).hasFDerivAt.add
        (differentiableAt_of_contDiffOn_omega (cOm_smooth G) hz).hasFDerivAt).fderiv]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol X ((c • F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ)) z =
      c * (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      show fderiv ℂ (c • (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) z (z * X) =
        c * fderiv ℂ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z (z * X)
      erw [fderiv_const_smul (differentiableAt_of_contDiffOn_omega (cOm_smooth F) hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

theorem rOm_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : cOm n) :
    ((rOm X F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =
      (OmegaP n).indicator (Rhol X (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) := rfl

theorem rOm_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : rOm (n := n) (X - Y) = rOm X - rOm Y := by
  refine LinearMap.ext fun F => Subtype.ext (funext fun z => ?_)
  simp only [LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, rOm_apply]
  by_cases hz : z ∈ OmegaP n
  · simp only [Set.indicator_of_mem hz]
    exact rightHol_sub X Y _ z
  · simp only [Set.indicator_of_notMem hz, sub_zero]

theorem rOm_zero : rOm (n := n) 0 = 0 := by
  have h := rOm_sub (n := n) 0 0
  rwa [sub_zero, sub_self] at h

theorem rOm_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    rOm X * rOm Y - rOm Y * rOm X = rOm (n := n) (X * Y - Y * X) := by
  refine LinearMap.ext fun F => Subtype.ext (funext fun z => ?_)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, rOm_apply]
  by_cases hz : z ∈ OmegaP n
  · simp only [Set.indicator_of_mem hz]
    have e1 : ∀ W : Matrix (Fin n) (Fin n) ℂ, Set.EqOn
        ((OmegaP n).indicator (Rhol W (F : Matrix (Fin n) (Fin n) ℂ → ℂ)))
        (Rhol W (F : Matrix (Fin n) (Fin n) ℂ → ℂ)) (OmegaP n) :=
      fun W w hw => Set.indicator_of_mem hw _
    rw [rightHol_congr_on_omega (e1 Y) hz, rightHol_congr_on_omega (e1 X) hz]
    have hinf := (cOm_smooth F).contDiffAt (isOpen_positiveOmega.mem_nhds hz)
    have h2 : ContDiffAt ℂ 2 (F : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      first
        | exact hinf.of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
        | exact contDiffAt_infty.1 hinf 2
        | exact hinf.of_le (by norm_cast)
        | exact hinf.of_le (by simp)
    exact rightHol_commutator h2 X Y
  · simp only [Set.indicator_of_notMem hz, sub_zero]

def eOm (a b : Fin n) : Module.End ℂ (cOm n) := rOm (Matrix.single a b 1)

def phiOm (μ : Fin n → ℤ) : cOm n :=
  ⟨(OmegaP n).indicator (PhiP μ), mem_cOm.2 ⟨(contDiffOn_powerDet μ).congr fun _ hz => Set.indicator_of_mem hz _,
    fun _ hz => Set.indicator_of_notMem hz _⟩⟩

private theorem single_one_mul_single_one_eq_ite (i j k l : Fin n) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h
    first
      | rw [Matrix.single_mul_single_same, mul_one]
      | simp
  · first
      | rw [Matrix.single_mul_single_of_ne h]
      | simp [h]

theorem isGlRep_eOm : IsGlRep (eOm (n := n)) := by
  intro a b c d
  simp only [eOm]
  rw [rOm_comm, rOm_sub, single_one_mul_single_one_eq_ite, single_one_mul_single_one_eq_ite]
  split_ifs <;> first | rfl | simp only [rOm_zero, sub_zero, zero_sub]

def mmSub (μ : Fin n → ℤ) : Submodule ℂ (cOm n) := genSub (eOm (n := n)) (Submodule.span ℂ {phiOm μ})

theorem mmSub_stable (μ : Fin n → ℤ) (a b : Fin n) : ∀ x ∈ mmSub μ, eOm a b x ∈ mmSub μ := by
  intro x hx
  simp only [mmSub, genSub] at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro T hT
  exact hT.2 a b x (hx T hT)

theorem phiOm_mem (μ : Fin n → ℤ) : phiOm μ ∈ mmSub μ := by
  simp only [mmSub, genSub]
  rw [Submodule.mem_sInf]
  intro T hT
  exact hT.1 (Submodule.subset_span (Set.mem_singleton _))

abbrev MMT (μ : Fin n → ℤ) : Type := ↥(mmSub μ)

def eMM (μ : Fin n → ℤ) (a b : Fin n) : Module.End ℂ (MMT μ) := (eOm a b).restrict (mmSub_stable μ a b)

def phiMM (μ : Fin n → ℤ) : MMT μ := ⟨phiOm μ, phiOm_mem μ⟩

theorem k2vM (lam : Fin n → ℝ) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    IsGlRep (eMM μ) ∧ (∀ a b, b < a → eMM μ a b (phiMM μ) = 0) ∧
      (∀ a, eMM μ a a (phiMM μ) = ((lam a + rho n a : ℝ) : ℂ) • phiMM μ) ∧
      genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) = ⊤ := by
  have hgl : IsGlRep (eMM μ) := by
    intro a b c d
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h := LinearMap.congr_fun (isGlRep_eOm (n := n) a b c d) (v : cOm n)
    split_ifs at h ⊢ <;> simpa [eMM, LinearMap.restrict_coe_apply] using h
  refine ⟨hgl, ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol (Matrix.single a b 1) ((OmegaP n).indicator (PhiP μ))) z = 0
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, rightHol_congr_on_omega (fun y hy => Set.indicator_of_mem hy _) hz]
      exact rightHol_powerDet_lower_eq_zero μ hab hz
    · exact Set.indicator_of_notMem hz _
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    funext z
    show (OmegaP n).indicator (Rhol (Matrix.single a a 1) ((OmegaP n).indicator (PhiP μ))) z =
      ((lam a + rho n a : ℝ) : ℂ) * (OmegaP n).indicator (PhiP μ) z
    by_cases hz : z ∈ OmegaP n
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        rightHol_congr_on_omega (fun y hy => Set.indicator_of_mem hy _) hz, rightHol_powerDet_diag μ a hz, ← hμ a]
      norm_cast
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  · have hGS : Submodule.span ℂ {phiMM μ} ≤ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) :=
      le_sInf fun T hT => hT.1
    have hGc : ∀ a b, ∀ v ∈ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}),
        eMM μ a b v ∈ genSub (eMM μ) (Submodule.span ℂ {phiMM μ}) :=
      fun a b v hv => Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)
    have key : mmSub μ ≤ (genSub (eMM μ) (Submodule.span ℂ {phiMM μ})).map (mmSub μ).subtype := by
      apply sInf_le
      refine Set.mem_setOf.2 ⟨?_, ?_⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_map.2 ⟨phiMM μ, hGS (Submodule.subset_span (Set.mem_singleton _)), rfl⟩
      · rintro a b _ ⟨y, hy, rfl⟩
        exact Submodule.mem_map.2 ⟨eMM μ a b y, hGc a b y hy, rfl⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 (key v.2)
    rwa [← Subtype.ext hyv]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
