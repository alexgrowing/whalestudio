import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPosCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem psd_of_rep {α ι H : Type} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Finset α)
    (U : ι → α → H) (K : α → α → ℂ) (hK : ∀ x y, K x y = ∑ k, inner ℂ (U k y) (U k x)) : TB.PSDOn Y K := by
  unfold TB.PSDOn
  have key : (Matrix.of fun x y : Y => K x y) = ∑ k, (Matrix.gram ℂ (fun x : Y => U k x)).transpose := by
    ext x y
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.transpose_apply, Matrix.gram_apply, hK]
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => (Matrix.posSemidef_gram ℂ _).transpose

theorem psd_smul {α : Type} (Y : Finset α) (k : α → α → ℂ) (a : ℝ) (ha : 0 ≤ a) (hk : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (a : ℂ) * k x y) := by
  rw [PBA.psd_iff_qf] at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rw [hk.1 x hx y hy, map_mul, Complex.conj_ofReal]
  · have : PBA.qf Y (fun x y => (a : ℂ) * k x y) c = (a : ℂ) * PBA.qf Y k c := by
      unfold PBA.qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [this, Complex.re_ofReal_mul]
    exact mul_nonneg ha (hk.2 c)

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_top_rep (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → C.LPt → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      ∀ x y, p.RR F (P.r + 1) w x y = ∑ k, inner ℂ (U k y) (U k x) := by
  by_cases hw : w = []
  · refine ⟨Unit, inferInstance, fun _ x => if D.IsLocPt x (P.r + 1) then
      B.hsVec (D.vecV p.T.base p.ν' p.m₀ F x) else 0, fun x y => ?_⟩
    simp only [Fintype.univ_unit, Finset.sum_singleton]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dif_pos ⟨hx, hy⟩, dif_neg (by omega), if_pos rfl, if_pos hw]
        simp only [hx, hy, if_true, B.hsInner]
      · rw [dif_neg (fun h => hy h.2)]
        simp [hy]
    · rw [dif_neg (fun h => hx h.1)]
      simp [hx]
  · refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance, fun k x => if D.IsLocPt x (P.r + 1) then
      ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w x k.1 k.2 : ℝ) : ℂ) •
        B.hsVec ((p.TP.E k.2).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w k.1 F) x)) else 0, fun x y => ?_⟩
    rw [Fintype.sum_prod_type]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dif_pos ⟨hx, hy⟩, dif_neg (by omega), if_pos rfl, if_neg hw]
        unfold Top.topOf
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
        simp only [hx, hy, if_true, B.hsInner, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
        push_cast
        ring
      · rw [dif_neg (fun h => hy h.2)]
        simp [hy]
    · rw [dif_neg (fun h => hx h.1)]
      simp [hx]

end top

section pos

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (PBL.setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  have hgpos := PBL.g_pos_of_built hB
  have hu : ∀ h, PBL.CV ((p v).T.bs j) (PBL.uY S p F v ε j hj w Y h) := by
    intro h
    unfold PBL.uY
    split_ifs
    · unfold PBL.uB
      split_ifs with hh
      · exact PBL.cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w _
          ((PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh) (hF v ε hε) e
      · exact PBL.cv_zero
    · exact PBL.cv_zero
  set c0 : ℝ := 1 / (PBL.ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := PBL.gam_pos hB j
    have := PBL.sizeAt_nonneg S v w
    positivity
  have hG := PBL.gram_psd (PBL.CV (S := Fin w.length) ((p v).T.bs j))
    (fun x y => (c0 : ℂ) * (p v).form j hj w x y) PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
    (fun c x hx => PBL.cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [PBL.form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [PBL.form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (PBL.uY S p F v ε j hj w Y) hu
  refine PBL.psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (PBL.uY S p F v ε j hj w Y x) (PBL.uY S p F v ε j hj w Y y) = _
  rw [PBL.uY_mem S p F v ε j hj w Y x hx, PBL.uY_mem S p F v ε j hj w Y y hy, PBL.gN_uB hB F hF v ε hε j hj w x y]

theorem gramLoc_top_psd (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ)
    (w : List C.Letter) (Y : Finset C.LPt) :
    TB.PSDOn Y ((PBL.setC S p F).gramLoc v ε (S.G.r + 1) w) := by
  obtain ⟨ι, _, U, hU⟩ := rr_top_rep (p v) (F v ε) w
  set a : C.LPt → ℝ := fun x => √(PBL.nnS S x) / PBL.bS S x * √(1 / PBL.ΓS S (S.G.r + 1)) with ha
  have hΓ := PBL.gam_pos hB (S.G.r + 1)
  refine psd_of_rep Y (fun k x => ((a x : ℝ) : ℂ) • U k (PBL.stdS S x)) _ fun x y => ?_
  rw [PBL.gramLoc_setC hB, hU]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : √(1 / PBL.ΓS S (S.G.r + 1)) * √(1 / PBL.ΓS S (S.G.r + 1)) = 1 / PBL.ΓS S (S.G.r + 1) :=
    Real.mul_self_sqrt (by positivity)
  have e1 : ((√(PBL.nnS S x) * √(PBL.nnS S y) : ℝ) : ℂ) *
      ((1 / (PBL.bS S x * PBL.bS S y * PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((a y : ℝ) : ℂ) * ((a x : ℝ) : ℂ) := by
    rw [ha]
    push_cast
    rw [show ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) from rfl]
    have hs' : ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) * ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) =
        1 / (PBL.ΓS S (S.G.r + 1) : ℂ) := by exact_mod_cast hs
    calc _ = (√(PBL.nnS S x) : ℂ) * (√(PBL.nnS S y) : ℂ) * ((PBL.bS S x : ℂ)⁻¹ * (PBL.bS S y : ℂ)⁻¹) *
          (1 / (PBL.ΓS S (S.G.r + 1) : ℂ)) := by rw [one_div, one_div, mul_inv, mul_inv]; ring
      _ = _ := by rw [← hs']; ring
  rw [← mul_assoc, e1]
  ring

end pos

theorem posB_of (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) : PosB := by
  intro Cb
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB F hF v ε hε i hi w Y
  change i ≤ S.G.r + 1 at hi
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -⟩ := hB'
  rcases Nat.lt_or_ge i (S.G.r + 1) with hlt | hge
  · have hj : i ≤ S.G.r := by omega
    have hCI := PBCut.cutInside_of_built hB
    have hw := PBD.cutWord_of_adm S hGo hCI w v
    have hpsd := gN_psdC hA hFP hB F hF v ε hε i hj (w.1 v) hw Y
    have hsa := PBL.sizeAt_pos S hGo v (w.1 v) ⟨w, rfl⟩
    refine PBL.psd_congr (fun x _ y _ => ?_) (psd_smul Y _ _ hsa.le hpsd)
    show (S.sizeAt v (w.1 v) : ℂ) * KB.gN (PBL.setC S p F) v ε i (w.1 v) x y = _
    unfold KB.gN
    have : ((PBL.setC S p F).sizeAt v (w.1 v) : ℂ) = (S.sizeAt v (w.1 v) : ℂ) := rfl
    rw [this]
    have hne : (S.sizeAt v (w.1 v) : ℂ) ≠ 0 := by exact_mod_cast hsa.ne'
    field_simp
  · have hi' : i = S.G.r + 1 := by omega
    subst hi'
    exact gramLoc_top_psd hB F v ε (w.1 v) Y

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem positivity_bound : P5.ThmPActualCpt → PBASM.PosB := fun hA => PBASM.posB_of hA module_form_pos_compact_support

end Formalism.FourierDecayAlt.P
