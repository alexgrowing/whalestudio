import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

theorem glGram : GLGram := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn i hi w hw hN
  have hpos : TBBx5.FormNonneg p := TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p
  have hnC : 0 < TBB.normC nn w := by
    unfold TBB.normC
    refine List.prod_pos fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact hnn _
  set c0 : ℝ := 1 / TBB.normC nn w with hc0
  have hc0n : 0 ≤ c0 := by positivity
  let sq : C.LPt → ℝ := fun a => Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a)
  let u : C.LPt → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) := fun a =>
    if ha : D.IsLocPt a i then ((sq a : ℝ) : ℂ) • KB.slv p.T F i hi w a ha.2 else 0
  have hslv : ∀ a (ha : D.IsLocPt a i), PBL.CV (p.T.bs i) (KB.slv p.T F i hi w a ha.2) :=
    fun a ha e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F i hi w a ha hF e
  have hu : ∀ a, PBL.CV (p.T.bs i) (u a) := by
    intro a
    by_cases ha : D.IsLocPt a i
    · simp only [u, dif_pos ha]; exact PBL.cv_smul _ (hslv a ha)
    · simp only [u, dif_neg ha]; exact PBL.cv_zero
  let β : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) →
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → ℂ :=
    fun x y => (c0 : ℂ) * p.form i hi w x y
  have hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (fun a b => β (u a) (u b)) := by
    intro Y'
    refine PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) β PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
      (fun c x hx => PBL.cv_smul c hx) ?_ ?_ ?_ Y' u hu
    · intro x₁ x₂ y c h₁ h₂ hy
      simp only [β, PBL.form_slC p i hi w x₁ x₂ y c h₁ h₂ hy]; ring
    · intro x y₁ y₂ c hx h₁ h₂
      simp only [β, PBL.form_srC p i hi w x y₁ y₂ c hx h₁ h₂]; ring
    · intro x hx
      obtain ⟨ε, hε, hnv⟩ := PBL.nv_of_cv hx
      exact mul_nonneg (by exact_mod_cast hc0n) (hpos i hi w hw.1 x ε hε hnv)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov _ hpsd
  refine ⟨H, i1, i2, i3, V, fun a b => ?_⟩
  rw [← hV]
  simp only [β]
  by_cases ha : D.IsLocPt a i
  · by_cases hb : D.IsLocPt b i
    · simp only [u, dif_pos ha, dif_pos hb]
      rw [formC_smul_l p i hi w _ _ _ (hslv a ha) (PBL.cv_smul _ (hslv b hb)),
        formC_smul_r p i hi w _ _ _ (hslv a ha) (hslv b hb), Complex.conj_ofReal]
      have hrr : p.RR F i w a b = p.form i hi w (KB.slv p.T F i hi w a ha.2) (KB.slv p.T F i hi w b hb.2) := by
        unfold KB.Pl.RR D.RRplace
        rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
        rfl
      unfold TBB.NP
      rw [hrr, hc0]
      simp only [sq]
      push_cast
      ring
    · simp only [u, dif_neg hb]
      rw [formC_zero_r p i hi w _ (hu a)]
      unfold TBB.NP KB.Pl.RR D.RRplace
      rw [dif_neg (fun h => hb h.2)]
      simp
  · simp only [u, dif_neg ha]
    rw [formC_zero_l p i hi w _ (hu b)]
    unfold TBB.NP KB.Pl.RR D.RRplace
    rw [dif_neg (fun h => ha h.1)]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP

theorem Formalism.FourierDecayAlt.P.CutBP.low_level_gram : Formalism.FourierDecayAlt.P.CutBP.GLGram := Formalism.FourierDecayAlt.P.CutBP.glGram
