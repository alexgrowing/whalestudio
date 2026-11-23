import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffBumpG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightCosetActionMeasurePreserving

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vars

variable (k p ρ : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev XL (σ : Equiv.Perm (Fin p)) : Type :=
  (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)))

abbrev XR : Type := (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ))

variable {k p ρ}

def muL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) : Measure (XL k p ρ σ) :=
  (Bj.μW.prod Bj.μN).prod ((U.muRC k p ρ).prod
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ))))

def muR (Bj : B.RealPlaceData k ρ Wp Wq) : Measure (XR k p ρ) :=
  (Bj.μW'.prod Bj.μN).prod ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))

def splitE (σ : Equiv.Perm (Fin p)) : B.SS k ρ × U.Xi k p 0 ρ σ ≃ᵐ XL k p ρ σ × XR k p ρ where
  toFun q := ((q.1.1, (q.2.1.1, (q.2.2.1, q.2.2.2.1))), (q.1.2, (q.2.1.2, q.2.2.2.2)))
  invFun x := ((x.1.1, x.2.1), ((x.1.2.1, x.2.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : B.SS k ρ × U.Xi k p 0 ρ σ =>
      ((q.1.1, (q.2.1.1, (q.2.2.1, q.2.2.2.1))), (q.1.2, (q.2.1.2, q.2.2.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun x : XL k p ρ σ × XR k p ρ =>
      ((x.1.1, x.2.1), ((x.1.2.1, x.2.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2.2.2))))
    fun_prop

theorem splitE_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (splitE σ) (Bj.μSS.prod (U.muXi k p 0 ρ σ)) ((muL Bj σ).prod (muR Bj)) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite Bj.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have hXi : U.muXi k p 0 ρ σ = ((U.muRC k p ρ).prod (U.muRC k p ρ)).prod
      ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (G.UT p → ℂ)))) := by
    unfold U.muXi U.muXiH
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod (α := U.LW σ → ℂ)]
    rfl

  have h1 := (measurePreserving_prodAssoc
    (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))) (volume : Measure (U.LW σ → ℂ))
    (volume : Measure (G.UT p → ℂ))).symm
  have h2 := (MeasurePreserving.id ((U.muRC k p ρ).prod (U.muRC k p ρ))).prod h1
  have h3 := Formalism.FourierDecayAlt.P.Dx2.SplitM.middle_four_swap_measure_preserving (U.muRC k p ρ) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))
    (volume : Measure (G.UT p → ℂ))
  have h4 := (MeasurePreserving.id Bj.μSS).prod (h3.comp h2)
  have h5 := Formalism.FourierDecayAlt.P.Dx2.SplitM.middle_four_swap_measure_preserving (Bj.μW.prod Bj.μN) (Bj.μW'.prod Bj.μN)
    ((U.muRC k p ρ).prod
      ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ))))
    ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))
  rw [hXi]
  have hall := h5.comp h4
  convert hall using 1
  · funext q; rfl
  · rfl

end vars

section defs

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def GoodL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : Prop :=
  (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ

def GoodR (Bj : B.RealPlaceData k ρ Wp Wq) (y : XR k p ρ) : Prop :=
  (Matrix.of y.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z' ∧ (Matrix.of y.1.2 : B.Mat k ρ) ∈ Nset k ρ

open Classical in

def sxL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : B.Mat k (p + ρ) :=
  if GoodL Bj σ x then
    U.Rn k p ρ (-x.2.1) * U.muP k p ρ (lhOf σ x.2.2.2)ᴴ⁻¹ *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
  else 1

def cL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : ℂ :=
  psi k ρ Bj.z cStd (Matrix.of x.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2.1) *
    G.psi U.betaU (U.subS (lhOf σ x.2.2.2))

def ellL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  cL Bj σ x • ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1))

def NR (y : XR k p ρ) : B.Mat k (p + ρ) :=
  U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) * U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1)

def PsiR (y : XR k p ρ) : Mt k (p + ρ) × Mt k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1, Matrix.of.symm (NR y))

def KrI (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ))
    (q : Mt k (p + ρ) × Mt k (p + ρ)) : Wq →L[ℂ] Wp :=
  star (psi k (p + ρ) B0.z' cStd (Matrix.of q.2)) • (H (y₀ * Matrix.of q.2 * Matrix.of q.1)).comp (B0.π' (Matrix.of q.1)⁻¹)

theorem kr_eq_int (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ q, KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN) := rfl

def FL (Bj : B.RealPlaceData k ρ Wp Wq) (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (q : B.SS k ρ × U.Xi k p 0 ρ σ) : Wq →L[ℂ] Wp :=
  JF.xiP Bj q.1 • (Bj.π (Matrix.of q.1.1.1)).comp
    ((U.psiStar k ρ σ z0 z0' q.2 • H (U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g))).comp
      (Bj.π' (Matrix.of q.1.2.1)⁻¹))

end defs

section djU

variable {k p m : ℕ}

theorem n_col (nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) (b : Fin p) (c : Fin (2 * (p + m) + k + 1))
    (hc : b.val ≤ c.val) : nn c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
  have h := hn.2.1 ⟨b.val, by omega⟩ c hc
  have e : eI k (p + m) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
  rw [e] at h
  rw [h]
  by_cases hcb : c.val = b.val
  · rw [if_pos (Fin.ext hcb), if_pos hcb]
  · rw [if_neg (fun h' => hcb (congrArg Fin.val h')), if_neg hcb]

theorem zh_mul_N (g nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) :
    U.Zh k p m (g * nn) = U.Zh k p m g * Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩) := by
  ext a b
  simp only [U.Zh, Matrix.mul_apply, Matrix.of_apply]
  symm
  refine Finset.sum_bij_ne_zero (fun c _ _ => (⟨c.val, by omega⟩ : Fin (2 * (p + m) + k + 1))) ?_ ?_ ?_ ?_
  · intro c _ _; exact Finset.mem_univ _
  · intro c₁ _ _ c₂ _ _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro c _ hc
    have hcp : c.val < p := by
      by_contra hcp
      apply hc
      rw [n_col nn hn b c (by omega), if_neg (by omega), mul_zero]
    exact ⟨⟨c.val, hcp⟩, Finset.mem_univ _, by simpa using hc, rfl⟩
  · intro c _ _; rfl

theorem det_N_block (nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) :
    (Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun c _ => ?_
    simp only [Matrix.of_apply]
    rw [n_col nn hn c _ le_rfl, if_pos rfl]
  · intro c b hcb
    have hcb' : b.val < c.val := hcb
    simp only [Matrix.of_apply]
    rw [n_col nn hn b _ (le_of_lt hcb'), if_neg (by simp only; omega)]

theorem djU_mul_N (g nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) : U.DjU k p m (g * nn) = U.DjU k p m g := by
  unfold U.DjU
  rw [zh_mul_N g nn hn, Matrix.det_mul, det_N_block nn hn, mul_one]

theorem djU_mul_UW (z : Fin (2 * (p + m) + k + 1) → ℂ) (g h : B.Mat k (p + m)) (hh : h ∈ UWset k (p + m) z) :
    U.DjU k p m (g * h) = U.DjU k p m g := by
  unfold U.DjU
  congr 1
  ext a b
  simp only [U.Zh, Matrix.mul_apply]
  have hcol : ∀ c : Fin (2 * (p + m) + k + 1), h c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
    intro c
    have h1 := congrFun (hh.2.1 ⟨b.val, by omega⟩).1 c
    have e : eI k (p + m) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
    rw [e] at h1
    rw [← Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply h ⟨b.val, by omega⟩ c, h1]
    unfold bvec
    by_cases hcb : c.val = b.val
    · rw [if_pos hcb, Pi.single_apply, if_pos (Fin.ext hcb)]
    · rw [if_neg hcb, Pi.single_apply, if_neg (fun h' => hcb (congrArg Fin.val h'))]
  rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [hcol, if_pos rfl, mul_one]
  · intro c _ hc
    rw [hcol, if_neg (fun h' => hc (Fin.ext h')), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end djU

section split

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gpsi_add (β a b : ℂ) : G.psi β (a + b) = G.psi β a * G.psi β b := by
  unfold G.psi
  rw [← Complex.exp_add, mul_add, Complex.add_re, Complex.ofReal_add, mul_add]

theorem cornerA_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) : U.cornerA a = 0 := by
  unfold U.cornerA; rw [dif_neg (fun h => absurd h.1 (lt_irrefl 0))]

theorem cornerB_zero {p : ℕ} (b : Fin p → Fin 0 → ℂ) : U.cornerB b = 0 := by
  unfold U.cornerB; rw [dif_neg (fun h => absurd h.1 (lt_irrefl 0))]

theorem of_levMt (x : Mt k ρ) : (Matrix.of (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl x) : B.Mat k (p + ρ)) =
    U.embG k p ρ (Matrix.of x) := by
  unfold Formalism.FourierDecayAlt.P.PBM.levMt
  rw [Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]

theorem fl_split (hGS : GaXiSplit) (hPR : PsiRight) (hPA : PsiRnAct) (hPM : PsiMuP)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (y : XR k p ρ)
    (hx : GoodL Bj σ x) (hy : GoodR Bj y) :
    FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g ((splitE σ).symm (x, y)) =
      ellL Bj σ x (KrI B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g) (PsiR y)) := by
  obtain ⟨hh, hν⟩ := hx
  obtain ⟨hh', hν'⟩ := hy
  have uh : IsUnit (Matrix.of x.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hh
  have uν : IsUnit (Matrix.of x.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hν
  have uh' : IsUnit (Matrix.of y.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z').unit _ hh'
  have hH' : (Matrix.of y.1.1 : B.Mat k ρ)ᴴ * Hpk k ρ * Matrix.of y.1.1 = Hpk k ρ := hh'.1

  have hpt : U.gaXi k ρ σ d ((splitE σ).symm (x, y)).2 (fun a => a.elim0) (B.sgs ((splitE σ).symm (x, y)).1 g) =
      sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g * Matrix.of (PsiR y).2 * Matrix.of (PsiR y).1 := by
    have := hGS k p ρ σ d ((splitE σ).symm (x, y)).2 (fun a => a.elim0) (Matrix.of x.1.1) (Matrix.of x.1.2)
      (Matrix.of y.1.1) (Matrix.of y.1.2) g uh uν hH'
    rw [show B.sgs ((splitE σ).symm (x, y)).1 g = (Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g *
      Matrix.of y.1.2 * Matrix.of y.1.1 from rfl]
    convert this using 1
    simp only [sxL, if_pos (show GoodL Bj σ x from ⟨hh, hν⟩), PsiR, NR, of_levMt, Equiv.apply_symm_apply]
    rfl

  have hpi : B0.π' (Matrix.of (PsiR y).1)⁻¹ = Bj.π' (Matrix.of y.1.1)⁻¹ := by
    simp only [PsiR, of_levMt]
    rw [← Formalism.FourierDecayAlt.P.LeftFubiniLemmas.embG_inv uh', hπ']

  have hN : psi k (p + ρ) B0.z' cStd (Matrix.of (PsiR y).2) =
      psi k ρ Bj.z' cStd (Matrix.of y.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper y.2.2)) *
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ y.2.1) := by
    simp only [PsiR, NR, Equiv.apply_symm_apply, hz']
    rw [hPR k p ρ Bj.z' _ _ _ Bj.z'_mem hν', hPA k p ρ Bj.z' _ _ Bj.z'_mem hh']
  have hM := hPM k p ρ Bj.z' y.2.2 Bj.z'_mem
  have hS : U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ((splitE σ).symm (x, y)).2 =
      psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2.1) *
        star (psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ y.2.1)) *
        (G.psi U.betaU (U.subS (lhOf σ x.2.2.2)) * G.psi U.betaU (U.supS (G.upper y.2.2))) := by
    simp only [U.psiStar, U.psiH, splitE, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      cornerA_zero, cornerB_zero, add_zero, gpsi_add]
    rfl
  unfold FL ellL KrI
  rw [hpt, hpi, hS, hN]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, smul_smul, JF.xiP, cL, star_mul', ← hM]
  congr 1
  · simp only [splitE, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk]
    ring

end split

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
