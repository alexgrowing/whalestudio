import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts

namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

section lev

variable {k : ℕ}

theorem castV_mulVec' {a b : ℕ} (h : a = b) (M : B.Mat k a) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h (M *ᵥ v) = D.castM h M *ᵥ D.castV h v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]

theorem zL_lift {o ρ r : ℕ} (h : o + ρ = r) (v : Fin (2 * ρ + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (D.castV h (liftVec k o ρ v)) = v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]
  funext i
  have := Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_levPos_gen (k := k) o ρ v i
  simpa [Formalism.FourierDecayAlt.P.Dx2.Tower.zL, levPos] using this

theorem zL_smul {o ρ r : ℕ} (h : o + ρ = r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (c • v) = c • Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v := by
  funext i; simp [Formalism.FourierDecayAlt.P.Dx2.Tower.zL]

theorem hermitian_form_anisotropic_part {m : ℕ} (v w : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) (hw : inWb k m w) :
    herm (Hpk k m) v w = herm (Hb k) (wbPart k m v) (wbPart k m w) := by
  have := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m w)
  rwa [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hw] at this

theorem herm_zL {o ρ r : ℕ} (h : o + ρ = r) (v w : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k ρ) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h w) = herm (Hpk k r) v w := by
  rw [hermitian_form_anisotropic_part _ _ (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h v hv) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h w hw),
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, hermitian_form_anisotropic_part v w hv hw]

theorem inWb_last {r : ℕ} (v : Fin (2 * (r - r) + k + 1) → ℂ) : inWb k (r - r) v := by
  intro i hi; exfalso; have := i.isLt; omega

theorem inWb_liftLast {r : ℕ} (h : r + (r - r) = r) (v : Fin (2 * (r - r) + k + 1) → ℂ) :
    inWb k r (D.castV h (liftVec k r (r - r) v)) := by
  intro i hi
  simp only [D.castV]
  apply Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_out_gen
  simp only [Fin.val_cast]
  omega

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nuR (p : KB.Pl P Wp Wq) : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) (by omega) p.ν'

def m0R (p : KB.Pl P Wp Wq) : B.Mat P.k (P.r - P.r) :=
  fun i j => p.m₀ ⟨i.val + P.r, by have := i.isLt; omega⟩ ⟨j.val + P.r, by have := j.isLt; omega⟩

theorem base_point_block_eq (p : KB.Pl P Wp Wq) :
    D.castM (by omega : P.r + (P.r - P.r) = P.r) (ιLev P.k P.r (P.r - P.r) (m0R p)) = p.m₀ := by
  obtain ⟨-, -, -, ⟨hmU, hmfix⟩, -⟩ := p.hF
  have hme : ∀ a : Fin P.r, p.m₀ *ᵥ ee P.k P.r a = ee P.k P.r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin P.r, p.m₀ *ᵥ es P.k P.r a = es P.k P.r a := fun a => (hmfix a a.isLt).2
  have hcol : ∀ (i j : Fin (2 * P.r + P.k + 1)), (j.val < P.r ∨ P.r + P.k < j.val) →
      p.m₀ i j = if i = j then 1 else 0 := by
    intro i j hj
    rcases hj with hj | hj
    · have e : bvec j = ee P.k P.r ⟨j.val, hj⟩ := by simp [ee, eI]
      have := congrFun (hme ⟨j.val, hj⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
    · have hj2 := j.isLt
      have e : bvec j = es P.k P.r ⟨2 * P.r + P.k - j.val, by omega⟩ := by
        simp only [es, esI]; congr 1; ext; simp; omega
      have := congrFun (hms ⟨2 * P.r + P.k - j.val, by omega⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
  have hrow : ∀ (i j : Fin (2 * P.r + P.k + 1)), (i.val < P.r ∨ P.r + P.k < i.val) →
      (P.r ≤ j.val ∧ j.val ≤ P.r + P.k) → p.m₀ i j = 0 := by
    intro i j hi hj
    have hmj : (p.m₀ *ᵥ bvec j) i = p.m₀ i j := by
      simp [mulVec, dotProduct, bvec, Pi.single_apply]
    rcases hi with hi | hi
    · have h1 := herm_es (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨i.val, hi⟩
      rw [← hms ⟨i.val, hi⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_es] at h1
      have hi' : eI P.k P.r ⟨i.val, hi⟩ = i := by ext; simp [eI]
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
    · have hi2 := i.isLt
      have h1 := herm_ee (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨2 * P.r + P.k - i.val, by omega⟩
      rw [← hme ⟨2 * P.r + P.k - i.val, by omega⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_ee] at h1
      have hi' : esI P.k P.r ⟨2 * P.r + P.k - i.val, by omega⟩ = i := by ext; simp [esI]; omega
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
  ext i j
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold ιLev
  by_cases hi : P.r ≤ i.val ∧ i.val ≤ P.r + P.k <;> by_cases hj : P.r ≤ j.val ∧ j.val ≤ P.r + P.k
  · rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    simp only [m0R]
    congr 1 <;> ext <;> simp <;> omega
  · rw [dif_pos (by simp; omega), dif_neg (by simp; omega), hcol i j (by omega)]
    rw [if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [dif_neg (by simp; omega)]
    rw [hrow i j (by omega) hj, if_neg]
    · intro h; apply hi; have := congrArg Fin.val h; simp at this; omega
  · rw [dif_neg (by simp; omega), hcol i j (by omega)]
    congr 1
    apply propext; constructor
    · intro h; ext; have := congrArg Fin.val h; simpa using this
    · intro h; subst h; rfl

theorem levFrame_nuR (p : KB.Pl P Wp Wq) : LevFrame p (nuR p) (m0R p) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := p.hF
  have h : P.r + (P.r - P.r) = P.r := by omega
  have hZ : (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z := by
    show (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z
    rw [← p.T.z_lev P.r le_rfl, zL_lift]
  have hZ' : (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z' := by
    show (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z'
    rw [← p.T.z'_lev P.r le_rfl, zL_lift]
  have hz := p.T.base.z_mem
  have hz' := p.T.base.z'_mem
  have hblk := base_point_block_eq p

  set Lf : (Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) → (Fin (2 * P.r + P.k + 1) → ℂ) :=
    fun v => D.castV h (liftVec P.k P.r (P.r - P.r) v) with hLf
  have hLm : ∀ v, Lf (m0R p *ᵥ v) = p.m₀ *ᵥ Lf v := by
    intro v
    simp only [hLf]
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mulVec_lift, castV_mulVec', hblk]
  have hLh : ∀ v w, herm (Hpk P.k (P.r - P.r)) v w = herm (Hpk P.k P.r) (Lf v) (Lf w) := by
    intro v w
    rw [← herm_zL h (Lf v) (Lf w) (inWb_liftLast h v) (inWb_liftLast h w), zL_lift, zL_lift]
  refine ⟨Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h p.ν' hν, hblk, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact inWb_last _
  · rw [hZ', nuR, herm_zL h _ _ hν hz', hνz]
  · rw [nuR, herm_zL h _ _ hν hν, hνν]
  · apply B2x4.mem_UH_of_herm
    intro x y
    rw [hLh, hLh x y, hLm, hLm, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]
  · intro a _; exact absurd a.isLt (by omega)
  · have e1 : m0R p *ᵥ (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.m₀ *ᵥ p.T.base.z') := by
      have := congrArg (Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h) (hLm (p.T.bs P.r).z')
      rw [zL_lift] at this
      rw [this, hZ']
      simp only [hLf]
      rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h _ hz']
    rw [e1, hmz, zL_smul, ← hZ, hZ', hZ, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz,
      Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz']

end place

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem levFrameExists_statement : PBI.LevFrameExists := by
  intro Wp Wq _ _ _ _ _ _ P p
  exact ⟨PBI.nuR p, PBI.m0R p, PBI.levFrame_nuR p⟩

end Formalism.FourierDecayAlt.P
