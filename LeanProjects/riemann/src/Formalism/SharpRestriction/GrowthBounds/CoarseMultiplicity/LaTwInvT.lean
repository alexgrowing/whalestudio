import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FockRAddRight

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

abbrev vecH (TT : Finset (Fin n')) : TT × Bool → Bool := fun x => x.2

theorem HHL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHL (O := O) ι σ TT aT bT (colSpan W ℓ) ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val ℓ) := by
  have e := tensor_lattice_twist_eq hS m (vecH TT) (hhDegs TT aT bT) (fun x => x.1.val) ℓ hℓ
  unfold LatM
  rw [← e]
  rfl

theorem HHLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHLe p ι σ w TT aT bT e ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  have := hS.frac_O
  have e1 : (fun x : TT × Bool => H0 O m (letterWt m (hhDegs TT aT bT x) (vecH TT x)) (LeAt p ι σ w x.1.val.val e)) =
      fun x => nablaLTw O Kf m (letterWt m (hhDegs TT aT bT x) (vecH TT x))
        (la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  unfold LatM
  rw [← e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

def XiH (c : Kf) : ↥(VHH (m := m) Kf TT aT bT) →ₗ[Kf] Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) :=
  TY (vec := vecH TT) (d := hhDegs TT aT bT) thK c

theorem XiH_apply (c : Kf) (P Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT))) :
    XiH thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf)
      (Q : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf) :=
  TY_apply (vec := vecH TT) (d := hhDegs TT aT bT) thK c P Q

abbrev zK (Kf : Type) [Field Kf] (p κ : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : Kf :=
  (p : Kf) ^ κ / (((∏ x : TT × Bool, (hhDegs TT aT bT x).factorial : ℕ) : ℕ) : Kf)

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (ReHH p ι σ w TT aT bT e.dual)) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (ReHH' p ι σ w TT aT bT e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD
      (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun x => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HHLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HHLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun x => ((la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun x => dualM hS x.1.val.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT))
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (HHL (O := O) ι σ TT aT bT (colSpan W ((ℓ⁻¹).transpose)))) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (dualLat O Kf (HHL (O := O) ι σ TT aT bT (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD (fun x => la_tw ι σ x.1.val.val ℓ)
    (fun x => la_tw_det _ _ _ _ hℓ) u y0 ((HHL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HHL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((ℓ⁻¹).transpose)) =
      fun x => ((la_tw ι σ x.1.val.val ℓ)⁻¹).transpose :=
    funext fun x => la_tw_invT x.1.val.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
