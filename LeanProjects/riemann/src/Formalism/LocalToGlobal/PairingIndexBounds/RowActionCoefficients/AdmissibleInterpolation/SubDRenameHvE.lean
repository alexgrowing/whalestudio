import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TransposedFrameImageBlockwiseHolds
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace XAAux

section Rule

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem NJ_pos : 0 < NJ X j := by
  unfold NJ NN
  omega

theorem hvE_congr {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h h' : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) (hh' : ∀ k, h' k ≤ n) (e : h = h') : hvE x y c h hh = hvE x y c h' hh' := by
  subst e
  rfl

theorem rename_yV (b : BX X) :
    (yV X.G.Kf (NJ X j)).map ((rename (emX X j b) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →ₐ[X.G.Kf] (X.Pj j).Xsp) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →+* (X.Pj j).Xsp) = yL X j b.1 b.2 := by
  refine Matrix.ext fun a t => ?_
  simp only [Matrix.map_apply, yV, RingHom.coe_coe, rename_X]
  rfl

theorem rename_hvO (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    rename (emX X j b) (hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h) = hvOdd X j b.1 b.2 x c h := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvO, rename_yV]
  unfold hvO hvOdd
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  funext a i
  rw [RingHom.coe_coe, rename_C]

theorem subD_rename_hvE (b : BX X) (ho : ¬ IsOddPos b.2) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NJ X j) :
    subD X Kc j (rename (emX X j b) (hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h hh)) =
      hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvE, rename_yV, ← RingHom.coe_coe (subD X Kc j), map_hvE]
  congr 1
  · funext a i
    rw [RingHom.coe_coe, RingHom.coe_coe, rename_C]
    exact (subD X Kc j).commutes (x a i)
  · have := subD_yL X Kc j b.1 b.2
    unfold ySub at this
    rw [if_neg ho] at this
    exact this

theorem hvE_dy (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NJ X j)
    (hh' : ∀ k, h k ≤ NJ X (j + 1)) :
    hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh =
      hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) c h hh' := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  refine Matrix.ext fun i t => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  exact pair_dy X Kc j b.1 b.2 x i.val (Fin.castLE (hh k) t)

end Rule

end XAAux

theorem xA_of (hS : XShape) : XA := by
  intro p _ X Kc _ _ j x
  have key := polDel_hv X Kc j (fun v s => x ⟨v, s⟩) (fun v s => cX X j ⟨v, s⟩)
    (fun v s k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
    (fun v s => rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)))
    (fun v s _ k => colH_le _ _) (fun v s _ => cMu_toNat X v j s)
    (fun v s _ => by
      rw [← sum_colHt X v j s]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hS p X j ⟨v, s⟩).2.2.2.2.1 k.val)
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  have h1 : (∏ v, ∏ s, rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩))) =
      ∏ v, ∏ s, if IsOddPos s then hvOdd X j v s (x ⟨v, s⟩) (cX X j ⟨v, s⟩) (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
        else rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)) := by
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    split_ifs with ho
    · unfold srcN
      rw [if_pos ho]
      exact XAAux.rename_hvO X j ⟨v, s⟩ _ _ _
    · rfl
  rw [h1, key]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  obtain ⟨-, -, hanti, hle, hc1, hc2, he1, he2, -, -⟩ := hS p X j ⟨v, s⟩
  unfold tgtD
  split_ifs with ho
  · unfold hvOdd' hvO
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hc1, hc2]
  · have hf := highest_vector_full_holds (DA X Kc j) (NJ X j) (muX X j (NJ X j) ⟨v, s⟩) (hanti _) (cX X j ⟨v, s⟩) (eX X j ⟨v, s⟩)
      (hle _) he1 he2 (XAAux.NJ_pos X j) (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s)
    have hnu : nuS X j ⟨v, s⟩ = fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩ := if_neg ho
    have hdet : (Matrix.of fun a i : Fin (NJ X j) => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i.val)).det =
        algebraMap X.G.Kf (DA X Kc j) (Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det := by
      rw [RingHom.map_det]
      rfl
    have h2 : hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) =
        hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s) (cX X j ⟨v, s⟩)
          (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) := by
      rw [XAAux.hvE_dy X Kc j ⟨v, s⟩ _ _ _ _ (fun k => (colH_le _ k.val).trans (NN_le X j))]
      exact XAAux.hvE_congr _ _ _ _ _ _ _ (funext fun k => by rw [hc1, hc2])
    show _ = hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val)
    rw [h2, hf, hdet]
    unfold srcN
    rw [if_neg ho, map_mul, map_mul, rename_C, XAAux.subD_rename_hvE X Kc j ⟨v, s⟩ ho,
      show subD X Kc j (C ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩)) =
        algebraMap X.G.Kf (DA X Kc j) ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩) from
        (subD X Kc j).commutes _, map_pow, mul_pow,
      XAAux.hvE_congr _ _ _ (fun k => colH (nuS X j ⟨v, s⟩) k.val)
        (fun k => colH (fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩) k.val) _ (fun k => colH_le _ k.val) (by rw [hnu])]
    show _ * _ * (dyMat X Kc j v s).det ^ eX X j ⟨v, s⟩ = _
    ring

namespace XAAux

section Span

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem pairD_mem [Infinite Kc] (W : Submodule Kc (XspC (X.Pj (j + 1)) Kc)) (P : DA X Kc j)
    (h : ∀ d0 : X.ZA j → Kc, evD X Kc j d0 P ∈ W) (f : MvPowerSeries (X.ZA j) Kc) : pairD X Kc j P f ∈ W := by
  by_contra hn
  obtain ⟨l, hl, hW⟩ := Submodule.exists_le_ker_of_notMem hn
  refine hl ?_
  rw [pairing_series_linear_form_holds p X Kc j P f l 0 fun d0 => by rw [map_zero, LinearMap.mem_ker.1 (hW (h d0))]]
  simp

theorem map_bidet {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {r n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : map φ (bideterminant K sz hsz I) = bideterminant K' sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem tgtN_mem [CharZero Kc] (hS : XShape) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → Kc) :
    tgtN X Kc j b z ∈ dualWeyl Kc (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b) := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  unfold tgtN nuT
  split_ifs with ho
  · exact highest_vector_mem_odd Kc _ _ (hanti _) _ (hle _) z
  · exact highest_vector_mem_even Kc _ _ (hanti _) _ (hle _) z

end Span

end XAAux

theorem xSpanN_of (hS : XShape) : XSpanN := by
  intro p _ X Kc _ _ _ j x f
  classical
  rw [delF_apply, xA_of hS p X Kc j x]
  refine XAAux.pairD_mem X Kc j _ _ (fun d0 => ?_) f
  rw [map_prod]
  simp only [frame_change_compatibility_holds p X Kc j]
  refine prod_span (R := Kc) (fun b : BX X => {y : XspC (X.Pj (j + 1)) Kc |
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ NJ X (j + 1)) (I : ∀ k, Fin (sz k) → Fin (NJ X (j + 1))),
        shapeDeg sz = nuT X j b ∧ y = rename (emX X (j + 1) b) (bideterminant Kc sz hsz I)}) _ (fun g hg => ?_) _ (fun b => ?_)
  · choose K sz hsz I hsh hgb using hg
    refine Submodule.subset_span ⟨fun b => bideterminant X.G.Kf (sz b) (hsz b) (I b), fun b => ?_, ?_⟩
    · rw [← hsh b]
      exact bidetMem X.G.Kf _ _ _ _ _ _
    · rw [map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hgb b, map_rename, XAAux.map_bidet]
  · have h1 := XAAux.tgtN_mem X Kc j hS b
      (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x b a i))
    rw [standardMonomialSpanDomain Kc] at h1
    have h2 := Submodule.mem_map_of_mem (f := (rename (emX X (j + 1) b) :
      MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc).toLinearMap) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨q, ⟨K, sz, hsz, I, hsh, rfl⟩, rfl⟩
    exact ⟨K, sz, hsz, I, hsh, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
