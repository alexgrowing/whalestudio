import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

open GlobalTheory.LocMod (Place Frame)

section Entries

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem epsV_even (t : T) (w : Pl D.host.E) {j : ℕ} (hj : Even j) : epsV G t w (D.R.m, j) = 1 := by
  rw [epsV_apply]
  split_ifs
  · refine Units.ext ?_
    rw [sgnAt, GlobalTheory.SplitFlip.diagGL_val, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rw [if_neg (fun h => (Nat.not_odd_iff_even.2 hj) h.1)]
    rfl
  · rfl

theorem baseM_val (t : T) (w : Pl D.host.E) (j : ℕ) : (baseM G t w j).val = diagonal fun x =>
    if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1 := by
  unfold baseM
  split_ifs with h
  · subst h
    have e : (stair (locGrid G t w) (unifAt w) (cosExp G w) 0)⁻¹ =
        GlobalTheory.SplitFlip.diagGL fun x : Fin ((locGrid G t w).rank ((locGrid G t w).m, 0)) =>
          (unifAt w ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) 0)))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      rw [Units.val_mul, stair, GlobalTheory.SplitFlip.diagGL_val, GlobalTheory.SplitFlip.diagGL_val, diagonal_mul_diagonal, Units.val_one,
        ← diagonal_one]
      congr 1
      funext x
      simp
    have e2 := congrArg Units.val e
    rw [GlobalTheory.SplitFlip.diagGL_val] at e2
    refine e2.trans ?_
    congr 1
    funext x
    simp
  · rw [Units.val_one, ← diagonal_one]

theorem mvFr_entries (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) (p : Place D (Kw w))
    {j : ℕ} (hj : j < D.R.m) (hje : Even j) (a : GA D (G.V (.grid D.R.m j)))
    (ha : (mt _ a).map p.π * (frRow S.B t w j hj.le).β = (frRow S.B t w j hj.le).β * (baseM G t w j).val) {c : ℕ}
    (hc : topRank (locGrid G t w) j + c = (locGrid G t w).rank (D.R.m, j)) (r : Fin (G.V (.grid D.R.m j)).rank) :
    (∀ q, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inl q) =
      ((frameMat _ _ (G.rowDec j hj).ι).map (algebraMap D.host.E (Kw w)) * (loc w (S.βp j)).val) r
        (Fin.cast (topRank_eq G t w hj.le) q)) ∧
    ∀ (q : Fin c) (q' : Fin (D.R.m - 1 - j)), q'.val = q.val →
      (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inr q) =
        algebraMap D.host.E (Kw w) ((G.rowDec j hj).a r q') * frameSign (Kw w) (D.R.m - 1 - j) q' := by
  have hrow := S.row t ht w hw j hj
  unfold IsSumFrame at hrow
  have hT := topRank_eq G t w hj.le
  have key : ∀ z, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r z =
      (loc w (S.B.β D.R.m j)).val r (Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc z)) *
        (if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * ((frame hc z).val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1) := by
    intro z
    show ((mt _ a).map p.π * (frRow S.B t w j hj.le).β * (epsV G t w (D.R.m, j)).val) r (frame hc z) = _
    rw [epsV_even t w hje, Units.val_one, Matrix.mul_one, ha, baseM_val, mul_diagonal]
    rfl
  refine ⟨fun q => ?_, fun q q' hq => ?_⟩
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inl q)) =
        frame (G.rowDec j hj).rank (Sum.inl (Fin.cast hT q)) := by
      ext; simp [frame]
    have e2 := congrFun (congrFun hrow r) (Sum.inl (Fin.cast hT q))
    rw [submatrix_apply, id, fromCols_apply_inl] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inl q)).val + 1 - topRank (locGrid G t w) j = 0 := by
      have := q.2; simp [frame]
    rw [e3]
    simp
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inr q)) =
        frame (G.rowDec j hj).rank (Sum.inr q') := by
      ext; simp [frame, hq, hT]
    have e2 := congrFun (congrFun hrow r) (Sum.inr q')
    rw [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inr q)).val + 1 - topRank (locGrid G t w) j = q'.val + 1 := by
      simp [frame, hq]; omega
    rw [e3]
    have hu : ((unifAt w : Kw w)) ≠ 0 := Units.ne_zero _
    split_ifs
    · field_simp
    · simp

end Entries

section Main

section Alg

variable {k : Type} [Field k]

theorem alg_e (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i ≤ σ) : y * 1 = (x ^ σ)⁻¹ * x ^ (σ - i) * (y * x ^ i) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + e := ⟨σ - i, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

theorem scalar_inv_pow_mul_cancel (x y : k) (hx : x ≠ 0) (σ : ℕ) : y * 1 = (x ^ σ)⁻¹ * (x ^ σ * y) := by
  field_simp

theorem alg_e' (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i < σ) :
    y * -1 = (x ^ σ)⁻¹ * (-(-((-x) ^ σ * x ^ σ)) / x) * (-1 / x) ^ (σ - 1 - i) * (y * ((-x) ^ i)⁻¹) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + 1 + e := ⟨σ - 1 - i, by omega⟩
  have hx' : -x ≠ 0 := neg_ne_zero.2 hx
  rw [show i + 1 + e - 1 - i = e by omega, show (-1 / x) = (-x)⁻¹ by rw [neg_div, one_div, neg_inv], inv_pow, pow_add (-x),
    pow_succ (-x)]
  have ha : (-x) ^ i ≠ 0 := pow_ne_zero _ hx'
  have hb : (-x) ^ e ≠ 0 := pow_ne_zero _ hx'
  generalize (-x) ^ i = a at ha ⊢
  generalize (-x) ^ e = b at hb ⊢
  field_simp

end Alg

section Core

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_vecB_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    GlobalTheory.RowUnf.coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB =
      GlobalTheory.RowUnf.midCol d h := by
    refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
    show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
        Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  show GlobalTheory.RowUnf.coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, e]
  funext k
  show ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h k j * x = _
  simp [GlobalTheory.RowUnf.midCol, mul_comm]

theorem nLine_norm (x : D.host.E) :
    star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => x) ⬝ᵥ (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => x) = -(star x * x) := by
  show ∑ i : Fin 1, star x * ∑ j : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i j * x = _
  simp [GlobalTheory.RowUnf.nLine_gram]

end Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem BesP₂ (ch : Choice R) : BesP ch := by
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have hjm : j < D.R.m := by omega
  have hje : Even j := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  have E := mvFr_entries ch.S.toGridChoice (Set.mem_univ t) hw p hjm hje a ha hc
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x => by
    rw [Place.pr, hp.2.1]
    exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hxi : p.xi = algebraMap D.host.E (Kw w) D.host.xi0 := hpr _
  have hx0 : algebraMap D.host.E (Kw w) D.host.xi0 ≠ 0 := hxi ▸ GlobalTheory.LocMod.Witness.xi_ne p
  have hTA : (locGrid ch.G t w).rank (D.R.m, j) + j + 1 = topRank (locGrid ch.G t w) j + D.R.m :=
    (topRank_add (G := locGrid ch.G t w) one_le_sLen j).symm
  have hc' : c = 2 * σ + 1 := by omega
  have hc2 : D.R.m - 1 - j = 2 * σ + 1 := by omega
  refine ⟨hc', fun r q => ?_, fun i q hiq r => ?_, fun q hq r => ?_, fun i q hiq r => ?_⟩
  · refine ((E r).1 q).trans ?_
    have e1 : ((besAt ch.G hM j σ hj vN).d.i₀ * (besAt ch.G hM j σ hj vN).o.iA) =
        frameMat (ch.G.V (Node.grid D.R.m j)) (ch.G.V (Node.top j)) (ch.G.rowDec j hjm).ι :=
      coreMat_iA_bes (ch.G.rowDec j hjm) hc2
    rw [e1]
    erw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact congrArg₂ (· * ·) (hpr _).symm rfl
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e r i = (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * D.host.xi0 ^ i.val := by
      show (((ch.G.rowDec j hjm).iso σ (by omega) * diagonal (GlobalTheory.RowChain.lam σ) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [HermitianOrthogonalExtensionData.iso, submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i) = _
      exact congrArg _ (Fin.ext (by simp [hiq]))
    rw [hd, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact alg_e _ _ hx0 σ i.val (by omega)
  · refine ((E r).2 q ⟨σ, by omega⟩ hq.symm).trans ?_
    have hv : (besAt ch.G hM j σ hj vN).d.i₀ *ᵥ vecB (besAt ch.G hM j σ hj vN).o (besAt ch.G hM j σ hj vN).ζ =
        fun k => D.host.xi0 ^ σ * (ch.G.rowDec j hjm).a k ⟨σ, by omega⟩ :=
      coreMat_vecB_bes (ch.G.rowDec j hjm) hc2 (D.host.xi0 ^ σ)
    rw [hv, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact scalar_inv_pow_mul_cancel _ _ hx0 σ
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e' r i =
        (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * (star (D.host.xi0 ^ i.val))⁻¹ := by
      show (((ch.G.rowDec j hjm).a.submatrix id (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev) *
        diagonal (fun a => (star (GlobalTheory.RowChain.lam (D := D) σ a))⁻¹) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i).rev = _
      exact congrArg _ (Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega))
    have hz : p.hz (besAt ch.G hM j σ hj vN) = algebraMap D.host.E (Kw w) (-(star (D.host.xi0 ^ σ) * D.host.xi0 ^ σ)) := by
      rw [Place.hz, hpr]
      exact congrArg _ (nLine_norm _)
    have hs : ∀ n : ℕ, star (D.host.xi0 ^ n) = (-D.host.xi0) ^ n := fun n => by
      rw [star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    rw [hd, hz, hpr, hxi, hs, hs, frameSign, if_pos (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    simp only [map_mul, map_neg, map_pow, map_inv₀]
    exact alg_e' _ _ hx0 σ i.val i.2

end Main

theorem Big₂ : Big fun ch => BesP ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ R _ _ ch _ _ => BesP₂ (R := R) ch⟩⟩

end GlobalTheory.FlatPlace
