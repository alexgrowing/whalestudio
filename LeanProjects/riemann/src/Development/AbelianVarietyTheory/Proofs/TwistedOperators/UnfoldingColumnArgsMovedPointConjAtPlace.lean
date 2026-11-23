import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.StdFrames

namespace GlobalTheory.TopLevelInv

section ColCoord

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem map_mt_cpt_colCoord (w : Pl D.host.E) (V : HSp D) (g : GA D V) :
    Matrix.map (Formalism.L2.Theta.mt V g) ((cpt w).comp (toEAf D)) = (loc w (Lev.finE V g)).val := rfl

theorem frAt_actO_colCoord (w : Pl D.host.E) {S T : HSp D} (β' : GL (Fin T.rank) (Lev.EAf D))
    (β : GL (Fin S.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    GlobalTheory.FunObj.frAt w β' β (actO S T g h x) =
      (loc w (β'⁻¹ * Lev.finE T h * β')).val * GlobalTheory.FunObj.frAt w β' β x *
        (loc w (β⁻¹ * Lev.finE S g * β))⁻¹.val := by
  have e0 : ∀ y : WO S T, GlobalTheory.FunObj.frAt w β' β y =
      (loc w β'⁻¹).val * Matrix.map y ((cpt w).comp (toEAf D)) * (loc w β).val := by
    intro y
    rw [GlobalTheory.FunObj.frAt, GlobalTheory.FunObj.Comparison₂.fr, Matrix.map_mul, Matrix.map_mul]
    rfl
  have e1 : Matrix.map (actO S T g h x) ((cpt w).comp (toEAf D)) =
      (loc w (Lev.finE T h)).val * Matrix.map x ((cpt w).comp (toEAf D)) * (loc w (Lev.finE S g))⁻¹.val := by
    rw [actO, Matrix.map_mul, Matrix.map_mul, map_mt_cpt_colCoord, map_mt_cpt_colCoord, map_inv, map_inv]
  rw [e0, e0, e1]
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hA : ∀ {c : Type} [Fintype c] (Y : Matrix (Fin T.rank) c (Kw w)), (loc w β').val * ((loc w β')⁻¹.val * Y) = Y := by
    intro c _ Y; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hB : (loc w β).val * ((loc w β)⁻¹.val * ((loc w (Lev.finE S g))⁻¹.val * (loc w β).val)) =
      (loc w (Lev.finE S g))⁻¹.val * (loc w β).val := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [hA, hB]

theorem loc_finE_u_colCoord {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {X : Node} (hX : DefNode D.R.m X) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : loc w (Lev.finE (G.V X) (S.N.u X).1) = 1 := by
  classical
  obtain ⟨P', a, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, hoff⟩ := S.N.u_supp X hX
  have hnot : ¬ Off S.N.S w := by
    intro h0
    have h3 := S.N.off w h0
    rcases Finset.mem_union.1 hw with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact h3.1 ((G.pl.under_w hv).symm ▸ hv)
    · exact h3.2.1 t ht w h rfl
  obtain ⟨q, hq, hqw⟩ : ∃ q ∈ S.N.S, ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    unfold Off at hnot; push_neg at hnot; exact hnot
  have hz : cpt w (toEAf D ((∑ PP ∈ P', es PP) + cA D (∑ PP ∈ P', es PP))) = 0 := by
    have hA : ∀ PP ∈ P', cpt w (toEAf D (es PP)) = 0 := fun PP hPP =>
      (cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq (e ▸ hqw)
    have hB : ∀ PP ∈ P', cpt w (sg D (toEAf D (es PP))) = 0 := by
      intro PP hPP
      refine cpt_sg_eq_zero ((cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq ?_)
      rw [← e]; exact (natCast_mem_cP w q).2 hqw
    simp only [map_add, toEAf_cA, map_sum]
    rw [Finset.sum_eq_zero hA, Finset.sum_eq_zero hB, add_zero]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun z => cpt w (toEAf D z)) (hsupp i j)
  simp only [map_mul, hz, zero_mul] at h1
  have h2 : cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = cpt w (toEAf D ((1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (AE D)) i j)) := by
    have := h1.symm
    rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero] at this
    exact this
  change cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (Kw w)) i j
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem submatrix_cast_mul_colCoord {K : Type} [CommRing K] {r n n' p r' p' : ℕ} (M : Matrix (Fin r) (Fin n) K)
    (N : Matrix (Fin n) (Fin p) K) (f : Fin r' → Fin r) (h : n' = n) (g : Fin p' → Fin p) :
    M.submatrix f (Fin.cast h) * N.submatrix (Fin.cast h) g = (M * N).submatrix f g :=
  Matrix.submatrix_mul_equiv M N f (finCongr h) g

end ColCoord

end GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem conj_inv_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : (b⁻¹ * f⁻¹ * b)⁻¹ = b⁻¹ * f * b := by group

theorem conj_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : b⁻¹ * f⁻¹ * b = (b⁻¹ * f * b)⁻¹ := by group

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem colAt_movedPt_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  intro D T L sc G W U S t ht j hj k w hw x
  have hu := loc_finE_u_colCoord S ht (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) hw
  set k' : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hk'def
  have hk : ∀ β : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D),
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k' : GA D (G.V (.top (j + 1)))) * β) =
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * β) := by
    intro β
    simp only [hk'def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu, inv_one, one_mul, mul_one]
  have hκ : (kapAt S t j hj k w).val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1))).val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := rfl
  have hκi : (kapAt S t j hj k w)⁻¹.val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1)))⁻¹.val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
    have h0 : (kapAt S t j hj k w)⁻¹.val =
        (loc w ((S.βp (j + 1))⁻¹ * (Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))))⁻¹ *
          S.βp (j + 1))).val.submatrix (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
      rw [kapAt, ← map_inv]; rfl
    rw [h0, conj_inv_colCoord, map_inv]
  funext i
  rcases eq_or_ne i (j + 1) with rfl | h1
  · rw [colAt_eq S t w _ hj]
    simp only [movedPt, Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove, Function.update_self]
    rw [colAt_eq S t w x hj, hκ, inv_one, map_one, mul_one, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      map_inv (Lev.finE (G.V (.top (j + 1)))), ← map_inv (loc w), conj_inv_inv_colCoord, hk, submatrix_cast_mul_colCoord]
  rcases eq_or_ne i j with rfl | h2
  · rw [colAt_eq S t w _ (show i < D.R.m by omega)]
    rw [movedPt, Function.update_of_ne (show (⟨i, by omega⟩ : Fin D.R.m) ≠ ⟨i + 1, hj⟩ by simp [Fin.ext_iff]),
      Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_self, colAt_eq S t w x (show i < D.R.m by omega), hκi, inv_one,
      map_one, mul_one, inv_mul_cancel, map_one, inv_one, Units.val_one, Matrix.mul_one,
      map_inv (Lev.finE (G.V (.top (i + 1)))), conj_inv_colCoord, map_inv (loc w), hk, submatrix_cast_mul_colCoord]
  by_cases hi : i < D.R.m
  · have hm : movedPt t j hj k' x ⟨i, hi⟩ = x ⟨i, hi⟩ := by
      rw [movedPt, Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ by simp [Fin.ext_iff, h1]),
        Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ by simp [Fin.ext_iff, h2])]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, colAt_eq S t w _ hi, colAt_eq S t w x hi, hm]
  · simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.colAt, dif_neg hi]

end GlobalTheory.TopLevelInv
