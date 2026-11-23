import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose

noncomputable section

namespace HeightCancellation.C2

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB SquareStatements.Sing
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)

variable {p q : ℕ}

theorem col_val (a : Fin (p + q)) : (SquareStatements.Sing.col p q a : ℕ) = if (a : ℕ) < p then q + a else a - p := by
  unfold SquareStatements.Sing.col
  split_ifs <;> rfl

theorem prod_col {R : Type} [CommRing R] (f : Fin (p + q) → R) (i : Fin (p + q)) :
    ∏ a ∈ Finset.Iic i, f (SquareStatements.Sing.col p q a) = (∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => q ≤ c ∧ (c : ℕ) ≤ q + i, f c) *
      ∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i, f c := by
  rw [← Finset.prod_union (Finset.disjoint_filter.2 fun c _ h h' => by omega)]
  refine Finset.prod_bij (fun a _ => SquareStatements.Sing.col p q a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    have h1 : (a : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 ha)
    have h2 := a.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, col_val]
    split_ifs <;> omega
  · intro a _ b _ h
    have h1 := congrArg Fin.val h
    have h2 := a.2
    have h3 := b.2
    rw [col_val, col_val] at h1
    refine Fin.ext ?_
    split_ifs at h1 <;> omega
  · intro c hc
    have h2 := c.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with hc | hc
    · refine ⟨⟨c - q, by omega⟩, Finset.mem_Iic.2 (show c - q ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_pos (show c - q < p by omega)]
      show q + (c - q) = c
      omega
    · refine ⟨⟨c + p, by omega⟩, Finset.mem_Iic.2 (show c + p ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_neg (show ¬ c + p < p by omega)]
      show c + p - p = c
      omega

open Classical in
theorem prod_diag {R : Type} [CommRing R] {B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hB : B.BlockTriangular id)
    (i : Fin (p + q)) : ∏ a ∈ Finset.Iic i, B (SquareStatements.Sing.col p q a) (SquareStatements.Sing.col p q a) =
      detFac p i B * if IsProperStep (p + q) p i then ∏ c ∈ stepCols (p + q) p i, B c c else 1 := by
  have hi := i.2
  rw [prod_col (fun c => B c c), detFac, MinorCalc.minorIJ_self_of_triangular B hB,
    MinorCalc.minorIJ_self_of_triangular B hB]
  unfold IsProperStep stepCols wIdx omIdx
  have key : ∀ {P Q : Fin (p + q) → Prop} [DecidablePred P] [DecidablePred Q], (∀ c, P c ↔ Q c) →
      ∏ c ∈ Finset.univ.filter P, B c c = ∏ c ∈ Finset.univ.filter Q, B c c := fun h => by
    rw [Finset.filter_congr fun c _ => h c]
  have key0 : ∀ {P : Fin (p + q) → Prop} [DecidablePred P], (∀ c, ¬ P c) →
      ∏ c ∈ Finset.univ.filter P, B c c = 1 := fun h => by
    rw [Finset.filter_eq_empty_iff.2 fun c _ => h c, Finset.prod_empty]
  by_cases hN : (i : ℕ) + 1 = p + q
  · rw [if_pos (by omega), if_pos hN, if_neg (fun h => h.2 hN), mul_one]
    congr 1
    · exact key fun c => by have := c.2; omega
    · exact key fun c => by have := c.2; omega
  · rw [if_neg hN, mul_one]
    rcases lt_trichotomy ((i : ℕ) + 1) p with h | h | h
    · rw [if_neg (by omega), if_pos ⟨h.ne, hN⟩, one_mul, key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega), mul_one]
      exact key fun c => by rw [if_pos h.le]; omega
    · rw [if_pos h.ge, if_neg (fun h' => h'.1 h), key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega)]
      congr 1
      exact key fun c => by have := c.2; omega
    · rw [if_pos h.le, if_pos ⟨h.ne', hN⟩]
      congr 1
      · exact key fun c => by have := c.2; omega
      · exact key fun c => by rw [if_neg (by omega)]; omega

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {N : ℕ}

theorem val_detFac (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) (j : ℕ) (i : Fin N) : ValAt ξ z (detFac j i A) (detFac j i h) := by
  choose _ s hs hs' using hv
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  exact ⟨hz, detFac j i (Matrix.of s), by rw [e1, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map],
    e2 ▸ (PositivityTheory.Xgp.c_bm_exists_hom.detFac_map (Scheme.stalkClosedPointTo z).hom i (Matrix.of s)).symm⟩

theorem val_pl (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) {u : Finset (Fin N) → Ω} {v : Finset (Fin N) → ℂ}
    (hu : ∀ I, ValAt ξ z (u I) (v I)) (C : Finset (Fin N)) :
    ValAt ξ z (∑ I, u I * minorIJ A I C) (∑ I, v I * minorIJ h I C) := by
  choose _ s hs hs' using hv
  choose _ t ht ht' using hu
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  refine ⟨hz, ∑ I, t I * minorIJ (Matrix.of s) I C, ?_, ?_⟩
  · rw [e1, map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map, ht]
  · rw [e2]
    refine (map_sum (Scheme.stalkClosedPointTo z).hom _ _).trans (Finset.sum_congr rfl fun I _ => ?_)
    exact (map_mul (Scheme.stalkClosedPointTo z).hom _ _).trans (congrArg₂ (· * ·) (ht' I)
      (CPts.minorIJ_map (Scheme.stalkClosedPointTo z).hom (Matrix.of s) I C).symm)

end Val

end HeightCancellation.C2

open AlgebraicGeometry Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB HeightCancellation.C2 SquareStatements.Sing in
theorem HeightCancellation.c2 : SquareStatements.Sing.C2 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐' z wb F τ B h hF gd hval hx ⟨bB, tB, _, _, _, hv⟩ i
  classical
  have hz := 𝔐'.all (centre z)
  have hT : ((F.T τ).map (algebraMap M.Ω Φ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (hF.1 τ).2
  have bT : IsBlockDiag D.p ((F.T τ).map (algebraMap M.Ω Φ)) := (hF.1 τ).1.map _
  have bX : IsBlockDiag D.p (inFrame M F τ B) := ((bT.inv hT.isUnit).mul (M.g_block τ)).mul bB
  have e : (F.T τ).map (algebraMap M.Ω Φ) * inFrame M F τ B = M.g τ * B := by
    rw [inFrame, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hT.isUnit]
  have e1 : algebraMap M.Ω Φ (detFac D.p i (F.T τ)) * detFac D.p i (inFrame M F τ B) =
      detFac D.p i (M.g τ) * detFac D.p i B := by
    rw [← MinorCalc.detFac_mul i bB, ← e, MinorCalc.detFac_mul i bX, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map]
  have e2 : algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') *
      ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k') = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow₀, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ ((map_ne_zero _).2 (hx k)))]
  have vd := val_detFac hz hv D.p i
  refine ⟨fun k hk m => ?_, fun hk => ?_⟩
  · have hp : IsProperStep (D.p + D.q) D.p i := by
      by_contra hn
      rw [(M.blk_none (τ, i)).2 hn] at hk
      cases hk
    have e3 := CPts.frame_gen M hF (RingHom.id Φ) (p := (τ, i)) hk m bX bB tB e
    simp only [RingHom.id_apply] at e3
    have v2 := val_pl hz hv (fun I => hval _ (gd.2.1 ⟨k, m⟩ I).1) (stepCols (D.p + D.q) D.p i)
    convert CxVal.mul vd v2 using 1
    rw [prod_diag tB, if_pos hp]
    linear_combination (-(∏ c ∈ stepCols (D.p + D.q) D.p i, B c c) * y ⟨k, m⟩ *
        ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
      (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
      (detFac D.p i (inFrame M F τ B) * ∑ I, algebraMap M.Ω Φ (F.u ⟨k, m⟩ I) *
        minorIJ (inFrame M F τ B) I (stepCols (D.p + D.q) D.p i)) * e2
  · have hp : ¬ IsProperStep (D.p + D.q) D.p i := (M.blk_none (τ, i)).1 hk
    obtain ⟨h0, r1, r2⟩ := gd.2.2 (τ, i) hk
    have v1 := hval _ r1
    have v2 := hval _ r2
    refine ⟨fun hv0 => ?_, ?_⟩
    · have v3 := CxVal.mul v1 v2
      rw [← map_mul, mul_inv_cancel₀ h0, map_one, hv0, zero_mul] at v3
      exact zero_ne_one (CxVal.unique v3 (CxVal.one hz))
    · have e3 := congrArg (algebraMap M.Ω Φ) (hF.2.2.2 (τ, i) hk)
      rw [map_mul, map_mul] at e3
      convert CxVal.mul vd v1 using 1
      rw [prod_diag tB, if_neg hp]
      linear_combination (-algebraMap M.Ω Φ (M.lam (τ, i)) *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
        (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
        (detFac D.p i (inFrame M F τ B) * algebraMap M.Ω Φ (F.υ (τ, i))) * e2
