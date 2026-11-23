import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

section Local

variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def ordP (p : ℕ) (x : Qq) : ℤ := by
  classical exact if h : ∃ n : ℤ, ∃ u : Wˣ, x = algebraMap W Qq u * (p : Qq) ^ n then h.choose else 0

def lenLat (p : ℕ) {k : ℕ} (L : Submodule W (Fin k → Qq)) : ℤ := by
  classical exact if h : IsLattice W L then -ordP W p h.choose.det else 0

variable {W}

theorem pQ_ne [IsDomain W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W)) : (p : Qq) ≠ 0 := by
  have h0 : (p : W) ≠ 0 := hp.ne_zero
  rw [← map_natCast (algebraMap W Qq) p]
  exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr h0

theorem unit_mul_zpow_congr_zpow_of_le [IsDomain W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W)) {n n' : ℤ} {u u' : Wˣ}
    (hle : n ≤ n') (h : algebraMap W Qq u * (p : Qq) ^ n = algebraMap W Qq u' * (p : Qq) ^ n') : n = n' := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hle)
  have hn' : n' = n + d := by omega
  subst hn'
  have hpq := pQ_ne (W := W) (Qq := Qq) hp
  rw [zpow_add₀ hpq, zpow_natCast] at h
  have h2 : algebraMap W Qq u * (p : Qq) ^ n = (algebraMap W Qq u' * (p : Qq) ^ d) * (p : Qq) ^ n := by
    rw [h]; ring
  have h3 := mul_right_cancel₀ (zpow_ne_zero n hpq) h2
  have h4 : (u : W) = u' * (p : W) ^ d := by
    apply IsFractionRing.injective W Qq
    rw [h3, map_mul, map_pow, map_natCast]
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    simp
  · exfalso
    apply hp.not_isUnit
    have h5 : IsUnit ((u' : W) * (p : W) ^ d) := h4 ▸ u.isUnit
    exact (isUnit_pow_iff (Nat.pos_iff_ne_zero.mp hd0)).mp (isUnit_of_mul_isUnit_right h5)

theorem unit_mul_zpow_congr_zpow [IsDomain W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W)) {n n' : ℤ} {u u' : Wˣ}
    (h : algebraMap W Qq u * (p : Qq) ^ n = algebraMap W Qq u' * (p : Qq) ^ n') : n = n' := by
  rcases le_total n n' with hle | hle
  · exact unit_mul_zpow_congr_zpow_of_le hp hle h
  · exact (unit_mul_zpow_congr_zpow_of_le hp hle h.symm).symm

theorem ordP_eq [IsDomain W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W)) (n : ℤ) (u : Wˣ) :
    ordP W p (algebraMap W Qq u * (p : Qq) ^ n) = n := by
  have hex : ∃ n' : ℤ, ∃ u' : Wˣ, algebraMap W Qq u * (p : Qq) ^ n = algebraMap W Qq u' * (p : Qq) ^ n' :=
    ⟨n, u, rfl⟩
  rw [ordP, dif_pos hex]
  obtain ⟨u', hu'⟩ := hex.choose_spec
  exact (unit_mul_zpow_congr_zpow hp hu').symm

theorem exists_eq_unit_mul_zpow₂ [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W))
    {x : Qq} (hx : x ≠ 0) : ∃ n : ℤ, ∃ u : Wˣ, x = algebraMap W Qq u * (p : Qq) ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨na, ua, hua⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hp
  obtain ⟨nb, ub, hub⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hp
  refine ⟨(na : ℤ) - nb, ua * ub⁻¹, ?_⟩
  have hpq := pQ_ne (W := W) (Qq := Qq) hp
  have hu : algebraMap W Qq ub ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr ub.ne_zero
  rw [hua, hub, zpow_sub₀ hpq, zpow_natCast, zpow_natCast, Units.val_mul]
  simp only [map_mul, map_pow, map_natCast, map_units_inv]
  field_simp

theorem ordP_mul_zpow [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ}
    (hp : Irreducible (p : W)) {x : Qq} (hx : x ≠ 0) (m : ℤ) : ordP W p (x * (p : Qq) ^ m) = ordP W p x + m := by
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hx
  have hpq := pQ_ne (W := W) (Qq := Qq) hp
  rw [mul_assoc, ← zpow_add₀ hpq, ordP_eq hp, ordP_eq hp]

theorem ordP_mul_unit [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ}
    (hp : Irreducible (p : W)) {x : Qq} (hx : x ≠ 0) (u : Wˣ) : ordP W p (x * algebraMap W Qq u) = ordP W p x := by
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hx
  rw [mul_right_comm, ← map_mul, ← Units.val_mul, ordP_eq hp, ordP_eq hp]

theorem exists_mul_of_le {k : ℕ} (g g' : Matrix (Fin k) (Fin k) Qq) (h : colSpan W g' ≤ colSpan W g) :
    ∃ A : Matrix (Fin k) (Fin k) W, g' = g * A.map (algebraMap W Qq) := by
  have hc : ∀ c : Fin k, ∃ a : Fin k → W, ∑ i, a i • (fun r => g r i) = (fun r => g' r c) := by
    intro c
    have hmem : (fun r => g' r c) ∈ colSpan W g := h (Submodule.subset_span ⟨c, rfl⟩)
    simp only [colSpan, Submodule.mem_span_range_iff_exists_fun] at hmem
    exact hmem
  choose a ha using hc
  refine ⟨Matrix.of fun i c => a c i, ?_⟩
  refine Matrix.ext fun r c => ?_
  rw [Matrix.mul_apply]
  have h1 := congrFun (ha c) r
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.of_apply, Matrix.map_apply, mul_comm]

theorem det_of_colSpan_eq [IsDomain W] [IsFractionRing W Qq] {k : ℕ} (g g' : Matrix (Fin k) (Fin k) Qq)
    (hg : IsUnit g.det) (h : colSpan W g = colSpan W g') : ∃ u : Wˣ, g'.det = g.det * algebraMap W Qq u := by
  have hmd : ∀ M : Matrix (Fin k) (Fin k) W, (M.map (algebraMap W Qq)).det = algebraMap W Qq M.det := by
    intro M
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  obtain ⟨A, hA⟩ := exists_mul_of_le g g' h.symm.le
  obtain ⟨B, hB⟩ := exists_mul_of_le g' g h.le
  have hAB : A.map (algebraMap W Qq) * B.map (algebraMap W Qq) = 1 := by
    have hg' : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hg
    have h2 : g * (A.map (algebraMap W Qq) * B.map (algebraMap W Qq)) = g * 1 := by
      rw [mul_one, ← mul_assoc, ← hA, ← hB]
    exact hg'.mul_left_cancel h2
  have hdet : IsUnit A.det := by
    have h3 := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one, hmd, hmd, ← map_mul] at h3
    have h4 : A.det * B.det = 1 := IsFractionRing.injective W Qq (by rw [h3, map_one])
    exact isUnit_iff_exists_inv.mpr ⟨_, h4⟩
  refine ⟨hdet.unit, ?_⟩
  rw [hA, Matrix.det_mul, IsUnit.unit_spec, hmd]

theorem lenLat_colSpan [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ}
    (hp : Irreducible (p : W)) {k : ℕ} (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    lenLat W p (colSpan W g) = -ordP W p g.det := by
  have hL : IsLattice W (colSpan W g) := ⟨g, hg, rfl⟩
  rw [lenLat, dif_pos hL]
  obtain ⟨_, heq⟩ := hL.choose_spec
  obtain ⟨u, hu⟩ := det_of_colSpan_eq g hL.choose hg heq
  rw [hu, ordP_mul_unit hp hg.ne_zero]

theorem det_dD (p r k : ℕ) (hr : r ≤ k) : (Formalism.MainNotions.Pf14.dD Qq p r k).det = (p : Qq) ^ (-(r : ℤ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold Formalism.MainNotions.Pf14.dD
  rw [Matrix.det_diagonal, Fin.prod_univ_eq_prod_range (fun i => if i < r then ((p : Qq))⁻¹ else 1) (r + d),
    Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range r, (if x < r then ((p : Qq))⁻¹ else 1) = ((p : Qq))⁻¹ ^ r := by
    calc ∏ x ∈ Finset.range r, (if x < r then ((p : Qq))⁻¹ else 1)
        = ∏ x ∈ Finset.range r, ((p : Qq))⁻¹ :=
          Finset.prod_congr rfl fun x hx => if_pos (Finset.mem_range.mp hx)
      _ = ((p : Qq))⁻¹ ^ r := by rw [Finset.prod_const, Finset.card_range]
  have h2 : ∏ x ∈ Finset.range d, (if r + x < r then ((p : Qq))⁻¹ else 1) = 1 :=
    Finset.prod_eq_one fun x _ => if_neg (by omega)
  rw [h1, h2, mul_one, zpow_neg, zpow_natCast, inv_pow]

theorem edge_le [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p n' r k : ℕ}
    (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hp2 : 2 ≤ p) (hn : 0 < n')
    (e : Edge W Qq k) (he : IsEdge p n' r e) : r ≤ k := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨g, h1, h2, h3⟩ := Formalism.MainNotions.G.LatticeSystems.lc_main p n' r k hp hcard hp2 hn e he
  have hb : IsEdgeBasis p k e g := by
    have hdiag : (fun c : Fin k => if c.val < r then ((p : Qq))⁻¹ else 1) =
        fun c : Fin k => if c.val < k then ((p : Qq))⁻¹ else 1 := by
      funext c
      have c1 : c.val < r := lt_trans c.isLt hlt
      rw [if_pos c1, if_pos c.isLt]
    refine ⟨h1, h2, ?_⟩
    rw [h3, hdiag]
  have he' := Formalism.MainNotions.Pf14.isEdge_of_basis p n' k hp.ne_zero hcard le_rfl e g hb
  have := he.2.2.2.2.symm.trans he'.2.2.2.2
  have h4 := Nat.pow_right_injective hp2 this
  have h5 := Nat.eq_of_mul_eq_mul_left hn h4
  omega

theorem lenLat_edge [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p n' r k : ℕ}
    (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hp2 : 2 ≤ p) (hn : 0 < n')
    (e : Edge W Qq k) (he : IsEdge p n' r e) : lenLat W p e.src = lenLat W p e.tgt - r := by
  obtain ⟨g, hg, hs, ht⟩ := Formalism.MainNotions.G.LatticeSystems.lc_main p n' r k hp hcard hp2 hn e he
  have hrk := edge_le hp hcard hp2 hn e he
  have hpq := pQ_ne (W := W) (Qq := Qq) hp
  have hdD : (Matrix.diagonal fun c : Fin k => if c.val < r then ((p : Qq))⁻¹ else 1).det = (p : Qq) ^ (-(r : ℤ)) :=
    det_dD p r k hrk
  have hgd : IsUnit (g * Matrix.diagonal fun c : Fin k => if c.val < r then ((p : Qq))⁻¹ else 1).det := by
    rw [Matrix.det_mul, hdD]
    exact hg.mul (isUnit_iff_ne_zero.mpr (zpow_ne_zero _ hpq))
  rw [hs, ht, lenLat_colSpan hp g hg, lenLat_colSpan hp _ hgd, Matrix.det_mul, hdD, ordP_mul_zpow hp hg.ne_zero]
  ring

end Local

section Global

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def len (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) : ℤ :=
  lenLat ((X.Pj j).W (X.vJ j v)) p (L (X.vJ j v))

theorem vJ_vB (j : ℕ) (v' : Fin (X.Pj j).nV) : X.vJ j (X.vB j v') = v' := by
  exact Fin.ext rfl

theorem vB_vJ (j : ℕ) (v : X.Pl) : X.vB j (X.vJ j v) = v := by
  exact Fin.ext rfl

theorem len_edge : ∀ j (v' : Fin (X.Pj j).nV) (i : ℕ) (L : (X.Pj j).Tup)
    (L'' : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v')),
    IsEdge p ((X.Pj j).n' v') i ⟨L'', L v'⟩ →
      len X (X.vB j v') j (Function.update L v' L'') = len X (X.vB j v') j L - i := by
  intro j v' i L L'' he
  have hS := (X.Pj j).setting v'
  haveI := hS.frac_alt
  unfold len
  rw [vJ_vB]
  have hu : Function.update L v' L'' v' = L'' := by
    first
    | exact Function.update_self _ _ _
    | exact Function.update_same _ _ _
    | exact dif_pos rfl
  rw [hu]
  exact lenLat_edge hS.p_unif hS.res_card (by have := hS.five_le; omega) (by have := hS.two_le; omega) _ he

theorem len_other : ∀ j (v' : Fin (X.Pj j).nV) (v : X.Pl) (L : (X.Pj j).Tup)
    (L'' : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v')),
    v ≠ X.vB j v' → len X v j (Function.update L v' L'') = len X v j L := by
  intro j v' v L L'' hv
  unfold len
  have hne : X.vJ j v ≠ v' := by
    intro h
    apply hv
    rw [← h, vB_vJ]
  have hu : Function.update L v' L'' (X.vJ j v) = L (X.vJ j v) := by
    first
    | exact Function.update_of_ne hne _ _
    | exact Function.update_noteq hne _ _
    | exact dif_neg hne
  rw [hu]

end Global

end Formalism.L2.G.Pend
