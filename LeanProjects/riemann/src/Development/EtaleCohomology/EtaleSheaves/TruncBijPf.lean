import Development.EtaleCohomology.EtaleSheaves.TruncPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncBijPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K K' L : CochainComplex C ℤ}

def preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) : Cochain K L j := (Cochain.ofHom g).comp z (zero_add j)

theorem preC_v (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (p q : ℤ) (h : p + j = q) :
    (preC g z).v p q h = g.f p ≫ z.v p q h := by
  simp [preC]

theorem δ_preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (k : ℤ) : δ j k (preC g z) = preC g (δ j k z) :=
  δ_ofHom_comp g z k

theorem preC_zero (g : K ⟶ K') (j : ℤ) : preC g (0 : Cochain K' L j) = 0 := by
  simp [preC]

theorem preC_inj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) {x y : Cochain K' L j}
    (h : preC g x = preC g y) : x = y := by
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have := hg p (by omega)
    have h' := congrArg (fun z : Cochain K L j => z.v p q hpq) h
    simp only [preC_v] at h'
    exact (cancel_epi (g.f p)).1 h'

theorem preC_surj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) (y : Cochain K L j) :
    ∃ x : Cochain K' L j, preC g x = y := by
  refine ⟨Cochain.mk fun p q hpq =>
    if h : -(n + 1) ≤ p then (haveI := hg p h; inv (g.f p)) ≫ y.v p q hpq else 0, ?_⟩
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have hp : -(n + 1) ≤ p := by omega
    rw [preC_v, Cochain.mk_v, dif_pos hp, IsIso.hom_inv_id_assoc]

end General

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) :=
  CochainComplex.isZero_of_isStrictlyGE (injectiveResolution F).cochainComplex 0 q hq

theorem pull_mk (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (m : ℤ) (x : Cocycle K' (res R F) m) :
    ∃ y : Cocycle K (res R F) m, HK.pull R g F m (CohomologyClass.mk x) = CohomologyClass.mk y ∧
      (y : Cochain K (res R F) m) = preC g (x : Cochain K' (res R F) m) :=
  ⟨_, rfl, rfl⟩

end LateralTheory.E.TruncBijPf

open LateralTheory.E.TruncBijPf in
theorem LateralTheory.E.TruncPf.TruncBij_of : LateralTheory.E.TruncPf.TruncBij := by
  intro R _ F K K' g n hg m hm
  have hL := res_isZero R F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, hy, hy'⟩ := pull_mk R F g m x
    rw [hy, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := preC_surj g n hg hL (by omega) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
    refine ⟨β', preC_inj g n hg hL (by omega) ?_⟩
    rw [← δ_preC, hβ, hy']
  · intro y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, hx⟩ := preC_surj g n hg hL (j := m) (by omega) (y : Cochain K (res R F) m)
    have hδ : δ m (m + 1) x = 0 := by
      apply preC_inj g n hg hL (by omega)
      rw [← δ_preC, hx, preC_zero, Cocycle.δ_eq_zero]
    obtain ⟨y', hy, hy'⟩ := pull_mk R F g m (Cocycle.mk x (m + 1) rfl hδ)
    refine ⟨_, hy.trans (congrArg CohomologyClass.mk (Cocycle.ext ?_))⟩
    rw [hy', ← hx]
    rfl
