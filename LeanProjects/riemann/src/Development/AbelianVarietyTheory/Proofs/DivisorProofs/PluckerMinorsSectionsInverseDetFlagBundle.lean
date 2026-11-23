import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

theorem det_submatrix_mul_tri {R : Type} [CommRing R] {n p m : ℕ} (A : Matrix (Fin n) (Fin p) R)
    (B : Matrix (Fin p) (Fin p) R) (hB : B.BlockTriangular id) (h : m + 1 ≤ p) (r : Fin (m + 1) → Fin n) :
    ((A * B).submatrix r (Fin.castLE h)).det =
      (A.submatrix r (Fin.castLE h)).det * ∏ i : Fin (m + 1), B (Fin.castLE h i) (Fin.castLE h i) := by
  have e : (A * B).submatrix r (Fin.castLE h) =
      A.submatrix r (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun _ => rfl)
    have : ¬ (b : ℕ) < m + 1 := fun hb' => hb ⟨⟨b, hb'⟩, rfl⟩
    have h0 : B b (Fin.castLE h l) = 0 := hB (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le l.2 (not_lt.1 this)))
    rw [h0, mul_zero]
  rw [e, Matrix.det_mul, Matrix.det_of_upperTriangular (M := B.submatrix (Fin.castLE h) (Fin.castLE h))]
  · rfl
  · intro i l hil
    exact hB (show Fin.castLE h l < Fin.castLE h i from hil)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem plkU_map_ev (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (hk : ⊤ ≤ w ⁻¹ᵁ F.U k) (hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U)
    (hx' : ⊤ ≤ (w ≫ π) ⁻¹ᵁ (F.M k).U) :
    (plkU F Mc k σ).map (ev w _ h) =
      (lieBasis Mc (w ≫ π) hx).toMatrix (lieBasis (F.M k).toMChart (w ≫ π) hx') * F.uAt k w hk σ := by
  unfold plkU
  rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    ← chg_map Mc (F.M k).toMChart (w ≫ π) hx hx' (le_preimage_inf hx hx')]
  congr 1
  · ext i j; exact ev_appLE w π _ h _ _
  · ext i j; exact ev_res w _ h hk _

theorem plkU_map_ev_chg (F : Frames Y π) (Mc : MChart Y) (k k' : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (h' : ⊤ ≤ w ⁻¹ᵁ (F.U k' ⊓ π ⁻¹ᵁ Mc.U))
    (hh : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    (plkU F Mc k' σ).map (ev w _ h') = (plkU F Mc k σ).map (ev w _ h) * (F.B k k' σ).map (ev w _ hh) := by
  have hk := le_preimage_mono inf_le_left hh
  have hk' := le_preimage_mono inf_le_right hh
  have hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U := fun p hp => (h hp).2
  have a := F.inM hk rfl
  have b := F.inM hk' rfl
  rw [plkU_map_ev F Mc k' σ w h' hk' hx b, plkU_map_ev F Mc k σ w h hk hx a,
    ← Module.Basis.toMatrix_mul_toMatrix (lieBasis Mc (w ≫ π) hx) (lieBasis (F.M k).toMChart (w ≫ π) a),
    ← chg_map (F.M k).toMChart (F.M k').toMChart (w ≫ π) a b (le_preimage_inf a b), Matrix.mul_assoc,
    F.chg_uAt k k' w hk hk' hh rfl (le_preimage_inf a b) σ, Matrix.mul_assoc]

open Classical in
theorem prod_zpow_neg_ind {G : Type} [CommGroup G] (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Ix Dw → G) :
    ∏ ix, t ix ^ (-ind σ m ix) = (∏ i : Fin ((m : ℕ) + 1), t (some ⟨σ, Fin.castLE m.2 i⟩))⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib]
  congr 1
  symm
  refine Fintype.prod_of_injective (fun i : Fin ((m : ℕ) + 1) => (some ⟨σ, Fin.castLE m.2 i⟩ : Ix Dw)) ?_ _
    (fun ix => t ix ^ ind σ m ix) (fun b hb => ?_) (fun i => ?_)
  · intro i i' e
    simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
    exact Fin.castLE_injective _ e
  · rcases b with _ | ⟨τ, j⟩
    · simp [ind]
    · have : ind σ m (some ⟨τ, j⟩) = 0 := by
        simp only [ind, Option.elim]
        rw [if_neg]
        rintro ⟨rfl, hj⟩
        exact hb ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
      rw [this, zpow_zero]
  · simp [ind, not_lt.2 (Nat.lt_succ_iff.1 i.2)]

theorem plkLoc_sec (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) :
    ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  refine ⟨⟨plkLoc F Mc g hg σ m q, fun j j' => ?_⟩, rfl⟩
  unfold plkLoc
  rcases plkIdx Mc m q with _ | r
  · simp
  · refine ext_ev fun S _ z hz => ?_
    have ha := le_preimage_mono inf_le_left hz
    have hb := le_preimage_mono inf_le_right hz
    have h1 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j) ha
    have h2 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j') hb
    have hh : ⊤ ≤ (z ≫ g) ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ F.U (j' PUnit.unit)) :=
      le_preimage_inf (le_preimage_mono inf_le_left h1) (le_preimage_mono inf_le_left h2)
    rw [map_mul, ev_res z _ hz ha, ev_res z _ hz hb, ev_appLE z g _ ha h1, ev_appLE z g _ hb h2,
      ev_pull_g (F.LL (ind σ m)) g j j' z hz hh]
    erw [F.ev_LL_g _ _ _ (z ≫ g) hh]
    unfold plkMinor
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← Matrix.submatrix_map, plkU_map_ev_chg F Mc _ _ σ (z ≫ g) h1 h2 hh,
      det_submatrix_mul_tri (m := (m : ℕ)) _ _ (F.B_map_tri (j PUnit.unit) (j' PUnit.unit) σ (ev (z ≫ g) _ hh)) m.2 r,
      prod_zpow_neg_ind]
    have e : ∏ i : Fin ((m : ℕ) + 1), (F.B (j PUnit.unit) (j' PUnit.unit) σ).map (ev (z ≫ g) _ hh)
        (Fin.castLE m.2 i) (Fin.castLE m.2 i) =
        ((∏ i : Fin ((m : ℕ) + 1), F.TAt (j PUnit.unit) (j' PUnit.unit) (z ≫ g) hh
          (some ⟨σ, Fin.castLE m.2 i⟩) : (S)ˣ) : S) := by
      rw [Units.coe_prod]; rfl
    rw [e, _root_.mul_left_comm, Units.inv_mul, _root_.mul_one]

end GlobalTheory.FlagPlucker

end
