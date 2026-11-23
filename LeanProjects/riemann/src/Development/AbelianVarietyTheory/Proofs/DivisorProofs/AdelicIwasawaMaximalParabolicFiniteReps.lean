import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.IwaParab

def projP (R : Type) [CommRing R] (a r : ℕ) : Matrix (Fin a) (Fin a) R :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

theorem projP_mul_self (R : Type) [CommRing R] (a r : ℕ) : projP R a r * projP R a r = projP R a r := by
  rw [projP, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem entry_QMP {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    ((1 - projP R a r) * M * projP R a r) i j = if r ≤ (i : ℕ) ∧ (j : ℕ) < r then M i j else 0 := by
  simp only [projP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

theorem entry_PMQ {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    (projP R a r * M * (1 - projP R a r)) i j = if (i : ℕ) < r ∧ r ≤ (j : ℕ) then M i j else 0 := by
  simp only [projP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

theorem nilM_neg {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) : nilM (-x) = -nilM x := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]; split_ifs <;> simp

theorem exists_unip_mul {R : Type} [CommRing R] (a r : ℕ) (g : GL (Fin a) R)
    (hg : ∀ i j : Fin a, (j : ℕ) < r → r ≤ (i : ℕ) → g.1 i j = 0) :
    ∃ (y : BlockIx a r → R) (m : GL (Fin a) R),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧ g = unip y * m := by
  classical
  set P := projP R a r with hPdef
  have hPP : P * P = P := projP_mul_self R a r
  set G : Matrix (Fin a) (Fin a) R := g.1 with hG
  set H : Matrix (Fin a) (Fin a) R := (g⁻¹ : GL (Fin a) R).1 with hH
  have hHG : H * G = 1 := by rw [hH, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  let blk : Fin a → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hBT : G.BlockTriangular blk := by
    intro i j h
    have : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      simp only [blk] at h; split_ifs at h <;> first | (exfalso; omega) | (constructor <;> omega)
    exact hg i j this.1 this.2
  letI : Invertible G := Units.invertible g
  have hBTi : H.BlockTriangular blk := by
    have h := Matrix.blockTriangular_inv_of_blockTriangular hBT
    have e : H = G⁻¹ := by rw [hH, hG, Matrix.coe_units_inv]
    rw [e]; exact h
  have hGP : (1 - P) * G * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hg i j h.2 h.1
    · rfl
  have hHP : (1 - P) * H * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hBTi (by simp only [blk]; split_ifs <;> omega)
    · rfl

  set X : Matrix (Fin a) (Fin a) R := P * (G * (1 - P) * H) * (1 - P) with hX
  let y : BlockIx a r → R := fun p => X p.1.1 p.1.2
  have hy : nilM y = X := by
    ext i j
    simp only [nilM, Matrix.of_apply, y]
    split_ifs with h
    · rfl
    · rw [hX, entry_PMQ, if_neg h]
  refine ⟨y, unip (-y) * g, ?_, ?_⟩
  · have hm : (unip (-y) * g).1 = (1 - X) * G := by
      change (1 + nilM (-y)) * G = _
      rw [nilM_neg, hy, sub_eq_add_neg]
    have h1 : (1 - P) * (unip (-y) * g).1 * P = 0 := by
      rw [hm]
      have e : (1 - P) * ((1 - X) * G) * P =
          (1 - P) * G * P - (P - P * P) * (G * (1 - P) * H * (1 - P) * G * P) := by
        rw [hX]; noncomm_ring
      rw [e, hGP, hPP, sub_self, zero_mul, sub_zero]
    have key : (1 - P) * H * (1 - P) * G * (1 - P) = 1 - P := by
      have e2 : (1 - P) * H * (1 - P) * G * (1 - P) =
          (1 - P) * (H * G) * (1 - P) - ((1 - P) * H * P) * (G * (1 - P)) := by noncomm_ring
      have e3 : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by noncomm_ring
      rw [e2, hHG, hHP, zero_mul, sub_zero, mul_one, e3, hPP, sub_self, sub_zero]
    have h2 : P * (unip (-y) * g).1 * (1 - P) = 0 := by
      rw [hm]
      have e : P * ((1 - X) * G) * (1 - P) =
          P * G * (1 - P) - (P * P) * G * ((1 - P) * H * (1 - P) * G * (1 - P)) := by
        rw [hX]; noncomm_ring
      rw [e, key, hPP]; noncomm_ring
    intro i j
    by_cases hij : ((i : ℕ) < r ↔ (j : ℕ) < r)
    · exact Or.inl hij
    · right
      by_cases hi : (i : ℕ) < r
      · have := congrFun (congrFun h2 i) j
        rw [entry_PMQ, if_pos ⟨hi, by by_contra hj; exact hij ⟨fun _ => by omega, fun _ => hi⟩⟩] at this
        exact this
      · have := congrFun (congrFun h1 i) j
        rw [entry_QMP, if_pos ⟨by omega, by by_contra hj; exact hij ⟨fun h => absurd h hi, fun h => absurd h hj⟩⟩] at this
        exact this
  · rw [← mul_assoc, ← unip_add, add_neg_cancel]
    have h0 : unip (0 : BlockIx a r → R) = 1 := by
      ext i j
      change (1 + nilM (0 : BlockIx a r → R)) i j = (1 : Matrix (Fin a) (Fin a) R) i j
      simp [nilM]
    rw [h0, one_mul]

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

open scoped Pointwise

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ k ∈ PIW.ClassFinD.KGL E a, ∃ t ∈ T, ∃ l ∈ L, k = t * l := by
  classical
  have hK := GlobalTheory.isCompact_KGL E a
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun t : PIW.ClassFinD.KGL E a => (t : GL (Fin a) (Af E)) • (L : Set (GL (Fin a) (Af E))))
    (fun t => hL.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, ⟨1, L.one_mem, mul_one k⟩⟩)
  refine ⟨s.image Subtype.val, fun k hk => ?_⟩
  obtain ⟨t, ht, hkt⟩ := Set.mem_iUnion₂.1 (hs hk)
  obtain ⟨l, hl, hlk⟩ := hkt
  exact ⟨t, Finset.mem_image_of_mem _ ht, l, hl, hlk.symm⟩

theorem upper_infGL_mul_finGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (b : GL (Fin a) (Cinf E)) (hb : (b : Matrix (Fin a) (Fin a) (Cinf E)).BlockTriangular id)
    (c : GL (Fin a) (Af E)) (hc : (c : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id) :
    ((infGL E a b * finGL E a c : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).BlockTriangular id := by
  rw [Units.val_mul]
  refine Matrix.BlockTriangular.mul ?_ ?_
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sInf E) b).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hb h, map_zero]
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sFin E) c).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hc h, map_zero]

theorem iwasawa_parab : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ g : GA E a, ∃ (y : BlockIx a r → Ad E) (m : GA E a),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧
      ∃ t ∈ T, ∃ k : Kinf E a, ∃ l ∈ L,
        g = unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l := by
  intro E _ _ _ a r L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E a L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hbk⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E a (Matrix.GeneralLinearGroup.map (pInf E) g)
  obtain ⟨u, s, kf, hu, hs, hkf, hx⟩ := GlobalTheory.IwasawaFinAd.iwasawaAf E a (Matrix.GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, hkt⟩ := hT kf hkf
  have hus : ((u * s : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id := by
    rw [Units.val_mul]
    exact Matrix.BlockTriangular.mul (fun i j h => hu.1 i j h) (fun i j h => hs i j (ne_of_gt h))
  have hB := upper_infGL_mul_finGL b hb (u * s) hus
  obtain ⟨y, m, hm, hBm⟩ := exists_unip_mul a r (infGL E a b * finGL E a (u * s))
    (fun i j hj hi => hB (show j < i from Fin.lt_def.2 (by omega)))
  refine ⟨y, m, hm, t, ht, k, l, hl, ?_⟩
  rw [← hBm]
  conv_lhs => rw [← infGL_mul_finGL g, hbk, hx, hkt]
  have e : u * s * (t * l) = u * s * t * l := by group
  rw [e]
  rw [map_mul (finGL E a) (u * s * t) l, map_mul (infGL E a) b, map_mul (finGL E a) (u * s) t]
  have c : infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t) =
      finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k) := by
    rw [← map_mul]; exact infGL_comm _ _
  calc infGL E a b * infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t * finGL E a l)
      = infGL E a b * (infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t)) * finGL E a l := by
        simp only [mul_assoc]
    _ = infGL E a b * (finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k)) * finGL E a l := by rw [c]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.IwaParab
