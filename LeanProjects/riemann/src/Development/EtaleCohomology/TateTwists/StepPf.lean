import Development.EtaleCohomology.TateTwists.TensorVanishing

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.StepPf
open LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    Tens.res (k ≫ g) w x = Tens.res k w (Tens.res g w x) := by
  ext p
  rw [res_apply, res_apply, res_apply]
  generalize x p = v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ix_eq {w : ℤ} (p : Ix w) (a b : ℤ) (h : p.1.2 = b) (ha : a + b = w) : p = ⟨(a, b), ha⟩ :=
  Subtype.ext (Prod.ext (show p.1.1 = a by have := p.2; omega) h)

theorem lof_back {U : Scheme.{0}} {w : ℤ} (i j : Ix w) (h : i = j) (v : Cmp C J U w i) :
    DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) j ((DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v) j) =
      DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v := by
  subst h; rw [lof_same]

theorem ev_zsmul {U : Scheme.{0}} {w : ℤ} (c : ℤ) (f : Tens C J U w) (q : Ix w) : (c • f) q = c • f q := rfl

theorem Dm_comp (U : Scheme.{0}) (n t0 : ℤ) (y : Tens C J U n) :
    (Dm U n (n + 1) rfl y) ⟨(n - t0 + 1, t0), by omega⟩ =
      TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(n - t0, t0), by omega⟩) +
      (Dm U n (n + 1) rfl (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(n - t0 + 1, t0 - 1), by omega⟩
        (y ⟨(n - t0 + 1, t0 - 1), by omega⟩))) ⟨(n - t0 + 1, t0), by omega⟩ := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, DirectSum.add_apply] at ha hb ⊢
    rw [ha, hb]; abel
  | of p v =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    by_cases h0 : p.1.2 = t0
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at h0; subst h0
      obtain rfl : a = n - b := by omega
      rw [Dm_lof, DirectSum.add_apply, ev_zsmul]
      dsimp only
      rw [lof_same, lof_ne _ _ _ _ (by simp), smul_zero, add_zero,
        lof_same, lof_ne _ _ _ _ (by simp; omega), map_zero, map_zero, DirectSum.zero_apply, add_zero]
    by_cases h1 : p.1.2 = t0 - 1
    · rw [lof_back p _ (ix_eq p (n - t0 + 1) (t0 - 1) h1 (by omega)), lof_ne _ _ _ _ h0, map_zero, zero_add]
    · rw [Dm_lof, DirectSum.add_apply, ev_zsmul, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ (by simp; omega),
        smul_zero, add_zero, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ h1, map_zero, map_zero, map_zero,
        DirectSum.zero_apply, add_zero]

theorem Step_of : LateralTheory.EtaleFoundations.stairPf.Step := by
  intro R _ C J T τ hτ hc n t0 V x hx hd
  have hD : τ.lift V (n + 1) (Dm V n (n + 1) rfl x) = 0 := by rw [lift_Dm, hd]
  refine loc_bind (hτ.2 V (n + 1) _ hD) fun W g hW => ?_
  have hc0 : TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op W)).hom LinearMap.id
      (Tens.res g n x ⟨(n - t0, t0), by omega⟩) = 0 := by
    rw [res_apply, nat_tens]
    have h1 := congrArg (fun z => z ⟨(n - t0 + 1, t0), by omega⟩) hW
    simp only at h1
    rw [res_apply, Dm_comp, hx ⟨(n - t0 + 1, t0 - 1), by omega⟩ (by simp)] at h1
    simp only [map_zero, DirectSum.zero_apply, add_zero] at h1
    exact h1
  refine loc_mono (hc W (n - t0) t0 _ hc0) fun W' k hk => ?_
  obtain ⟨y0, hy0⟩ := hk
  refine ⟨Tens.res (k ≫ g) n x - Dm W' (n - 1) n (by ring)
      (DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0),
    DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0, ?_,
    (sub_add_cancel _ _).symm⟩
  intro p hp
  rw [DirectSum.sub_apply, Dm_lof, DirectSum.add_apply, ev_zsmul]
  rcases lt_or_eq_of_le (show p.1.2 ≤ t0 by omega) with h | h
  · rw [res_apply, hx p h, map_zero, lof_ne _ _ _ _ (by simp; omega), lof_ne _ _ _ _ (by simp; omega),
      smul_zero, add_zero, sub_zero]
  · obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at h; subst h
    obtain rfl : a = n - b := by omega
    dsimp only
    rw [lof_shift W' n (n - b - 1) (n - b) b (by ring) (by omega) (by omega), lof_same,
      lof_ne _ _ _ _ (by simp), smul_zero, add_zero, hy0, tens_res_comp, res_apply k, sub_self]

end LateralTheory.EtaleFoundations.StepPf
