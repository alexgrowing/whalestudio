import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFpSupp
import Development.DiscreteGroups.GlobalIrreducibility.DzFpVec

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_cell {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : GL (Fin m) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin m), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k m, ∀ x, W (x * b) = W x) (L : GL (Fin m) k → ℂ)
    (hL : ∀ u ∈ unipB k (Fin m), ∀ x, L (u * x) = (ψ (superDiag u) : ℂ) * L x) :
    ∑ᶠ x, L x * W x = (Nat.card (unipB k (Fin m)) : ℂ) * W 1 * ∑ᶠ b : lowB k m, L b := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  have hinj : Function.Injective (fun p : unipB k (Fin m) × lowB k m => (p.1 : GL (Fin m) k) * p.2) := by
    rintro ⟨u, b⟩ ⟨u', b'⟩ h
    simp only at h
    have h3 : ((u' : GL (Fin m) k)⁻¹ * u : GL (Fin m) k) = b' * (b : GL (Fin m) k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
    have h4 : ((u' : GL (Fin m) k)⁻¹ * u : GL (Fin m) k) = 1 :=
      eq_one_of_unip_lower (mul_mem (inv_mem u'.2) u.2) (by rw [h3]; exact mem_lowB.1 (mul_mem b'.2 (inv_mem b.2)))
    have hu : u = u' := Subtype.ext (inv_mul_eq_one.1 h4).symm
    subst hu
    have hb : b = b' := Subtype.ext (mul_left_cancel h)
    rw [hb]
  calc ∑ x, L x * W x
      = ∑ x ∈ Finset.univ.image (fun p : unipB k (Fin m) × lowB k m => (p.1 : GL (Fin m) k) * p.2), L x * W x := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
        by_contra hne
        have hW : W x ≠ 0 := fun h => hne (by rw [h, mul_zero])
        obtain ⟨u, hu, b, hb, rfl⟩ := supp ψ hψ W h1 h2 x hW
        exact hx (Finset.mem_image.2 ⟨(⟨u, hu⟩, ⟨b, hb⟩), Finset.mem_univ _, rfl⟩)
    _ = ∑ p : unipB k (Fin m) × lowB k m, L (p.1 * p.2) * W (p.1 * p.2) :=
        Finset.sum_image (fun p _ q _ h => hinj h)
    _ = ∑ p : unipB k (Fin m) × lowB k m, L p.2 * W 1 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have hW1 : W p.2 = W 1 := by simpa using h2 _ p.2.2 1
        have hz := Circle.coe_ne_zero (ψ (superDiag (p.1 : GL (Fin m) k)))
        rw [hL _ p.1.2, h1 _ p.1.2, hW1, Circle.coe_inv]
        field_simp
    _ = _ := by
        simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
        ring

theorem corner_lower {m : ℕ} {b : GL (Fin m) k} (hb : b ∈ lowB k m) :
    ∀ r c : Fin (m + 1), r < c → (corner b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = 0 := by
  intro r c hrc
  induction r using Fin.lastCases with
  | last => exact absurd hrc (not_lt.2 (Fin.le_last _))
  | cast r =>
    induction c using Fin.lastCases with
    | last => exact corner_cs_last b r
    | cast c => rw [corner_cs_cs]; exact mem_lowB.1 hb r c (Fin.castSucc_lt_castSucc_iff.1 hrc)

theorem corner_last_row {m : ℕ} (b : GL (Fin m) k) (c : Fin (m + 1)) :
    (corner b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c := by
  induction c using Fin.lastCases with
  | last => rw [corner_last_last, Matrix.one_apply_eq]
  | cast c => rw [corner_last_cs, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne']

theorem corner_ne_one {m : ℕ} {b : GL (Fin m) k} (hb : b ≠ 1) : corner b ≠ 1 := by
  intro h
  apply hb
  ext i j
  have := congrArg (fun z : GL (Fin (m + 1)) k => (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc) h
  simp only [corner_cs_cs, Units.val_one, Matrix.one_apply, Fin.castSucc_inj] at this
  rw [this, Units.val_one, Matrix.one_apply]

theorem sum_lower_corner {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) {ρ : Representation ℂ (GL (Fin (m + 1)) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin (m + 1)), ρ u v = (ψ (superDiag u) : ℂ) • v) :
    ∑ᶠ b : lowB k m, l (ρ (corner (b : GL (Fin m) k)) v) = l v := by
  classical
  rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single (1 : lowB k m)]
  · simp [corner_one]
  · intro b _ hb
    exact vanish_lower hψ hl hv _ (corner_lower b.2) (corner_last_row _)
      (corner_ne_one fun h => hb (Subtype.ext h))
  · simp

theorem corner_fixed {m : ℕ} (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (v : V) (b' : GL (Fin m) k)
    (hb' : b' ∈ lowB k m) :
    ρ (corner b') (∑ᶠ b : lowB k m, ρ (corner (b : GL (Fin m) k)) v) = ∑ᶠ b : lowB k m, ρ (corner (b : GL (Fin m) k)) v := by
  classical
  rw [finsum_eq_sum_of_fintype, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨b', hb'⟩ : lowB k m)) _ _ fun b => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, corner_mul, map_mul, Module.End.mul_apply]

theorem map_finsum_lower {m : ℕ} (f : V →ₗ[ℂ] ℂ) (F : lowB k m → V) : f (∑ᶠ b, F b) = ∑ᶠ b, f (F b) := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]

theorem map_finsum_lower' {m : ℕ} (f : V →ₗ[ℂ] V) (F : lowB k m → V) : f (∑ᶠ b, F b) = ∑ᶠ b, f (F b) := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]

end DiscreteGroups.sglob.DzFp
