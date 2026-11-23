import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.PrincData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E : E →+* E).toIntAlgHom)

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G (c • x) y = (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl]; ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G x (c • y) = cc (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def]
  simp only [cc, map_mul]
  ring

theorem exists_nat_herm_int (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (hL : L.FG) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((n : E) * herm G x y) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y0, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ((s ×ˢ s).image fun p => herm G p.1 p.2)
  have hgen : ∀ a ∈ s, ∀ b ∈ s, IsIntegral ℤ ((y0 : E) * herm G a b) := fun a ha b hb => by
    have h := hy _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩)
    rwa [zsmul_eq_mul] at h
  have hright : ∀ a ∈ s, ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G a y) := by
    intro a ha y hy'
    induction hy' using Submodule.span_induction with
    | mem b hb => exact hgen a ha b hb
    | zero => simpa [herm, cc] using isIntegral_zero
    | add u v _ _ hu hv => rw [herm_add_right, mul_add]; exact hu.add hv
    | smul c u _ hu => rw [herm_smul_right, mul_left_comm]; exact (isIntegral_cc c.2).mul hu
  have hall : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)), ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G x y) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hright a ha
    | zero => intro y _; simpa [herm] using isIntegral_zero
    | add u v _ _ hu hv => intro y hy'; rw [herm_add_left, mul_add]; exact (hu y hy').add (hv y hy')
    | smul c u _ hu => intro y hy'; rw [herm_smul_left, mul_left_comm]; exact c.2.mul (hu y hy')
  refine ⟨y0.natAbs, Int.natAbs_pos.2 hy0, fun x hx y hy' => ?_⟩
  have key := hall x hx y hy'
  rcases Int.natAbs_eq y0 with h | h
  · have e : ((y0.natAbs : ℕ) : E) = (y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact key
  · have e : ((y0.natAbs : ℕ) : E) = -(y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact key.neg

theorem exists_nat_int (k : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * k) := by
  have halg : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hyi⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hyi
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact hyi
  · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact hyi.neg

theorem exists_princ_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  intro E _ _ _ r M X0 Λ hM hfg hsp
  obtain ⟨n, hn, hnint⟩ := exists_nat_herm_int X0.Gm Λ hfg
  obtain ⟨k, hk, hkint⟩ := exists_nat_int X0.κ0
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ (((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y) := by
    intro x hx y hy
    have e : ((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y =
        ((k : E) * X0.κ0) * ((n : E) * herm X0.Gm x y) := by
      push_cast
      field_simp
    rw [e]
    exact hkint.mul (hnint x hx y hy)
  obtain ⟨X, hΨ, hG, hp, hΛ, -, -, -, hΓ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r X0.p0 M (M * n * k)
    X0.Ψ X0.Gm Λ X0.ξ0 X0.κ0 X0.cmType X0.Gm_herm X0.Gm_det X0.p0_le
    (fun τ hτ => X0.signature ⟨τ, hτ⟩) hfg hsp hM X0.ξ0_im X0.ξ0_ne X0.κ0_xi
    (fun τ hτ => X0.κ0_sign ⟨τ, hτ⟩) (by positivity) hint
  refine ⟨X, hG, hΨ, hp, hΛ, fun γ => ?_⟩
  rw [hΓ γ]
  refine and_congr Iff.rfl (forall₂_congr fun x _ => exists_congr fun y => and_congr Iff.rfl ?_)
  exact sub_eq_iff_eq_add'.symm

end GlobalTheory.PrincData
