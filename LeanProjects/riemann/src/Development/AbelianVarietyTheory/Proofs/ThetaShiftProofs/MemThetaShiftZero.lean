import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcThetaSpaces

open TwistedTheta

section

variable {P : Out.PolAV (Sp ℂ)} {g : ℕ} {u : HolUnif P.A P.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem eq_zero_of_val (u : HolUnif P.A P.L g) (U : P.A.left.Opens) (f : Γ(P.A.left, U))
    (h : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U f = 0) : f = 0 := by
  have := P.isAb.smooth
  have := isReduced_of_smooth_complex _ P.A.hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq P.A.hom _ _ _ fun x hx hi => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
  rw [h z hi, valAt'_zero]

theorem finite_thetaShift (hT : Out.GlobalSectionsRankAlgClosed) {j : ℕ} (hj : 1 ≤ j)
    (h₁ : ∀ s, ∃ θ, u.IsFnPow j s θ) (h₂ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ) (c : Fin g → ℂ) :
    Module.Finite ℂ (thetaShift u Hm χ j c) := by
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℂ, c = j • b := ⟨(j : ℂ)⁻¹ • c, by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (by omega))]⟩
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P j hj
  choose φ hφ using h₁
  have hle : thetaShift u Hm χ j (j • b) ≤ Submodule.span ℂ (Set.range fun i z => φ (β i) (z + b)) := by
    intro θ hθ
    obtain ⟨s, hs⟩ := h₂ _ (isThetaFn_sub hθ)
    obtain ⟨a, ha, -⟩ := hβ s
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨a, funext fun z => ?_⟩
    have hi := FrameValue.le_chartAt P.isLB (u.ex (z + b)).left
    set i := FrameValue.chartAt P.isLB (u.ex (z + b)).left
    have hi' : ⊤ ≤ (u.ex (z + b)).left ⁻¹ᵁ (lbPow P.L j).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := (valAt'_sum _ _ _ _).symm.trans
      ((congrArg (valAt' _ _) (ha fun _ => i)).symm.trans (hs (fun _ => i) (z + b) hi'))
    simp only [add_sub_cancel_right] at e
    refine mul_right_cancel₀ (pow_ne_zero j (u.fr_ne i _ hi)) (Eq.trans ?_ e)
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      (valAt'_constFn _ _ (Over.w (u.ex (z + b))) _ _ hi') (hφ _ _ _ hi'))).symm
    simp [_root_.mul_assoc]
  have := Module.Finite.span_of_finite ℂ (Set.finite_range fun i z => φ (β i) (z + b))
  exact Submodule.finiteDimensional_of_le hle

theorem mem_thetaShift_zero {j : ℕ} {θ : (Fin g → ℂ) → ℂ} (h : u.IsThetaFn Hm χ j θ) : θ ∈ thetaShift u Hm χ j 0 :=
  ⟨h.1, fun l z => by rw [h.2 l z, FrameValue.hermForm_zero_left]; simp⟩

theorem exists_ne_zero (hT : Out.GlobalSectionsRankAlgClosed) (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  obtain ⟨β, hβ⟩ := PowSec.exists_indep_sections hT P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  by_contra hne
  push_neg at hne
  have h0 : ∀ i j, (β i).f j = 0 := fun i j => eq_zero_of_val u _ _ fun z hz => by
    obtain ⟨θ, h, h'⟩ := h₁ (β i)
    rw [h' j z hz, hne θ h, Pi.zero_apply, zero_mul]
  exact one_ne_zero (congrFun (hβ 1 fun j => by simp [h0]) i₀)

theorem exists_isFn (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) (th : P.L.Sec) (h : ∃ j, th.f j ≠ 0) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 ∧ u.IsFn th θ := by
  obtain ⟨θ, h₂, h₃⟩ := h₁ (secToPow th 1)
  have hf : u.IsFn th θ := fun i z hi => by
    have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := h₃ (fun _ => i) z hi'
    rw [pow_one] at e
    refine Eq.trans ?_ e
    exact ((valAt'_res _ _ (th.f i ^ 1) hi').trans (by rw [pow_one])).symm
  refine ⟨θ, h₂, ?_, hf⟩
  rintro rfl
  obtain ⟨j, hj⟩ := h
  exact hj (eq_zero_of_val u _ _ fun z hz => by rw [hf j z hz, Pi.zero_apply, zero_mul])

end

theorem sections_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ (j : ℕ) (α : Λ.A.X), 1 ≤ j → (∀ s, Λ.fn j α s ∈ Λ.A.Theta j α) ∧ ∀ th ∈ Λ.A.Theta j α, ∃! s, Λ.fn j α s = th) ∧ AnFin Λ.A ∧ ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∃ θ ∈ Λ.A.Theta 1 0, θ ≠ 0 ∧ Λ.u.IsFn th θ := by
  intro hL _ E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hT := theta_eq_thetaShift Λ.A Λ.u (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) Λ.lam
    (fun l l' e => congrArg Λ.A.chi (Subtype.ext e))
  have h0 : Λ.A.ct 0 = 0 := map_zero _
  have hθ : ∀ n θ, Λ.u.IsThetaFn Λ.A.Hm (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) n θ → ∃ s, Λ.u.IsFnPow n s θ :=
    fun n θ h => ((Λ.pow n).2 θ h).exists
  refine ⟨fun j α hj => ?_, ⟨fun j α hj => ?_, ?_⟩, fun th h => ?_⟩
  · rw [hT]
    refine ⟨fun s => secFn_mem Λ.ah (Λ.ct α) s, fun th hth => ?_⟩
    obtain ⟨s, hs⟩ := exists_secFn_eq Λ.ah (by omega) (hθ j) (Λ.ct α) hth
    exact ⟨s, hs, fun t ht => secFn_injective (Λ.ct α) (ht.trans hs.symm)⟩
  · rw [hT]
    exact finite_thetaShift hL.globalSectionsRank hj (fun s => ((Λ.pow j).1 s).exists.imp fun _ h => h.2) (hθ j) _
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_ne_zero hL.globalSectionsRank fun s => ((Λ.pow 1).1 s).exists
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_isFn (fun s => ((Λ.pow 1).1 s).exists) th h
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩

end GlobalTheory.ArcThetaSpaces
