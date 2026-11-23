import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveField

open GlobalTheory.Ex.UnifModel GlobalTheory.Ex.TorsionField

theorem exists_finset_fixed (hM : Out.MulNSt) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (P : Out.PolAV (Sp M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsIntegral ℚ z) ∧ ∀ τ : ℂ →+* ℂ, (∀ x ∈ M, τ x = x) → (∀ z ∈ s, τ z = z) →
      ∀ x : Over.mk (spMap (algebraMap M ℂ)) ⟶ P.A, x ^ n = 1 → spMap τ ≫ x.left = x.left := by
  classical
  let F := algebraicClosure M ℂ
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure M ℂ).isAlgClosed
  obtain ⟨s, hs⟩ := exists_finset (F := F) hM P hn
  refine ⟨s.image Subtype.val, fun z hz => ?_, fun τ h₁ h₂ x hx => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact isIntegral_trans (A := M) _ (mem_algebraicClosure_iff'.1 y.2)
  · let k : Subfield F := RingHom.eqLocusField (τ.comp (algebraMap F ℂ)) (algebraMap F ℂ)
    obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hM P (algebraMap M F) (algebraMap F ℂ) (algebraMap M ℂ)
      (fun _ => rfl) hn x hx
    obtain ⟨z, hz⟩ := hs k k.subtype (fun c => ⟨⟨algebraMap M F c, h₁ c c.2⟩, rfl⟩)
      (fun c hc => ⟨⟨c, h₂ c (Finset.mem_image_of_mem _ hc)⟩, rfl⟩) y hy
    have e₁ : spMap (algebraMap F ℂ) ≫ spMap k.subtype = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun _ => rfl
    have e₂ : spMap τ ≫ spMap ((algebraMap F ℂ).comp k.subtype) = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun c => c.2
    rw [← hy', ← hz, reassoc_of% e₁, reassoc_of% e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_wC_eq (H : Host E) (a : ℤ × ℤ) :
    ∃ m k : ℤ, wC H a = (m : ℂ) + k * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  have h : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_pow_eq_one (C : Curve H) {n : ℕ} (hn : 0 < n) (a : ℤ × ℤ) :
    (C.u.ex fun _ => C.c * (wC H a / n)) ^ n = 1 := by
  obtain ⟨m, k, h⟩ := exists_wC_eq H a
  rw [← ex_nsmul, C.u.ker]
  refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← h, Pi.smul_apply, nsmul_eq_mul]
  field_simp

theorem exists_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M)
    (P : Out.PolAV (Sp M)) (C : Curve H) (ψ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap (algebraMap M ℂ)) ψ := by
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, -, ⟨P₀, π, -, -, ⟨hg₀, hπ, hL₀⟩, -⟩, hcm, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := exists_baseChange firstFiveLaws.1.polBaseChange (spMap (algebraMap M ℂ)) P₀
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  have hL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀.symm)
  obtain ⟨c, hc, hΛ⟩ := hcm PC (ψ ≫ π)
    ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp fun _ => rfl) rfl, hL.symm⟩ u
  rw [hw] at hΛ
  exact ⟨M, inferInstance, P₀, ⟨PC, hgC.trans (hg₀.trans hg), u, hu, c, hc, hΛ⟩, ψ, hψ⟩

theorem exists_curveOver (H : Host E) {n : ℕ} (hn : 0 < n) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F n := by
  obtain ⟨M, _, P, C, ψ, hψ⟩ := exists_model H
  obtain ⟨s, hs, hfix⟩ := exists_finset_fixed firstFiveLaws.1.mulN M P hn
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := (s : Set ℂ)) hs
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (s : Set ℂ), inferInstance, fun τ hτ => ?_⟩
  have h₁ : ∀ x ∈ M, (τ : ℂ →+* ℂ) x = x := fun x hx => hτ x (le_sup_left (a := M) hx)
  have h₂ : ∀ z ∈ s, (τ : ℂ →+* ℂ) z = z := fun z hz =>
    hτ z (le_sup_right (a := M) (IntermediateField.subset_adjoin ℚ _ hz))
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap (algebraMap M ℂ) = spMap (algebraMap M ℂ) :=
    spMap_comp fun c => h₁ c c.2
  have w : ψ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap (algebraMap M ℂ) := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr e.symm (hψ.1.lift_fst _ _ w).symm) (hψ.1.lift_snd _ _ w),
    fun a => ?_⟩
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  rw [h1, _root_.one_mul]
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) (spMap (algebraMap M ℂ)) (Category.id_comp _).symm
  have hx := hfix τ h₁ h₂ (ε (C.u.ex fun _ => C.c * (wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (ex_pow_eq_one C hn a)).trans (map_one ε))
  rw [hε] at hx
  have ho : C.pt (wC H a / n) ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * (wC H a / n))
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hψ.1.lift_fst, Category.assoc]
    exact hx.symm
  · rw [Category.assoc, hψ.1.lift_snd, Category.assoc, ho, reassoc_of% ho, Category.comp_id]

theorem exists_coeff_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ), 0 < n → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → CurveOver H c''.F n := by
  intro E _ _ _ H l c n hn
  obtain ⟨F, _, hF⟩ := exists_curveOver H hn
  have := c.fin
  exact ⟨⟨c.F ⊔ F, inferInstance, fun τ a => le_sup_left (b := F) (c.conj τ a), le_sup_left (b := F) c.zeta_mem,
    c.le.trans le_sup_left⟩, le_sup_left, fun c'' h τ hτ => hF τ fun x hx => hτ x (h (le_sup_right (a := c.F) hx))⟩

end GlobalTheory.CurveField
