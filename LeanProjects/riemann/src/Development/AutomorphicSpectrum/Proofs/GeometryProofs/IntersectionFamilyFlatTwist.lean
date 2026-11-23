import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitSectionAvoidStatement

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hermLine_eq_of_a_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem exists_tensorPow_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} (hW : IsArithVar W (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) {B : HermLine ι} (hB : IsSmoothHerm B) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : HermLine ι, IsSmoothHerm C ∧ (∀ k, C.a k = m * B.a k) ∧ (∀ z, C.h z = B.h z ^ m) ∧
      I W (n + 1) (Fin.snoc L C) = m * I W (n + 1) (Fin.snoc L B) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨B, hB, by simp, by simp, by simp⟩
  | succ m hm ih =>
    obtain ⟨C, hC, ha, hh, hi⟩ := ih
    refine ⟨C.tensor B, ContDiffOn.mul hC hB, fun k => ?_, fun z => ?_, ?_⟩
    · simp only [HermLine.tensor, Pi.add_apply, ha]
      push_cast
      ring
    · simp only [HermLine.tensor, hh, pow_succ]
    · rw [hI.2.1 W n L C B hW hL hC hB, hi]
      push_cast
      ring

theorem IsUnitSec.mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {f g : MRing ι} (h : IsUnitSec P f g) (hPW : P ≤ W) : IsUnitSec W f g := by
  intro W' h1 h2 h3
  obtain ⟨a, b, ha, hb, hab⟩ := h W' h1 (hPW.trans h2) h3
  exact ⟨a, b, ha, hb, hPW hab⟩

theorem FlatHerm.inter_eq_neg_integral : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type)
    [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u →
    I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  intro K _ ι _ Ω _ F _ _ y φ I W n L A S d u hI hP hY hPW hW hL hA hu
  have hnu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z :=
    fun c z hc => by simp only [hu.inv c z hc]

  set B : HermLine ι := A.tensor (HermLine.ofWeight (fun z => -u z) hnu) with hBdef
  have hBh : ∀ z, B.h z = A.h z * Real.exp (u z) := fun z => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hBa : ∀ k, B.a k = A.a k := fun k => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hexp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.exp (u z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    Real.contDiff_exp.comp_contDiffOn hu.smooth
  have hB : IsSmoothHerm B := by
    have e : B.h = fun z => A.h z * Real.exp (u z) := funext hBh
    unfold IsSmoothHerm
    rw [e]
    exact ContDiffOn.mul hA hexp
  have hBA : B.tensor (HermLine.ofWeight u hu.inv) = A := by
    refine hermLine_eq_of_a_h ?_ ?_
    · funext k
      simp [HermLine.tensor, HermLine.ofWeight, hBa]
    · funext z
      have : (B.tensor (HermLine.ofWeight u hu.inv)).h z = B.h z * Real.exp (-u z) := rfl
      rw [this, hBh, mul_assoc, ← Real.exp_add]
      simp
  have hchange : I W (n + 1) (Fin.snoc L A) = I W (n + 1) (Fin.snoc L B) - ptsIntegral W (pot L) u := by
    have := metricChange K ι I hI W n L B u hu.inv hW hL hB hu.smooth
    rwa [hBA] at this

  obtain ⟨C, hC, hCa, hCh, hCI⟩ := exists_tensorPow_last hI hW hL hB (m := S.M) S.M_pos
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, -, hun, hnorm⟩ :=
    GlobalTheory.T.flat_herm_unit_section_avoid K ι Ω F y φ A S d W hY hP hA hW.2.1 hPW
  have hunW := IsUnitSec.mono hun hPW
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.unit_section_divisor_eq K ι W f' g' hunW
  have hvert := GlobalTheory.T.vertical_statement_holds K ι I hI W n L C f' g' hW hL hC
    ⟨df', dg', hf', hg', hfW, hgW, fun k => by rw [hdeg k, hCa k, hBa k]⟩
    (fun W' _ => by rw [c1]) (fun W' _ hm => c2 W' hm) (fun z hz => by
      have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
      obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hY z hzP
      have hz1 : u z = Real.log (S.κ σ) := (hu.near σ z hσ).self_of_nhds
      have hn := hnorm σ z hσ
      have hCz : C.h z = (S.κ σ * A.h z) ^ S.M := by
        rw [hCh, hBh, hz1, Real.exp_log (S.κ_pos σ), mul_comm]
      rw [hCz, mul_comm]
      exact hn)
  have hzero : I W (n + 1) (Fin.snoc L B) = 0 := by
    have h0 : (S.M : ℝ) * I W (n + 1) (Fin.snoc L B) = 0 := by
      rw [← hCI, hvert, c3 n L, sub_self]
    have hM : (S.M : ℝ) ≠ 0 := by exact_mod_cast S.M_pos.ne'
    exact (mul_eq_zero.mp h0).resolve_left hM
  rw [hchange, hzero, zero_sub]

end GlobalTheory.CompanionTheory.Ar.Flat
