import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DatumExistsPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open PureTypeVector in

theorem cmDatum_form_sqrtNegD_pure_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {ρ : ℂ}
    (hty : ∀ i, ty i (H.rt : E) = ρ) {x : D.La} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ρ.im * r := by
  obtain ⟨hlin, hinj, -, -, Hm, hH, hpos, hEF⟩ := hP
  have hw0 : Pe (H.w0 • x) = ((1 + ρ) / 2) • Pe x := by
    funext i
    rw [hlin, Pi.smul_apply, smul_eq_mul]
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simpa [map_ofNat] using this
    have h3 := congrArg (ty i) h2
    rw [map_mul, map_add, map_one, map_ofNat, hty i] at h3
    rw [← h3]; ring
  set r : ℝ := (hermForm Hm (Pe x) (Pe x)).re with hr
  have hre : hermForm Hm (Pe x) (Pe x) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [hermForm_self_im hH])
  have hr0 : 0 < r := hpos _ fun h => hx (hinj (by rw [h, map_zero]))
  refine ⟨r / 2, by positivity, ?_⟩
  rw [← hEF, hw0]
  have := hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [this, hre]
  simp
  ring

theorem definite_datum_form_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ),
      (D.q = 0 ∧ 0 < ((ε : ℤ) : ℝ) * H.rt0.im) ∨ (D.p = 0 ∧ ((ε : ℤ) : ℝ) * H.rt0.im < 0) →
      ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := by
  intro E _ _ _ H D ε h x hx
  obtain ⟨g, ty, hty⟩ : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
    have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩⟩
  obtain ⟨Pe, hP⟩ := datum_exists_period E H D g ty hty
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := fun i =>
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    Nat.card_pos.ne'
  have key : ∃ ρ : ℂ, (∀ i, ty i (H.rt : E) = ρ) ∧ 0 < ((ε : ℤ) : ℝ) * ρ.im := by
    rcases h with ⟨hq, hε⟩ | ⟨hp, hε⟩
    · refine ⟨H.rt0, fun i => ?_, hε⟩
      by_contra hne
      exact hcard i (((hty (ty i)).2 hne).trans hq)
    · refine ⟨-H.rt0, fun i => ?_, by simpa using hε⟩
      have hne : ty i (H.rt : E) ≠ H.rt0 := fun he => hcard i (((hty (ty i)).1 he).trans hp)
      have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
        have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
        simpa using this
      have h3 : ty i (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, h2, H.sqrt_neg_disc_sq]; simp
      exact (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left hne
  obtain ⟨ρ, hρ, hε⟩ := key
  obtain ⟨r, hr, hE⟩ := cmDatum_form_sqrtNegD_pure_period D hP hρ hx
  have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((D.EF (H.w0 • x) x : ℤ) : ℝ) := by
    rw [hE, ← _root_.mul_assoc]; exact mul_pos hε hr
  exact_mod_cast this

end GlobalTheory.CM
