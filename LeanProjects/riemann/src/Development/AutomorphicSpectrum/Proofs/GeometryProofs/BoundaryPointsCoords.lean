import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem eval_map_mul_of_isHomogeneous {σ : Type} [Fintype σ] {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d)
    (r : σ → ℂ) (t : ℂ) :
    MvPolynomial.eval (fun i => r i * t) (MvPolynomial.map (Int.castRingHom ℂ) G) =
      t ^ d * MvPolynomial.eval r (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  have hP : (MvPolynomial.map (Int.castRingHom ℂ) G).IsHomogeneous d := hG.map _
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_ratEval_val {Ω : Type} [Field Ω] {N : ℕ} {S : Subring Ω} (φ : S →+* ℂ) (x : Fin (N + 1) → Ω)
    (c : Fin (N + 1)) (r : Fin (N + 1) → ℂ) (hreg : ∀ i, x i / x c ∈ S) (hval : ∀ i, φ ⟨_, hreg i⟩ = r i)
    (G : MRing (fun _ : Unit => Fin (N + 1))) :
    ∃ ha : ratEval x c G ∈ S, φ ⟨_, ha⟩ =
      MvPolynomial.eval (fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2) (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  induction G using MvPolynomial.induction_on with
  | C n =>
    have h : ratEval x c (MvPolynomial.C n) = ((n : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (n : S).2, ?_⟩
    have e : (⟨ratEval x c (MvPolynomial.C n), h ▸ (n : S).2⟩ : S) = (n : S) := Subtype.ext h
    rw [e]
    simp
  | add f g hf hg =>
    obtain ⟨ha, hA⟩ := hf
    obtain ⟨hb, hB⟩ := hg
    have h : ratEval x c (f + g) = ((⟨_, ha⟩ + ⟨_, hb⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f + g), h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2⟩ : S) = ⟨_, ha⟩ + ⟨_, hb⟩ := Subtype.ext h
    rw [e, map_add, hA, hB]
    simp
  | mul_X f i hf =>
    obtain ⟨ha, hA⟩ := hf
    have h : ratEval x c (f * MvPolynomial.X i) = ((⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f * MvPolynomial.X i), h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2⟩ : S) =
        ⟨_, ha⟩ * ⟨_, hreg i.2⟩ := Subtype.ext h
    rw [e, map_mul, hA, hval]
    simp

theorem mem_mcPts_span_bdGens_iff : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)), IsCptGen ξ →
    (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G)) →
    ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
      (w ∈ mcPts (Ideal.span (Mdl.bdGens ξ x B)) ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ X ξ N x B hξ hB z w hC
  obtain ⟨hu, hco⟩ := hC
  obtain ⟨c, hc⟩ := hu ()
  obtain ⟨hxc, hr⟩ := hco () c hc
  choose r hrV hrw using hr
  obtain ⟨h, -⟩ := hrV c
  obtain ⟨φ, hφ, hφu⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z h hξ
  have hreg : ∀ i, x i / x c ∈ regAt ξ ⟨centre z, h⟩ := fun i => ((hφ _ _).1 (hrV i)).choose
  have hval : ∀ i, φ ⟨_, hreg i⟩ = r i := fun i => ((hφ _ _).1 (hrV i)).choose_spec
  have hchart : InChart ξ x c ⟨centre z, h⟩ := ⟨hxc, hreg⟩
  have hp0 : Char0 ξ ⟨centre z, h⟩ := char_zero_centre_complex_point Ω X ξ z h hξ
  have hw0 : w ⟨(), c⟩ ≠ 0 := hc.ne_zero
  have hw : w = fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2 * w ⟨(), c⟩ := by
    funext ⟨u, i⟩
    exact hrw i

  have key : ∀ (G : MRing (fun _ : Unit => Fin (N + 1))) (d : ℕ), G.IsHomogeneous d →
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) G) = 0 ↔
        ¬ unitAt ξ ⟨centre z, h⟩ (ratEval x c G)) := by
    intro G d hG
    obtain ⟨ha, hA⟩ := exists_ratEval_val φ x c r hreg hval G
    have hu' := hφu ⟨_, ha⟩
    rw [hw, eval_map_mul_of_isHomogeneous hG, ← hA]
    simp only [mul_eq_zero, pow_eq_zero_iff', hw0, false_and, false_or]
    rw [← show IsUnit (φ ⟨_, ha⟩) ↔ unitAt ξ ⟨centre z, h⟩ (ratEval x c G) from hu', isUnit_iff_ne_zero, not_not]
  constructor
  · rintro ⟨-, hv⟩
    refine ⟨h, ?_⟩
    by_contra hpB
    obtain ⟨G, hG, hGu⟩ := hB c ⟨centre z, h⟩ hp0 hchart hpB
    obtain ⟨d, hd, -⟩ := id hG
    exact (key G d hd).1 (hv G (Ideal.subset_span hG)) hGu
  · rintro ⟨h', hpB⟩
    refine ⟨fun _ => ⟨c, hw0⟩, fun f hf => ?_⟩
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨d, hd, hv⟩ := hG
      exact (key G d hd).2 (hv c _ hpB hchart)
    | zero => simp
    | add f g _ _ hf hg => simp [hf, hg]
    | smul a f _ hf => simp [hf]

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
