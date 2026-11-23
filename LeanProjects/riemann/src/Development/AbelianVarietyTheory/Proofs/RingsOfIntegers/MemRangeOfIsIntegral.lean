import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PushMemHarmK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ColumnMapShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PushIntegral

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}

theorem push_letB (ga : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (v : Fin n → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v) = letB c σ i (ga.mulVec v) := by
  simp only [letB, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, GlobalTheory.PushHarm.push_X,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_range_of_isIntegral (T : CDVR) (io : c.F →+* T.Fr) {x : c.F} (hi : IsIntegral ℤ x) :
    ∃ y : T.V, algebraMap T.V T.Fr y = io x := by
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io x) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.1 hV

theorem mem_range_of_smul (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V)) (σ : E →+* ℂ) {x : E}
    (hx : (k : E) * x ∈ (1 : Submodule (𝓞 E) E)) : ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ x) := by
  obtain ⟨s, hs⟩ := Submodule.mem_one.1 hx
  have hi : IsIntegral ℤ (embF c σ (algebraMap (𝓞 E) E s)) :=
    map_isIntegral_int (embF c σ) (NumberField.RingOfIntegers.isIntegral_coe s)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io hi
  obtain ⟨u, hu⟩ := hk.exists_left_inv
  refine ⟨u * y, ?_⟩
  have h1 : algebraMap T.V T.Fr u * (k : T.Fr) = 1 := by
    rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hu, map_one]
  rw [map_mul, hy, hs, map_mul, map_mul, map_natCast, map_natCast, ← _root_.mul_assoc, h1, _root_.one_mul]

theorem coeff_mem (Λ : GenLat E n) (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V))
    (ga : Matrix (Fin n) (Fin n) E) (hin : ∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) (m : LtN Dw n →₀ ℕ) :
    (MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P)).coeff m ∈ (algebraMap T.V T.Fr).range := by
  have hle : symO (Dw := Dw) c Λ ≤
      (MvPolynomial.map (σ := LtN Dw n) (algebraMap T.V T.Fr)).range.comap
        ((MvPolynomial.map io).comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c ga).toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, v, hv, rfl⟩)
    · obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io o.2
      refine ⟨MvPolynomial.C y, ?_⟩
      simp [hy]
    · have h : ∀ j, ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ (ga.mulVec v j)) := fun j =>
        mem_range_of_smul c T io hk σ (hin v hv j (Set.mem_univ j))
      choose y hy using h
      refine ⟨∑ j, MvPolynomial.C (y j) * MvPolynomial.X ⟨σ, i, j⟩, ?_⟩
      change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v))
      rw [push_letB]
      simp [letB, hy]
  obtain ⟨Q, hQ⟩ := hle hP
  change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P) at hQ
  rw [← hQ, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem push_one (P : MvPolynomial (LtN Dw n) c.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c (1 : Matrix (Fin n) (Fin n) E) P = P := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ, i, j⟩
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push, letB, Matrix.one_apply, apply_ite, ite_mul]
  rw [h]; rfl

theorem aeval_smul_of_degree {J K A : Type} [CommRing K] [CommRing A] [Algebra K A] (t : A) (f : J → A)
    (P : MvPolynomial J K) (d : ℕ) (hP : ∀ s ∈ P.support, (s.sum fun _ e => e) = d) :
    MvPolynomial.aeval (fun i => t * f i) P = t ^ d * MvPolynomial.aeval f P := by
  classical
  rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hP s hs]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem degree_eq_totalDegree {a : (E →+* ℂ) → ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : RowDeg Dw.mult n c.F a P) : ∀ s ∈ P.support, (s.sum fun _ e => e) = P.totalDegree := by
  classical
  have h : ∀ s ∈ P.support, (s.sum fun _ e => e) = ∑ σ : E →+* ℂ, ∑ i : Fin (Dw.mult σ), a σ i := by
    intro s hs
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP s hs σ i
  intro s hs
  refine le_antisymm (MvPolynomial.le_totalDegree hs) ?_
  exact Finset.sup_le fun s' hs' => ((h s' hs').trans (h s hs).symm).le

end

theorem map_pushL_mem_FFV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (T : CDVR) (io : c.F →+* T.Fr) (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), IsUnit (k : T.V) → (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) → (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) → MvPolynomial.map io (pushL c ga P) ∈ FFV (Dw := Dw) T w n ∧ pushL c 1 P = P ∧ ∀ m : ℕ, pushL c ((m : E) • ga) P = MvPolynomial.C ((m : c.F) ^ P.totalDegree) * pushL c ga P := by
  intro E _ _ _ H Dw l c n Λ w P hP T io k ga hk hu hin
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary ga := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hu i j
  have hr := GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n ga P (fun τ i => w (τ, i))
  refine ⟨⟨⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io (GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n ga P hU h1),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map io (hr.1 h2), ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map io (hr.2 h3)⟩,
    coeff_mem c Λ T io hk ga hin h4⟩, push_one c P, fun m => ?_⟩
  rw [map_pow, pushL, pushL, ← aeval_smul_of_degree _ _ P _ (degree_eq_totalDegree c h3)]
  congr 2
  funext ℓ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [_root_.mul_assoc]

end GlobalTheory.PushIntegral
