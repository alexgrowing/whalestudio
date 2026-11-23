import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_add {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' z'' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : ∀ s, z'' s - (z s + z' s) ∈ b.S _) (hc : Rep a b z c) (hc' : Rep a b z' c') :
    Rep a b z'' (c + c') := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  obtain ⟨f', hf', rfl, e'⟩ := hc'
  refine ⟨f + f', by rw [map_add, hf, hf', add_zero], rfl, fun s => ?_⟩
  change (show sqM a b _ from f s).1 + (show sqM a b _ from f' s).1 = _
  rw [e s, e' s, ← map_add]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem rep_neg {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z' s - (-z s) ∈ b.S _) (hc : Rep a b z c) : Rep a b z' (-c) := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  refine ⟨-f, by rw [map_neg, hf, neg_zero], rfl, fun s => ?_⟩
  change -(show sqM a b _ from f s).1 = _
  rw [e s, ← map_neg]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem sum_wz_sub {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    {ι : Type} [Fintype ι] (I : ι → Fin j → Fin d) (s : ComposableArrows C j)
    (y y' : ι → Φ.A.obj (s.obj (Fin.last j))) (h : ∀ i, y i - y' i ∈ Φ.J.S _) :
    ∑ i, wz u (I i) s * y i - ∑ i, wz u (I i) s * y' i ∈ (Fil ((j : ℤ) + 1)).S _ := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  have h1 : y i - y' i ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact h i
  have := hF.mul j 1 _ (wz_mem hF u hu (I i) s) h1
  rwa [Nat.cast_add, Nat.cast_one] at this

end Abstract

section Forms
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_add_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T (f + g) - (lft W T f + lft W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, lft_spec T h, lft_spec T h, lft_spec T h, map_add, sub_self]

theorem lft_neg_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    lft W T (-f) - (-lft W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec T h, lft_spec T h, map_neg, sub_self]

theorem lift_cocycle {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

end Forms

theorem stAdd : StAdd := by
  intro O _ X q W d t u hu P hP r x x' c c' hc hc'
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

end GlobalTheory.CompanionTheory.GrForm
