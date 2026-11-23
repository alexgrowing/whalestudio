import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem isLift_lft {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) : IsLift (q := q) W t (fun i T => lft W T (t i)) :=
  fun i T h => lft_spec T h (t i)

theorem rep_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    (c : CH.H (sq a b) j) (h : Rep a b (fun s => 0) c) : c = 0 := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  have e : f = 0 := by
    funext s
    apply Subtype.ext
    rw [show (show sqM a b _ from f s).1 = _ from hz s]
    simp
  subst e
  rfl

theorem van : StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → StVan := by
  intro hFr hL hP O _ l s hb X q W d c r j hrs hjr
  obtain ⟨E, σ, θ, hGr, hbot, -, -, -⟩ := hFr l s hb q c _ (isLift_lft W c.t)
  obtain ⟨Q, hQ⟩ := hP (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hCr : ∀ r' ≤ (r : ℤ) + 1, Q.Crit (sFil (SS q l s W)) r' := fun r' h => (hQ r' (by omega)).1
  have key := hL Q (GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)) E σ hGr (r : ℤ) hCr j
  rcases lt_or_gt_of_ne hjr with hlt | hlt
  · obtain ⟨h1, -⟩ := key.2 (r - j) (by omega)
    have all : ∀ cl : CH.H (gr (sFil (SS q l s W)) (r : ℤ)) j, cl = 0 := by
      intro cl
      obtain ⟨x, hx, hR⟩ := h1 cl
      have x0 : ∀ I, x I = 0 := fun I => by
        have h := hx I
        rw [hbot (r - j) (by omega)] at h
        exact h
      have e : (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) = fun s => 0 := by
        funext s
        refine Finset.sum_eq_zero fun I _ => ?_
        simp [x0, Frame.form]
      rw [e] at hR
      exact rep_zero _ _ cl hR
    exact ⟨fun a b => (all a).trans (all b).symm⟩
  · exact key.1 (by exact_mod_cast hlt)

end GlobalTheory.CompanionTheory.GrForm
