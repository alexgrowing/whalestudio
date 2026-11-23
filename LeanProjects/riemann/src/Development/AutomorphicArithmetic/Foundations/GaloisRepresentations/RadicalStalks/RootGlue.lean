import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma rootGlue_uniq {R : Type*} [CommRing R] [IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (hab : a ^ p = b ^ p) : a = b := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim a b
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    haveI : Fact p.Prime := ⟨hp⟩
    apply frobenius_inj R p
    simpa [frobenius_def] using hab

theorem UpperTheory.Gal.Ord.rootGlue :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X], (p : Γ(X, ⊤)) = 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      (∀ (V : X.Opens) (hV : V ≤ U), IsAffineOpen V → ∃ r : Γ(X, V), r ^ p = X.presheaf.map (homOfLE hV).op s) → ∃ r : Γ(X, U), r ^ p = s := by
  intro p _ X _ hp U s hloc
  have hpr : p.Prime := Fact.out
  have hpV : ∀ V : X.Opens, (p : Γ(X, V)) = 0 := by
    intro V
    have h0 := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) hp
    rwa [map_natCast, map_zero] at h0
  let Idx := {V : X.Opens // V ≤ U ∧ IsAffineOpen V}
  choose r hr using fun i : Idx => hloc i.1 i.2.1 i.2.2
  have hcover : U ≤ ⨆ i : Idx, i.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hxV⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i : Idx => i.1) r := by
    intro i j
    apply rootGlue_uniq hpr (hpV _)
    change (X.presheaf.map _ (r i)) ^ p = (X.presheaf.map _ (r j)) ^ p
    rw [← map_pow, ← map_pow, hr i, hr j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, U), ∀ i : Idx, X.presheaf.map (homOfLE i.2.1).op t = r i :=
    X.sheaf.existsUnique_gluing' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover r hcomp
  refine ⟨t, ?_⟩
  have key : ∀ i : Idx,
      X.presheaf.map (homOfLE i.2.1).op (t ^ p) = X.presheaf.map (homOfLE i.2.1).op s := by
    intro i
    rw [map_pow, ht i, hr i]
  exact X.sheaf.eq_of_locally_eq' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover _ _ key
