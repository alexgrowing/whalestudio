import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConjStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem natCast_self_residueField_padicAlgCl_eq_zero (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℕ) : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  have : (((p : ℕ) : OO p) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [this, PadicAlgCl.valuation_p]
  have h1 : (1 : NNReal) < p := by exact_mod_cast hp.out.one_lt
  rw [div_lt_one (lt_trans zero_lt_one h1)]
  exact h1

theorem ker_isMaximal_of_forall_pow_eq_one {A k : Type*} [CommRing A] [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) (φ : A →+* k) :
    (RingHom.ker φ).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨by simp, fun J a hJ ha haJ => ?_⟩
  obtain ⟨n, hn, h⟩ := hk (φ a) ha
  have h1 : 1 - a ^ n ∈ J := hJ (by simp [RingHom.mem_ker, h])
  have h2 : a ^ n ∈ J := J.pow_mem_of_mem haJ n hn
  simpa using J.add_mem h1 h2

theorem isClosed_image_point_of_forall_pow_eq_one {k : Type} [Field k]
    (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) {X : Scheme.{0}} [JacobsonSpace X]
    (x : Sp k ⟶ X) (s : Sp k) : IsClosed ({x s} : Set X) := by
  obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing x
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hs : Spec.map φ s ∈ closedPoints (Spec Γ(X, V)) := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ?_
    have := (s : PrimeSpectrum k).isPrime
    have e : (s : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have : (Spec.map φ s : PrimeSpectrum Γ(X, V)).asIdeal = RingHom.ker φ.hom := by
      change Ideal.comap φ.hom (s : PrimeSpectrum k).asIdeal = _
      rw [e]; rfl
    rw [this]
    exact ker_isMaximal_of_forall_pow_eq_one hk φ.hom
  rw [← h] at hs
  rw [Scheme.Hom.comp_apply]
  exact hs

theorem exists_residueField_factor_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}}
    (x : Sp k ⟶ X) (s : Sp k) (z : X) (hz : x s = z) :
    ∃ r : X.residueField z ⟶ CommRingCat.of k, Spec.map r ≫ X.fromSpecResidueField z = x := by
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst hz
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩

theorem exists_integral_point_lifting_residue_point :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens),
      (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime],
        (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧
        (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  intro X _ π _ _ U hU p hp
  obtain ⟨hJ, hfin, -⟩ := jacobson_closedPoints_tools_int X π
  obtain ⟨-, hord, hgal⟩ := GlobalTheory.T.kb_isAlgClosed_and_conj' p
  have hcl : ∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X) :=
    fun x s => isClosed_image_point_of_forall_pow_eq_one hord x s
  refine ⟨fun x => ?_, hcl⟩
  let s : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  obtain ⟨q, hq, y, hy, hyU⟩ := padicAlgCl_integral_points.1 X π (x s) (hcl x s) U hU
  have hfz := hfin _ (hcl x s)
  obtain ⟨r', hr'⟩ := exists_residueField_factor_of_apply_eq x s _ rfl
  have hy' : (rPt q ≫ y) (IsLocalRing.closedPoint (kb q)) = x s := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO q))
  obtain ⟨r, hr⟩ := exists_residueField_factor_of_apply_eq (rPt q ≫ y) _ _ hy'
  obtain rfl : p = q := by
    have h1 : ((p : ℕ) : X.residueField (x s)) = 0 := by
      apply r'.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero p
    have h2 : ((q : ℕ) : X.residueField (x s)) = 0 := by
      apply r.hom.injective
      rw [map_natCast, map_zero]
      exact natCast_self_residueField_padicAlgCl_eq_zero q
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hp.out).mpr h1
    have := (CharP.charP_iff_prime_eq_zero (R := X.residueField (x s)) hq.out).mpr h2
    exact CharP.eq (X.residueField (x s)) ‹CharP _ p› ‹CharP _ q›
  obtain ⟨σ, hσ⟩ := hgal (X.residueField (x s)) r.hom r'.hom
  refine ⟨spMap σ.toRingHom ≫ y, ?_, ?_⟩
  · let τ : kb p →+* kb p := IsLocalRing.ResidueField.map (σ : OO p →+* OO p)
    have e1 : rPt p ≫ spMap σ.toRingHom = spMap τ ≫ rPt p := by
      refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
      rfl
    have e2 : r ≫ CommRingCat.ofHom τ = r' := by
      ext a
      obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (r.hom a)
      change τ (r.hom a) = r'.hom a
      rw [← hσ a c hc, ← hc]
      rfl
    rw [← Category.assoc, e1, Category.assoc]
    refine (congrArg (spMap τ ≫ ·) hr.symm).trans (Eq.trans ?_ hr')
    rw [← e2, Spec.map_comp, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    apply hyU
    refine ⟨t, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    congr 1
    have := (t : PrimeSpectrum (PadicAlgCl p)).isPrime
    have e : (t : PrimeSpectrum (PadicAlgCl p)).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    apply PrimeSpectrum.ext
    ext a
    change (a : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal ↔
      ((σ a : OO p) : PadicAlgCl p) ∈ (t : PrimeSpectrum (PadicAlgCl p)).asIdeal
    rw [e]
    simp

end GlobalTheory
