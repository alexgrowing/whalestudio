import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsetOfForallPtMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp

set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

noncomputable section

namespace GlobalTheory.HSShort.Supp

theorem finite_of_finite_pts {k : Type} [Field k] (S : LinSys k) (hS : S.IsVariety) (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y) (hZ : IsClosed Z)
    (h : {x : S.Pt Ω | ptOf x.1 ∈ Z}.Finite) : Z.Finite := by
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  have hf : (Z ∩ closedPoints S.Y).Finite := by
    refine (h.image fun x => ptOf x.1).subset ?_
    rintro y ⟨hyZ, hy⟩
    by_contra hne
    refine subset_of_forall_pt_mem k S hS Ω {y} hy ∅ isOpen_empty (fun x hx => hne ⟨x, ?_, hx⟩) rfl
    have e : ptOf x.1 = y := hx
    change ptOf x.1 ∈ Z
    rw [e]
    exact hyZ
  have hc : IsClosed (Z ∩ closedPoints S.Y) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints S.Y)]
    exact hf.isClosed_biUnion fun y hy => hy.2
  rw [← JacobsonSpace.closure_inter_closedPoints hZ, hc.closure_eq]
  exact hf

theorem exists_finite_lines {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {G : MvPolynomial (Fin 1 × Fin N) K}
    (hG : G ≠ 0) : ∃ R : Set (Fin N → K), R.Finite ∧ ∀ y : Fin N → K, y ≠ 0 →
      (∀ ξ : Fin N → K, ∑ j, ξ j * y j = 0 → eval (fun p => ξ p.2) G = 0) → ∃ r ∈ R, ∃ c : K, y = c • r := by
  classical
  refine ⟨(fun p : MvPolynomial (Fin 1 × Fin N) K => fun j => coeff (Finsupp.single ((0 : Fin 1), j) 1) p) ''
    (UniqueFactorizationMonoid.factors G).toFinset, (Finset.finite_toSet _).image _, fun y hy hz => ?_⟩
  have irr := HyperplaneFactor.irreducible_lin hy
  obtain ⟨n, hn⟩ := HyperplaneFactor.exists_dvd_pow_of_zeros (a := lin y) (b := G) fun x hx => by
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz (fun j => x (0, j)) (by rwa [HyperplaneFactor.eval_lin] at hx)
    simpa only [e] using h1
  obtain ⟨q, hq, ha⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG irr (irr.prime.dvd_of_dvd_pow hn)
  obtain ⟨a, ha⟩ := ha.symm
  obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
  rw [ht, mul_comm] at ha
  refine ⟨_, ⟨q, by simpa using hq, rfl⟩, t, funext fun j => ?_⟩
  have h1 := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) ha
  rw [coeff_C_mul, HyperplaneFactor.coeff_lin] at h1
  simpa using h1.symm

theorem finite_and_inOpen : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → ∀ (g : MvPolynomial (Fin T.N) F), (∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0) → (∀ (K : Type) [Field K] [Algebra F K] (y : Fin T.N → K), {x : T.Pt K | aeval (T.coords x.1) g ≠ 0 ∧ ∃ c : K, T.coords x.1 = c • y}.Finite) → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f ≠ 0 → (∀ x ∈ T.geomPts E (T.linSection E s), aeval (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1) g ≠ 0) → ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite ∧ T.InOpen E (T.linSection E s) := by
  intro F _ _ T hT δ f hf g hbd hfin E _ _ s hG hg
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  refine ⟨finite_of_finite_pts _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed ?_, ?_⟩
  · obtain ⟨R, hR, hl⟩ := exists_finite_lines hG
    refine ((hR.biUnion fun y _ => hfin (AlgebraicClosure E) y).preimage
      (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).1.injOn).subset fun x hx => ?_
    have hm : x ∈ T.geomPts E (T.linSection E s) := (LinSys.mem_subPts_iff _ _ x).2 hx
    have hy := hT.alg.bpf.coords_ne_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1
    obtain ⟨r, hr, hc⟩ := hl _ hy fun ξ hξ => by
      rw [EtaleSection.eval_spec]
      refine (GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F T.D T.N δ _ f hf).1 _ _ ξ _ hy (fun p hp => ?_)
        ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hm) hξ
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hp
      rwa [LinSys.baseHom_ptOver] at this
    exact Set.mem_biUnion hr ⟨hg x hm, hc⟩
  · exact subset_of_forall_pt_mem E _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed
      (T.toLinSys.bcFst E ⁻¹' (T.U : Set T.Y)) (T.U.isOpen.preimage (T.toLinSys.bcFst E).continuous)
      fun x hx hb => hg x ((LinSys.mem_subPts_iff _ _ x).2 hx)
        (hbd (AlgebraicClosure E) (LinSys.toBase x) hb)

end GlobalTheory.HSShort.Supp
