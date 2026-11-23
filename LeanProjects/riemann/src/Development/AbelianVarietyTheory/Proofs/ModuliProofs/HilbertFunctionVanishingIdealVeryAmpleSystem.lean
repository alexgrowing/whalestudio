import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousIdealSectionsOfLineBundlePowerStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.HilbFn

theorem exists_forms_basis {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    ∃ G : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → MvPolynomial σ K, (∀ i, (G i).IsHomogeneous e) ∧
      ∀ F : MvPolynomial σ K, F.IsHomogeneous e → ∃! a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
        F - ∑ i, a i • G i ∈ I := by
  classical
  have hQ : ∀ x, x ∈ GlobalTheory.quotPiece I e ↔
      ∃ y, y ∈ MvPolynomial.homogeneousSubmodule σ K e ∧ Ideal.Quotient.mkₐ K I y = x := by
    intro x
    rw [GlobalTheory.quotPiece_natCast, Submodule.mem_map]
    rfl
  have : Module.Finite K (GlobalTheory.quotPiece I e) := by
    rw [GlobalTheory.quotPiece_natCast]
    exact Module.Finite.map _ _
  let b := Module.finBasis K (GlobalTheory.quotPiece I e)
  have hlift : ∀ i, ∃ G : MvPolynomial σ K, G.IsHomogeneous e ∧
      Ideal.Quotient.mkₐ K I G = (b i : MvPolynomial σ K ⧸ I) := fun i =>
    (hQ _).1 (b i).2
  choose G hG hGb using hlift
  have hsum : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      Ideal.Quotient.mkₐ K I (∑ i, a i • G i) =
        ((∑ i, a i • b i : GlobalTheory.quotPiece I e) : MvPolynomial σ K ⧸ I) := by
    intro a
    simp only [map_sum, map_smul, hGb, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨G, hG, fun F hF => ?_⟩
  have hF' : Ideal.Quotient.mkₐ K I F ∈ GlobalTheory.quotPiece I e := (hQ _).2 ⟨F, hF, rfl⟩
  have hiff : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      F - ∑ i, a i • G i ∈ I ↔ (∑ i, a i • b i) = (⟨_, hF'⟩ : GlobalTheory.quotPiece I e) := by
    intro a
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk K, hsum,
      Subtype.ext_iff, eq_comm]
  refine ⟨fun i => b.repr ⟨_, hF'⟩ i, (hiff _).2 (b.sum_repr _), fun a ha => ?_⟩
  funext i
  rw [← (hiff a).1 ha, b.repr_sum_self]

theorem dimDeg_add {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    dimDeg I e + Module.finrank K (GlobalTheory.quotPiece I e) =
      Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  classical
  let H := MvPolynomial.homogeneousSubmodule σ K e
  let f : H →ₗ[K] MvPolynomial σ K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap.comp H.subtype
  have hr : LinearMap.range f = GlobalTheory.quotPiece I e := by
    rw [GlobalTheory.quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker f = (I.restrictScalars K).comap H.subtype := by
    ext x
    simp [f, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk] at hrk
  have hm : Module.finrank K ((I.restrictScalars K).comap H.subtype) =
      Module.finrank K ↥(H ⊓ I.restrictScalars K) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  unfold dimDeg
  rw [← hm, add_comm]
  exact hrk

variable {K σ : Type} [Field K] {X : Scheme.{0}}

def toPw (M : LB X) (e : ℕ) (t : (lbPow M e).Sec) : (AbLaw.pw M e).Sec where
  f := fun k => resG X (show M.U k ≤ (lbPow M e).U (fun _ => k) from
    fun _ hy => Set.mem_iInter.2 fun _ => hy) (t.f fun _ => k)
  compat := fun (i j : M.ι) => by
    have h := congrArg (resG X (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
      inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy)))
      (t.compat (fun _ => i) (fun _ => j))
    rw [map_mul] at h
    refine (AbLaw.rs_rs _ _ _).trans (((AbLaw.rs_rs _ _ _).symm.trans h).trans ?_)
    congr 1
    · have hu : res (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
          inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy))
          ((lbPow M e).g (fun _ => i) (fun _ => j)) = M.g i j ^ (e : ℤ) := by
        first
          | (change res _ (∏ _k : PUnit, _) = _
             rw [Fintype.prod_unique, map_zpow])
          | refine (congrArg (res _) (@Fintype.prod_unique PUnit _ _ _ _ _)).trans ((map_zpow _ _ _).trans ?_)
          | refine (congrArg (res _) (Fintype.prod_unique _)).trans ((map_zpow _ _ _).trans ?_)
        congr 1
        ext
        exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_self _ _)
      exact congrArg Units.val hu
    · exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_rs _ _ _).symm

theorem eventually_surj [Finite σ] [Nonempty σ] (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec) (hM : M.IsLB)
    (h : VAmp p M th) : ∀ᶠ e : ℕ in Filter.atTop, ∀ t : (lbPow M e).Sec, ∃ F : MvPolynomial σ K,
      F.IsHomogeneous e ∧ ∀ j, t.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F := by
  obtain ⟨m, ε, hε⟩ := h.exists_veryAmpleBy
  obtain ⟨t₀, ht⟩ := (AbLaw.serre_h1Zero_and_sections_polynomial).2 K X p M m (fun i => th (ε i)) hM hε
  refine Filter.eventually_atTop.2 ⟨t₀, fun e he t => ?_⟩
  obtain ⟨F, hF, hFe⟩ := ht e he (toPw M e t)
  refine ⟨MvPolynomial.rename ε F, hF.rename_isHomogeneous, fun j => ?_⟩
  have hj := hFe (j PUnit.unit)
  unfold toPw at hj
  unfold AbLaw.cst at hj
  have hrs : ∀ {U V : X.Opens} (hUV : V ≤ U), resG X hUV = AbLaw.rs X hUV := fun _ => rfl
  have hA : (lbPow M e).U j ≤ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit
  have hj' := congrArg (AbLaw.rs X hA) hj
  simp only [hrs] at hj' ⊢
  erw [AbLaw.rs_rs, AbLaw.rs_self] at hj'
  rw [hj', MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂_rename, MvPolynomial.coe_eval₂Hom]
  congr 1
  ext a
  simp only [RingHom.comp_apply, AbLaw.rs_rs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertFunction_idealOf : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  intro K σ _ _ _ X p M th hM h
  classical
  obtain ⟨hhom, -, hsec⟩ := GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power K σ X p M th hM h
  have hI : (idealOf p M th (𝟙 X)).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K) := by
    intro i r hr
    convert hhom r hr i using 1
    exact MvPolynomial.decomposition.decompose'_apply r i
  refine ⟨GlobalTheory.idealHilbertPoly (idealOf p M th (𝟙 X)), ?_⟩
  filter_upwards [GlobalTheory.eventually_finrank_quotPiece hI, eventually_surj p M th hM h] with e he hsurj
  refine ⟨Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e), ?_, he, dimDeg_add _ e⟩
  obtain ⟨G, hG, hGu⟩ := exists_forms_basis (idealOf p M th (𝟙 X)) e
  choose s hs1 hs2 hs3 using fun i => hsec e (G i) (hG i)
  have lin : ∀ (R : Type) [CommRing R] (φ : K →+* R) (v : σ → R)
      (a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K),
      MvPolynomial.eval₂ φ v (∑ i, a i • G i) = ∑ i, φ (a i) * MvPolynomial.eval₂ φ v (G i) := by
    intro R _ φ v a
    rw [← MvPolynomial.coe_eval₂Hom, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hsumG : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K,
      (∑ i, a i • G i).IsHomogeneous e := by
    intro a
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (hG i))
  have hzero : ∀ D : MvPolynomial σ K, D.IsHomogeneous e →
      ((∀ j : (lbPow M e).ι, MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) D = 0) ↔
        D ∈ idealOf p M th (𝟙 X)) := by
    intro D hD
    obtain ⟨τ, hτ1, hτ2, -⟩ := hsec e D hD
    rw [← hτ2]
    exact forall_congr' fun j => by rw [hτ1 j]; exact Iff.rfl
  refine ⟨s, fun t => ?_⟩
  obtain ⟨F, hF, hFt⟩ := hsurj t
  obtain ⟨a, ha, hau⟩ := hGu F hF
  refine ⟨a, fun j => ?_, fun a' ha' => hau a' ?_⟩
  · have h0 := (hzero _ (hF.sub (hsumG a))).2 ha j
    rw [MvPolynomial.eval₂_sub, sub_eq_zero] at h0
    rw [hFt j, h0, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl
  · refine (hzero _ (hF.sub (hsumG a'))).1 fun j => ?_
    rw [MvPolynomial.eval₂_sub, sub_eq_zero, ← hFt j, ha' j, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl

end GlobalTheory.ZV.HilbFn
end
