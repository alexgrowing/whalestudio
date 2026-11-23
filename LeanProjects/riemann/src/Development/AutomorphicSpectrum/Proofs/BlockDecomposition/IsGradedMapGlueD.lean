import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

variable {ι : Type} [LinearOrder ι] {A : Type} [CommRing A]
  {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
  [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)]
  (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')

def glueD : (∀ i : ι, P {i}) →ₗ[MvPolynomial ι A] ∀ k : ι × ι, P {k.1, k.2} :=
  LinearMap.pi fun k => res _ _ (sub_pair_left k.1 k.2) ∘ₗ LinearMap.proj k.1 -
    res _ _ (sub_pair_right k.1 k.2) ∘ₗ LinearMap.proj k.2

def glue : Submodule (MvPolynomial ι A) (∀ i : ι, P {i}) := LinearMap.ker (glueD res)

variable {res} in
theorem mem_glue {c : ∀ i : ι, P {i}} : c ∈ glue res ↔
    ∀ i j, res {i} {i, j} (sub_pair_left i j) (c i) = res {j} {i, j} (sub_pair_right i j) (c j) := by
  rw [glue, LinearMap.mem_ker]
  constructor
  · intro h i j
    have hk := congrFun h (i, j)
    simpa [glueD, sub_eq_zero] using hk
  · intro h
    funext k
    simp [glueD, sub_eq_zero, h k.1 k.2]

def evAt (i : ι) (I : Finset ι) (hi : i ∈ I) : glue res →ₗ[MvPolynomial ι A] P I :=
  res {i} I (Finset.singleton_subset_iff.2 hi) ∘ₗ LinearMap.proj i ∘ₗ (glue res).subtype

theorem evAt_apply (i : ι) (I : Finset ι) (hi : i ∈ I) (m : glue res) :
    evAt res i I hi m = res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) := rfl

def ev (I : Finset ι) (hI : I.Nonempty) : glue res →ₗ[MvPolynomial ι A] P I :=
  evAt res (I.min' hI) I (I.min'_mem hI)

variable {res}

theorem evAt_eq (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {i i' : ι} {I : Finset ι} (hi : i ∈ I) (hi' : i' ∈ I) (m : glue res) :
    evAt res i I hi m = evAt res i' I hi' m := by
  have hsub : ({i, i'} : Finset ι) ⊆ I := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hi'
  have hm := (mem_glue.1 m.2) i i'
  have e1 : res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) =
      res {i, i'} I hsub (res {i} {i, i'} (sub_pair_left i i') (m.1 i)) :=
    (hcomp _ _ _ _ _ _).symm
  have e2 : res {i'} I (Finset.singleton_subset_iff.2 hi') (m.1 i') =
      res {i, i'} I hsub (res {i'} {i, i'} (sub_pair_right i i') (m.1 i')) :=
    (hcomp _ _ _ _ _ _).symm
  rw [evAt_apply, evAt_apply, e1, e2, hm]

theorem ev_eq (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {i : ι} {I : Finset ι} (hI : I.Nonempty) (hi : i ∈ I) (m : glue res) :
    ev res I hI m = res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) := by
  show evAt res (I.min' hI) I (I.min'_mem hI) m = _
  rw [evAt_eq hcomp (I.min'_mem hI) hi m, evAt_apply]

theorem res_ev (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {I J : Finset ι} (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (m : glue res) :
    res I J h (ev res I hI m) = ev res J hJ m := by
  have hi := I.min'_mem hI
  rw [ev_eq hcomp hI hi, ev_eq hcomp hJ (h hi), hcomp]

variable [Fintype ι] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, DirectSum.Decomposition (𝒢 S)]

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
theorem isGradedMap_glueD (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) :
    IsGradedMap (grPi fun i : ι => 𝒢 {i}) (grPi fun k : ι × ι => 𝒢 {k.1, k.2}) (glueD res) := by
  unfold glueD
  refine IsGradedMap.pi fun k => ?_
  beta_reduce
  rw [sub_eq_add_neg]
  exact ((hgr _ _ _).comp (isGradedMap_piProj _ _ k.1)).add
    ((hgr _ _ _).comp (isGradedMap_piProj _ _ k.2)).neg

variable (res) in

def glueGr : ℤ → Submodule A (glue res) := grSub (grPi fun i : ι => 𝒢 {i}) (glue res)

@[instance_reducible]
def glueDec (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) :
    DirectSum.Decomposition (glueGr res 𝒢) :=
  grSubDecomposition _ (isGradedMap_glueD 𝒢 hgr).isHomogeneous_ker

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
instance glueGr.polyGradedSMul [∀ S, PolyGradedSMul ι (𝒢 S)] :
    PolyGradedSMul ι (glueGr res 𝒢) :=
  grSub.polyGradedSMul _ _

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
theorem isGradedMap_ev (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h))
    (I : Finset ι) (hI : I.Nonempty) : IsGradedMap (glueGr res 𝒢) (𝒢 I) (ev res I hI) := by
  unfold ev evAt glueGr
  exact (hgr _ _ _).comp ((isGradedMap_piProj _ _ _).comp (isGradedMap_subtype _ _))

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
