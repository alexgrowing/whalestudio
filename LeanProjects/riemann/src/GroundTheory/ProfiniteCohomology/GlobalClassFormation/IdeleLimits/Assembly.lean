import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsTrans
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield IdeleLimit DirectSum

noncomputable section

variable {K : FiniteSubfield} (n : ℕ)

abbrev levelTransitionG {p q : GLevel K} (h : p ≤ q) :
    cohomology (ideleRep K.1 p.1.1) n ⟶ cohomology (ideleRep K.1 q.1.1) n :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelTransition K p.1 q.1 n

theorem levelTransitionG_comp_levelInfl {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelInfl K q.1 n).hom ((levelTransitionG n h).hom y) = (levelInfl K p.1 n).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  exact congrArg (fun φ => φ.hom y) (levelTransition_comp_levelInfl (K := K) (F := p.1) (E := q.1) n)

theorem levelTransitionG_trans {p q r : GLevel K} (h₁ : p ≤ q) (h₂ : q ≤ r)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelTransitionG n h₂).hom ((levelTransitionG n h₁).hom y) =
      (levelTransitionG n (h₁.trans h₂)).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h₁⟩
  haveI : Fact (q.1 ≤ r.1) := ⟨h₂⟩
  haveI : Fact (p.1 ≤ r.1) := ⟨h₁.trans h₂⟩
  exact congrArg (fun φ => φ.hom y)
    (levelTransition_comp_levelTransition (K := K) (F := p.1) (E := q.1) (M := r.1) n)

variable (K) in

structure LevelDecomposition where

  L : Place K.1 → GLevel K → Type
  [grp : ∀ v p, AddCommGroup (L v p)]

  e : ∀ v (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ L v p

  lt : ∀ v {p q : GLevel K}, p ≤ q → L v p →+ L v q

  compat : ∀ v {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n),
    e v q ((cohomologyMap (placeProj v) n).hom ((levelTransitionG n h).hom y)) =
      lt v h (e v p ((cohomologyMap (placeProj v) n).hom y))

attribute [instance] LevelDecomposition.grp

structure LocalLimit {n : ℕ} (D : LevelDecomposition K n) where

  T : Place K.1 → Type
  [grp : ∀ v, AddCommGroup (T v)]

  infl : ∀ v (p : GLevel K), D.L v p →+ T v
  infl_compat : ∀ v {p q : GLevel K} (h : p ≤ q) (z : D.L v p), infl v q (D.lt v h z) = infl v p z
  exists_infl : ∀ v (t : T v), ∃ (p : GLevel K) (z : D.L v p), infl v p z = t
  exists_lt_eq_zero : ∀ v (p : GLevel K) (z : D.L v p), infl v p z = 0 →
    ∃ (q : GLevel K) (h : p ≤ q), D.lt v h z = 0

attribute [instance] LocalLimit.grp

variable {n} (D : LevelDecomposition K n) (T : LocalLimit D) (hn : 1 ≤ n)

include hn in

def levelSum (p : GLevel K) : cohomology (ideleRep K.1 p.1.1) n →+ ⨁ v : Place K.1, T.T v :=
  (DFinsupp.mapRange.addMonoidHom fun v => (T.infl v p).comp (D.e v p).toAddMonoidHom).comp
    (idelesCohomologyEquiv hn).symm.toAddMonoidHom

theorem levelSum_apply (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) (v : Place K.1) :
    levelSum D T hn p y v = T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change T.infl v p (D.e v p ((idelesCohomologyEquiv hn).symm y v)) = _
  rw [idelesCohomologyEquiv_symm_apply]

theorem levelSum_levelTransition {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    levelSum D T hn q ((levelTransitionG n h).hom y) = levelSum D T hn p y := by
  ext v
  rw [levelSum_apply, levelSum_apply, D.compat, T.infl_compat]

theorem levelSum_eq_of_levelInfl_eq {p q : GLevel K} (y : cohomology (ideleRep K.1 p.1.1) n)
    (y' : cohomology (ideleRep K.1 q.1.1) n)
    (h : (levelInfl K p.1 n).hom y = (levelInfl K q.1 n).hom y') :
    levelSum D T hn p y = levelSum D T hn q y' := by
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  have hz : (levelInfl K r.1 n).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := by
    rw [map_sub, levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl, h, sub_self]
  obtain ⟨s, hrs, hs⟩ := exists_levelTransition_eq_zero n r _ hz
  have hs' : (levelTransitionG n hrs).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := hs
  rw [map_sub, sub_eq_zero] at hs'
  rw [← levelSum_levelTransition D T hn hpr, ← levelSum_levelTransition D T hn hrs, hs',
    levelSum_levelTransition, levelSum_levelTransition]

def pick (x : cohomology (limitRep K) n) : Σ p : GLevel K, cohomology (ideleRep K.1 p.1.1) n :=
  ⟨(exists_levelInfl_eq n x).choose, (exists_levelInfl_eq n x).choose_spec.choose⟩

theorem levelInfl_pick (x : cohomology (limitRep K) n) :
    (levelInfl K (pick x).1.1 n).hom (pick x).2 = x :=
  (exists_levelInfl_eq n x).choose_spec.choose_spec

def limitCohomologyFun (x : cohomology (limitRep K) n) : ⨁ v : Place K.1, T.T v :=
  levelSum D T hn (pick x).1 (pick x).2

theorem limitCohomologyFun_eq (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (x : cohomology (limitRep K) n) (h : (levelInfl K p.1 n).hom y = x) :
    limitCohomologyFun D T hn x = levelSum D T hn p y :=
  levelSum_eq_of_levelInfl_eq D T hn (pick x).2 y ((levelInfl_pick x).trans h.symm)

set_option maxHeartbeats 4000000 in
theorem limitCohomologyFun_add (x₁ x₂ : cohomology (limitRep K) n) :
    limitCohomologyFun D T hn (x₁ + x₂) = limitCohomologyFun D T hn x₁ + limitCohomologyFun D T hn x₂ := by
  obtain ⟨p₁, y₁, rfl⟩ := exists_levelInfl_eq n x₁
  obtain ⟨p₂, y₂, rfl⟩ := exists_levelInfl_eq n x₂
  obtain ⟨r, h1r, h2r⟩ := GLevel.exists_ge p₁ p₂
  have hsum : (levelInfl K r.1 n).hom ((levelTransitionG n h1r).hom y₁ +
      (levelTransitionG n h2r).hom y₂) = (levelInfl K p₁.1 n).hom y₁ + (levelInfl K p₂.1 n).hom y₂ := by
    rw [map_add, levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl]
  rw [limitCohomologyFun_eq D T hn p₁ y₁ _ rfl, limitCohomologyFun_eq D T hn p₂ y₂ _ rfl,
    limitCohomologyFun_eq D T hn r _ _ hsum, map_add, levelSum_levelTransition, levelSum_levelTransition]

def limitCohomologyHom : cohomology (limitRep K) n →+ ⨁ v : Place K.1, T.T v :=
  AddMonoidHom.mk' (limitCohomologyFun D T hn) (limitCohomologyFun_add D T hn)

theorem limitCohomologyHom_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) :
    limitCohomologyHom D T hn ((levelInfl K p.1 n).hom y) = levelSum D T hn p y :=
  limitCohomologyFun_eq D T hn p y _ rfl

theorem eq_zero_of_forall_placeProj {n : ℕ} (hn : 1 ≤ n) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (h : ∀ v : Place K.1, (cohomologyMap (placeProj v) n).hom y = 0) : y = 0 := by
  apply (idelesCohomologyEquiv hn).symm.injective
  rw [map_zero]
  ext v
  rw [idelesCohomologyEquiv_symm_apply, h v]
  rfl

theorem limitCohomologyHom_injective : Function.Injective (limitCohomologyHom D T hn) := by
  classical
  refine (injective_iff_map_eq_zero (limitCohomologyHom D T hn)).2 fun x hx => ?_
  obtain ⟨p, y, rfl⟩ := exists_levelInfl_eq n x
  rw [limitCohomologyHom_levelInfl] at hx
  have hv : ∀ v, T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) = 0 := fun v => by
    have := congrArg (fun ζ : ⨁ v : Place K.1, T.T v => ζ v) hx
    rw [levelSum_apply] at this
    exact this
  choose q hpq hq using fun v => T.exists_lt_eq_zero v p _ (hv v)
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p (((idelesCohomologyEquiv hn).symm y).support.image q))
  have hpr : p ≤ r := hr _ (Finset.mem_insert_self _ _)
  have hzero : (levelTransitionG n hpr).hom y = 0 := by
    refine eq_zero_of_forall_placeProj hn r _ fun v => (D.e v r).injective ?_
    rw [map_zero]
    by_cases hvS : v ∈ ((idelesCohomologyEquiv hn).symm y).support
    · have hqr : q v ≤ r := hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvS))
      rw [← levelTransitionG_trans n (hpq v) hqr, D.compat, D.compat, hq v, map_zero]
    · have h0 : (cohomologyMap (placeProj v) n).hom y = 0 := by
        rw [← idelesCohomologyEquiv_symm_apply hn]
        exact DFinsupp.notMem_support_iff.1 hvS
      rw [D.compat, h0, map_zero, map_zero]
  rw [← levelTransitionG_comp_levelInfl n hpr, hzero, map_zero]

theorem limitCohomologyHom_surjective : Function.Surjective (limitCohomologyHom D T hn) := by
  classical
  intro ζ
  choose p z hz using fun v => T.exists_infl v (ζ v)
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (GLevel K))
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p₀ (ζ.support.image p))
  have hpr : ∀ v ∈ ζ.support, p v ≤ r := fun v hv =>
    hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))
  let ξ : ⨁ v : Place K.1, cohomology (placeRep r.1.1 v) n :=
    DFinsupp.mk ζ.support fun v => (D.e v.1 r).symm (D.lt v.1 (hpr v.1 v.2) (z v.1))
  refine ⟨(levelInfl K r.1 n).hom (idelesCohomologyEquiv hn ξ), ?_⟩
  rw [limitCohomologyHom_levelInfl]
  ext v
  rw [levelSum_apply, ← idelesCohomologyEquiv_symm_apply hn, AddEquiv.symm_apply_apply]
  by_cases hv : v ∈ ζ.support
  · have : ξ v = (D.e v r).symm (D.lt v (hpr v hv) (z v)) := by
      simp only [ξ, DFinsupp.mk_apply, dif_pos hv]
    rw [this, AddEquiv.apply_symm_apply, T.infl_compat, hz]
  · have : ξ v = 0 := by
      simp only [ξ, DFinsupp.mk_apply, dif_neg hv]
    rw [this, map_zero, map_zero, DFinsupp.notMem_support_iff.1 hv]

def limitCohomologyEquiv : cohomology (limitRep K) n ≃+ ⨁ v : Place K.1, T.T v :=
  AddEquiv.ofBijective (limitCohomologyHom D T hn)
    ⟨limitCohomologyHom_injective D T hn, limitCohomologyHom_surjective D T hn⟩

theorem limitCohomologyEquiv_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (v : Place K.1) :
    limitCohomologyEquiv D T hn ((levelInfl K p.1 n).hom y) v =
      T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change limitCohomologyHom D T hn _ v = _
  rw [limitCohomologyHom_levelInfl, levelSum_apply]

end

end GroundTheory.ProfCoh
