import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

section Sequence

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M]

abbrev ptGlobalToLocal (r : ℕ) :=
  globalToLocal φ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _) r

abbrev ptCompactToGlobal (r : ℕ) :=
  compactToGlobal φ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _) r

abbrev ptLocalToCompact (r : ℕ) :=
  localToCompact φ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _) r

def ptRes (v : ι) (r : ℕ) : cohomology M r →+ cohomology (Rep.res (φ v).toMonoidHom M) r :=
  (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) r).hom.toAddMonoidHom

theorem ptGlobalToLocal_apply (r : ℕ) (x : cohomology M r) (v : ι) :
    (ptGlobalToLocal φ M r).hom x v = ptRes φ M v r x :=
  rfl

theorem ptExact_global (r : ℕ) :
    Function.Exact (ptCompactToGlobal φ M r).hom (ptGlobalToLocal φ M r).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactCohomology_exact_global φ M _ (fun _ => 𝟙 _) r)

theorem ptExact_local (r : ℕ) :
    Function.Exact (ptGlobalToLocal φ M r).hom (ptLocalToCompact φ M r).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactCohomology_exact_local φ M _ (fun _ => 𝟙 _) r)

theorem ptExact_compact (r : ℕ) :
    Function.Exact (ptLocalToCompact φ M r).hom (ptCompactToGlobal φ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactCohomology_exact_compact φ M _ (fun _ => 𝟙 _) r)

def ptSha (r : ℕ) : AddSubgroup (cohomology M r) :=
  (ptGlobalToLocal φ M r).hom.toAddMonoidHom.ker

theorem mem_ptSha {r : ℕ} (x : cohomology M r) :
    x ∈ ptSha φ M r ↔ (ptGlobalToLocal φ M r).hom x = 0 :=
  AddMonoidHom.mem_ker

theorem ptRes_eq_zero_of_mem_ptSha {r : ℕ} {x : cohomology M r} (hx : x ∈ ptSha φ M r) (v : ι) :
    ptRes φ M v r x = 0 := by
  rw [← ptGlobalToLocal_apply, (mem_ptSha φ M x).1 hx]
  rfl

theorem ptCompactToGlobal_mem_ptSha {r : ℕ} (x : compactCohomologyRes φ M r) :
    (ptCompactToGlobal φ M r).hom x ∈ ptSha φ M r :=
  (mem_ptSha φ M _).2 ((ptExact_global φ M r _).2 ⟨x, rfl⟩)

theorem exists_ptCompactToGlobal_eq_of_mem_ptSha {r : ℕ} {x : cohomology M r}
    (hx : x ∈ ptSha φ M r) : ∃ y : compactCohomologyRes φ M r, (ptCompactToGlobal φ M r).hom y = x :=
  (ptExact_global φ M r x).1 ((mem_ptSha φ M x).1 hx)

theorem exists_ptLocalToCompact_eq_of_ptCompactToGlobal_eq_zero {r : ℕ}
    {x : compactCohomologyRes φ M (r + 1)} (hx : (ptCompactToGlobal φ M (r + 1)).hom x = 0) :
    ∃ ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r, (ptLocalToCompact φ M r).hom ξ = x :=
  (ptExact_compact φ M r x).1 hx

end Sequence

section Pairings

variable (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]

instance isDiscreteRep_res_dualRep_of_finite {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (ψ : K →ₜ* G) : IsDiscreteRep (Rep.res ψ.toMonoidHom (dualRep D M)) :=
  have : IsDiscreteRep (dualRep D M) := isDiscreteRep_dualRep D M
  isDiscreteRep_res_toMonoidHom ψ (dualRep D M)

abbrev ptLocalEval (v : ι) :
    Rep.res (φ v).toMonoidHom M ⊗ Rep.res (φ v).toMonoidHom (dualRep D M) ⟶
      Rep.res (φ v).toMonoidHom D :=
  (Rep.resFunctor (φ v).toMonoidHom).map (evalPairing D M)

variable (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)

def ptLocalPairing (v : ι) {r s : ℕ} (h : r + s = 2) :
    cohomology (Rep.res (φ v).toMonoidHom M) r →+
      cohomology (Rep.res (φ v).toMonoidHom (dualRep D M)) s →+ QZ :=
  (AddMonoidHom.compHom (inv v)).comp (bilinAddHom (cupPairing (ptLocalEval φ D M v) h))

theorem ptLocalPairing_apply (v : ι) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res (φ v).toMonoidHom M) r)
    (η : cohomology (Rep.res (φ v).toMonoidHom (dualRep D M)) s) :
    ptLocalPairing φ D M inv v h ξ η = inv v (cupPairing (ptLocalEval φ D M v) h ξ η) :=
  rfl

def ptLocalDualMap [Fintype ι] {r s : ℕ} (h : r + s = 2) :
    (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r) →+
      (cohomology (dualRep D M) s →+ QZ) where
  toFun ξ := ∑ v, (ptLocalPairing φ D M inv v h (ξ v)).comp (ptRes φ (dualRep D M) v s)
  map_zero' := AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
    exact Finset.sum_eq_zero fun v _ => DFunLike.congr_fun ((ptLocalPairing φ D M inv v h).map_zero) _
  map_add' ξ ξ' := AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply, AddMonoidHom.finsetSum_apply,
      AddMonoidHom.finsetSum_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ =>
      DFunLike.congr_fun ((ptLocalPairing φ D M inv v h).map_add (ξ v) (ξ' v)) _

theorem ptLocalDualMap_apply [Fintype ι] {r s : ℕ} (h : r + s = 2)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r) (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h ξ y =
      ∑ v, ptLocalPairing φ D M inv v h (ξ v) (ptRes φ (dualRep D M) v s y) := by
  change (∑ v, (ptLocalPairing φ D M inv v h (ξ v)).comp (ptRes φ (dualRep D M) v s)) y = _
  rw [AddMonoidHom.finsetSum_apply]
  rfl

variable {n : ℕ} (t : compactCohomologyRes φ D 3 →+ ZMod n)

def ptCompactDualMap {r s : ℕ} (h : r + s = 3) :
    compactCohomologyRes φ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp t)).comp
    (bilinAddHom (compactCupRes φ (evalPairing D M) h))

theorem ptCompactDualMap_apply {r s : ℕ} (h : r + s = 3) (x : compactCohomologyRes φ M r)
    (y : cohomology (dualRep D M) s) :
    ptCompactDualMap φ D M t h x y = zmodToQZ n (t (compactCupRes φ (evalPairing D M) h x y)) :=
  rfl

theorem compactCupRes_ptLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r) (y : cohomology (dualRep D M) s) :
    compactCupRes φ (evalPairing D M) h' ((ptLocalToCompact φ M r).hom ξ) y =
      (localToCompact φ D _ (fun _ => 𝟙 _) 2).hom
        (fun v => cupPairing (ptLocalEval φ D M v) h (ξ v) (ptRes φ (dualRep D M) v s y)) :=
  compactCup_localToCompact φ (evalPairing D M) _ _ h h' ξ y

theorem ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero {x : compactCohomologyRes φ M 1}
    (hx : (ptCompactToGlobal φ M 1).hom x = 0) {y : cohomology (dualRep D M) 2}
    (hy : y ∈ ptSha φ (dualRep D M) 2) :
    ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) x y = 0 := by
  obtain ⟨ξ, rfl⟩ := exists_ptLocalToCompact_eq_of_ptCompactToGlobal_eq_zero φ M (r := 0) hx
  have h0 : (fun v => cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ v)
      (ptRes φ (dualRep D M) v 2 y)) = 0 := by
    funext v
    rw [ptRes_eq_zero_of_mem_ptSha φ (dualRep D M) hy v]
    exact map_zero _
  rw [ptCompactDualMap_apply, compactCupRes_ptLocalToCompact φ D M (show 0 + 2 = 2 from rfl), h0,
    map_zero, map_zero, map_zero]

def ptShaLift (x : ptSha φ M 1) : compactCohomologyRes φ M 1 :=
  (exists_ptCompactToGlobal_eq_of_mem_ptSha φ M x.2).choose

omit [Finite M] in
theorem ptCompactToGlobal_ptShaLift (x : ptSha φ M 1) :
    (ptCompactToGlobal φ M 1).hom (ptShaLift φ M x) = x :=
  (exists_ptCompactToGlobal_eq_of_mem_ptSha φ M x.2).choose_spec

def ptShaPairing : ptSha φ M 1 →+ ptSha φ (dualRep D M) 2 →+ QZ where
  toFun x := (ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) (ptShaLift φ M x)).comp
    (ptSha φ (dualRep D M) 2).subtype
  map_zero' := by
    refine AddMonoidHom.ext fun y => ?_
    refine ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t ?_ y.2
    rw [ptCompactToGlobal_ptShaLift]
    rfl
  map_add' x x' := by
    refine AddMonoidHom.ext fun y => ?_
    have hz := ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t
      (x := ptShaLift φ M (x + x') - ptShaLift φ M x - ptShaLift φ M x') ?_ y.2
    · rw [map_sub, map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, sub_sub,
        sub_eq_zero] at hz
      simpa using hz
    · rw [map_sub, map_sub, ptCompactToGlobal_ptShaLift, ptCompactToGlobal_ptShaLift,
        ptCompactToGlobal_ptShaLift]
      simp

theorem ptShaPairing_apply (x : compactCohomologyRes φ M 1) (y : ptSha φ (dualRep D M) 2) :
    ptShaPairing φ D M t ⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩ y =
      ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) x y := by
  have hz := ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t
    (x := ptShaLift φ M ⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩ - x) ?_ y.2
  · rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero] at hz
    exact hz
  · rw [map_sub, ptCompactToGlobal_ptShaLift, sub_self]

end Pairings

end GroundTheory.ProfCoh
