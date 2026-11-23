import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
import GroundTheory.ProfiniteCohomology.RealPlaces.DevissageNatural
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.NormHomotopy
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2

section NormClass

variable {k F : Type} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem exists_normClass_cycle (B : Rep k F) [IsDiscreteRep B] (m : B) :
    ∃ z : (cochainsComplex B).cycles 0, normClass B m = ((cochainsComplex B).homologyπ 0).hom z ∧
      ((cochainsComplex B).iCycles 0).hom z = zeroCochain B (B.ρ.norm m) :=
  ⟨_, rfl, (cochainsComplex B).i_cyclesMk _ _ _ _⟩

theorem H0Iso_hom_normClass (B : Rep k F) [IsDiscreteRep B] (m : B) :
    (((H0Iso B).hom.hom (normClass B m) : B.ρ.invariants) : B) = B.ρ.norm m := by
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle B m
  rw [hz]
  refine (H0Iso_hom_cohomology_class_zero B z).trans ?_
  change cochainOf B (((cochainsComplex B).iCycles 0).hom z) Fin.elim0 = _
  rw [hiz]
  rfl

theorem normClass_mem_normClasses (B : Rep k F) [IsDiscreteRep B] (m : B) :
    normClass B m ∈ normClasses B := by
  have hN : B.ρ.norm m ∈ B.ρ.invariants := fun g => Representation.self_norm_apply _ _ _
  refine (mem_normClasses_iff B _).2 ⟨m, hN, ?_⟩
  have key : (H0Iso B).hom.hom (normClass B m) = ⟨B.ρ.norm m, hN⟩ :=
    Subtype.ext (H0Iso_hom_normClass B m)
  rw [← key]
  exact (hom_apply_hom_apply_of_comp_eq (H0Iso B).hom_inv_id _).symm

theorem exists_normClass_eq_of_mem (B : Rep k F) [IsDiscreteRep B] (x : cohomology B 0)
    (hx : x ∈ normClasses B) : ∃ m, normClass B m = x := by
  obtain ⟨a, h, rfl⟩ := (mem_normClasses_iff B x).1 hx
  refine ⟨a, ?_⟩
  have key : (H0Iso B).hom.hom (normClass B a) = ⟨B.ρ.norm a, h⟩ :=
    Subtype.ext (H0Iso_hom_normClass B a)
  rw [← key]
  exact (hom_apply_hom_apply_of_comp_eq (H0Iso B).hom_inv_id _).symm

theorem cupPairing_normClass_eq_zero {X Y Z : Rep k F} [IsDiscreteRep X] [IsDiscreteRep Y]
    [IsDiscreteRep Z] (μ : X ⊗ Y ⟶ Z) (e : X) {s : ℕ} (y : cohomology Y (s + 1)) :
    cupPairing μ (zero_add (s + 1)) (normClass X e) y = 0 := by
  rw [← cupLeibniz_homology]
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ (s + 1) y
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle X e
  rw [hz, LeibnizPairing.homology_homologyπ]
  refine (homologyπ_succ_eq_zero_iff (cochainsComplex Z) s _).2
    ⟨normHomotopy μ rfl e (((cochainsComplex Y).iCycles (s + 1)).hom c), ?_⟩
  rw [LeibnizPairing.iCycles_cycles]
  have hd : ((cochainsComplex Y).d (s + 1) (s + 1 + 1)).hom
      (((cochainsComplex Y).iCycles (s + 1)).hom c) = 0 :=
    (hom_apply_hom_apply_of_comp_eq ((cochainsComplex Y).iCycles_d (s + 1) (s + 1 + 1)) c).trans rfl
  have key := d_normHomotopy_add μ e (((cochainsComplex Y).iCycles (s + 1)).hom c)
  rw [hd, map_zero, add_zero] at key
  rw [key, hiz]
  rfl

end NormClass

section Sequence

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M]

abbrev ptTLocal (r : ℕ) : Type :=
  (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) r) × (∀ w, cohomology (Rep.res (ψ w).toMonoidHom M) r)

abbrev ptTGlobalToLocal (r : ℕ) :=
  tateGlobalToLocal φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _) r

abbrev ptTToGlobal (r : ℕ) :=
  tateToGlobal φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _) r

abbrev ptTLocalToCompact (r : ℕ) :=
  tateLocalToCompact φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _) r

omit [∀ w, Fintype (F w)] in
theorem ptTGlobalToLocal_apply (r : ℕ) (x : cohomology M r) :
    (ptTGlobalToLocal φ ψ M r).hom x = (fun v => ptRes φ M v r x, fun w => ptRes ψ M w r x) :=
  tateGlobalToLocal_hom_apply φ ψ M _ _ _ _ r x

theorem ptTExact_global (r : ℕ) :
    Function.Exact (ptTToGlobal φ ψ M (r + 1)).hom (ptTGlobalToLocal φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_global φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

theorem ptTExact_local (r : ℕ) :
    Function.Exact (ptTGlobalToLocal φ ψ M (r + 1)).hom (ptTLocalToCompact φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_local φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

theorem ptTExact_compact (r : ℕ) :
    Function.Exact (ptTLocalToCompact φ ψ M r).hom (ptTToGlobal φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_compact φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

abbrev ptTLocalHat : Type :=
  (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) 0) ×
    (∀ w, cohomologyTateZero (Rep.res (ψ w).toMonoidHom M))

def ptTHatMk : ptTLocal φ ψ M 0 →+ ptTLocalHat φ ψ M :=
  AddMonoidHom.prodMap (AddMonoidHom.id _)
    (AddMonoidHom.pi fun w => (normClasses (Rep.res (ψ w).toMonoidHom M)).mkQ.toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w => cohomology (Rep.res (ψ w).toMonoidHom M) 0) w))

omit [IsTopologicalGroup G] in
theorem ptTHatMk_apply (ξ : ptTLocal φ ψ M 0) :
    ptTHatMk φ ψ M ξ = (ξ.1, fun w => Submodule.Quotient.mk (ξ.2 w)) :=
  rfl

omit [IsTopologicalGroup G] in
theorem ptTHatMk_surjective : Function.Surjective (ptTHatMk φ ψ M) := fun ξ => by
  choose y hy using fun w => Submodule.Quotient.mk_surjective _ (ξ.2 w)
  exact ⟨(ξ.1, y), Prod.ext rfl (funext hy)⟩

omit [IsTopologicalGroup G] in
theorem ptTHatMk_eq_zero_iff (ξ : ptTLocal φ ψ M 0) :
    ptTHatMk φ ψ M ξ = 0 ↔ ξ.1 = 0 ∧ ∀ w, ξ.2 w ∈ normClasses (Rep.res (ψ w).toMonoidHom M) := by
  rw [ptTHatMk_apply]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, fun w =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.snd h) w)⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (funext fun w => (Submodule.Quotient.mk_eq_zero _).2 (h2 w))

def ptTGlobalToLocalHat : cohomology M 0 →+ ptTLocalHat φ ψ M :=
  (ptTHatMk φ ψ M).comp (ptTGlobalToLocal φ ψ M 0).hom.toAddMonoidHom

theorem ptTGlobalToLocalHat_apply (x : cohomology M 0) :
    ptTGlobalToLocalHat φ ψ M x = ptTHatMk φ ψ M ((ptTGlobalToLocal φ ψ M 0).hom x) :=
  rfl

def descendAddHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B)
    (hf : Function.Surjective f) (g : A →+ C) (h : f.ker ≤ g.ker) : B →+ C :=
  (QuotientAddGroup.lift _ g h).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm.toAddMonoidHom

theorem descendAddHom_apply {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (hf : Function.Surjective f) (g : A →+ C) (h : f.ker ≤ g.ker) (a : A) :
    descendAddHom f hf g h (f a) = g a := by
  have e : (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f a) = (a : A ⧸ f.ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  change QuotientAddGroup.lift _ g h ((QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f a)) = g a
  rw [e]
  rfl

theorem ptTLocalToCompact_of_hatMk_eq_zero (ξ : ptTLocal φ ψ M 0) (hξ : ptTHatMk φ ψ M ξ = 0) :
    (ptTLocalToCompact φ ψ M 0).hom ξ = 0 := by
  obtain ⟨h1, h2⟩ := (ptTHatMk_eq_zero_iff φ ψ M ξ).1 hξ
  choose e he using fun w => exists_normClass_eq_of_mem _ (ξ.2 w) (h2 w)
  have hx : (tateGlobalZeroToLocal φ ψ M (fun v => Rep.res (φ v).toMonoidHom M) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom M) (fun _ => 𝟙 _)).hom (0, e) = ξ := by
    rw [tateGlobalZeroToLocal_hom_apply, map_zero, map_zero, zero_add]
    exact Prod.ext h1.symm (funext he)
  rw [← hx]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalZeroToLocal_tateLocalToCompact φ ψ M _ _ _ _) _

def ptTLocalHatToCompact : ptTLocalHat φ ψ M →+ tateCompactCohomologyRes φ ψ M 1 :=
  descendAddHom (ptTHatMk φ ψ M) (ptTHatMk_surjective φ ψ M)
    (ptTLocalToCompact φ ψ M 0).hom.toAddMonoidHom
    fun ξ hξ => ptTLocalToCompact_of_hatMk_eq_zero φ ψ M ξ hξ

theorem ptTLocalHatToCompact_hatMk (ξ : ptTLocal φ ψ M 0) :
    ptTLocalHatToCompact φ ψ M (ptTHatMk φ ψ M ξ) = (ptTLocalToCompact φ ψ M 0).hom ξ :=
  descendAddHom_apply _ _ _ _ ξ

def ptTSha (r : ℕ) : AddSubgroup (cohomology M r) :=
  (ptTGlobalToLocal φ ψ M r).hom.toAddMonoidHom.ker

omit [∀ w, Fintype (F w)] in
theorem mem_ptTSha {r : ℕ} (x : cohomology M r) :
    x ∈ ptTSha φ ψ M r ↔ (ptTGlobalToLocal φ ψ M r).hom x = 0 :=
  AddMonoidHom.mem_ker

theorem ptTToGlobal_mem_ptTSha {r : ℕ} (x : tateCompactCohomologyRes φ ψ M (r + 1)) :
    (ptTToGlobal φ ψ M (r + 1)).hom x ∈ ptTSha φ ψ M (r + 1) :=
  (mem_ptTSha φ ψ M _).2 ((ptTExact_global φ ψ M r _).2 ⟨x, rfl⟩)

theorem exists_ptTToGlobal_eq_of_mem_ptTSha {r : ℕ} {x : cohomology M (r + 1)}
    (hx : x ∈ ptTSha φ ψ M (r + 1)) :
    ∃ y : tateCompactCohomologyRes φ ψ M (r + 1), (ptTToGlobal φ ψ M (r + 1)).hom y = x :=
  (ptTExact_global φ ψ M r x).1 ((mem_ptTSha φ ψ M x).1 hx)

end Sequence

section Pairings

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D]
  (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M]
  (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
  (invr : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom D) 2 →+ QZ)

def ptTLocalDualMap {r s : ℕ} (h : r + s = 2) :
    ptTLocal φ ψ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (ptLocalDualMap φ D M inv h).comp (AddMonoidHom.fst _ _) +
    (ptLocalDualMap ψ D M invr h).comp (AddMonoidHom.snd _ _)

omit [∀ w, Fintype (F w)] in
theorem ptTLocalDualMap_apply {r s : ℕ} (h : r + s = 2) (ξ : ptTLocal φ ψ M r)
    (y : cohomology (dualRep D M) s) :
    ptTLocalDualMap φ ψ D M inv invr h ξ y =
      ∑ v, ptLocalPairing φ D M inv v h (ξ.1 v) (ptRes φ (dualRep D M) v s y) +
        ∑ w, ptLocalPairing ψ D M invr w h (ξ.2 w) (ptRes ψ (dualRep D M) w s y) := by
  change ptLocalDualMap φ D M inv h ξ.1 y + ptLocalDualMap ψ D M invr h ξ.2 y = _
  rw [ptLocalDualMap_apply, ptLocalDualMap_apply]

theorem ptTLocalDualMap_of_hatMk_eq_zero (ξ : ptTLocal φ ψ M 0) (hξ : ptTHatMk φ ψ M ξ = 0) :
    ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) ξ = 0 := by
  obtain ⟨h1, h2⟩ := (ptTHatMk_eq_zero_iff φ ψ M ξ).1 hξ
  refine AddMonoidHom.ext fun y => ?_
  rw [ptTLocalDualMap_apply, AddMonoidHom.zero_apply, h1]
  refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v _ => ?_) (Finset.sum_eq_zero fun w _ => ?_)).trans
    (add_zero 0)
  · exact DFunLike.congr_fun (map_zero (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))) _
  · obtain ⟨e, he⟩ := exists_normClass_eq_of_mem _ (ξ.2 w) (h2 w)
    rw [ptLocalPairing_apply, ← he]
    refine (congrArg (invr w) ?_).trans (map_zero _)
    exact cupPairing_normClass_eq_zero (s := 1) _ e _

def ptTLocalHatDualMap : ptTLocalHat φ ψ M →+ (cohomology (dualRep D M) 2 →+ QZ) :=
  descendAddHom (ptTHatMk φ ψ M) (ptTHatMk_surjective φ ψ M)
    (ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl))
    fun ξ hξ => ptTLocalDualMap_of_hatMk_eq_zero φ ψ D M inv invr ξ hξ

theorem ptTLocalHatDualMap_hatMk (ξ : ptTLocal φ ψ M 0) :
    ptTLocalHatDualMap φ ψ D M inv invr (ptTHatMk φ ψ M ξ) =
      ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) ξ :=
  descendAddHom_apply _ _ _ _ ξ

variable {n : ℕ} (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)

def ptTCompactDualMap {r s : ℕ} (h : r + s = 3) :
    tateCompactCohomologyRes φ ψ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp t)).comp
    (bilinAddHom (tateCompactCupRes φ ψ (evalPairing D M) h))

omit [Fintype ι] [Fintype κ] in
theorem ptTCompactDualMap_apply {r s : ℕ} (h : r + s = 3) (x : tateCompactCohomologyRes φ ψ M r)
    (y : cohomology (dualRep D M) s) :
    ptTCompactDualMap φ ψ D M t h x y =
      zmodToQZ n (t (tateCompactCupRes φ ψ (evalPairing D M) h x y)) :=
  rfl

omit [Fintype ι] [Fintype κ] in

theorem tateCompactCupRes_ptTLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ptTLocal φ ψ M r) (y : cohomology (dualRep D M) s) :
    tateCompactCupRes φ ψ (evalPairing D M) h' ((ptTLocalToCompact φ ψ M r).hom ξ) y =
      (ptTLocalToCompact φ ψ D 2).hom
        (fun v => cupPairing (ptLocalEval φ D M v) h (ξ.1 v) (ptRes φ (dualRep D M) v s y),
          fun w => cupPairing (ptLocalEval ψ D M w) h (ξ.2 w) (ptRes ψ (dualRep D M) w s y)) :=
  tateCompactCup_tateLocalToCompact φ ψ (evalPairing D M) _ _ _ _ h h' ξ y

omit [Fintype ι] [Fintype κ] [∀ w, Fintype (F w)] [Finite M] in
theorem ptRes_eq_zero_of_mem_ptTSha {r : ℕ} {x : cohomology M r} (hx : x ∈ ptTSha φ ψ M r) :
    (∀ v, ptRes φ M v r x = 0) ∧ ∀ w, ptRes ψ M w r x = 0 := by
  have h := (mem_ptTSha φ ψ M x).1 hx
  rw [ptTGlobalToLocal_apply] at h
  exact ⟨fun v => congrFun (congrArg Prod.fst h) v, fun w => congrFun (congrArg Prod.snd h) w⟩

omit [Fintype ι] [Fintype κ] in

theorem ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero {x : tateCompactCohomologyRes φ ψ M 1}
    (hx : (ptTToGlobal φ ψ M 1).hom x = 0) {y : cohomology (dualRep D M) 2}
    (hy : y ∈ ptTSha φ ψ (dualRep D M) 2) :
    ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) x y = 0 := by
  obtain ⟨ξ, rfl⟩ := (ptTExact_compact φ ψ M 0 x).1 hx
  obtain ⟨h1, h2⟩ := ptRes_eq_zero_of_mem_ptTSha φ ψ (dualRep D M) hy
  rw [ptTCompactDualMap_apply, tateCompactCupRes_ptTLocalToCompact φ ψ D M (show 0 + 2 = 2 from rfl)]
  have h0 : ((fun v => cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ.1 v)
      (ptRes φ (dualRep D M) v 2 y)), (fun w => cupPairing (ptLocalEval ψ D M w)
        (show 0 + 2 = 2 from rfl) (ξ.2 w) (ptRes ψ (dualRep D M) w 2 y))) = (0 : ptTLocal φ ψ D 2) := by
    refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
    · change cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ.1 v)
        (ptRes φ (dualRep D M) v 2 y) = 0
      rw [h1 v]
      exact map_zero _
    · change cupPairing (ptLocalEval ψ D M w) (show 0 + 2 = 2 from rfl) (ξ.2 w)
        (ptRes ψ (dualRep D M) w 2 y) = 0
      rw [h2 w]
      exact map_zero _
  rw [h0, map_zero, map_zero, map_zero]

def ptTShaLift (x : ptTSha φ ψ M 1) : tateCompactCohomologyRes φ ψ M 1 :=
  (exists_ptTToGlobal_eq_of_mem_ptTSha φ ψ M (r := 0) x.2).choose

omit [Fintype ι] [Fintype κ] [Finite M] in
theorem ptTToGlobal_ptTShaLift (x : ptTSha φ ψ M 1) :
    (ptTToGlobal φ ψ M 1).hom (ptTShaLift φ ψ M x) = x :=
  (exists_ptTToGlobal_eq_of_mem_ptTSha φ ψ M (r := 0) x.2).choose_spec

def ptTShaPairing : ptTSha φ ψ M 1 →+ ptTSha φ ψ (dualRep D M) 2 →+ QZ where
  toFun x := (ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) (ptTShaLift φ ψ M x)).comp
    (ptTSha φ ψ (dualRep D M) 2).subtype
  map_zero' := by
    refine AddMonoidHom.ext fun y => ?_
    refine ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t ?_ y.2
    rw [ptTToGlobal_ptTShaLift]
    rfl
  map_add' x x' := by
    refine AddMonoidHom.ext fun y => ?_
    have hz := ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t
      (x := ptTShaLift φ ψ M (x + x') - ptTShaLift φ ψ M x - ptTShaLift φ ψ M x') ?_ y.2
    · rw [map_sub, map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, sub_sub,
        sub_eq_zero] at hz
      simpa using hz
    · rw [map_sub, map_sub, ptTToGlobal_ptTShaLift, ptTToGlobal_ptTShaLift, ptTToGlobal_ptTShaLift]
      simp

omit [Fintype ι] [Fintype κ] in

theorem ptTShaPairing_apply (x : tateCompactCohomologyRes φ ψ M 1) (y : ptTSha φ ψ (dualRep D M) 2) :
    ptTShaPairing φ ψ D M t ⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩ y =
      ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) x y := by
  have hz := ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t
    (x := ptTShaLift φ ψ M ⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩ - x) ?_ y.2
  · rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero] at hz
    exact hz
  · rw [map_sub, ptTToGlobal_ptTShaLift, sub_self]

end Pairings

end GroundTheory.ProfCoh
