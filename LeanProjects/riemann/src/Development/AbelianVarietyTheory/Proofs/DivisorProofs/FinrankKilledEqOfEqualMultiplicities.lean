import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfRankEq

noncomputable section

open GlobalTheory.CuspMult

namespace GlobalTheory.RepCount

variable {H W X : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

def modMap {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) : σ.asModule →ₗ[MonoidAlgebra ℂ H] ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
    (f.intertwiningMap_of_isIntertwiningMap σ ρ hf)

theorem modMap_apply {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) (x : σ.asModule) :
    ρ.asModuleEquiv (modMap f hf x) = f (σ.asModuleEquiv x) := rfl

def subEquiv {ρ : Representation ℂ H X} (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ H] U.asSubmodule :=
  LinearEquiv.ofBijective
    ((modMap (σ := U.toRepresentation) (ρ := ρ) U.toSubmodule.subtype (fun _ _ => rfl)).codRestrict
      U.asSubmodule (fun x => (U.toRepresentation.asModuleEquiv x).2))
    ⟨fun a b h => U.toRepresentation.asModuleEquiv.injective (Subtype.ext (congrArg Subtype.val h)),
     fun y => ⟨U.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv y.1, y.2⟩, rfl⟩⟩

variable [TopologicalSpace H]

theorem isAdmissible_of_injective {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (f : W →ₗ[ℂ] X) (hf : ∀ g s, f (σ g s) = ρ g (f s)) (hi : Function.Injective f)
    (h : GlobalTheory.PRep.IsAdmissible ρ) : GlobalTheory.PRep.IsAdmissible σ := by
  refine ⟨fun v => ?_, fun K hK hK' => ?_⟩
  · have : {g : H | σ g v = v} = {g : H | ρ g (f v) = f v} := by
      ext g
      simp only [Set.mem_setOf_eq, ← hf, hi.eq_iff]
    rw [this]
    exact h.1 _
  · haveI := h.2 K hK hK'
    refine FiniteDimensional.of_injective
      (f.restrict (p := GlobalTheory.PRep.fixed σ K) (q := GlobalTheory.PRep.fixed ρ K) (fun v hv k => ?_)) ?_
    · rw [← hf, hv k, map_smul]
    · intro a b hab
      exact Subtype.ext (hi (congrArg Subtype.val hab))

def pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) :=
  {m | ∃ U : Subrepresentation ρ, (U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation) ∧ U.asSubmodule = m}

theorem simple_of_mem_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule} (hm : m ∈ pieces ρ C) :
    IsSimpleModule (MonoidAlgebra ℂ H) m := by
  obtain ⟨U, ⟨-, hU, -⟩, rfl⟩ := hm
  exact IsSimpleModule.congr (subEquiv U).symm

theorem mem_sSup_pieces_of_mem {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : X}
    (hx : x ∈ irrSum ρ C) : ρ.asModuleEquiv.symm x ∈ sSup (pieces ρ C) := by
  have : irrSum ρ C ≤ ((sSup (pieces ρ C)).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun U hU y hy => ?_
    exact (le_sSup (s := pieces ρ C) ⟨U, hU, rfl⟩ : U.asSubmodule ≤ _) hy
  exact this hx

theorem mem_of_mem_sSup_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : ρ.asModule}
    (hx : x ∈ sSup (pieces ρ C)) : ρ.asModuleEquiv x ∈ C := by
  rw [sSup_eq_iSup'] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv x ∈ C) hx ?_ ?_ ?_
  · rintro ⟨_, U, hU, rfl⟩ y hy
    exact hU.1 hy
  · simp
  · intro a b ha hb
    rw [map_add]
    exact C.add_mem ha hb

theorem semisimple_sSup_pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)) := by
  rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => ?_
  haveI := simple_of_mem_pieces hm
  infer_instance

theorem apply_mem_irrSum {σ : Representation ℂ H W} {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) {f : W →ₗ[ℂ] X}
    (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf.2
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | h0
  · have hi' : Function.Injective f := hi
    let e : W ≃ₗ[ℂ] F.range.toSubmodule := LinearEquiv.ofInjective f hi'
    have he : ∀ g s, e (σ g s) = F.range.toRepresentation g (e s) :=
      fun g s => Subtype.ext (hf.2 g s)
    have he' : ∀ g s, e.symm (F.range.toRepresentation g s) = σ g (e.symm s) := by
      intro g s
      rw [LinearEquiv.symm_apply_eq, he, e.apply_symm_apply]
    have hirr : F.range.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact IsSimpleModule.congr
        (LinearEquiv.ofBijective (modMap e.symm.toLinearMap he') e.symm.bijective)
    have hle : F.range.toSubmodule ≤ irrSum ρ C :=
      le_iSup₂_of_le (f := fun (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧
        U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) =>
          U.toSubmodule) F.range ⟨by rintro _ ⟨t, rfl⟩; exact hf.1 t, hirr,
            isAdmissible_of_injective e.symm.toLinearMap he' e.symm.injective h2⟩ le_rfl
    exact hle ⟨s, rfl⟩
  · have : f s = 0 := DFunLike.congr_fun h0 s
    rw [this]
    exact Submodule.zero_mem _

theorem rank_homInto {σ : Representation ℂ H W} (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) :
    Module.rank ℂ (homInto σ ρ C) =
      Module.rank ℂ (σ.asModule →ₗ[MonoidAlgebra ℂ H] ↥(sSup (pieces ρ C))) := by
  refine LinearEquiv.rank_eq (LinearEquiv.ofBijective
    { toFun := fun f => (modMap f.1 f.2.2).codRestrict _
        (fun s => mem_sSup_pieces_of_mem (apply_mem_irrSum h1 h2 f.2 (σ.asModuleEquiv s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ⟨fun a b hab => ?_, fun g => ?_⟩)
  · ext s
    exact congrArg Subtype.val (LinearMap.congr_fun hab (σ.asModuleEquiv.symm s))
  · refine ⟨⟨ρ.asModuleEquiv.toLinearMap ∘ₗ
      (((sSup (pieces ρ C)).subtype ∘ₗ g).restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap,
      fun s => mem_of_mem_sSup_pieces (g _).2, fun x s => ?_⟩, rfl⟩
    change ρ.asModuleEquiv (g (σ.asModuleEquiv.symm (σ x s))).1 =
      ρ x (ρ.asModuleEquiv (g (σ.asModuleEquiv.symm s)).1)
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

theorem exists_rep {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (U : Submodule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)))
    (hU : IsSimpleModule (MonoidAlgebra ℂ H) U) :
    ∃ V : Subrepresentation ρ, V.toRepresentation.IsIrreducible ∧
      GlobalTheory.PRep.IsAdmissible V.toRepresentation ∧
      Nonempty (U ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule) := by
  let e := Submodule.equivMapOfInjective _ (sSup (pieces ρ C)).injective_subtype U
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) (U.map (sSup (pieces ρ C)).subtype) :=
    IsSimpleModule.congr e.symm
  haveI : ∀ m : pieces ρ C, IsSimpleModule (MonoidAlgebra ℂ H) m :=
    fun m => simple_of_mem_pieces m.2
  obtain ⟨_, ⟨V, hV, rfl⟩, ⟨e'⟩⟩ := (U.map (sSup (pieces ρ C)).subtype).linearEquiv_of_le_sSup
    (pieces ρ C) (Submodule.map_subtype_le _ _)
  exact ⟨V, hV.2.1, hV.2.2, ⟨(e.trans e').trans (subEquiv V).symm⟩⟩

def killedEquiv {ρ : Representation ℂ H X} {C : Submodule ℂ X} (I : Set (MonoidAlgebra ℂ H))
    (hC : IsDecomp ρ C) (ho : ∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) :
    (C ⊓ killed ρ I : Submodule ℂ X) ≃ₗ[ℂ]
      GlobalTheory.SemisimpleCount.killed I ↥(sSup (pieces ρ C)) where
  toFun x := ⟨⟨ρ.asModuleEquiv.symm x.1, mem_sSup_pieces_of_mem (hC _ x.2.1 (ho _ x.2.2))⟩,
    fun r hr => Subtype.ext (mem_killed.1 x.2.2 r hr)⟩
  invFun y := ⟨ρ.asModuleEquiv y.1.1, mem_of_mem_sSup_pieces y.1.2,
    mem_killed.2 fun r hr => congrArg Subtype.val (y.2 r hr)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace H] in
theorem killed_ne_bot {σ : Representation ℂ H W} {I : Set (MonoidAlgebra ℂ H)} {S : Type}
    [AddCommGroup S] [Module (MonoidAlgebra ℂ H) S]
    (e : S ≃ₗ[MonoidAlgebra ℂ H] σ.asModule) {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    killed σ I ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨σ.asModuleEquiv (e s), mem_killed.2 fun r hr => ?_, by simpa using hs⟩
  rw [← Representation.asModuleEquiv_map_smul, ← map_smul, hI r hr, map_zero, map_zero]

theorem finrank_inf_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ X Y _ _ _ _ ρ ρ' C C' I hC hC' hm ho ho' f f'
  have e := killedEquiv I hC ho
  have e' := killedEquiv I hC' ho'
  rw [e.finrank_eq, e'.finrank_eq]
  refine GlobalTheory.SemisimpleCount.finrank_killed_eq (MonoidAlgebra ℂ H) _ _ I _ _
    (semisimple_sSup_pieces ρ C) (semisimple_sSup_pieces ρ' C') (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    e.finiteDimensional e'.finiteDimensional ?_ ?_
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))

end GlobalTheory.RepCount

end
