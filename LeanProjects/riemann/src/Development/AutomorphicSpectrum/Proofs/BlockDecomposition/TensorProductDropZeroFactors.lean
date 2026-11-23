import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FineProd.TensorLine

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [Subsingleton.elim g 1, map_one]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have hS : S = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with h | h
    · exfalso
      rw [h] at hvS
      exact hv ((Submodule.mem_bot ℂ).1 hvS)
    · exact h
  have htop : ∀ w : V, w ∈ Submodule.span ℂ {v} := fun w => by
    have : w ∈ S.toSubmodule := by
      rw [hS]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))
    exact this
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v) ⟨?_, ?_⟩).symm⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop w)
    exact ⟨c, by simpa using hc⟩

theorem subsingleton_GL {k : Type} [Field k] {n : ℕ} (h : n = 0) : Subsingleton (GL (Fin n) k) := by
  subst h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

variable {r r' : ℕ}

abbrev Off (o : Fin r' → Fin r) : Type := {j : Fin r // j ∉ Set.range o}

def blockEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) : Fin r' ⊕ Off o ≃ Fin r :=
  Equiv.ofBijective (Sum.elim o Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (ho h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range o
      · obtain ⟨a, rfl⟩ := hj
        exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩)

variable {X : Fin r → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]

open scoped Classical in

def dropEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) :
    (⨂[ℂ] j, X j) ≃ₗ[ℂ] ⨂[ℂ] a, X (o a) :=
  (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm).trans <|
    ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv)).trans
        (TensorProduct.rid ℂ _)

open scoped Classical in

theorem dropEquiv_tprod (o : Fin r' → Fin r) (ho : Function.Injective o)
    (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) (x : ∀ j, X j) :
    dropEquiv o ho φ (PiTensorProduct.tprod ℂ x) =
      (∏ c : Off o, φ c (x c)) • PiTensorProduct.tprod ℂ fun a => x (o a) := by
  have h1 : PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => x (blockEquiv o ho i) :=
    PiTensorProduct.reindex_tprod _ _
  have h2 := PiTensorProduct.tmulEquivDep_symm_apply ℂ (fun i => X (blockEquiv o ho i))
    (fun i => x (blockEquiv o ho i))
  have h3 : (PiTensorProduct.congr fun c : Off o => φ c)
      (PiTensorProduct.tprod ℂ fun c : Off o => x c) = PiTensorProduct.tprod ℂ fun c : Off o => φ c (x c) :=
    PiTensorProduct.congr_tprod _ _
  have ht : ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
      (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c)) =
      (PiTensorProduct.tprod ℂ fun a => x (o a)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun c : Off o => x c) :=
    (congrArg _ h1).trans h2
  show (TensorProduct.rid ℂ _) ((TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv))
      ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
        (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c))) = _
  rw [ht, TensorProduct.congr_tmul, LinearEquiv.trans_apply, h3, TensorProduct.rid_tmul]
  congr 1
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem piTensor_drop_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL k) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  intro k _ _ _ _ r r' y o ho hy
  have hz : ∀ c : Off o, (y c).1 = 0 := fun c => by
    by_contra h
    exact c.2 (hy c h)
  have hφ : ∀ c : Off o, Nonempty ((y c).2.rep.V ≃ₗ[ℂ] ℂ) := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    exact exists_line (y c).2.rep.irr
  let φ : ∀ c : Off o, (y c).2.rep.V ≃ₗ[ℂ] ℂ := fun c => (hφ c).some
  refine ⟨Representation.Equiv.mk (dropEquiv o ho.injective φ) fun g => ?_⟩
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  have hc : ∀ c : Off o, (y c).rep (g c) (x c) = x c := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    rw [Subsingleton.elim (g c) 1, map_one]
    rfl
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, dropEquiv_tprod, hc, map_smul]
  congr 1
  exact (piTensor_tprod (fun a => (y (o a)).rep) (fun a => g (o a)) (fun a => x (o a))).symm

end GlobalTheory.CompanionTheory.FineProd.TensorLine

end
