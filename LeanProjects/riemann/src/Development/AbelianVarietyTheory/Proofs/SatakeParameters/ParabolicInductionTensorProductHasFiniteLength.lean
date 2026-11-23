import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ProdFiniteLength

open GlobalTheory.SmGL

theorem piTensor_mulSingle_eq_map {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (a : α)
    (g : Γ a) :
    piTensor ρ (Pi.mulSingle a g) =
      PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) a (ρ a g)) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem exists_mem_adjoin_eq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible)
    (hS : ∀ φ : V →ₗ[ℂ] V, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ (Set.range π), ∀ x ∈ s, T x = f x := by
  classical
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range π)
  have hmem : ∀ g, π g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  haveI : IsSimpleOrder (Subrepresentation π) := hirr
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { exists_pair_ne := ?_, eq_bot_or_eq_top := fun U => ?_ }
    · obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
        by_contra h
        push_neg at h
        apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
        ext v
        simp [h v]
      refine ⟨⊥, ⊤, fun h => hx ?_⟩
      have : x ∈ (⊤ : Submodule A V) := trivial
      rw [← h] at this
      exact (Submodule.mem_bot A).1 this
    · let W : Subrepresentation π :=
        { toSubmodule := U.restrictScalars ℂ
          apply_mem_toSubmodule := fun g v hv => U.smul_mem (⟨π g, hmem g⟩ : A) hv }
      rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
      · left
        ext v
        constructor
        · intro hv
          have : v ∈ W.toSubmodule := hv
          rw [h] at this
          exact (Submodule.mem_bot A).2 this
        · intro hv
          rw [(Submodule.mem_bot A).1 hv]
          exact U.zero_mem
      · right
        refine eq_top_iff.2 fun v _ => ?_
        have : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
        rw [← h] at this
        exact this
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := hS (φ.restrictScalars ℂ) fun g x => φ.map_smul (⟨π g, hmem g⟩ : A) x
    exact ⟨c, fun m => by simpa using LinearMap.congr_fun hc m⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩

theorem piTensor_isIrreducible_of_schur {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hirr : ∀ a, (ρ a).IsIrreducible)
    (hS : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id) :
    (piTensor ρ).IsIrreducible := by
  classical
  cases nonempty_fintype α
  have hnt : ∀ a, Nontrivial (X a) := fun a => by
    haveI : IsSimpleOrder (Subrepresentation (ρ a)) := hirr a
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
    ext v
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩
  haveI : ∀ a, Nontrivial (X a) := hnt
  haveI : Nontrivial (PiTensorProduct ℂ fun a => X a) := GlobalTheory.ProdSupport.nontrivial_piTensor X hnt
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (x : PiTensorProduct ℂ fun a => X a),
      PiTensorProduct.map (fun a => f a ∘ₗ g a) x =
        PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  show IsSimpleOrder (Subrepresentation (piTensor ρ))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : PiTensorProduct ℂ fun a => X a)
    have : x ∈ (⊤ : Subrepresentation (piTensor ρ)).toSubmodule := trivial
    rw [← h] at this
    exact hx this
  by_cases hU : ∀ x ∈ U.toSubmodule, x = 0
  · left
    ext v
    refine ⟨hU v, fun h => ?_⟩
    rw [show v = 0 from h]
    exact U.toSubmodule.zero_mem
  push_neg at hU
  obtain ⟨x, hxU, hx0⟩ := hU
  right
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ x ∈ U.toSubmodule,
        PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T) x ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb x hx => by
        have := ha _ (hb x hx)
        rw [← hcomp] at this
        convert this using 3
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb x hx => by
        rw [PiTensorProduct.map_update_add]
        exact U.toSubmodule.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id]
        exact U.toSubmodule.smul_mem c hx }
  have hA : ∀ a, Algebra.adjoin ℂ (Set.range (ρ a)) ≤ Asub a := fun a =>
    Algebra.adjoin_le (by
      rintro _ ⟨g, rfl⟩ y hy
      rw [← piTensor_mulSingle_eq_map]
      exact U.apply_mem_toSubmodule _ hy)
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ U.toSubmodule, PiTensorProduct.map T y ∈ U.toSubmodule := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ U.toSubmodule,
        PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id) y ∈ U.toSubmodule := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro y hy; simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 3
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  have htop : U.toSubmodule = ⊤ := by
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    let b := fun a => Module.Free.chooseBasis ℂ (X a)
    let B := Basis.piTensorProduct b
    obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (B.repr x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (ρ a) (hirr a) (hS a) (f a)
          ((B.repr x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have e : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, B, f, Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : PiTensorProduct.map T x = PiTensorProduct.map f x := by
      rw [← B.linearCombination_repr x, Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxU
    rw [hmap, e] at h4
    exact (U.toSubmodule.smul_mem_iff hp).1 h4
  ext y
  exact ⟨fun _ => trivial, fun _ => by rw [htop]; trivial⟩

theorem multiProd_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ)
    (σ : ∀ a, Irr k (d a)) (e : (Σ a, Fin (d a)) ≃ Fin n),
    HasFiniteLength (multiProd e fun a => (σ a).π) := by
  intro hBZ k _ _ _ _ s n d σ e
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    piTensor_isIrreducible_of_schur (fun a => (σ a).π) (fun a => (σ a).irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (Fin (d a)) k) (KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr
        (hAdm (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr) φ hφ
  exact hInd (Fin s) (Fin n) (fun a => Fin (d a)) e _ _ (isSmooth_piTensor fun a => (σ a).smooth)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.ProdFiniteLength
