import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeFrob

theorem rt_mul_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (a b : GAf L n) (f : GAf L n → W) :
    NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
  funext g; simp [NG.rt, mul_assoc]

theorem exists_ne_zero_of_irrRep {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.SmGL.IrrRep G) :
    ∃ a : σ.V, a ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h := σ.irr
  haveI : Subsingleton σ.V := ⟨fun a b => by rw [hne a, hne b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem mem_iSup_range_locMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  intro L _ _ _ n π s σ i T hTi hTS hT g hg
  set I : Submodule ℂ (GAf L n → π.W) :=
    ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 with hIdef
  have hIS : I ≤ π.S := iSup_le fun T' => by
    rintro _ ⟨a, rfl⟩
    exact T'.2.1 a
  have hsub : NG.IsSubrep π.ρ I := by
    refine ⟨hIS.trans π.irrS.1.le, ?_⟩
    intro h f hf
    obtain ⟨x, y, hx, hy, rfl⟩ := (GlobalTheory.SplitAdelic.main L n s).1 h
    have hcomm := (GlobalTheory.SplitAdelic.main L n s).2.1
    refine Submodule.iSup_induction (motive := fun f => NG.rt L n (x * y) f ∈ I) _ hf ?_ ?_ ?_
    · rintro T' _ ⟨a, rfl⟩
      let T'' : σ.V →ₗ[ℂ] (GAf L n → π.W) := (NG.rt L n y).comp T'.1
      have hT'' : (∀ a, T'' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'' := by
        refine ⟨fun a => π.irrS.1.stable y _ (T'.2.1 a), fun z hz a => ?_⟩
        change NG.rt L n y (T'.1 _) = NG.rt L n z (NG.rt L n y (T'.1 a))
        rw [T'.2.2 z hz a, ← rt_mul_apply, ← rt_mul_apply, (hcomm z y hz hy).eq]
      have key : NG.rt L n (x * y) (T'.1 a) =
          T'' (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) := by
        rw [hT''.2 x hx a, rt_mul_apply]
        rfl
      rw [key]
      exact Submodule.mem_iSup_of_mem ⟨T'', hT''⟩ ⟨_, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [map_add]; exact add_mem h₁ h₂
  rcases π.irrS.2.2 I hsub hIS with hbot | htop
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne_zero_of_irrRep σ
    have hmem : T a ∈ I := Submodule.mem_iSup_of_mem ⟨T, hTS, hT⟩ ⟨a, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ha (hTi (hmem.trans (map_zero T).symm))
  · rw [htop]; exact hg

end GlobalTheory.HeckeFrob
