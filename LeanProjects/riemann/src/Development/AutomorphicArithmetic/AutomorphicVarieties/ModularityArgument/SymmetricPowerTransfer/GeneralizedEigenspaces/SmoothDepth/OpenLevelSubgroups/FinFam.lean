import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AutProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CoefAut

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem comp_of_proj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {π σ : Submodule ℂ (UA L n → ℂ)} (hπ : IsAutRepU π)
    (P : GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n) (hP : ∀ φ, (P φ).1 ∈ σ)
    (he : ∀ x φ, P (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P φ))
    (ψ : GlobalTheory.DefU.autU L n) (hψ : ψ.1 ∈ π) (h0 : P ψ ≠ 0) (w : Plc L) (τ : SmIrr (GL (Fin n) (Kw w)))
    (h : Comp π w τ) : Comp σ w τ := by
  have hle : π ≤ GlobalTheory.DefU.autU L n := hπ.aut
  have hK : π ⊓ (LinearMap.ker P).map (GlobalTheory.DefU.autU L n).subtype = ⊥ := by
    refine (hπ.irred _ inf_le_left ?_).resolve_right fun e => h0 ?_
    · rintro x _ ⟨h1, φ, h2, rfl⟩
      refine ⟨hπ.stable x _ h1, GlobalTheory.DefU.autRep L n x φ, ?_, rfl⟩
      have h2' : P φ = 0 := h2
      change P _ = 0
      rw [he, h2', map_zero]
    · obtain ⟨-, φ, h2, h3⟩ := e.ge hψ
      obtain rfl : φ = ψ := Subtype.ext h3
      exact h2
  obtain ⟨h1, f, hf0, hf, h2⟩ := h
  let g := f.codRestrict (GlobalTheory.DefU.autU L n) fun v => hle (hf v)
  refine ⟨h1, (GlobalTheory.DefU.autU L n).subtype ∘ₗ P ∘ₗ g, fun e => hf0 (LinearMap.ext fun v => ?_), fun v => hP _,
    fun x v => ?_⟩
  · have h3 : P (g v) = 0 := Subtype.ext (LinearMap.congr_fun e v)
    exact hK.le ⟨hf v, g v, h3, rfl⟩
  · have h3 : g (τ.ρ (((cLoc w).comp (locU n w).subtype) x) v) = GlobalTheory.DefU.autRep L n x (g v) :=
      Subtype.ext (h2 x v)
    exact congrArg Subtype.val ((congrArg P h3).trans (he x _))

theorem UpperTheory.V.Z.Sym.Al.finFam :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ) ∧
          ∀ π, IsAutRepU π → ∀ φ : UA L n → V, φ ≠ 0 → IsAF R U φ → CoefIn φ π → ∃ σ ∈ A, ∀ w τ, Comp π w τ → Comp σ w τ := by
  intro L _ _ _ n V _ _ _ R hR U hU
  have := afFin L n V R U hU
  let b := Module.finBasis ℂ V
  let T : Fin (Module.finrank ℂ V) → AF R U →ₗ[ℂ] GlobalTheory.DefU.autU L n := fun i =>
    (((b.coord i).compLeft (UA L n)) ∘ₗ (AF R U).subtype).codRestrict _ fun φ =>
      coefAut L n V R hR U hU φ.1 φ.2 (b.coord i)
  obtain ⟨κ, _, σ, P, h1, h2, h3, h4⟩ := autProj L n (⨆ i, LinearMap.range (T i)) inferInstance
  refine ⟨Set.range σ, Set.finite_range σ, ?_, fun π hπ φ h0 hφ hc => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact h1 i
  obtain ⟨i, hi⟩ : ∃ i, T i ⟨φ, hφ⟩ ≠ 0 := by
    by_contra! h
    refine h0 (funext fun g => b.ext_elem fun i => ?_)
    have h5 : b.coord i (φ g) = 0 := congrFun (congrArg Subtype.val (h i)) g
    simpa using h5
  obtain ⟨k, hk⟩ : ∃ k, P k (T i ⟨φ, hφ⟩) ≠ 0 := by
    by_contra! h
    refine hi ?_
    rw [← h4 (T i ⟨φ, hφ⟩) (Submodule.mem_iSup_of_mem i ⟨_, rfl⟩)]
    simp [h]
  exact ⟨σ k, ⟨k, rfl⟩, comp_of_proj hπ (P k) (h2 k) (h3 k) _ (hc (b.coord i)) hk⟩
