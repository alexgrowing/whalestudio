import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AutProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CoefAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompOfEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.UnrSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AwayCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OutRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Refine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.RegUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.EigTS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ContE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SmoothDepth

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

theorem UpperTheory.V.Z.Sym.U.finFamU :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
          ∀ π, IsAutRepU π → ∀ φ : UA L n → V, φ ≠ 0 → IsAF R U φ → CoefIn φ π → ∃ σ ∈ A, ∀ w τ, Comp π w τ → Comp σ w τ := by
  intro L _ _ _ n V _ _ _ R hR U hU
  have := afFin L n V R U hU
  let b := Module.finBasis ℂ V
  let T : Fin (Module.finrank ℂ V) → AF R U →ₗ[ℂ] GlobalTheory.DefU.autU L n := fun i =>
    (((b.coord i).compLeft (UA L n)) ∘ₗ (AF R U).subtype).codRestrict _ fun φ =>
      coefAut L n V R hR U hU φ.1 φ.2 (b.coord i)
  obtain ⟨κ, _, σ, P, h1, h2, h3, h4⟩ := autProj L n (⨆ i, LinearMap.range (T i)) inferInstance
  refine ⟨{s ∈ Set.range σ | ∃ φ ∈ s, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ}, (Set.finite_range σ).subset fun _ h => h.1, ?_,
    fun π hπ φ h0 hφ hc => ?_⟩
  · rintro _ ⟨⟨i, rfl⟩, h⟩
    exact ⟨h1 i, h⟩
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
  refine ⟨σ k, ⟨⟨k, rfl⟩, (P k (T i ⟨φ, hφ⟩)).1, h2 k _, fun e => hk (Subtype.ext e), fun u hu => ?_⟩,
    comp_of_proj hπ (P k) (h2 k) (h3 k) _ (hc (b.coord i)) hk⟩
  have e : GlobalTheory.DefU.autRep L n u (T i ⟨φ, hφ⟩) = T i ⟨φ, hφ⟩ :=
    Subtype.ext (funext fun g => congrArg (b.coord i) (hφ.level u hu g))
  have := h3 k u (T i ⟨φ, hφ⟩)
  rw [e] at this
  exact congrArg Subtype.val this.symm

private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _

def UpperTheory.V.Z.Sym.U.AdLiftU : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ (S₀ : Finset (Plc L)) (P : Set (Plc L)),
    Disjoint (S₀ : Set (Plc L)) P → Places ((S₀ : Set (Plc L)) ∪ P) → HasTwo S₀ →
    ∀ π : Submodule ℂ (UA L 2 → ℂ), IsAutRepU π → ∀ j : ℕ, 1 ≤ j →
    (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
    (∀ w : Plc L, (∀ w' ∈ S₀, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
    ∀ ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ w ∈ (S₀ : Set (Plc L)) ∪ P, CompEq π w (ψ w)) →
    (∀ w ∈ P, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ Reg (ψ w 0 / ψ w 1)) →
    (∃ σ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ ∧
      (∀ w : Plc L, (∀ w' ∈ S₀, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU σ w) ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) ∨
    ∃ σ : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2

private theorem unram_of {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) (h : ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ lev (Kall L n) S V, RU L n u φ = φ) (w : Plc L)
    (hw : ∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : IsUnramU σ w := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨φ, h1, h2, fun x hx hK => h3 x ?_⟩
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨((factor L n w).2.2.2.2.1 x hx).2 hK, fun w' hw' => ?_⟩
  have := (factor L n w').2.2.1 w (hw w' hw').symm hx
  simp only [away, Subgroup.mem_iInf] at this
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
  exact one_mem _

private theorem pigeon {X I : Type} (A : Set X) (hA : A.Finite) (P : X → I → Prop)
    (h : ∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) : ∃ x ∈ A, ∀ i, P x i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf using fun x : A => hn x.1 x.2
  haveI := hA.fintype
  obtain ⟨x, hx, h1⟩ := h (Finset.univ.image f)
  exact hf ⟨x, hx⟩ (h1 _ (Finset.mem_image_of_mem f (Finset.mem_univ _)))
