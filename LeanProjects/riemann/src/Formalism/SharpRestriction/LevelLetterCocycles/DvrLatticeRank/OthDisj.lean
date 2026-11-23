import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FinrankMapMkQ
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrMultVOfNotJump

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34
open scoped TensorProduct

section DiscreteGroups

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem oth_disj [CharZero Qp] [FiniteDimensional Qp K] (τ : K →ₐ[Qp] LL) :
    Disjoint (DdRE PD ρ τ) (⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Qp K
  have hint : IsIntegral Qp α := IsIntegral.of_finite Qp α
  have hadj : Algebra.adjoin Qp {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun τ : K →ₐ[Qp] LL => τ α) := by
    intro τ₁ τ₂ h
    have hle := AlgHom.adjoin_le_equalizer τ₁ τ₂ (s := {α}) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h)
    rw [hadj] at hle
    exact AlgHom.ext fun y => hle (Algebra.mem_top (x := y))
  set f : Module.End LL (V ⊗[Qp] BdR) := mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) α
  have hE : ∀ τ' : K →ₐ[Qp] LL, DdRE PD ρ τ' ≤ f.eigenspace (τ' α) := by
    intro τ' x hx
    rw [Module.End.mem_eigenspace_iff]
    have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hx).2 α
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h
  have hind := Module.End.eigenspaces_iSupIndep f (τ α)
  refine Disjoint.mono (hE τ) ?_ hind
  refine iSup₂_le fun τ' hτ' => ?_
  exact le_trans (hE τ') (le_iSup₂_of_le (τ' α) (fun h => hτ' (hinj h)) le_rfl)

end DiscreteGroups

section Pt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem dR_le (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] :
    DdRE PD T.ρ τ ≤ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
  obtain ⟨hi, hhi⟩ := fr_fildR_hi PD T.ρ τ
  obtain ⟨lo, hlo⟩ := fr_fildR_lo PD T.ρ τ
  have key : ∀ d : ℕ, FildR PD T.ρ τ (hi - d) ≤
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
    intro d
    induction d with
    | zero =>
      rw [Nat.cast_zero, sub_zero, hhi hi le_rfl]
      exact bot_le
    | succ d ih =>
      intro w hw
      have e1 : -(-(hi - ((d + 1 : ℕ) : ℤ))) = hi - ((d + 1 : ℕ) : ℤ) := neg_neg _
      obtain ⟨x, a, -, -, hx⟩ := (hp4.2 c ζ τ hPt).2.2 (-(hi - ((d + 1 : ℕ) : ℤ))) w (by rwa [e1])
      have e2 : -(-(hi - ((d + 1 : ℕ) : ℤ))) + 1 = hi - (d : ℤ) := by push_cast; ring
      rw [e2] at hx
      have hmem1 : a • W.levN T c ζ ((letE c : LetA O n) • x) (-(hi - ((d + 1 : ℕ) : ℤ))) ∈
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' :=
        Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_inf.1 ((hp4.2 c ζ τ hPt).2.1 x (-(hi - ((d + 1 : ℕ) : ℤ))))).1)
      have hF : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (hi - (d : ℤ)) ≤
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
        unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
        exact sup_le ih le_sup_right
      have := Submodule.sub_mem _ hmem1 (hF hx)
      rwa [sub_sub_cancel] at this
  have h := key (hi - lo).toNat
  rwa [hlo _ (by omega)] at h

end Pt

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
