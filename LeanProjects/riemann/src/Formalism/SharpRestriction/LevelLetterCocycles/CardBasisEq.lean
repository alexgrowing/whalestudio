import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem finrank_lat [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    finrank O ↥T.L.T = finrank LL T.V := by
  have := T.L.free
  have hfg : Module.Finite O ↥T.L.T := ⟨(Submodule.fg_top _).mpr T.L.fg⟩
  let e := Module.Free.chooseBasis O ↥T.L.T
  let w : Module.Free.ChooseBasisIndex O ↥T.L.T → T.V := fun j => (e j : T.V)
  have hli : LinearIndependent O w := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli' : LinearIndependent LL w := (LinearIndependent.iff_fractionRing O LL).mp hli
  have hspO : Submodule.span O (Set.range w) = T.L.T := by
    have : Set.range w = T.L.T.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    rw [← T.L.span, Submodule.span_le]
    intro x hx
    rw [← hspO] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' hsp), Module.finrank_eq_card_chooseBasisIndex]

theorem card_basis_eq [Nontrivial O] [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) {r : ℕ} (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    r = finrank O ↥T.L.T := by
  classical
  let w : Fin r → ↥(W.N T) := fun j => ⟨b j, hb j⟩
  have hli : LinearIndependent (LetA O n) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : (0 : W.DD T) = ∑ j, g j • b j := by
      have := congrArg Subtype.val hg
      simpa [w, Submodule.coe_sum] using this.symm
    have h1 : (0 : W.DD T) = ∑ j, (0 : Fin r → LetA O n) j • b j := by simp
    obtain ⟨a, _, ha⟩ := huniq 0 (W.N T).zero_mem
    have e1 := ha g h0
    have e2 := ha 0 h1
    intro j
    rw [e1, ← e2]; rfl
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • w j := by
      apply Subtype.ext
      simp [w, Submodule.coe_sum, ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := (W.N_base T hT).basis bN
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  have h1 := Module.finrank_eq_card_basis bD
  rw [(W.DD_free T).2, Fintype.card_fin] at h1
  exact h1.symm

end

end Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN
