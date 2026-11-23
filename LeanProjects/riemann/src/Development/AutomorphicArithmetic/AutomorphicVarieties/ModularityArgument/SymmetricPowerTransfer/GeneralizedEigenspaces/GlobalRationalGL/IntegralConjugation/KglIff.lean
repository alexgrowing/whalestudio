import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem kgl_iff {L : Type} [Field L] [NumberField L] (w : Plc L) (x : GL (Fin 2) (w.adicCompletion L)) :
    x ∈ GlobalTheory.LFun.KGL w 2 ↔ (∀ i j, x.val i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, (x⁻¹).val i j ∈ w.adicCompletionIntegers L :=
  ⟨fun h => ⟨fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ h i j,
      fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ (inv_mem h) i j⟩,
    fun h => GlobalTheory.CptCent.mem_GLint_of_entries' _ x h.1 h.2⟩

theorem UpperTheory.V.Z.Sym.Dict.Br.okS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v ∈ KD _ (Ov v) ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) ∈ GlobalTheory.LFun.KGL w 2) ∧ (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : SA B.Δ), cLoc w (B.bS g : UA L 2) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eD S.hs ((g : DA B.Δ).1 (un w))) := by
  intro L _ _ _ B
  have loc : ∀ (g : SA B.Δ) (w : Plc L) i j, (cLoc w (B.bS g : UA L 2)).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w)) i j) := fun g w i j => by
    have := B.bS_loc g w
    exact congrFun (congrFun this i) j
  have locI : ∀ (g : SA B.Δ) (w : Plc L) i j, ((cLoc w (B.bS g : UA L 2))⁻¹).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w))⁻¹ i j) := fun g w i j => by
    have h := loc g⁻¹ w i j
    rw [map_inv] at h
    simpa using h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · rw [mem_KD]
    constructor
    · rintro ⟨h1, h2⟩ w rfl
      refine (kgl_iff w _).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [loc]
        exact (B.ρ_int _ _).1 (h1 i j) w rfl
      · rw [locI]
        exact (B.ρ_int _ _).1 (h2 i j) w rfl
    · intro h
      refine ⟨fun i j => (B.ρ_int _ _).2 fun w hw => ?_, fun i j => (B.ρ_int _ _).2 fun w hw => ?_⟩
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).1 i j
        rwa [loc] at this
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).2 i j
        rwa [locI] at this
  · constructor
    · rintro h w rfl
      apply Units.ext
      refine Matrix.ext fun i j => ?_
      rw [loc, h]
      change B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    · intro h
      have e : Glob.mt ((g : DA B.Δ).1 v) = 1 := by
        ext1 i j
        rw [← sub_eq_zero]
        refine B.ρ_inj v _ fun w hw => ?_
        subst hw
        have h1 := loc g w i j
        rw [h w rfl] at h1
        rw [map_sub, ← h1]
        change (1 : Matrix (Fin 2) (Fin 2) _) i j - B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = 0
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [Matrix.one_apply_ne hij]
      exact Subtype.ext (Units.ext e)
  · apply Units.ext
    refine Matrix.ext fun i j => ?_
    rw [loc]
    exact S.ρ_eq _
