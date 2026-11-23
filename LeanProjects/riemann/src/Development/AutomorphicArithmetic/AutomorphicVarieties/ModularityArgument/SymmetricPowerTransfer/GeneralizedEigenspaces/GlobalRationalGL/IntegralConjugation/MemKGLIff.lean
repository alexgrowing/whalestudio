import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallOpenCompactNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_KGL_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) {n : ℕ}
    (x : GL (Fin n) (Kw w)) : x ∈ GlobalTheory.LFun.KGL w n ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin n) (Kw w)) : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L := by
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]
  have h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L := fun y => ((intsOv L w).2 y).symm
  simp only [h]

theorem UpperTheory.V.Z.Sym.Dict.Br.okG :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w 3) ∧ (∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ), cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w))) := by
  intro L _ _ _ B
  have hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j) :=
    fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j
  have hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i)) := by
    intro g w i j
    have h := hm g⁻¹ w i j
    rw [map_inv, InvMemClass.coe_inv, map_inv] at h
    exact h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · constructor
    · intro hK w h
      subst h
      rw [mem_KGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [hm]
        exact (B.ρ_int _ _).1 (hK i j).1 w rfl
      · rw [hi]
        exact (B.ρ_int _ _).1 (hK j i).2 w rfl
    · intro H i j
      refine ⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).1 i j
        rwa [hm] at this
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).2 j i
        rwa [hi] at this
  · constructor
    · intro h1 w h
      subst h
      apply Units.ext
      have := B.bG_loc g w
      rw [h1] at this
      refine this.trans ?_
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro H
      apply Subtype.ext
      refine Matrix.ext fun i j => ?_
      apply sub_eq_zero.1
      apply B.ρ_inj
      intro w h
      cases h
      have e2 := hm g w i j
      rw [H w rfl, Units.val_one] at e2
      have e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j :=
        congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j
      rw [map_sub, ← e2]
      exact sub_eq_zero.2 e3.symm
  · apply Units.ext
    refine (B.bG_loc g w).trans ?_
    refine Matrix.ext fun i j => ?_
    exact S.ρ_eq _
