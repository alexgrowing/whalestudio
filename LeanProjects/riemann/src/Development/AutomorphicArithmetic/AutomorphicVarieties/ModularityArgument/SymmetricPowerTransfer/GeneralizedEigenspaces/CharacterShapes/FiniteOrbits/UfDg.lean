import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.MemNOfJ

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem uf_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (V : Lev k) (d d' : Fin 2 → kˣ) (hd : Dom d) (hd' : Dom d') : UF (V.J 2) (dg d) (dg d') := by
  intro g
  have h := dCMul k V 2 d d' hd hd' g
  have hm : dg (d * d') = dg d * dg d' := map_mul _ _ _
  simp only [Lev.DC, hm] at h
  exact h

theorem UpperTheory.V.Z.Sym.So.dMul :
    UpperTheory.V.Z.Sym.So.DMul := by
  intro F _ _ Δ A hA g d hg
  classical
  let P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
  have hpv : ∀ (x : DA Δ) v, P.p v x = (x : (v : Pl F) → ↥(DX ((cv v) Δ))) v := fun _ _ => rfl
  have hU : ∀ v ∉ A.Sg, A.dat.J2v v = KD ((cv v) Δ) (Ov v) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv]
  have hJ : ∀ v (hv : v ∈ A.Sg),
      A.dat.J2v v = Subgroup.comap (eD (A.hs v hv)) ((A.V v).J 2) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv, Lev.data]
  have hok := datOk F Δ A hA
  have hout : ∀ (x : DA Δ) (e : ParN F 2), A.IsElD x e → ∀ v ∉ A.Sg, P.p v x ∈ A.dat.J2v v := by
    intro x e hx v hv
    rw [hU v hv, hpv, hx.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (DA Δ) (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
    A.dat.J2v P A.Sg hU g (hout g d hg)
  have key : ∀ v (hv : v ∈ A.Sg),
      UpperTheory.V.AlgebraTools.FinOrb (A.dat.J2v v) (A.dat.J2v v) (P.p v g) ∧
      ∀ (g' : DA Δ) (d' : ParN F 2), A.IsElD g' d' → Dom (d v) → Dom (d' v) →
        UF (A.dat.J2v v) (P.p v g) (P.p v g') := by
    intro v hv
    obtain ⟨hI, h2, hs0, -, -⟩ := hok.2.2.1 v hv
    have hb := (eD_facts (Kv v) (Ov v) hI h2 ((cv v) Δ) (A.s v) (A.hs v hv) hs0).1
    rw [hJ v hv]
    constructor
    · have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g)
      rw [dm.2.1, hpv, hg.1 v hv]
      exact ((finFacts (Kv v) (A.V v)).2.2.2.2.2 2).1 _
    · intro g' d' hg' hd hd'
      have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g')
      rw [dm.2.2.1, hpv, hpv, hg.1 v hv, hg'.1 v hv]
      exact uf_dg (A.V v) (d v) (d' v) hd hd'
  refine ⟨hbox.2.1 (fun v hv => (key v hv).1), fun g' d' hg' hd hd' => ?_⟩
  exact hbox.2.2 g' (hout g' d' hg') (fun v hv => (key v hv).2 g' d' hg' (hd v hv) (hd' v hv))

end
