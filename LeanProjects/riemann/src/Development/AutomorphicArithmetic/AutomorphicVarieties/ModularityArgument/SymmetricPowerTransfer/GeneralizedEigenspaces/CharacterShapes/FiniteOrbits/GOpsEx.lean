import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.MemNOfJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RLin

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem uf_dg (V : Lev k) (d d' : Fin 3 → kˣ) (hd : Dom d) (hd' : Dom d') :
    UF (V.J 3) (dg d) (dg d') := by
  intro g
  have h := dCMul k V 3 d d' hd hd' g
  have hm : dg (d * d') = dg d * dg d' := map_mul _ _ _
  simp only [Lev.DC, hm] at h
  exact h

private theorem dg_mem (V : Lev k) (d : Fin 3 → kˣ) (hd : ∀ i, d i ∈ V.H) : dg d ∈ V.J 3 := by
  refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
  exact ⟨d, by simpa [Subgroup.mem_pi] using hd, rfl⟩

end Local

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem jv_in (A : SD Δ) {v : Pl F} (h : v ∈ A.Sg) :
    A.dat.Jv v = ((A.V v).J 3).comap (eU (A.hs v h)) := by
  simp [Dat.Jv, SD.dat, h, Lev.data]

private theorem jv_off (A : SD Δ) {v : Pl F} (h : v ∉ A.Sg) : A.dat.Jv v = KU (Ov v) _ := if_neg h

private theorem eU_bij (A : SD Δ) (hA : A.Ok) {v : Pl F} (h : v ∈ A.Sg) :
    Function.Bijective (eU (A.hs v h)) := by
  obtain ⟨h1, h2, h3, -⟩ := (datOk F Δ A hA).2.2.1 v h
  exact (eU_facts (Kv v) (Ov v) h1 h2 (cv v Δ) (A.s v) (A.hs v h) h3).1

private theorem finOrb_G (A : SD Δ) (hA : A.Ok) (g : GA Δ) (d : ParN F 3) (hg : A.IsElG g d) :
    AlgebraTools.FinOrb A.dat.UG A.dat.UG g := by
  classical
  let P := rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
  have hpv : ∀ (x : GA Δ) v, P.p v x = (x : (v : Pl F) → U3 ((cv v) Δ)) v := fun _ _ => rfl
  have hout : ∀ v ∉ A.Sg, P.p v g ∈ A.dat.Jv v := by
    intro v hv
    rw [jv_off A hv, hpv, hg.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (GA Δ) (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
    A.dat.Jv P A.Sg (fun v hv => jv_off A hv) g hout
  refine hbox.2.1 (fun v hv => ?_)
  rw [jv_in A hv]
  have dm := dcMap _ _ ℂ (eU (A.hs v hv)) (eU_bij A hA hv) ((A.V v).J 3) (P.p v g) (P.p v g)
  rw [dm.2.1, hpv, hg.1 v hv]
  exact ((finFacts (Kv v) (A.V v)).2.2.2.2.2 3).1 _

private theorem uf_G (A : SD Δ) (hA : A.Ok) (g g' : GA Δ) (d d' : ParN F 3) (hg : A.IsElG g d)
    (hg' : A.IsElG g' d') (hd : A.DomS d) (hd' : A.DomS d') : UF A.dat.UG g g' := by
  classical
  let P := rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
  have hpv : ∀ (x : GA Δ) v, P.p v x = (x : (v : Pl F) → U3 ((cv v) Δ)) v := fun _ _ => rfl
  have hout : ∀ (x : GA Δ) (e : ParN F 3), A.IsElG x e → ∀ v ∉ A.Sg, P.p v x ∈ A.dat.Jv v := by
    intro x e hx v hv
    rw [jv_off A hv, hpv, hx.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (GA Δ) (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
    A.dat.Jv P A.Sg (fun v hv => jv_off A hv) g (hout g d hg)
  refine hbox.2.2 g' (hout g' d' hg') (fun v hv => ?_)
  rw [jv_in A hv]
  have dm := dcMap _ _ ℂ (eU (A.hs v hv)) (eU_bij A hA hv) ((A.V v).J 3) (P.p v g) (P.p v g')
  rw [dm.2.2.1, hpv, hpv, hg.1 v hv, hg'.1 v hv]
  exact uf_dg (A.V v) (d v) (d' v) (hd v hv) (hd' v hv)

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.gOpsEx :
    UpperTheory.V.Z.Sym.So.GOpsEx := by
  intro F _ _ Δ A hA V _ _ ch B s hB
  classical
  obtain ⟨hG, -, hmul, -, -⟩ := elEx F Δ A hA
  have hF := hecke_operators_on_twisted_base_function F Δ A hA V ch B s hB
  let gd : ParN F 3 → GA Δ := fun d => (hG d).exists.choose
  have hgd : ∀ d, A.IsElG (gd d) d := fun d => (hG d).exists.choose_spec
  have huniq : ∀ d g, A.IsElG g d → g = gd d := fun d g h => (hG d).unique h (hgd d)
  let u : ParN F 3 → Module.End ℂ ↥B.Forms :=
    fun d => (Base.Tw.one B).R fun y => one (y ∈ DC B.U (gd d))
  have hω := hB.ω
  have hU := hB.U
  have hfin : ∀ d, AlgebraTools.FinOrb A.dat.UG A.dat.UG (gd d) := fun d => finOrb_G A hA _ d (hgd d)
  have hop : ∀ d, ∀ φ : ↥B.Forms, ((u d φ : ↥B.Forms) : GA Δ → V) = dcF A.dat.UG (gd d) φ := by
    intro d φ
    have h := (opDc _ _ _ B hω (gd d) (by rw [hU]; exact hfin d)).2 φ
    exact h.trans (by rw [hU])
  have hinv : ∀ φ : ↥B.Forms, ∀ x ∈ A.dat.UG, ∀ g,
      (φ : GA Δ → V) (g * x) = (φ : GA Δ → V) g := by
    intro φ x hx g
    have h := φ.2.2 g ⟨x, by rw [hU]; exact hx⟩
    rw [hω] at h
    simpa using h
  refine ⟨u, s.R (A.F0 1), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d g hd hg φ
    rw [huniq d g hg]
    exact hop d φ
  · intro d d' hd hd'
    have he : gd (d * d') = gd d * gd d' := (huniq _ _ (hmul _ _ _ _ (hgd d) (hgd d'))).symm
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    simp only [Module.End.mul_apply, hop]
    rw [he]
    exact (uFMul _ V A.dat.UG (gd d) (gd d') (hfin d) (hfin d') (by rw [← he]; exact hfin _)
      (uf_G A hA _ _ d d' (hgd d) (hgd d') hd hd') (φ : GA Δ → V) (hinv φ)).symm
  · intro d hd
    have hmem : gd d ∈ A.dat.UG := by
      show gd d ∈ (rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))).box A.dat.Jv
      simp only [RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
      intro v
      by_cases hv : v ∈ A.Sg
      · rw [jv_in A hv, Subgroup.mem_comap]
        show eU (A.hs v hv) ((gd d : (v : Pl F) → U3 ((cv v) Δ)) v) ∈ _
        rw [(hgd d).1 v hv]
        exact dg_mem (A.V v) (d v) (hd v hv)
      · rw [jv_off A hv]
        show ((gd d : (v : Pl F) → U3 ((cv v) Δ)) v) ∈ _
        rw [(hgd d).2 v hv]
        exact one_mem _
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    rw [hop, (dcBasic _ V A.dat.UG (gd d) (hfin d) (φ : GA Δ → V) (hinv φ)).2.2.2.1 hmem]
    rfl
  · intro d hd
    have f1 := ((hF.1 (SD.sg d) (gd (SD.sg d)) (hgd _))).2.1
    have f2 := ((hF.1 d (gd d) (hgd d))).2.2
    exact f2.symm.trans f1
  · intro t ht
    rw [hF.2 t ht]
    have hl := Tf.rLin _ _ _ B s _ A.Ys (fun _ => 1) (fun y => A.F0 (A.dG t y))
      (fun y _ => (hF.1 _ _ (hgd _)).1)
    simp only [one_mul, one_smul] at hl
    rw [hl.2]
    exact Finset.sum_congr rfl fun y _ => (hF.1 _ _ (hgd _)).2.1

end
