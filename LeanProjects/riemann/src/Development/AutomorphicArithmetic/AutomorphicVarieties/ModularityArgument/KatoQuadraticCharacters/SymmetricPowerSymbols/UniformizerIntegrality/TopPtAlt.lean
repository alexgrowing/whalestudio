import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.EdgeGeo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ChB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.PT.ptGam :
    UpperTheory.V.Z.Kato.Sym.PT.PtGam := by
  intro Ω _ _ _ ε X l n M hl hM hdiv u v hu hv huF hvF e he η hη γ hγ
  obtain ⟨-, hmul, hgeo, -, -⟩ := cjB Ω ε X M e he
  obtain ⟨σ, hσ⟩ := (admB Ω ε X).2.2.2.2.2.2.1 (slR X (ofSL γ))
  have hσL : ∀ f ∈ topL X M, σ (io X f) = io X f := by
    intro f hf
    rw [hσ f]
    congr 1
    exact (mem_lev_iff X _ f).1 hf γ hγ
  obtain ⟨hσF, hσg⟩ := hgeo σ hσL
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨-, -, hlg, -, -, -, hcyc⟩ := lgB Ω ε X (l ^ n) hm
  refine ⟨σ, hσ, 1, by simp, ?_⟩
  intro h hh
  have hhF : FixF X M h := fun f _ => hh f
  obtain ⟨-, hhg⟩ := hgeo h (fun f _ => hh f)
  obtain ⟨-, hσiF, -, hσinv⟩ := hmul σ σ hσF hσF
  obtain ⟨h1F, -, h1eq, -⟩ := hmul σ⁻¹ h hσiF hhF
  obtain ⟨-, -, h2eq, -⟩ := hmul (σ⁻¹ * h) σ h1F hσF
  have hU := chB Ω ε X l n M hl hM hdiv u hu.1 huF e he
  have hV := chB Ω ε X l n M hl hM hdiv v hv.1 hvF e he
  have e0 : ka X (l ^ n) 1 h = 0 := by
    simp only [ka, map_one]
    exact hlg 1 1 0 one_ne_zero (by simp)
  have hE := (edgeGeo (topGal X M) (l ^ n) (geo (topF X M) (topL X M) (topBar X M))
    (topChar X M l n u) (topChar X M l n v) η hη.1).1 (cj X M e σ)⁻¹ (inv_mem hσg) (cj X M e h) hhg
  rw [TopW.edge_inv] at hE
  rw [e0]
  simp only [dif, Pt.mv, topPt, (hcyc 1 1).2.1, one_pow, one_mul]
  have k1 : lg X (l ^ n) (σ (e (topRoot X M (l ^ n) u))) (e (topRoot X M (l ^ n) u))
      = ka X (l ^ n) (e (topRoot X M (l ^ n) u)) σ := rfl
  have k2 : lg X (l ^ n) (σ (e (topRoot X M (l ^ n) v))) (e (topRoot X M (l ^ n) v))
      = ka X (l ^ n) (e (topRoot X M (l ^ n) v)) σ := rfl
  rw [k1, k2, hU.2 h hhF, hU.2 σ hσF, hV.2 h hhF, hV.2 σ hσF, h2eq, h1eq, hσinv]
  linear_combination (-1 : ZMod (l ^ n)) * hE
