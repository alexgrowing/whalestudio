import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ChB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.EdgeGeo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.PT.ptGal :
    UpperTheory.V.Z.Kato.Sym.PT.PtGal := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF e he η hη s hs w hw f hf
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hm : 0 < l ^ n := pow_pos hl.pos n
  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  obtain ⟨-, -, -, -, -, -, hlift, -⟩ := admB Ω ε X
  obtain ⟨σ, hσ⟩ := hlift (X.gal s)
  obtain ⟨c1, c2, c3, c4, c5⟩ := cjB Ω ε X M e he
  obtain ⟨-, -, -, -, -, -, hcyc⟩ := lgB Ω ε X (l ^ n) hm
  have hfix : FixF X M σ := fun g hg => by
    rw [hσ g, ((mem_mdl_iff X _ _ _).1 hg).2 s hs]
  have hc : cyc (l ^ n) s = 1 := by
    have hζ := isPrimitiveRoot_eOm ε hm.ne'
    have h1 := (hcyc s s).2.2 _ hζ.pow_eq_one
    rw [(mem_fixMu_iff s).1 hs _ ((hζ.pow_eq_one_iff_dvd M).2 hd)] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt (cyc (l ^ n) s)) (ZMod.val_lt (1 : ZMod (l ^ n))) (by
      rw [← h1, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one])
    exact ZMod.val_injective _ h2
  have hL : IsTopLift X M s (cj X M e σ) := fun g =>
    ⟨⟨X.gal s g, gal_mem_topL X hM.ne' hs g.2⟩, rfl, e.injective (by rw [c1 σ hfix, he, he, hσ])⟩
  have h0 := isTopLift_topLift X hM.ne' hs
  have hg := IsTopLift.inv_mul_mem_geo h0 hL
  obtain ⟨hw0, θ, hθ, hk⟩ := hw
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hθ
    exact hw0 ((algebraMap (topL X M) (topBar X M)).injective (by rw [← hθ, map_zero]))
  refine ⟨σ, hσ, e θ, by rw [← map_pow, hθ, he, hf], fun h hh => ?_⟩
  obtain ⟨hhF, hgeo⟩ := c3 h fun g _ => hh g
  have k1 : ka X (l ^ n) (e θ) h = GlobalTheory.NeedB.kum (K := topF X M) (N := l ^ n) (topZeta X M l n) θ (cj X M e h) := by
    unfold ka
    rw [← c1 h hhF]
    exact c5 l n hl.ne_zero h hhF _ _ hθ0 _
      (TopW.apply_eq_kum (isPrimitiveRoot_topZeta X M hl.ne_zero n) hw0 hθ hgeo)
  have hconj : (topLift X M s)⁻¹ * cj X M e h * (topLift X M s)⁻¹⁻¹ ∈ geo (topF X M) (topL X M) (topBar X M) := by
    rw [TopW.mem_geo] at hgeo ⊢
    intro z
    obtain ⟨z', -, hz⟩ := h0 z
    rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hz, hgeo, ← hz, ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]
  have k2 : GlobalTheory.KEdge.edge (topChar X M l n u) (topChar X M l n v) η (cj X M e σ)⁻¹ (cj X M e h) =
      GlobalTheory.KEdge.edge (topChar X M l n u) (topChar X M l n v) η (topLift X M s)⁻¹ (cj X M e h) := by
    have e1 : (cj X M e σ)⁻¹ = ((topLift X M s)⁻¹ * cj X M e σ)⁻¹ * (topLift X M s)⁻¹ := by group
    rw [e1, TopW.edge_mul_conj, (edgeGeo _ _ _ _ _ η hη.1).1 _ (inv_mem hg) _ hconj, zero_add]
  have hi := (c2 σ σ hfix hfix).2
  have e2 : cj X M e (σ⁻¹ * h * σ) = (cj X M e σ)⁻¹ * cj X M e h * cj X M e σ := by
    rw [(c2 _ σ (c2 _ h hi.1 hhF).1 hfix).2.2.1, (c2 _ h hi.1 hhF).2.2.1, hi.2.2]
  have a := (chB Ω ε X l n M hl hM hd u hu.1 huF e he).2
  have b := (chB Ω ε X l n M hl hM hd v hv.1 hvF e he).2
  rw [k1, hk _ hgeo, ← k2, TopW.edge_inv, hc, ← e2, ← a h hhF, ← a σ hfix, ← b h hhF, ← b σ hfix]
  simp only [dif, Pt.mv, topPt, one_pow, one_mul]
  rfl
