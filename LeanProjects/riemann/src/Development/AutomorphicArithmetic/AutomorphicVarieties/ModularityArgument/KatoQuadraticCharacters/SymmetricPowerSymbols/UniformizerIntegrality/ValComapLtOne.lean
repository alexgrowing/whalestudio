import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ChB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.UnifLc

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

private theorem val_lt_one_iff {K : Type} [Field K] (B : ValuationSubring K) (x : K) :
    B.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < B.valuation x := by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).2 hx
    rw [← one_lt_inv₀ h0, ← map_inv₀, ← not_le, B.valuation_le_one_iff]
    simp [hx]

private theorem val_comap_lt_one {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (e : K →+* L) (x : K)
    (h : B.valuation (e x) < 1) : (B.comap e).valuation x < 1 := by
  rw [val_lt_one_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl ((map_eq_zero e).1 h)
  · right
    rw [ValuationSubring.mem_comap, map_inv₀]
    exact h

theorem UpperTheory.V.Z.Kato.Sym.PT.ptIs :
    UpperTheory.V.Z.Kato.Sym.PT.PtIs := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF e he η hη
  obtain ⟨hau, hku⟩ := chB Ω ε X l n M hl hM hd u hu.1 huF e he
  obtain ⟨hav, hkv⟩ := chB Ω ε X l n M hl hM hd v hv.1 hvF e he
  obtain ⟨c1, c2, c3, -, -⟩ := cjB Ω ε X M e he
  obtain ⟨hcob, hlc, hun⟩ := hη
  have hD : ∀ g, InD X g → FixF X M g ∧ cj X M e g ∈ geo (topF X M) (topL X M) (topBar X M) :=
    fun g hg => c3 g fun f _ => hg f
  refine ⟨hu, hv, hau, hav, fun g h hg hh => ?_, ?_, ?_⟩
  · show ka X (l ^ n) (e (topRoot X M (l ^ n) u)) g * ka X (l ^ n) (e (topRoot X M (l ^ n) v)) h =
      η (cj X M e h) - η (cj X M e (g * h)) + η (cj X M e g)
    rw [hku g (hD g hg).1, hkv h (hD h hh).1, (c2 g h (hD g hg).1 (hD h hh).1).2.2.1]
    exact hcob _ (hD g hg).2 _ (hD h hh).2
  · classical
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
    haveI : IsGalois (topL X M) (topBar X M) := inferInstance
    obtain ⟨B, hB⟩ := lcGeo (topF X M) (topL X M) (topBar X M) _ η hlc
    refine ⟨B.image e, fun h h' hh hh' hb => ?_⟩
    refine hB _ (hD h hh).2 _ (hD h' hh').2 fun b hbB => e.injective ?_
    rw [c1 h (hD h hh).1, c1 h' (hD h' hh').1]
    exact hb _ (Finset.mem_image_of_mem _ hbB)
  · intro B h hB hh hin
    refine hun (B.comap (e : topBar X M →+* Kb X)) _ (fun f hf => ?_) (fun z hz => ?_) (hD h hh).2
    · rw [ValuationSubring.mem_comap]
      show e _ ∈ B
      rw [he f]
      rcases hf with hf | ⟨c, hc⟩
      · rw [hf]; exact hB.2
      · rw [← hc]; exact hB.1 c
    · apply val_comap_lt_one
      rw [ValuationSubring.valuation_le_one_iff] at hz
      show B.valuation (e _) < 1
      rw [map_sub, c1 h (hD h hh).1]
      exact hin _ ((ValuationSubring.valuation_le_one_iff _ _).2 hz)
