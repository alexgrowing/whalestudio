import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

theorem exists_mulVec_eq_of_maps {K : Type} [Field K] {n : ℕ} (M : GL (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ u ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ S) :
    ∀ u ∈ S, ∃ u₀ ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u₀ = u := by
  intro u hu
  let f : S →ₗ[K] S := (M : Matrix (Fin n) (Fin n) K).mulVecLin.restrict hS
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have e : (M : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = (M : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K) :=
      congrArg Subtype.val hab
    have e2 := congrArg (fun x => ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) e
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using e2
  obtain ⟨a, ha⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨u, hu⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitHom_mulVec_mem_wPart (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V}
    {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v} (hg : g ∈ parab hc V (Fv F v) W) {u : Fin V.rank → Fv F v}
    (hu : u ∈ wPart τ W) :
    ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u
      ∈ wPart τ W := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨act hc V g y, mem_parab_iff_maps.1 hg y hy, splitVec_matHom_mulVec τ g y⟩

theorem flagChain_eq_X (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨i, by omega⟩ = wPart τ (𝔉.X i) := by
  rw [flagChain_of_le 𝔉 τ (show (i : ℕ) ≤ 𝔉.k by omega)]

theorem flagChain_eq_perp (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨2 * 𝔉.k + 1 - i, by omega⟩ = wPart τ (perp V (𝔉.X i)) := by
  rw [flagChain_of_lt 𝔉 τ (show 𝔉.k < 2 * 𝔉.k + 1 - (i : ℕ) by omega)]
  congr 3
  ext
  simp only
  omega

theorem mem_par_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
    · rw [flagChain_of_le 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (Subgroup.mem_iInf.1 hg _) hu
    · rw [flagChain_of_lt 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (parab_le_perp (Subgroup.mem_iInf.1 hg _)) hu
  · intro H
    refine Subgroup.mem_iInf.2 fun i => mem_parab_iff_maps.2 fun y hy => ?_
    have H1 := H ⟨i, by omega⟩
    rw [flagChain_eq_X] at H1
    have H2 := H ⟨2 * 𝔉.k + 1 - i, by omega⟩
    rw [flagChain_eq_perp] at H2
    have key : ∀ τ' : E →ₐ[F] Fv F v, splitVec τ' (act hc V g y) =
        ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ' g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v))
          *ᵥ splitVec τ' y := fun τ' => splitVec_matHom_mulVec τ' g y
    rw [mem_extSub_iff_split hc h τ] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [key]
      exact H1 _ hy1
    · rw [key, mem_wPart_comp_iff hc h hJ τ]
      intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := exists_mulVec_eq_of_maps _ _ H2 u hu
      rw [pairing_splitHom]
      exact (mem_wPart_comp_iff hc h hJ τ).1 hy2 u₀ hu₀

end GlobalTheory.SplitFlag
