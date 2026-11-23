import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.FrameMatch

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem frGL_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL (β * intGL F E n y) z = frGL β (y * z * y⁻¹) := by
  show MulAut.conj (β * intGL F E n y) (intGL F E n z) = MulAut.conj β (intGL F E n (y * z * y⁻¹))
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group

theorem St_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    St (β * intGL F E n y) = St β := by
  ext x
  show x ∈ (frGL (β * intGL F E n y)).range ↔ x ∈ (frGL β).range
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨y * z * y⁻¹, (frGL_mul_intGL β y z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨y⁻¹ * z * y, ?_⟩
    rw [frGL_mul_intGL]
    congr 1
    group

theorem redFn_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n y) PP x =
      (Formalism.UG.bc (resS F PP) y)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) y := by
  by_cases hx : x ∈ St β
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hx
    have h1 : frGL β z = frGL (β * intGL F E n y) (y⁻¹ * z * y) := by
      rw [frGL_mul_intGL]
      congr 1
      group
    conv_lhs => rw [h1]
    rw [redFn_frGL, redFn_frGL]
    rw [map_mul, map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n y) := by rwa [St_mul_intGL]
    simp only [redFn, ext1, dif_neg hx, dif_neg hx', mul_one, inv_mul_cancel]

theorem frGL_mul (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL β y * β = β * intGL F E n y := by
  simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_intGL_of_isFrame {β₁ β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : IsFrame β₁ Λ) (h₂ : IsFrame β₂ Λ) : ∃ m : GL (Fin n) (Formalism.L2.Herm.intAf F E), β₂ = β₁ * intGL F E n m := by
  classical

  have key : ∀ {γ δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}, IsFrame γ Λ → IsFrame δ Λ → ∀ i j,
      ((γ⁻¹ * δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j ∈
        Formalism.L2.Herm.intAf F E := by
    intro γ δ hγ hδ i j
    set v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
      (δ : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (Pi.single j 1) with hv
    have hvL : v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
      rw [hδ v]
      intro k
      rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rcases eq_or_ne k j with hk | hk
      · subst hk
        simp only [Pi.single_eq_same]
        exact Subring.one_mem _
      · simp only [Pi.single_eq_of_ne hk]
        exact Subring.zero_mem _
    have hi := (hγ v).1 hvL i
    rw [hv, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← Units.val_mul] at hi
    simpa [Matrix.transpose_apply] using hi
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₁ h₂ i j⟩
  let N : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₂ h₁ i j⟩
  have hM : M.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₁⁻¹ * β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hN : N.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₂⁻¹ * β₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hinj : Function.Injective
      (fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => A.map (Formalism.L2.Herm.intAf F E).subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hone : (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hMN : M * N = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₁⁻¹ * β₂ * (β₂⁻¹ * β₁) = 1 by group, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₂⁻¹ * β₁ * (β₁⁻¹ * β₂) = 1 by group, Units.val_one])
  refine ⟨⟨M, N, hMN, hNM⟩, ?_⟩
  have hm : intGL F E n ⟨M, N, hMN, hNM⟩ = β₁⁻¹ * β₂ := by
    ext1
    rw [← hM]
    exact Formalism.UG.P.bc_coe _ _
  rw [hm]
  group

end General

set_option maxHeartbeats 1000000 in

theorem frames_match : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  classical
  intro D V Pg hPg β₁ β₂ h₁ h₂
  obtain ⟨m, hm⟩ := exists_intGL_of_isFrame h₁ h₂

  obtain ⟨β₀, ⟨c, h₀⟩, -⟩ := GlobalTheory.StdFrames.exists_frame_std V
  have hB : IsBaseFrame V β₁ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₁, h₀.2⟩

  have hloc : ∀ PP, ∃ κ : GA D V, κ ∈ GfC V ∧ finE V κ ∈ St β₁ ∧
      (PP ∈ Pg → redFn β₁ PP (finE V κ) = Formalism.UG.bc (resS D.host.F PP) m) ∧
      ∀ P', P' ≠ PP → (PP ∈ Pg → ¬ IsConjPl (D := D) PP P') → redFn β₁ P' (finE V κ) = 1 := by
    intro PP
    by_cases hPP : PP ∈ Pg
    · obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (hPg PP hPP PP hPP)
      obtain ⟨κ, -, k1, k2, k3, k4⟩ :=
        GlobalTheory.ParahoricLift.exists_local_lift hB he (Formalism.UG.bc (resS D.host.F PP) m)
      exact ⟨κ, k1, k2, fun _ => k3, fun P' hP' hc => k4 P' hP' (hc hPP)⟩
    · refine ⟨1, Subgroup.one_mem _, ?_, fun h => absurd h hPP, fun P' _ _ => ?_⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · rw [map_one]
        exact blockDiagonalExtendByOnePrimeField_one (St β₁) (redAt β₁ P')
  choose κ hκG hκS hκR hκO using hloc
  have hprod := GlobalTheory.ParahoricLift.redFn_list_prod V β₁ (Pg.toList.map κ) (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκS b)

  have hred : ∀ PP ∈ Pg, redFn β₁ PP (finE V (Pg.toList.map κ).prod) = Formalism.UG.bc (resS D.host.F PP) m := by
    intro PP hPP
    have hs := GlobalTheory.ParahoricLift.prod_map_single (Finset.nodup_toList Pg) (Finset.mem_toList.2 hPP)
      (fun b => redFn β₁ PP (finE V (κ b)))
      (fun b hb => hκO b PP (Ne.symm hb) (fun hbP => hPg b hbP PP hPP))
    rw [hprod.2 PP, List.map_map]
    exact hs.trans (hκR PP hPP)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hprod.1
  refine ⟨(Pg.toList.map κ).prod, (GfC V).list_prod_mem (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκG b), GlobalTheory.StabLatInv.isFrame_mul_of_mem_St β₁ _ _ h₁ hprod.1, ?_⟩
  intro PP hPP x
  have hz' : Formalism.UG.bc (resS D.host.F PP) z = Formalism.UG.bc (resS D.host.F PP) m := by
    rw [← redFn_frGL β₁ PP z, hz]
    exact hred PP hPP
  rw [← hz, frGL_mul, hm, redFn_mul_intGL, redFn_mul_intGL, hz']

end GlobalTheory.FrameMatch

end
