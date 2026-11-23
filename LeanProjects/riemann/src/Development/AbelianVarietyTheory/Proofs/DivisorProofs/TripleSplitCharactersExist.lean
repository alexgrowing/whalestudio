import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedSpaceTwoBlockIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLinearModelAtBasePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterBasePlaceLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzMembershipCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactLevelEmbeddingUnitaryStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.ThetaAtGoodLocal

set_option maxHeartbeats 1000000 in

theorem localHalf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsUnram (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ P : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)),
        (∀ ξ, ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁, P φ = ξ) ∧
        (∀ φ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), P φ = 0 →
          φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
            ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ ∧ z = φ₁ - φ₀}) ∧
        ∀ (g : GL (Fin (a + a')) (Fv F B.v₁)) (x : GLoc σ (c • G.W.J.map σ) B.v₁),
          IsCompAt σ (c • G.W.J.map σ) B.τ₁ 1 g x → ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ φ₁ ∈ G.M'.SoLoc B.ψ B.τ₁,
            Acts (evFin F B.v₁) (om' (1, (toGAd hσ G.W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x))) φ₀ φ₁ ∧
            P φ₁ = pairInd (Fv F B.v₁) b hb χ g (P φ₀) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hK.base F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁
  obtain ⟨ν₀, hν₀u, hν₀n, hV⟩ := GlobalTheory.T.unramified_character_base_place_lift hK F E σ B a a' G X om om' hT
  obtain ⟨χW, ε, C, hχu, hχn, hW⟩ := GlobalTheory.T.unramified_linear_model_at_base_place hK F E σ B a a' G X om om' hT
  have hSo := GlobalTheory.T.local_schwartz_membership_criterion hK F E σ B a a' G X om om' hT ι hι
  have hbij : Set.BijOn ι (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _)
      (GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁)) : Set _) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  obtain ⟨Z, hZmem, hZonto, hZker, hZeq⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso (Fv F B.v₁) a' (a + a') ν₀ (by omega)
    (isSmoothChar_of_isUnram hν₀u)
  obtain ⟨b, hb, χ', T, hbχ, hTbij, hTeq⟩ := GlobalTheory.T.induced_space_two_block_intertwiner (Fv F B.v₁) a a' ν₀ χW (isSmoothChar_of_isUnram hχu) ε C
  set S := G.M'.SoLoc B.ψ B.τ₁ with hS
  have hSSB : ∀ φ ∈ S, φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) := fun φ hφ => hφ.1
  set N := Submodule.span ℂ S with hN
  have hNSB : N ≤ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) := Submodule.span_le.2 hSSB
  have hSfull : ∀ φ ∈ S, ι φ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a') :=
    fun φ hφ => ⟨hbij.mapsTo (hSSB φ hφ), (hSo φ (hSSB φ hφ)).1 hφ⟩
  have hNfull : ∀ φ ∈ N, ι φ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a') := by
    have : N ≤ (GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a')).comap ι := Submodule.span_le.2 hSfull
    exact fun φ hφ => this hφ
  let Zr : N →ₗ[ℂ] GlobalTheory.FullRankCoinv.indSp (Fv F B.v₁) a' (a + a') ν₀ :=
    ((Z.comp ι).comp N.subtype).codRestrict _ (fun φ => hZmem _ (hNfull φ.1 φ.2))
  obtain ⟨N', hN'⟩ := Submodule.exists_isCompl N
  let P := T.comp (Zr.comp (Submodule.linearProjOfIsCompl N N' hN'))
  have hP : ∀ φ (hφ : φ ∈ N), P φ = T ⟨Z (ι φ), hZmem _ (hNfull φ hφ)⟩ := by
    intro φ hφ
    have e : Submodule.linearProjOfIsCompl N N' hN' φ = ⟨φ, hφ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hN' ⟨φ, hφ⟩
    simp only [P, LinearMap.comp_apply, e]
    rfl
  have u1 : IsUnram (χW * ν₀⁻¹) := fun x hx => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχu x hx, hν₀u x hx, inv_one, mul_one]
  have u2 : IsUnram ((χW * ν₀⁻¹)⁻¹) := fun x hx => by rw [MonoidHom.inv_apply, u1 x hx, inv_one]
  have u3 : IsUnram (χW⁻¹) := fun x hx => by rw [MonoidHom.inv_apply, hχu x hx, inv_one]
  have n1 : ∀ y, ‖(((χW * ν₀⁻¹) y : ℂˣ) : ℂ)‖ = 1 := fun y => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
      hχn, hν₀n, inv_one, mul_one]
  have n2 : ∀ y, ‖((((χW * ν₀⁻¹)⁻¹) y : ℂˣ) : ℂ)‖ = 1 := fun y => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, n1, inv_one]
  have n3 : ∀ y, ‖(((χW⁻¹) y : ℂˣ) : ℂ)‖ = 1 := fun y => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχn, inv_one]
  have hunr : ∀ j, IsUnram (χ' j) := by
    intro j
    rcases hbχ with ⟨-, -, e0, e1⟩ | ⟨-, -, e0, e1⟩ <;> fin_cases j
    · show IsUnram (χ' 0); rw [e0]; exact hχu
    · show IsUnram (χ' 1); rw [e1]; exact u1
    · show IsUnram (χ' 0); rw [e0]; exact u2
    · show IsUnram (χ' 1); rw [e1]; exact u3
  have hnorm : ∀ j y, ‖((χ' j y : ℂˣ) : ℂ)‖ = 1 := by
    intro j
    rcases hbχ with ⟨-, -, e0, e1⟩ | ⟨-, -, e0, e1⟩ <;> fin_cases j
    · show ∀ y, ‖((χ' 0 y : ℂˣ) : ℂ)‖ = 1; rw [e0]; exact hχn
    · show ∀ y, ‖((χ' 1 y : ℂˣ) : ℂ)‖ = 1; rw [e1]; exact n1
    · show ∀ y, ‖((χ' 0 y : ℂˣ) : ℂ)‖ = 1; rw [e0]; exact n2
    · show ∀ y, ‖((χ' 1 y : ℂˣ) : ℂ)‖ = 1; rw [e1]; exact n3
  refine ⟨b, hb, χ', ?_, hunr, hnorm, P, ?_, ?_, ?_⟩
  · rcases hbχ with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
  ·
    intro ξ
    obtain ⟨f, rfl⟩ := hTbij.2 ξ
    obtain ⟨Ψ, hΨ, hZΨ⟩ := hZonto f.1 f.2
    obtain ⟨φ, hφSB, hιφ⟩ := hbij.surjOn hΨ.1
    have hφS : φ ∈ S := (hSo φ hφSB).2 (by rw [hιφ]; exact hΨ.2)
    refine ⟨φ, hφS, ?_⟩
    rw [hP φ (Submodule.subset_span hφS)]
    congr 1
    exact Subtype.ext (by simp only [hιφ, hZΨ])
  ·
    intro φ hφN hP0
    set Q := Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ φ₀ ∈ S,
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ ∧ z = φ₁ - φ₀} with hQ
    have hQSB : Q ≤ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) := by
      rw [hQ, Submodule.span_le]
      rintro _ ⟨g, -, φ₀, hφ₀, φ₁, hφ₁, -, rfl⟩
      exact Submodule.sub_mem _ hφ₁ (hSSB φ₀ hφ₀)
    have hZ0 : Z (ι φ) = 0 := by
      rw [hP φ hφN] at hP0
      have := hTbij.1 (hP0.trans (map_zero T).symm)
      exact congrArg Subtype.val this
    have hAug := hZker _ (hNfull φ hφN) hZ0
    have hle : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ Q.map ι := by
      rw [GlobalTheory.FullRankCoinv.augRk, Submodule.span_le]
      rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
      obtain ⟨φ₀, hφ₀SB, hιφ₀⟩ := hbij.surjOn hΨ.1
      have hφ₀S : φ₀ ∈ S := (hSo φ₀ hφ₀SB).2 (by rw [hιφ₀]; exact hΨ.2)
      obtain ⟨g, hg, hg'⟩ := hV ι hι g₀
      obtain ⟨φ₁, hφ₁SB, hAct, hιφ₁⟩ := hg' φ₀ hφ₀SB
      refine ⟨φ₁ - φ₀, Submodule.subset_span ⟨g, hg, φ₀, hφ₀S, φ₁, hφ₁SB, hAct, rfl⟩, ?_⟩
      rw [map_sub, hιφ₁, hιφ₀]
    obtain ⟨q, hqQ, hq⟩ := Submodule.mem_map.1 (hle hAug)
    rw [hbij.injOn (hQSB hqQ) (hNSB hφN) hq] at hqQ
    exact hqQ
  ·
    intro g x hx φ₀ hφ₀
    obtain ⟨hUAt, hcomp⟩ := GlobalTheory.T.compact_level_embedding_unitary F E σ hσ (a + a') G.W c hc B.v₁ B.τ₁ g x hx
    let gT : GL (Fin (a + a')) (Fv F B.v₁) := ⟨((g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1)ᵀ, (g.1)ᵀ,
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
    let M : GL (Fin (a + a')) (Fv F B.v₁) := C * (if ε then gT else g) * C⁻¹
    have hM : M.1 = C.1 * (if ε then ((g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1)ᵀ else g.1) *
        (C⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1 := by
      cases ε <;> rfl
    obtain ⟨φ₁, hφ₁SB, hAct, hιφ₁⟩ := hW ι hι _ hUAt g M hcomp hM φ₀ (hSSB φ₀ hφ₀)
    have hdet : IsUnit (M.1).det := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
    have hφ₁S : φ₁ ∈ S := by
      refine (hSo φ₁ hφ₁SB).2 fun Y hY => ?_
      rw [hιφ₁]
      have h0 : ι φ₀ (Y * M.1) = 0 :=
        (hSo φ₀ (hSSB φ₀ hφ₀)).1 hφ₀ _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet])
      simp [h0]
    refine ⟨φ₁, hφ₁S, hAct, ?_⟩
    set s : ℂ := (χW (GlobalTheory.SplitFlip.gdet M) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet M) ((a' : ℂ) / 2) with hs
    have hZ1 : Z (ι φ₁) = fun y => s * Z (ι φ₀) (y * M) := by
      rw [hιφ₁, map_smul, hZeq _ (hSfull φ₀ hφ₀) M]
      rfl
    have hmem : (fun y => s * Z (ι φ₀) (y * M)) ∈ GlobalTheory.FullRankCoinv.indSp (Fv F B.v₁) a' (a + a') ν₀ :=
      hZ1 ▸ hZmem _ (hSfull φ₁ hφ₁S)
    rw [hP φ₁ (Submodule.subset_span hφ₁S), hP φ₀ (Submodule.subset_span hφ₀)]
    rw [← hTeq (Z (ι φ₀)) (hZmem _ (hSfull φ₀ hφ₀)) g M hM hmem]
    congr 1
    exact Subtype.ext hZ1

end GlobalTheory.ThetaAtGoodLocal
