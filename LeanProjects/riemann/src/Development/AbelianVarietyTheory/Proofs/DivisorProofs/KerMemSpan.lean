import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducibleStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.KerSoLoc

theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs
  rcases GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

theorem ker_mem_span : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ χ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), Rf.p' B.v₁ χ = 0 → χ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (GlobalTheory.AdelicU.evFin F B.v₁), ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (GlobalTheory.AdelicU.evFin F B.v₁) (om' (g, 1)) φ φ₁ ∧ z = φ₁ - φ} := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM χ hχ hp
  have hT := hM.triple
  have hv : X.Good B.v₁ := hT.chars.good
  obtain ⟨ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ :=
    GlobalTheory.WeilTransferAt.transfer_at hKP.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁

  set So' : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) :=
    SB _ ⊓ (GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a')).comap ι with hSo'def
  have hSo' : G.M'.SoLoc B.ψ B.τ₁ = (So' : Set _) := by
    ext φ
    constructor
    · intro h
      exact ⟨h.1, hbij.mapsTo h.1, (hso φ h.1).1 h⟩
    · rintro ⟨h1, -, h2⟩
      exact (hso φ h1).2 h2
  rw [hSo', Submodule.span_eq] at hχ
  set Gen := {z | ∃ g ∈ UAt σ G.V' (GlobalTheory.AdelicU.evFin F B.v₁), ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁,
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (GlobalTheory.AdelicU.evFin F B.v₁) (om' (g, 1)) φ φ₁ ∧ z = φ₁ - φ}
    with hGendef
  set Λ : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) := LinearMap.ker (Rf.p' B.v₁) ⊓ SB _ with hΛdef
  have hGenΛ : Submodule.span ℂ Gen ≤ Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    refine ⟨?_, Submodule.sub_mem _ hφ₁ hφ.1⟩
    exact hM.fin.inv' B.v₁ (Submodule.subset_span ⟨g, hgU, φ, hφ.1, φ₁, hφ₁, hA, rfl⟩)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (Submodule.span ℂ Gen).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    have hφS : φ ∈ G.M'.SoLoc B.ψ B.τ₁ := (hso φ hφ).2 hΨ.2
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφS, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := Λ.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hGenΛ))
  have hzero : ∀ h, Acts (GlobalTheory.AdelicU.evFin F B.v₁) (om (1, h)) (0 : (Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) 0 := by
    intro h r _
    have e : tens (GlobalTheory.AdelicU.evFin F B.v₁) (0 : (Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [e, map_zero]
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F B.v₁), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, ⟨hφk, hφS⟩, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ hφS
    have hk1 : Rf.p' B.v₁ φ₁ = 0 := by
      have e := hM.fin.equiv B.v₁ h hhU 0 (Submodule.zero_mem _) φ hφS 0 (Submodule.zero_mem _) φ₁ hφ₁ (hzero h) hA
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hφk).symm)
      rw [← e, map_zero]
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, ⟨Submodule.smul_mem _ _ (LinearMap.mem_ker.2 hk1), Submodule.smul_mem _ _ hφ₁⟩,
      by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hrk := (GlobalTheory.ThK.Inhab.two_le_rank hT).1
  rcases fullRk_irred hKP.base (Fv F B.v₁) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · have h1 : ι χ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ :=
      hE ▸ ⟨⟨χ, ⟨LinearMap.mem_ker.2 hp, hχ.1⟩, rfl⟩, hχ.2⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = χ := hinj w (hGenΛ hw).2 χ hχ.1 hwe
    rwa [← this]
  · exfalso
    have hC := GlobalTheory.T.theta_kernel_coinvariant hKP.base F E σ B a a' G X om om' R Rf hM
    haveI := hM.fin.nontriv B.v₁
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : Rf.Pi B.v₁)
    obtain ⟨φ, hφ, hpφ⟩ := (hC.1 B.v₁ hv).2.2.1 B.τ₁ ξ
    rw [hSo'] at hφ
    have h1 : ι φ ∈ N' := hE ▸ hφ.2
    obtain ⟨⟨φ', ⟨hφ'k, hφ'S⟩, he⟩, -⟩ := h1
    have : φ' = φ := hinj φ' hφ'S φ hφ.1 he
    subst this
    exact hξ (hpφ ▸ LinearMap.mem_ker.1 hφ'k)

end GlobalTheory.KerSoLoc
