import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank

noncomputable section

namespace GlobalTheory.SplitFlag

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

def wPart (τ : E →ₐ[F] Fv F v) (W : Submodule E V.V) : Submodule (Fv F v) (Fin V.rank → Fv F v) where
  carrier := splitVec τ '' (extSub (F := F) V (Fv F v) W : Set (Fin V.rank → Fv F v ⊗[F] E))
  zero_mem' := ⟨0, zero_mem _, funext fun _ => map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, splitVec_add τ y z⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    refine ⟨algebraMap (Fv F v) (Fv F v ⊗[F] E) c • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [splitVec_smul, AlgHom.commutes]
    rfl

theorem splitVec_mem_wPart (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E}
    (hy : y ∈ extSub (F := F) V (Fv F v) W) : splitVec τ y ∈ wPart τ W := ⟨y, hy, rfl⟩

theorem wPart_mono (τ : E →ₐ[F] Fv F v) {A B : Submodule E V.V} (h : A ≤ B) : wPart τ A ≤ wPart τ B := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, GlobalTheory.Cusp.extSub_mono V _ h hy, rfl⟩

section Perp

theorem le_perp_perp (W : Submodule E V.V) : W ≤ perp V (perp V W) := fun y hy =>
  GlobalTheory.Cusp.mem_perp.2 fun x hx => by
    have := GlobalTheory.Cusp.mem_perp.1 hx y hy
    simp only [HSpace.hD] at this ⊢
    rw [← V.herm.eq, this, map_zero]

theorem perp_perp (W : Submodule E V.V) : perp V (perp V W) = W := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_perp_perp W) ?_).symm
  have h1 := GlobalTheory.IsoDim.finrank_perp_add V W
  have h2 := GlobalTheory.IsoDim.finrank_perp_add V (perp V W)
  omega

end Perp

section Split

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (τ : E →ₐ[F] Fv F v)

include h in

theorem mem_extSub_iff_split {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E} :
    y ∈ extSub (F := F) V (Fv F v) W ↔
      splitVec τ y ∈ wPart τ W ∧ splitVec (τ.comp hc.sig) y ∈ wPart (τ.comp hc.sig) W := by
  refine ⟨fun hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, fun ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ => ?_⟩
  rw [← (splitVecEquiv h τ).symm_apply_apply y]
  change splitIncl h τ (splitVec τ y) + splitIncl h (τ.comp hc.sig) (splitVec (τ.comp hc.sig) y) ∈ _
  rw [← e₁, ← e₂, splitIncl_splitVec, splitIncl_splitVec]
  exact add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

include h in
theorem splitIncl_mem_extSub_iff {W : Submodule E V.V} {u : Fin V.rank → Fv F v} :
    splitIncl h τ u ∈ extSub (F := F) V (Fv F v) W ↔ u ∈ wPart τ W := by
  rw [mem_extSub_iff_split hc h τ, splitVec_splitIncl, splitVec_comp_splitIncl]
  exact and_iff_left (zero_mem _)

end Split

section Dual

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram) (τ : E →ₐ[F] Fv F v)

include h hJ in

theorem mem_wPart_comp_iff {W : Submodule E V.V} {u' : Fin V.rank → Fv F v} :
    u' ∈ wPart (τ.comp hc.sig) W ↔ ∀ u ∈ wPart τ (perp V W), u' ⬝ᵥ V.gram.map τ *ᵥ u = 0 := by
  rw [← splitIncl_mem_extSub_iff hc h (τ.comp hc.sig)]
  conv_lhs => rw [← perp_perp W]
  rw [GlobalTheory.Cusp.mem_extSub_perp hc V]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := congrArg (splitProj (τ.comp hc.sig)) (H x hx)
    change splitProj (τ.comp hc.sig) (hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x) = _ at this
    rwa [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero] at this
  · intro H x hx
    change hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x = 0
    refine split_ext h τ ?_ ?_
    · rw [splitProj_hLin, splitVec_splitIncl_comp, map_zero, Matrix.mulVec_zero, dotProduct_zero]
    · rw [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero]
      exact H _ ⟨x, hx, rfl⟩

end Dual

section Chain

def flagChain (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v) (j : Fin (2 * 𝔉.k + 2)) :
    Submodule (Fv F v) (Fin V.rank → Fv F v) :=
  if hj : (j : ℕ) ≤ 𝔉.k then wPart τ (𝔉.X ⟨j, by omega⟩)
  else wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩))

variable (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v)

theorem flagChain_of_le {j : Fin (2 * 𝔉.k + 2)} (hj : (j : ℕ) ≤ 𝔉.k) :
    flagChain 𝔉 τ j = wPart τ (𝔉.X ⟨j, by omega⟩) := dif_pos hj

theorem flagChain_of_lt {j : Fin (2 * 𝔉.k + 2)} (hj : 𝔉.k < (j : ℕ)) :
    flagChain 𝔉 τ j = wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩)) := dif_neg (not_le.2 hj)

theorem flagChain_mono : Monotone (flagChain 𝔉 τ) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  rcases le_or_gt (i : ℕ) 𝔉.k with hi | hi <;> rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_le 𝔉 τ hj]
    exact wPart_mono τ (𝔉.strictMono.monotone (Fin.mk_le_mk.2 hij'))
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (𝔉.le_perp _ _)
  · omega
  · rw [flagChain_of_lt 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (GlobalTheory.Cusp.perp_anti (𝔉.strictMono.monotone (Fin.mk_le_mk.2 (by omega))))

theorem wPart_bot : wPart τ (⊥ : Submodule E V.V) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, GlobalTheory.Cusp.extSub_bot, Submodule.mem_bot] at hy
  rw [hy, Submodule.mem_bot]
  exact funext fun _ => map_zero _

theorem wPart_top {hc : CMData F E} (h : IsCMExt F E hc.sig) : wPart τ (⊤ : Submodule E V.V) = ⊤ :=
  eq_top_iff.2 fun u _ => ⟨splitIncl h τ u, by rw [GlobalTheory.Cusp.extSub_top]; trivial, splitVec_splitIncl h τ u⟩

theorem flagChain_zero : flagChain 𝔉 τ 0 = ⊥ := by
  rw [flagChain_of_le 𝔉 τ (Nat.zero_le _)]
  convert wPart_bot τ
  exact 𝔉.zero

theorem flagChain_last {hc : CMData F E} (h : IsCMExt F E hc.sig) : flagChain 𝔉 τ (Fin.last _) = ⊤ := by
  rw [flagChain_of_lt 𝔉 τ (by simp; omega)]
  convert wPart_top τ h
  have : (⟨2 * 𝔉.k + 1 - (Fin.last (2 * 𝔉.k + 1) : ℕ), by simp⟩ : Fin (𝔉.k + 1)) = 0 := Fin.ext (by simp)
  rw [this, 𝔉.zero, GlobalTheory.Cusp.perp_bot]

end Chain

end GlobalTheory.SplitFlag
