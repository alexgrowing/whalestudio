import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.HodgeTateChains.CorrectedHypothesisWConsequences
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem tb1Full : StatTB1Full := by
  intro ℓ _ O _ X _ _ F x B u w s m e d U h
  obtain ⟨a1, a2, a3, a4, a5, hd, L, K, T, i1, i2, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
    b12, b13, b14, b15, b16⟩ := h
  have h' := B.map_f _ (tbFull ℓ u w s m e d a1 a2 a3 a4 a5 U B.D L K T i1 i2 hd b1 b2 b3 b4 b5 b6
    b7 b8 b9 b10 b11 b12 b13 b14 b15 b16)
  rw [transport O, B.map_y] at h'
  exact h'

theorem tb2 : StatTB2 := by
  intro O _ _ _ X _ _ Hc F deg hQ ℓ c
  obtain ⟨Cy, _, _, ι, π, hι, hex, hcy⟩ := hQ
  set B : Submodule O X := Hc ⊓ divBy F ((ℓ : O) ^ c) with hB
  let N : Submodule O (Hc ⧸ F.comap Hc.subtype) :=
    LinearMap.ker (LinearMap.lsmul O (Hc ⧸ F.comap Hc.subtype) ((ℓ : O) ^ c))
  let f : B →ₗ[O] (Hc ⧸ F.comap Hc.subtype) :=
    (F.comap Hc.subtype).mkQ ∘ₗ Submodule.inclusion (inf_le_left : B ≤ Hc)
  have hf0 : ∀ x : B, f x = 0 ↔ (x : X) ∈ F := by
    intro x
    simp only [f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
  have hN : ∀ x, f x ∈ N := by
    intro x
    have hx : ((ℓ : O) ^ c) • (x : X) ∈ F := x.2.2
    show ((ℓ : O) ^ c) • f x = 0
    rw [← map_smul, hf0]
    exact hx
  let g : (B ⧸ F.comap B.subtype) →ₗ[O] N :=
    (F.comap B.subtype).liftQ (f.codRestrict N hN) (by
      intro x hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      exact (hf0 x).2 hx)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    rw [LinearMap.mem_ker] at hx
    exact (hf0 x).1 (congrArg Subtype.val hx)
  have h1 := Module.length_le_of_injective g hg
  have h2 := tbLen O (Fin deg) _ Cy ι π hι hex hcy N ℓ c (fun x hx => hx)
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [Fintype.card_fin]
  ring

theorem cBle : StatCB := by
  intro ℓ t e what₂ s m gK U he w hw
  have h1 : cTB ℓ (s w) (m w) e (gK w) (U w) ≤ cB ℓ (s w) (m w) t (gK w) (U w) :=
    Finset.le_sup (f := fun e => cTB ℓ (s w) (m w) e (gK w) (U w)) (Finset.mem_range.2 he)
  exact h1.trans (Finset.le_sup (f := fun w => cB ℓ (s w) (m w) t (gK w) (U w)) hw)

theorem rowsJ : StatRows := by
  intro ℓ _ O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ E D what₂ deg Hc F t e u wm s m d U he h w hw
  obtain ⟨h1, h2, h3⟩ := h w hw
  refine ⟨h1, cBle ℓ t e what₂ s m (fun w => padicValNat ℓ (d w)) U he w hw, ?_, tb2 O _ (Hc w) (F w) (deg w) h3 ℓ _⟩
  intro ψ hψ z hz
  obtain ⟨B, hB⟩ := h2 ψ hψ z hz
  exact tb1Full ℓ O _ (F w) _ B (u w) (wm w) (s w) (m w) e (d w) (U w) hB

end Formalism.RepresentationBoundsCohomology.JT
