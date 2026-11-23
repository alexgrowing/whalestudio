import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VtBaseChange

theorem exists_mulTwist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (N : ℕ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L 1 T)} {s' : LB.Sec (LPow A L 1 T')}
    (hs : IsPullSec A L 1 (h ▷ A) (whiskerRight_snd _ _) s s')
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])} (g₀ : α₀.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])}
    (cα : LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ α₀ (snd T A).left))
    {s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)}
    (tw : IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, (snd T' A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α₀ (snd T' A).left) ∧
      IsTwistPull A L (mulT A T' N) (snd T' A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α' s'
        (GlobalTheory.VVRank.pullS A ((N : ℤ) ^ 2) h s₁) := by
  have e1 : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := GlobalTheory.VVRank.whisker_snd_left A h
  have e2 : (snd T' A).left ≫ (mulA A N).left = (snd T' A ^ N).left := by
    unfold mulA
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hm0 : mulT A T' N ≫ (h ▷ A) = (h ▷ A) ≫ mulT A T N := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [mulT]
    · simp [mulT, MonObj.comp_pow]
  have hm : (mulT A T' N).left ≫ (h ▷ A).left = (h ▷ A).left ≫ (mulT A T N).left := by
    rw [← Over.comp_left, hm0, Over.comp_left]
  obtain ⟨α', gα', vα'⟩ := GlobalTheory.VVRank.exists_gen_pullTo (φ' := ![(snd T' A).left, (snd T' A ^ N).left])
    α₀ g₀ (snd T' A).left (by intro k; fin_cases k; exacts [Category.comp_id _, e2])
  refine ⟨α', ?_, ?_⟩
  · refine corr_of_val hL fun y J hJ => ?_
    rw [vα' _ (𝟙 _) y J hJ, val_pull hJ]
  · obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A 1 h hs
    refine GlobalTheory.VVRank.isTwistPull_of_sv A hL gα' fun y J hJ => ?_
    rw [GlobalTheory.VVRank.sv_pullS A _ h s₁ _ y hJ, GlobalTheory.VVRank.sv_of_isTwistPull A tw _ y hJ,
      GlobalTheory.VVRank.sv_pullS A _ h s _ y hJ, vα' _ (𝟙 _) y J hJ, val_corr hJ cα, val_pull hJ]
    simp only [Category.id_comp, e1, hm]

theorem isVtOver_isUUOver_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ) (I : Ideal (𝓞 E)) (T T' : Over Xo.X) (h : T' ⟶ T) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s' → ∀ (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)) (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' → (∀ t : T ⟶ Xo.univ.t.G, IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s t F → IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s' (h ≫ t) F') ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s' (h ≫ x₁) (h ≫ x₂) F' := by
  intro E _ _ _ H Dw l Xo N I T T' h s s' hs F F' hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨fun t hV => ?_, fun x₁ x₂ hU => ?_⟩
  · unfold IsVtOver at hV ⊢
    obtain ⟨t₀, α₀, α, s₁, U, ht, hok, g₀, hnm, cα, tw, hsym, hact⟩ := hV
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U', -, -, hsym', hact'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U
    refine ⟨h ≫ t₀, α₀, α', _, U', ?_, ?_, g₀, hnm, cα', tw', hsym' _ _ hsym,
      hact' _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) hF⟩
    · rw [← MonObj.comp_pow, ht]
    · unfold KilledBy at hok ⊢
      intro a ha
      rw [Category.assoc, hok a ha, MonObj.comp_one]
  · unfold IsUUOver at hU ⊢
    obtain ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, hnm, cα, tw, hsym₁, hact₁, hsym₂, hact₂⟩ := hU
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U₁', -, -, hsym₁', hact₁'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₁
    obtain ⟨U₂', -, -, hsym₂', hact₂'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₂
    exact ⟨α₀, α', _, _, U₁', U₂', g₀, hnm, cα', tw', hsym₁' _ _ hsym₁,
      hact₁' _ _ _ _ hact₁ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂),
      hsym₂' _ _ hsym₂, hact₂' _ _ _ _ hact₂ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂) hF⟩

end GlobalTheory.VtBaseChange
