import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LisoSmulMem
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LTheta

noncomputable section

namespace Formalism.MainNotions.BridgeRowsLift

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module Formalism.MainNotions.BridgeLemma

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def rlift_Spl (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V) (P P' : S.V →ₗ[E] S.V) : Prop :=
  LAdj S P P' ∧ (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P ∧ LInt Λ P' ∧ ∀ w y, S.hT (P' w) (P' y) = 0

theorem rlift_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

theorem rlift_spl_of_retr (hcm : Formalism.HermitianLatticesTheory.IsCMUnram E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V)
    (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (P0 : S.V →ₗ[E] S.V) (hid : ∀ x ∈ X, P0 x = x) (hX : ∀ y, P0 y ∈ X) (hint : LInt Λ P0) :
    ∃ P P' : S.V →ₗ[E] S.V, rlift_Spl Λ X P P' ∧ ∀ y, (∀ x ∈ X, S.hT x y = 0) → P0 y = 0 → P y = 0 := by
  obtain ⟨P0', hadj, hint'⟩ := l_adj E S Λ huni P0 hint
  obtain ⟨θ, hθ⟩ := l_theta E hcm
  have hbar : star (θ : E) = ((1 - θ : 𝓞 E) : E) := by
    have : ((1 - θ : 𝓞 E) : E) = 1 - (θ : E) := by simp
    rw [this]
    linear_combination hθ
  have hrev : ∀ x y, S.hT (P0' x) y = S.hT x (P0 y) := by
    intro x y
    rw [← S.herm.eq y (P0' x), ← hadj y x, S.herm.eq]
  have hHX : ∀ y, P0 (P0' y) ∈ X := fun y => hX _
  have hHH : ∀ x y, S.hT (P0 (P0' x)) y = S.hT x (P0 (P0' y)) := by
    intro x y
    rw [hadj, hrev]
  have hzero' : ∀ y, (∀ x ∈ X, S.hT x y = 0) → P0' y = 0 := by
    intro y hy
    refine S.nondeg.2 _ (fun w => ?_)
    rw [← hadj]
    exact hy _ (hX w)
  have hzero : ∀ x ∈ X, P0' x = 0 := fun x hx => hzero' x (fun w hw => hiso w hw x hx)
  refine ⟨P0 - (θ : E) • (P0 ∘ₗ P0'), P0' - star (θ : E) • (P0 ∘ₗ P0'), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    rw [hadj, hHH]
  · intro x hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hzero x hx, map_zero, smul_zero, sub_zero, hid x hx]
  · intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact X.sub_mem (hX y) (X.smul_mem _ (hHX y))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact Λ.sub_mem (hint l hl) (liso_smul_mem Λ θ (hint _ (hint' l hl)))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hbar]
    exact Λ.sub_mem (hint' l hl) (liso_smul_mem Λ (1 - θ) (hint _ (hint' l hl)))
  · intro w y
    have e1 : S.hT (P0' w) (P0' y) = S.hT w (P0 (P0' y)) := hrev _ _
    have e2 : S.hT (P0' w) (P0 (P0' y)) = S.hT w (P0 (P0' y)) := by
      rw [hrev, hid _ (hHX y)]
    have e3 : S.hT (P0 (P0' w)) (P0' y) = S.hT w (P0 (P0' y)) := by
      rw [← hadj, hid _ (hHX w), hHH]
    have e4 : S.hT (P0 (P0' w)) (P0 (P0' y)) = 0 := hiso _ (hHX w) _ (hHX y)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, star_star, RingHom.id_apply]
    rw [e1, e2, e3, e4]
    linear_combination (-(S.hT w (P0 (P0' y)))) * hθ
  · intro y hy h0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [h0, hzero' y hy, map_zero, smul_zero, sub_zero]

theorem rlift_spl_exists (hcm : Formalism.HermitianLatticesTheory.IsCMUnram E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V)
    (hlat : Submodule.IsLattice E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (z m : S.V) (hz : z ∈ Λ) (hzX : ∀ x ∈ X, S.hT x z = 0) (hm : m ∈ Λ) (hmX : ∀ x ∈ X, S.hT x m = 0)
    (hmz : S.hT m z = 1) :
    ∃ P P' : S.V →ₗ[E] S.V, rlift_Spl Λ X P P' ∧ P z = 0 := by
  obtain ⟨product_zeroth_terms, hid, hX, hint⟩ := l_retr E S Λ X hlat
  have hdual : ∀ l ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT m l := by
    intro l hl
    have h1 : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [huni]; exact hl
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at h1
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h1 m hm)
    exact ⟨o, ho⟩
  obtain ⟨P, P', hS, hk⟩ := rlift_spl_of_retr hcm Λ X huni hiso (product_zeroth_terms - (S.hT m).smulRight (product_zeroth_terms z))
    (fun x hx => by
      simp only [LinearMap.sub_apply, LinearMap.smulRight_apply]
      rw [rlift_swap (hmX x hx), zero_smul, sub_zero, hid x hx])
    (fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smulRight_apply]
      exact X.sub_mem (hX y) (X.smul_mem _ (hX z)))
    (fun l hl => by
      simp only [LinearMap.sub_apply, LinearMap.smulRight_apply]
      obtain ⟨o, ho⟩ := hdual l hl
      rw [← ho]
      exact Λ.sub_mem (hint l hl) (liso_smul_mem Λ o (hint z hz)))
  refine ⟨P, P', hS, hk z hzX ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply]
  rw [hmz, one_smul, sub_self]

section Spl

variable {Λ : Submodule (𝓞 E) S.V} {X : Submodule E S.V} {P P' : S.V →ₗ[E] S.V}

theorem rlift_P'_perp (h : rlift_Spl Λ X P P') {y : S.V} (hy : ∀ x ∈ X, S.hT x y = 0) : P' y = 0 := by
  refine S.nondeg.2 _ (fun w => ?_)
  rw [← h.1]
  exact hy _ (h.2.2.1 w)

theorem rlift_PP' (h : rlift_Spl Λ X P P') (y : S.V) : P (P' y) = 0 := by
  refine S.nondeg.1 _ (fun w => ?_)
  rw [h.1]
  exact h.2.2.2.2.2 _ _

def rlift_R (P P' : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V := LinearMap.id - P - P'

theorem rlift_R_apply (y : S.V) : rlift_R P P' y = y - P y - P' y := rfl

theorem rlift_R_perp (h : rlift_Spl Λ X P P') (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (y : S.V) :
    ∀ x ∈ X, S.hT x (rlift_R P P' y) = 0 := by
  intro x hx
  rw [rlift_R_apply, map_sub, map_sub, hiso x hx _ (h.2.2.1 y), ← h.1, h.2.1 x hx]
  ring

theorem rlift_PR (h : rlift_Spl Λ X P P') (y : S.V) : P (rlift_R P P' y) = 0 := by
  rw [rlift_R_apply, map_sub, map_sub, h.2.1 _ (h.2.2.1 y), rlift_PP' h, sub_self, sub_zero]

theorem rlift_R_X (h : rlift_Spl Λ X P P') (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) {x : S.V} (hx : x ∈ X) :
    rlift_R P P' x = 0 := by
  rw [rlift_R_apply, h.2.1 x hx, rlift_P'_perp h (fun w hw => hiso w hw x hx), sub_self, sub_zero]

theorem rlift_R_of_perp (h : rlift_Spl Λ X P P') {y : S.V} (hy : ∀ x ∈ X, S.hT x y = 0) :
    rlift_R P P' y = y - P y := by
  rw [rlift_R_apply, rlift_P'_perp h hy, sub_zero]

theorem rlift_R_int (h : rlift_Spl Λ X P P') {l : S.V} (hl : l ∈ Λ) : rlift_R P P' l ∈ Λ :=
  Λ.sub_mem (Λ.sub_mem hl (h.2.2.2.1 l hl)) (h.2.2.2.2.1 l hl)

theorem rlift_decomp (y : S.V) : y = P y + rlift_R P P' y + P' y := by
  rw [rlift_R_apply]; abel

end Spl

theorem rlift_three {X : Submodule E S.V} (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    {x w y x' w' y' : S.V} (hx : x ∈ X) (hx' : x' ∈ X) (hw : ∀ v ∈ X, S.hT v w = 0) (hw' : ∀ v ∈ X, S.hT v w' = 0)
    (hyy : S.hT y y' = 0) (hwy : S.hT w y' = 0) (hyw : S.hT y w' = 0) :
    S.hT (x + w + y) (x' + w' + y') = S.hT x y' + S.hT w w' + S.hT y x' := by
  simp only [map_add, LinearMap.add_apply]
  rw [hiso x hx x' hx', hw' x hx, rlift_swap (hw x' hx'), hyy, hwy, hyw]
  ring

theorem rlift_main {X : Submodule E S.V} (hiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (hu₁ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ₁) (hu₂ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ₂)
    {P₁ P₁' P₂ P₂' : S.V →ₗ[E] S.V} (h₁ : rlift_Spl Λ₁ X P₁ P₁') (h₂ : rlift_Spl Λ₂ X P₂ P₂')
    {z : S.V} (hzX : ∀ x ∈ X, S.hT x z = 0) (hz₁ : P₁ z = 0) (hz₂ : P₂ z = 0)
    (hA : ∀ x ∈ X, x ∈ Λ₁ ↔ x ∈ Λ₂)
    (hL : ∀ l ∈ Λ₁, (∀ x ∈ X, S.hT x l = 0) → ∃ l₂ ∈ Λ₂, l - l₂ ∈ X) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ x ∈ X, n x = x) ∧ n z = z ∧
      (∀ y, (∀ x ∈ X, S.hT x y = 0) → n y - y ∈ X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  set nL : S.V →ₗ[E] S.V := P₁ + rlift_R P₂ P₂' ∘ₗ rlift_R P₁ P₁' + P₂' ∘ₗ P₁' with hnL
  have hn : ∀ a, nL a = P₁ a + rlift_R P₂ P₂' (rlift_R P₁ P₁' a) + P₂' (P₁' a) := fun a => rfl
  have hmem : ∀ (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → ∀ y,
      y ∈ Λ ↔ ∀ l ∈ Λ, S.hT l y ∈ (1 : Submodule (𝓞 E) E) := by
    intro Λ hu y
    conv_lhs => rw [← hu]
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  have hisom : ∀ a b, S.hT (nL a) (nL b) = S.hT a b := by
    intro a b
    have hwa := rlift_R_perp h₁ hiso a
    have hwb := rlift_R_perp h₁ hiso b
    have e1 : S.hT (nL a) (nL b) = S.hT (P₁ a) (P₂' (P₁' b)) +
        S.hT (rlift_R P₂ P₂' (rlift_R P₁ P₁' a)) (rlift_R P₂ P₂' (rlift_R P₁ P₁' b)) + S.hT (P₂' (P₁' a)) (P₁ b) := by
      rw [hn, hn]
      refine rlift_three hiso (h₁.2.2.1 a) (h₁.2.2.1 b) (rlift_R_perp h₂ hiso _) (rlift_R_perp h₂ hiso _)
        (h₂.2.2.2.2.2 _ _) ?_ ?_
      · rw [← h₂.1, rlift_PR h₂, map_zero, LinearMap.zero_apply]
      · refine rlift_swap ?_
        rw [← h₂.1, rlift_PR h₂, map_zero, LinearMap.zero_apply]
    have e2 : S.hT a b = S.hT (P₁ a) (P₁' b) + S.hT (rlift_R P₁ P₁' a) (rlift_R P₁ P₁' b) + S.hT (P₁' a) (P₁ b) := by
      conv_lhs => rw [rlift_decomp (P := P₁) (P' := P₁') a, rlift_decomp (P := P₁) (P' := P₁') b]
      refine rlift_three hiso (h₁.2.2.1 a) (h₁.2.2.1 b) hwa hwb (h₁.2.2.2.2.2 _ _) ?_ ?_
      · rw [← h₁.1, rlift_PR h₁, map_zero, LinearMap.zero_apply]
      · refine rlift_swap ?_
        rw [← h₁.1, rlift_PR h₁, map_zero, LinearMap.zero_apply]
    have e3 : ∀ x ∈ X, ∀ y, S.hT x (P₂' y) = S.hT x y := by
      intro x hx y
      rw [← h₂.1, h₂.2.1 x hx]
    have e4 : ∀ x ∈ X, ∀ y, S.hT (P₂' y) x = S.hT y x := by
      intro x hx y
      rw [← S.herm.eq x (P₂' y), e3 x hx, S.herm.eq]
    have e5 : S.hT (rlift_R P₂ P₂' (rlift_R P₁ P₁' a)) (rlift_R P₂ P₂' (rlift_R P₁ P₁' b)) =
        S.hT (rlift_R P₁ P₁' a) (rlift_R P₁ P₁' b) := by
      rw [rlift_R_of_perp h₂ hwa, rlift_R_of_perp h₂ hwb]
      simp only [map_sub, LinearMap.sub_apply]
      rw [hwb _ (h₂.2.2.1 _), rlift_swap (hwa _ (h₂.2.2.1 (rlift_R P₁ P₁' b))), hiso _ (h₂.2.2.1 _) _ (h₂.2.2.1 _)]
      ring
    rw [e1, e2, e3 _ (h₁.2.2.1 a), e4 _ (h₁.2.2.1 b), e5]
  have hinj : Function.Injective nL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    refine S.nondeg.1 _ (fun b => ?_)
    rw [← hisom, ha, map_zero, LinearMap.zero_apply]
  set n : S.V ≃ₗ[E] S.V := LinearEquiv.ofInjectiveEndo nL hinj with hndef
  have hnn : ∀ a, n a = nL a := fun a => congrFun (LinearEquiv.coe_ofInjectiveEndo nL hinj) a
  have hX : ∀ x ∈ X, nL x = x := by
    intro x hx
    rw [hn, h₁.2.1 x hx, rlift_R_X h₁ hiso hx, map_zero, rlift_P'_perp h₁ (fun w hw => hiso w hw x hx), map_zero,
      add_zero, add_zero]
  have hperp : ∀ y, (∀ x ∈ X, S.hT x y = 0) → nL y = y - P₂ (rlift_R P₁ P₁' y) := by
    intro y hy
    rw [hn, rlift_P'_perp h₁ hy, map_zero, add_zero, rlift_R_of_perp h₂ (rlift_R_perp h₁ hiso y), rlift_R_of_perp h₁ hy]
    abel
  have hsub : ∀ l ∈ Λ₁, nL l ∈ Λ₂ := by
    intro l hl
    rw [hn]
    refine Λ₂.add_mem (Λ₂.add_mem ?_ ?_) ?_
    · exact (hA _ (h₁.2.2.1 l)).1 (h₁.2.2.2.1 l hl)
    · obtain ⟨l₂, hl₂, hx⟩ := hL _ (rlift_R_int h₁ hl) (rlift_R_perp h₁ hiso l)
      have : rlift_R P₂ P₂' (rlift_R P₁ P₁' l) = rlift_R P₂ P₂' l₂ := by
        rw [← sub_eq_zero, ← map_sub]
        exact rlift_R_X h₂ hiso hx
      rw [this]
      exact rlift_R_int h₂ hl₂
    · rw [hmem Λ₂ hu₂]
      intro l' hl'
      rw [← h₂.1]
      exact (hmem Λ₁ hu₁ _).1 (h₁.2.2.2.2.1 l hl) _ ((hA _ (h₂.2.2.1 l')).2 (h₂.2.2.2.1 l' hl'))
  refine ⟨n, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hnn, hnn]
    exact hisom a b
  · intro x hx
    rw [hnn]
    exact hX x hx
  · rw [hnn, hperp z hzX, rlift_R_of_perp h₁ hzX, hz₁, sub_zero, hz₂, sub_zero]
  · intro y hy
    rw [hnn, hperp y hy, sub_sub_cancel_left]
    exact X.neg_mem (h₂.2.2.1 _)
  · ext y
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      change n l ∈ Λ₂
      rw [hnn]
      exact hsub l hl
    · intro hy
      refine ⟨n.symm y, ?_, by change n (n.symm y) = y; simp⟩
      rw [hmem Λ₁ hu₁]
      intro l hl
      have : S.hT l (n.symm y) = S.hT (nL l) y := by
        rw [← hisom, ← hnn (n.symm y), LinearEquiv.apply_symm_apply]
      rw [this]
      exact (hmem Λ₂ hu₂ y).1 hy _ (hsub l hl)

end Formalism.MainNotions.BridgeRowsLift

end
