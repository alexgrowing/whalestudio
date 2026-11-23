import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis.AllExt

open GlobalTheory.FramePull GlobalTheory.ConstFam

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

theorem exists_cmp_inv (hF : IsPullback F G.hom G₀.hom π) {T : Over Z} {T₀ : Over S} {u : T.left ⟶ T₀.left}
    {v : T₀.left ⟶ T.left} (huv : u ≫ v = 𝟙 _) (hvu : v ≫ u = 𝟙 _) (hu : u ≫ T₀.hom = T.hom ≫ π)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left ∧
        Ψ ≫ Φ = 𝟙 _ ∧ Φ ≫ Ψ = 𝟙 _ := by
  have w₀ : (snd T₀ G₀).left ≫ G₀.hom = (((fst T₀ G₀).left ≫ v) ≫ T.hom) ≫ π := by
    rw [Category.assoc, Category.assoc, ← hu, reassoc_of% hvu, Over.w, Over.w]
  obtain ⟨Ψ, c₁, c₂⟩ : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left = hF.lift _ _ w₀ :=
    ⟨pullback.lift ((fst T₀ G₀).left ≫ v) (hF.lift _ _ w₀) (hF.lift_snd _ _ w₀).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have c₃ : Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left := by
    rw [reassoc_of% c₂, hF.lift_fst]
  refine ⟨Ψ, c₁, c₃, FramePull.prod_ext ?_ ?_, FramePull.prod_ext ?_ ?_⟩
  · rw [Category.assoc, a₁, reassoc_of% c₁, hvu, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, a₂, c₃, Category.id_comp]
  · rw [Category.assoc, c₁, reassoc_of% a₁, huv, Category.id_comp, Category.comp_id]
  · rw [Category.id_comp]
    apply hF.hom_ext
    · rw [Category.assoc, Category.assoc, c₃, a₂]
    · rw [Category.assoc, Category.assoc, reassoc_of% c₂, hF.lift_snd, reassoc_of% a₁,
        reassoc_of% huv, Over.w, Over.w]

theorem basis_up (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}}
    {χ : V ⟶ Z} {χ₀ : V ⟶ S} (hχ : χ₀ = χ ≫ π) {T : Over Z} {T₀ : Over S} {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀}
    {u : T.left ⟶ T₀.left} (e : h₀.left = h.left ≫ u)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)}
    (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) (H : BasisAlong G L N h b) : BasisAlong G₀ L₀ N h₀ b₀ := by
  have hu : 𝟙 V ≫ (Over.mk χ₀).hom = (Over.mk χ).hom ≫ π := (Category.id_comp _).trans hχ
  obtain ⟨Φ', b₁, b₂⟩ := exists_cmp hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (𝟙 V) hu
  obtain ⟨Ψ, c₁, c₃, i₁, i₂⟩ := exists_cmp_inv hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (u := 𝟙 V) (v := 𝟙 V)
    (Category.id_comp _) (Category.id_comp _) hu b₁ b₂
  have hc := cmp_comm (h := h) (h₀ := h₀) a₁ a₂ b₁ b₂ ((Category.id_comp _).trans e)
  replace b₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left := b₁.trans (Category.comp_id _)
  replace c₁ : Ψ ≫ (fst (Over.mk χ) G).left = (fst (Over.mk χ₀) G₀).left := c₁.trans (Category.comp_id _)
  intro s₀
  obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL b₂ s₀
  refine (existsUnique_congr fun c => ?_).2 (H s)
  rw [FramePull.lin_iff, FramePull.lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ') z J₀ hJ₀
    rw [Category.assoc r Φ' (fst (Over.mk χ₀) G₀).left, b₁] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ Ψ) z hJ₀ hJ _).2 (H W (r ≫ Ψ) z J hJ)
    rw [Category.assoc r Ψ Φ', i₁, Category.comp_id, Category.assoc r Ψ, c₁] at this
    exact this

theorem exists_allBasis : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  intro hL _ Z G₀ _ L₀ hL₀ K _ x A φ w gp hw k hk
  obtain ⟨U, hU, b, hb⟩ := PolFrames.exists_local_basisAlong k hL.secBaseChange A hk (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have huv : (⊤ : (Sp K).Opens).ι ≫ (Sp K).topIso.inv = 𝟙 _ := (Sp K).topIso.hom_inv_id
  have hvu : (Sp K).topIso.inv ≫ (⊤ : (Sp K).Opens).ι = 𝟙 _ := (Sp K).topIso.inv_hom_id
  obtain ⟨Φ, a₁, a₂⟩ := exists_cmp gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    (⊤ : (Sp K).Opens).ι rfl
  obtain ⟨Ψ, -, c₃, -, i₂⟩ := exists_cmp_inv gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    huv hvu rfl a₁ a₂
  choose τ hτ using fun i => exists_thr_up hw hL₀ A.isLB c₃ i₂ (b i)
  refine ⟨_, τ, fun K' _ ga x' h => ?_⟩
  have e : spMap ga = (spMap ga ≫ (Sp K).topIso.inv) ≫ (⊤ : (Sp K).Opens).ι := by
    rw [Category.assoc, hvu, Category.comp_id]
  exact basis_up gp.1 hw hL₀ A.isLB (h.symm.trans (congrArg (· ≫ x) e)) e a₁ a₂ hτ
    (hb K' (spMap ga ≫ (Sp K).topIso.inv))

end GlobalTheory.OneBasis.AllExt
end
