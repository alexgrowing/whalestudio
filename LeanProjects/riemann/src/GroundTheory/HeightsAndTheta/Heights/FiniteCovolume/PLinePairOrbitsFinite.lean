import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdaptedReduction

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

universe u

section Sandwich

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem fg_map_of_fg {H : AddSubgroup A} (hH : H.FG) (φ : A →+ B) : (H.map φ).FG := by
  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hH ⊢
  obtain ⟨k, f, rfl⟩ := hH
  exact ⟨k, φ.comp f, by rw [AddMonoidHom.range_comp]⟩

theorem fg_of_le_fg {H K : AddSubgroup A} (hHK : H ≤ K) (hK : K.FG) : H.FG := by
  have hK' : K.toIntSubmodule.FG := (Submodule.fg_iff_addSubgroup_fg _).2 hK
  have := isNoetherian_of_fg_of_noetherian _ hK'
  exact (Submodule.fg_iff_addSubgroup_fg H.toIntSubmodule).1
    (Submodule.FG.of_le_of_isNoetherian (S := H.toIntSubmodule) (T := K.toIntSubmodule) hHK)

variable [NoZeroSMulDivisors ℕ A]

theorem finite_sandwich (M : AddSubgroup A) {n : ℕ} (hn : 0 < n) :
    {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}.Finite := by
  rcases Set.eq_empty_or_nonempty {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}
    with he | ⟨L₀, hML₀, -, hL₀⟩
  · rw [he]
    exact Set.finite_empty
  have hM : M.FG := fg_of_le_fg hML₀ hL₀
  let f : A →+ A := nsmulAddMonoidHom n
  have hf : Function.Injective f := fun x y hxy => by
    have hxy' : n • x = n • y := hxy
    exact smul_right_injective A hn.ne' hxy'

  let N : AddSubgroup A := M.comap f
  have hNM : (N.map f) ≤ M := AddSubgroup.map_comap_le _ _
  have hN : N.FG := by
    have h1 : (N.map f).FG := fg_of_le_fg hNM hM
    have h2 : N.toIntSubmodule.FG := by
      refine Submodule.fg_of_fg_map_injective f.toIntLinearMap hf ?_
      have : (N.toIntSubmodule.map f.toIntLinearMap) = (N.map f).toIntSubmodule := by
        ext x
        simp
      rw [this]
      exact (Submodule.fg_iff_addSubgroup_fg _).2 h1
    exact (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have hMN : M ≤ N := fun x hx => M.nsmul_mem hx n
  let M' : AddSubgroup N := M.addSubgroupOf N
  have : AddGroup.FG N := (AddGroup.fg_iff_addSubgroup_fg N).2 hN
  have : AddGroup.FG (N ⧸ M') :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective M')
  have : Finite (N ⧸ M') := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective M' q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact x.2

  let q : AddSubgroup A → Set (N ⧸ M') := fun L =>
    QuotientAddGroup.mk' M' '' {y : N | (y : A) ∈ L}
  refine Set.Finite.of_finite_image (f := q) (Set.toFinite _) ?_
  rintro L ⟨hML, hLn, -⟩ L' ⟨hML', hL'n, -⟩ hq
  have key : ∀ L L' : AddSubgroup A, M ≤ L' → (∀ x ∈ L, n • x ∈ M) → q L ⊆ q L' → L ≤ L' := by
    intro L L' hML' hLn hsub x hx
    have hxN : x ∈ N := hLn x hx
    obtain ⟨y, hy, hyx⟩ := hsub ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hyx
    have hd : -(y : A) + x ∈ M := by
      have := AddSubgroup.mem_addSubgroupOf.1 hyx
      simpa using this
    have : x = y + (-(y : A) + x) := by abel
    rw [this]
    exact L'.add_mem hy (hML' hd)
  exact le_antisymm (key L L' hML' hLn hq.le) (key L' L hML hL'n hq.ge)

end Sandwich

section Pairs

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]

theorem LinePairOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (h₂ : WittPartner.Statement h)
    (h₃ : ComplementForm.Statement h) (h₄ : ComplementExtension.Statement h)
    (h₅ : AdaptedReduction.Statement h) : LinePairOrbitsFinite.Statement h := by
  intro D
  by_cases hex : ∃ v₀ : W, v₀ ≠ 0 ∧ h.toSesq v₀ v₀ = 0
  swap
  · refine ⟨∅, Set.finite_empty, fun La l _ hl => ?_⟩
    exfalso
    have hne : l ≠ ⊥ := fun hb => by
      have := hl.1
      rw [hb, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact hex ⟨x, hx0, hl.2 x hxl x hxl⟩
  obtain ⟨v₀, hv₀, hv₀₀⟩ := hex
  obtain ⟨w₀, hvw, hww⟩ := h₂ v₀ hv₀ hv₀₀
  have hp : IsHyperbolicPair h v₀ w₀ := ⟨hv₀₀, hww, hvw⟩
  obtain ⟨h', hh'⟩ := h₃ v₀ w₀ hp
  obtain ⟨KK, hKK, n, D', hn, hred⟩ := h₅ v₀ w₀ hp h' hh' D
  have hdim : finrank E (hypComplement h v₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hv : v₀ ∈ hypComplement h v₀ w₀ := htop ▸ Submodule.mem_top
    have h1 : h.toSesq w₀ v₀ = 1 := by
      rw [← h.isSymm.eq v₀ w₀, hvw, map_one]
    exact one_ne_zero (h1 ▸ (mem_hypComplement.1 hv).2)
  obtain ⟨S', hS', hS'L⟩ := h₁ (hypComplement h v₀ w₀) h' hdim D'
  have : NoZeroSMulDivisors ℕ W := ⟨fun {c x} hcx => by
    rw [← Nat.cast_smul_eq_nsmul E] at hcx
    rcases smul_eq_zero.1 hcx with h0 | h0
    · exact Or.inl (Nat.cast_eq_zero.1 h0)
    · exact Or.inr h0⟩
  let Mof : AddSubgroup E × AddSubgroup E → AddSubgroup (hypComplement h v₀ w₀) →
      AddSubgroup W := fun p L =>
    p.1.map ((smulAddHom E W).flip v₀) ⊔ L.map (hypComplement h v₀ w₀).subtype.toAddMonoidHom ⊔
      p.2.map ((smulAddHom E W).flip w₀)
  refine ⟨(⋃ p ∈ KK, ⋃ L ∈ S', {La | Mof p L ≤ La ∧ (∀ x ∈ La, n • x ∈ Mof p L) ∧ La.FG}) ×ˢ
    {Submodule.span E {v₀}},
    (hKK.biUnion fun p _ => hS'.biUnion fun L _ => finite_sandwich _ hn).prod
      (Set.finite_singleton _), ?_⟩
  intro La l hLa hl
  obtain ⟨g, La₁, hgLa, hgv, hK, hsplit, hInt⟩ := hred La l hLa hl
  obtain ⟨L, hL, m, hmL⟩ := hS'L _ hInt
  obtain ⟨gm, hgv₀, hgw₀, hgx⟩ := h₄ v₀ w₀ hp h' hh' m

  have hsmul : ∀ (γ : h.unitaryGroup) (c : E) (x : W), γ • (c • x) = c • (γ • x) := fun γ c x =>
    map_smul (γ : W ≃ₗ[E] W) c x
  have hmem : ∀ x : W, x ∈ gm⁻¹ • La₁ ↔ gm • x ∈ La₁ := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
      simpa using hy
    · intro hx
      have := AddSubgroup.smul_mem_pointwise_smul _ gm⁻¹ La₁ hx
      rw [inv_smul_smul] at this
      exact this
  refine ⟨(gm⁻¹ • La₁, Submodule.span E {v₀}), ⟨?_, rfl⟩, g * gm, ?_, ?_⟩
  · refine Set.mem_iUnion₂.2 ⟨_, hK, Set.mem_iUnion₂.2 ⟨L, hL, ?_, ?_, ?_⟩⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [hmem]
        change gm • (a • v₀) ∈ La₁
        rw [hsmul, hgv₀]
        exact ha
      · rintro _ ⟨y, hy, rfl⟩
        rw [hmem]
        change gm • (y : W) ∈ La₁
        rw [hgx]
        have : m • y ∈ m • L := AddSubgroup.smul_mem_pointwise_smul y m L hy
        rw [hmL] at this
        exact this
      · rintro _ ⟨b, hb, rfl⟩
        rw [hmem]
        change gm • (b • w₀) ∈ La₁
        rw [hsmul, hgw₀]
        exact hb
    · intro x hx
      rw [hmem] at hx
      obtain ⟨a, ha, b, hb, hz⟩ := hsplit _ hx
      set z : W := n • (gm • x) - a • v₀ - b • w₀ with hzdef
      have hzL : z ∈ La₁ :=
        La₁.sub_mem (La₁.sub_mem (La₁.nsmul_mem hx n) ha) hb
      have hz' : (⟨z, hz⟩ : hypComplement h v₀ w₀) ∈ m • L := by
        rw [hmL]
        exact hzL
      obtain ⟨y, hy, hyz⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz'
      have hnx : n • x = a • v₀ + (y : W) + b • w₀ := by
        apply (MulAction.injective gm)
        show gm • (n • x) = gm • (a • v₀ + (y : W) + b • w₀)
        have e1 : gm • (n • x) = n • (gm • x) := map_nsmul (gm : W ≃ₗ[E] W) n x
        have e2 : gm • (y : W) = z := by
          rw [hgx, hyz]
        rw [e1, smul_add, smul_add, hsmul, hsmul, hgv₀, hgw₀, e2, hzdef]
        abel
      rw [hnx]
      refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a, ha, rfl⟩)
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right ⟨y, hy, rfl⟩)
      · exact AddSubgroup.mem_sup_right ⟨b, hb, rfl⟩
    · have hLa₁ : La₁ = g⁻¹ • La := by
        rw [← hgLa, inv_smul_smul]
      have hfg : ∀ (γ : h.unitaryGroup) (S : AddSubgroup W), S.FG → (γ • S).FG := by
        intro γ S hS
        have : γ • S = S.map (((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom) := by
          ext x
          constructor
          · intro hx
            obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
            exact ⟨y, hy, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact AddSubgroup.smul_mem_pointwise_smul y γ S hy
        rw [this]
        exact fg_map_of_fg hS _
      exact hfg _ _ (hLa₁ ▸ hfg _ _ hLa.isLattice.fg)
  · rw [mul_smul, smul_inv_smul, hgLa]
  · have hgv0 : (g : W ≃ₗ[E] W) v₀ ≠ 0 := fun h0 =>
      hv₀ ((g : W ≃ₗ[E] W).map_eq_zero_iff.1 h0)
    have hg' : ((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀ = (g : W ≃ₗ[E] W) v₀ := by
      change (g : W ≃ₗ[E] W) ((gm : W ≃ₗ[E] W) v₀) = _
      exact congrArg _ hgv₀
    change (Submodule.span E {v₀}).map _ = l
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span E {((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀} = l
    rw [hg']
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgv
    · rw [finrank_span_singleton hgv0, hl.1]

end Pairs

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
