import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDualIsogeny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardEqMapMulKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam.Swap

theorem id_pow_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (𝟙 G' ^ n).left ≫ φ = φ ≫ (𝟙 G ^ n).left := by
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  let Φ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ hw
  have key : ∀ m : ℕ, (Φ ^ m).left = (𝟙 G' ^ m).left ≫ φ := by
    intro m
    induction m with
    | zero =>
      let Ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have hΨ : Ψ * Ψ = Ψ * 1 := by
        rw [_root_.mul_one]
        apply Over.OverMorphism.ext
        have := h.2 G' 1 1 Ψ Ψ rfl rfl
        rw [this, _root_.mul_one]
        rfl
      have h1 : Ψ = 1 := mul_left_cancel hΨ
      simp only [pow_zero]
      rw [← h1]
      rfl
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact h.2 G' (𝟙 G' ^ m) (𝟙 G') (Φ ^ m) Φ ih (by simp [Φ])
  have hc : Φ ≫ 𝟙 G ^ n = Φ ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  calc (𝟙 G' ^ n).left ≫ φ = (Φ ^ n).left := (key n).symm
    _ = (Φ ≫ 𝟙 G ^ n).left := by rw [hc]
    _ = φ ≫ (𝟙 G ^ n).left := by simp [Φ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {P P' : Ideal (𝓞 E)} {p i : ℕ}

theorem isAdmissibleSplitHeckePrime_conj (h : admitted l P p) : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := by
  obtain ⟨hmax, hcop, hp, hpP, hl⟩ := h
  refine ⟨?_, ?_, hp, ?_, hl⟩
  · exact Ideal.map_isMaximal_of_equiv H.bar (p := P)
  · rw [GlobalTheory.HeckeDual.map_bar_map_bar, sup_comm]
    exact hcop
  · have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this

theorem isReduced_Hk (Z : Corr Xo P p i) : IsReduced Z.Hk := by
  have : Etale Z.π₁ := Z.et₁
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Z.Hk
    (Z.π₁ ≫ Xo.s) inferInstance).1

theorem isHecke (Z : Corr Xo P p i) : IsHecke Z.o₁ Z.o₂ P p i Z.ψ := ⟨Z.isog, Z.K, Z.ker, Z.hecke⟩

private theorem oAct_act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : OAct (𝓞 E) G) (n : ℕ) :
    A.act (n : 𝓞 E) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h0 := A.5 0 0
    rw [add_zero] at h0
    have h1 : A.act 0 * A.act 0 = A.act 0 * 1 := by rw [_root_.mul_one]; exact h0.symm
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel h1
  | succ n ih => rw [Nat.cast_succ, A.5, ih, A.3, pow_succ]

theorem exists_dual (Z : Corr Xo P p i) (h : admitted l P p) : ∃ χ : Z.o₂.t.G ⟶ Z.o₁.t.G,
    Z.ψ ≫ χ = 𝟙 Z.o₁.t.G ^ p ^ 2 ∧ χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2 ∧
      IsHecke Z.o₂ Z.o₁ (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i χ := by
  have hh := h
  obtain ⟨-, -, hp, -, hl⟩ := hh
  have := isReduced_Hk Z
  have hpb : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := (isAdmissibleSplitHeckePrime_conj h).2.2.2.1
  have hker : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.Hk) (z : Over.mk x ⟶ Z.o₁.t.G),
      z ≫ Z.ψ = 1 → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hK⟩ := Z.hecke k x
    have hzC : z ∈ C := (hC z).2 ((Z.ker k x z).1 hz)
    have hmem : ((p : 𝓞 E) * p) ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hpb
    have h1 : z ≫ Z.o₁.t.act.act ((p : 𝓞 E) * p) = 1 := hK.2.2.1 hzC _ hmem
    rw [← Nat.cast_mul, oAct_act_natCast, MonObj.comp_pow, Category.comp_id, ← sq] at h1
    exact h1
  obtain ⟨χ, h1, h2, h3⟩ :=
    exists_dual_isogeny E H D l p Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.o₂ Z.ψ hp hl Z.isog hker
  exact ⟨χ, h1, h2, GlobalTheory.isHecke_dual E H D l P p i Z.Hk _ Z.o₁ Z.o₂ Z.ψ χ h (isHecke Z) h3 h1⟩

def Exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (a : Z.Hk ⟶ Z'.Hk) : Prop :=
  a ≫ Z'.π₁ ≫ Xo.s = Z.π₁ ≫ Xo.s ∧ ∃ (n₁ : ObjMap Z.o₂ Z'.o₁ a) (n₂ : ObjMap Z.o₁ Z'.o₂ a),
    χ.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ Z'.ψ.left ∧ Z.ψ.left ≫ n₁.toSABMap.φ = n₂.toSABMap.φ ≫ χ'.left

theorem exists_exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (h : χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2) (h' : Z'.ψ ≫ χ' = 𝟙 Z'.o₁.t.G ^ p ^ 2) (hχ : IsHecke Z.o₂ Z.o₁ P' p i χ) :
    ∃ a, Exch Z Z' χ χ' a := by
  have := isReduced_Hk Z
  obtain ⟨a, ⟨ha1, n₁, n₂, hn⟩, -⟩ := Z'.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂ Z.o₁ χ hχ
  refine ⟨a, ha1, n₁, n₂, hn, ?_⟩
  obtain ⟨⟨⟨-, hfin, het, hsurj, -⟩, -⟩, -⟩ := hχ
  have : Epi χ.left := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi χ.left]
  have hp1 : IsGrpPullback Z.o₂.t.G Z'.o₁.t.G a n₁.toSABMap.φ := n₁.toSABMap.2
  calc χ.left ≫ Z.ψ.left ≫ n₁.toSABMap.φ = (χ ≫ Z.ψ).left ≫ n₁.toSABMap.φ := by simp
    _ = (𝟙 Z.o₂.t.G ^ p ^ 2).left ≫ n₁.toSABMap.φ := by rw [h]
    _ = n₁.toSABMap.φ ≫ (𝟙 Z'.o₁.t.G ^ p ^ 2).left := id_pow_left_comp hp1 (p ^ 2)
    _ = n₁.toSABMap.φ ≫ (Z'.ψ ≫ χ').left := by rw [h']
    _ = χ.left ≫ n₂.toSABMap.φ ≫ χ'.left := by rw [Over.comp_left, ← Category.assoc, ← hn, Category.assoc]

theorem Exch.comp_eq_id {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} {b : Z'.Hk ⟶ Z.Hk} (ha : Exch Z Z' χ χ' a)
    (hb : Exch Z' Z χ' χ b) : a ≫ b = 𝟙 _ := by
  obtain ⟨ha1, n₁, n₂, -, hn2⟩ := ha
  obtain ⟨hb1, m₁, m₂, hm1, -⟩ := hb
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Z.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₁ Z.o₂ Z.ψ (isHecke Z)
  obtain ⟨c₁, hc₁⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z'.o₂ Z.o₁).2
    b a m₁).1 n₂
  obtain ⟨c₂, hc₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z'.o₁ Z.o₂).2
    b a m₂).1 n₁
  obtain ⟨i₁, hi₁⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z.o₁ Z.o₁).1
  obtain ⟨i₂, hi₂⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z.o₂ Z.o₂).1
  have e1 := huniq (a ≫ b) ⟨by rw [Category.assoc, hb1, ha1], c₁, c₂, by
    rw [hc₁, hc₂, ← Category.assoc, hn2, Category.assoc, hm1, Category.assoc]⟩
  have e2 := huniq (𝟙 _) ⟨by rw [Category.id_comp], i₁, i₂, by rw [hi₁, hi₂, Category.id_comp, Category.comp_id]⟩
  exact e1.trans e2.symm

theorem Exch.comp_π₁ {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} (ha : Exch Z Z' χ χ' a) : a ≫ Z'.π₁ = Z.π₂ := by
  obtain ⟨ha1, n₁, n₂, -, -⟩ := ha
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Xo.rep Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂
  obtain ⟨c, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z'.o₁ Z.o₂).2
    Z'.π₁ a Z'.m₁).1 n₁
  have e1 := huniq (a ≫ Z'.π₁) ⟨by rw [Category.assoc]; exact ha1, ⟨c⟩⟩
  have e2 := huniq Z.π₂ ⟨Z.base₂, ⟨Z.m₂⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.HkFam.Swap

namespace GlobalTheory.HkFam

open Swap

theorem second_projection_finite_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsFinite Z.π₂ ∧ Etale Z.π₂ ∧ (i ≤ D.p + D.q → Surjective Z.π₂) := by
  intro E _ _ _ H D l Xo P p i Z hpq h
  have h' : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := isAdmissibleSplitHeckePrime_conj h
  obtain ⟨Z'⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i hpq h'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := exists_dual Z h
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := exists_dual Z' h'
  rw [GlobalTheory.HeckeDual.map_bar_map_bar] at hχ'3
  obtain ⟨a, ha⟩ := exists_exch Z Z' χ χ' hχ2 hχ'1 hχ3
  obtain ⟨b, hb⟩ := exists_exch Z' Z χ' χ hχ'2 hχ1 hχ'3
  have : IsIso a := ⟨b, Exch.comp_eq_id ha hb, Exch.comp_eq_id hb ha⟩
  have := Z'.fin₁
  have := Z'.et₁
  rw [← Exch.comp_π₁ ha]
  refine ⟨inferInstance, inferInstance, fun hi => ?_⟩
  have := (GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels E H D l Xo _ p i Z'.toKerScheme h').2 hi
  infer_instance

end GlobalTheory.HkFam

end
