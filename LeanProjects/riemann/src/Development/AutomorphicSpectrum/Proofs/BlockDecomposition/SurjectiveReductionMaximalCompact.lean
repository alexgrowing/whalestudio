import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGLStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImageStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RhoSplit

theorem exists_lift {A B C : Type} [Group A] [Group B] [Group C] (φ : A →* C) (ι : B →* C)
    (hι : Function.Injective ι) (h : ∀ a, φ a ∈ ι.range) : ∃ ρ : A →* B, ∀ a, φ a = ι (ρ a) := by
  refine ⟨((MonoidHom.ofInjective hι).symm.toMonoidHom).comp (φ.codRestrict ι.range h), fun a => ?_⟩
  have := (MonoidHom.ofInjective hι).apply_symm_apply (φ.codRestrict ι.range h a)
  exact (congrArg Subtype.val this).symm

theorem inL_injective {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L]
    (h : Function.Injective (algebraMap O L)) {n : ℕ} :
    Function.Injective (inL (O := O) (L := L) (n := n)) := by
  intro a b e
  apply Units.ext
  ext i j
  apply h
  have := congrArg (fun g : GL (Ix n) L => g.1 i j) e
  simpa using this

theorem mem_level_square_congruence_iff {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (ϖ : O) (κ : GL (Ix n) O) :
    κ ∈ Gam2 (n := n) ϖ ↔
      ∀ i j, κ.1 i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ Ideal.span {ϖ ^ 2} := by
  have h1 : (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) =
      (1 : Matrix (Ix n) (Ix n) O).map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  unfold Gam2
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, h1]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact Ideal.Quotient.eq.1 (by simpa using this)
  · intro h
    ext i j
    simpa using Ideal.Quotient.eq.2 (h i j)

theorem isOpen_ideal (D : D7) (v : Pl D) (ϖ : Ov D v) (h : ϖ ≠ 0) :
    IsOpen {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} := by
  have hc : algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) ≠ 0 := by
    intro e
    exact pow_ne_zero 2 h (Subtype.val_injective (by simpa using e))
  set c := algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) with hcdef
  have hO : IsOpen ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) :=
    Valued.isOpen_valuationSubring _
  have hs : {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} =
      (fun x => c⁻¹ * x) ⁻¹' ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have : c⁻¹ * algebraMap (Ov D v) (Lv D v) (z * ϖ ^ 2) = algebraMap (Ov D v) (Lv D v) z := by
        rw [map_mul, ← hcdef]; field_simp
      simp only [Set.mem_preimage, this]
      exact z.2
    · intro hx
      refine ⟨⟨c⁻¹ * x, hx⟩ * ϖ ^ 2, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [map_mul, ← hcdef]
      have : algebraMap (Ov D v) (Lv D v) ⟨c⁻¹ * x, hx⟩ = c⁻¹ * x := rfl
      rw [this]; field_simp
  rw [hs]
  exact hO.preimage (continuous_const.mul continuous_id)

theorem continuous_entry (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Ix n) :
    Continuous fun k : KAt D n v => (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j := by
  have h1 : Continuous fun k : KAt D n v =>
      splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k) :=
    (continuous_splitHom τ).comp ((continuous_proj _ _ v).comp continuous_subtype_val)
  have h2 : Continuous fun k : KAt D n v =>
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k)).1 :=
    Units.continuous_val.comp h1
  exact h2.matrix_elem (finSumFinEquiv i) (finSumFinEquiv j)

theorem exists_rho (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v),
      (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧
      Function.Surjective ρ ∧
      ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  have hinj : Function.Injective (inL (O := Ov D v) (L := Lv D v) (n := n)) :=
    inL_injective Subtype.val_injective
  have hmem : ∀ k : KAt D n v, ((thU D n v τ).comp ((proj D.sp.cm.sig (Jst D n) v).comp (KAt D n v).subtype)) k ∈
      (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
    intro k
    have hk : (k : G D n) ∈ GlobalTheory.LocIntw.KUpAd D.sp.cm.sig (Jst D n) := (Subgroup.mem_inf.1 k.2).1
    exact (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ _).1 ((GlobalTheory.LocIntw.mem_KUpAd.1 hk).1 v)
  obtain ⟨ρ, hρ⟩ := exists_lift _ _ hinj hmem
  have hρ' : ∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k) := hρ
  refine ⟨ρ, hρ', ?_, ?_⟩
  · intro κ
    obtain ⟨g, hg⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL (L := Lv D v) κ)
    have hK := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ g).2 ⟨κ, hg.symm⟩
    have h1 : emb D.sp.cm.sig (Jst D n) v g ∈ KAt D n v :=
      Subgroup.mem_inf.2 ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hK, by rw [← range_emb]; exact ⟨g, rfl⟩⟩
    refine ⟨⟨_, h1⟩, hinj ?_⟩
    rw [← hρ', proj_emb_self, hg]
  · intro ϖ hϖ
    have hU := isOpen_ideal D v ϖ hϖ.ne_zero
    set U := {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} with hUdef
    have hs : ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v))) =
        ⋂ i : Ix n, ⋂ j : Ix n, (fun k : KAt D n v =>
          (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j - (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j) ⁻¹' U := by
      ext k
      have he : ∀ i j, (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j -
          (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
          algebraMap (Ov D v) (Lv D v) ((ρ k).1 i j - (1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
        intro i j
        have h1 : (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
            algebraMap (Ov D v) (Lv D v) ((1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
          by_cases h : i = j
          · subst h
            rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
          · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
        rw [hρ', map_sub, h1]
        rfl
      simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, mem_level_square_congruence_iff, he, hUdef, Set.mem_setOf_eq]
      constructor
      · exact fun h i j => ⟨_, h i j, rfl⟩
      · intro h i j
        obtain ⟨y, hy, e⟩ := h i j
        have hA : Function.Injective (algebraMap (Ov D v) (Lv D v)) := Subtype.val_injective
        have e' := hA e
        rw [← e']
        exact hy
    rw [hs]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_)
    exact (continuous_entry D n v τ i j).sub continuous_const

end GlobalTheory.CompanionTheory.Jp.RhoSplit

end
