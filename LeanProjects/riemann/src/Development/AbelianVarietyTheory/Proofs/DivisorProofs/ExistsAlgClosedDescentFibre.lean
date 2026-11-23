import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePointPolarizedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBoundSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdDim.SiegSpec

theorem trLe_of_isAlgebraic {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] {n : ℕ}
    (h : TrLe K n) : TrLe L n := by
  have hb : ∀ x : (⊥ : Subfield K), algebraMap K L x ∈ (⊥ : Subfield L) := fun x =>
    (show (⊥ : Subfield K) ≤ (⊥ : Subfield L).comap (algebraMap K L) from bot_le) x.2
  let e : (⊥ : Subfield K) →+* (⊥ : Subfield L) := ((algebraMap K L).comp (Subfield.subtype _)).codRestrict _ hb
  letI := e.toAlgebra
  haveI : IsScalarTower (⊥ : Subfield K) (⊥ : Subfield L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul (⊥ : Subfield K) (⊥ : Subfield L) := (faithfulSMul_iff_algebraMap_injective _ _).2 e.injective
  have h₁ := trdeg_add_eq (⊥ : Subfield K) (⊥ : Subfield L) (A := L)
  have h₂ := trdeg_add_eq (⊥ : Subfield K) K (A := L)
  rw [trdeg_eq_zero (R := K) (A := L), add_zero] at h₂
  exact le_trans (le_trans (self_le_add_left _ _) (h₁.trans h₂.symm).le) h

theorem trLe_bot (k : Type) [Field k] (n : ℕ) : TrLe (⊥ : Subfield k) n := by
  have : Algebra.IsAlgebraic (⊥ : Subfield (⊥ : Subfield k)) (⊥ : Subfield k) := ⟨fun x => by
    have : (⊥ : Subfield k) ≤ (⊥ : Subfield (⊥ : Subfield k)).map (Subfield.subtype _) := bot_le
    obtain ⟨y, hy, hxy⟩ := this x.2
    obtain rfl : y = x := Subtype.ext hxy
    exact isAlgebraic_algebraMap (⟨y, hy⟩ : (⊥ : Subfield (⊥ : Subfield k)))⟩
  simp [TrLe, trdeg_eq_zero]

theorem exists_closure {κ k : Type} [Field κ] [Field k] [IsAlgClosed k] (c : κ →+* k) {n : ℕ} (h : TrLe κ n) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : IsAlgClosed k₀) (c₀ : κ →+* k₀) (ι₀ : k₀ →+* k), TrLe k₀ n ∧ ι₀.comp c₀ = c := by
  letI := c.toAlgebra
  let l : AlgebraicClosure κ →ₐ[κ] k := IsAlgClosed.lift
  exact ⟨AlgebraicClosure κ, inferInstance, inferInstance, algebraMap _ _, l.toRingHom, trLe_of_isAlgebraic h,
    RingHom.ext fun x => l.commutes x⟩

theorem trLe_residueField {X : Scheme.{0}} {K : Type} [Field K] (y : Sp K ⟶ X) {n : ℕ} (h : TrLe K n) (p : Sp K) :
    TrLe (X.residueField (y p)) n := by
  obtain rfl : p = closedPoint K := Subsingleton.elim _ _
  exact TrLe.of_ringHom (Scheme.descResidueField (Scheme.stalkClosedPointTo y)).hom h

theorem exists_factor {X : Scheme.{0}} {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) {n : ℕ}
    (h : TrLe (X.residueField (y (closedPoint k))) n) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : IsAlgClosed k₀) (ι₀ : k₀ →+* k) (y₀ : Sp k₀ ⟶ X), TrLe k₀ n ∧ spMap ι₀ ≫ y₀ = y := by
  obtain ⟨k₀, _, _, c₀, ι₀, h₀, e⟩ := exists_closure (Scheme.descResidueField (Scheme.stalkClosedPointTo y)).hom h
  refine ⟨k₀, inferInstance, inferInstance, ι₀, spMap c₀ ≫ X.fromSpecResidueField _, h₀, ?_⟩
  rw [← Category.assoc, spMap_comp_spMap, e]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X y

theorem exists_level (V : Type) [CommRing V] [IsLocalRing V] : ∃ m : ℕ, 3 ≤ m ∧ Odd m ∧ IsUnit (m : V) := by
  have h : IsUnit ((2 : V) * 3 + -5) := by
    have : (2 : V) * 3 + -5 = 1 := by norm_num
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, le_rfl, by decide, by simpa using isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, by norm_num, by decide, by simpa using h.neg⟩

theorem exists_small_fibre : GlobalTheory.Published.SiegelToroidalIntegral → ∀ (T : Formalism.L2.Pj.CDVR) (P : Out.PolAV (Sp T.V)) (σ : T.V →+* ℂ) (K : Type) [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (P₁ : Out.PolAV (Sp ℂ)) (φ : P₁.A.left ⟶ P.A.left) (φ₀ : P₁.A.left ⟶ P₀.A.left) (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] (r : T.V →+* k), Function.Injective σ → TrLe K n → IsPolFibre σ P P₁ φ → IsPolFibre ι P₀ P₁ φ₀ → ∃ (k₀ : Type) (_ : Field k₀) (_ : IsAlgClosed k₀) (ι₀ : k₀ →+* k) (B : Over (Sp k₀)) (_ : GrpObj B), TrLe k₀ n ∧ IsAbelianScheme B ∧ SameFibre P.A (spMap r) B (spMap ι₀) := by
  intro hS T P σ K _ _ ι P₀ P₁ φ φ₀ n k _ _ r hσ hK hφ hφ₀
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · have hP : IsIso P.A.hom := GlobalTheory.ZM.Model.isIso_of_dim_zero P.A P.isAb (hg ▸ P.smoothDim)
    obtain ⟨k₀, _, _, -, ι₀, h₀, -⟩ := exists_closure (Subfield.subtype (⊥ : Subfield k)) (trLe_bot k n)
    exact ⟨k₀, inferInstance, inferInstance, ι₀, (Out.Inh.zeroPolAV _).A, inferInstance, h₀, (Out.Inh.zeroPolAV _).isAb,
      (Out.Inh.zeroPolAV _).A, inferInstance, _, _, RankZero.isGrpPullback_zero (RankZero.isIso_unit _) hP _,
      RankZero.isGrpPullback_zero (RankZero.isIso_unit _) (RankZero.isIso_unit _) _⟩
  obtain ⟨m, hm, ho, hu⟩ := exists_level T.V
  obtain ⟨_, -, hF⟩ := hS P.g hg
  obtain ⟨F, -⟩ := hF m hm ho
  obtain ⟨V, _, _, ψ, σ', r', y, P', χ, α, α₂, hσ', rfl, rfl, hχ, hα, hα₂, hΛ⟩ :=
    GlobalTheory.T.exists_domain_lift_polarized_variety P.g m F T P σ k r hm ho hu rfl hσ
  obtain ⟨β, -, hβ⟩ := EllComp.exists_isPolFibre_lift hχ hφ
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare hβ.2.1.1.w
  haveI := P'.isAb.comm
  haveI := P₁.isAb.comm
  have hΛ₁ : LBIso (abelian₂ P₁.A P₁.L) (F.univ.P.pull (β₂ ≫ α₂)) :=
    LBIso.trans (DVR.linComb_isLB _ P₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ P'.isLB _ _) _) (pull_isLB F.univ.isLB _)
      (SiegPull.lbIso_lam_pull hβ.2.1 hβ.2.2.symm hβ₂) (SiegPull.lbIso_pull_comp hΛ β₂)
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.exists_fibre_point_polarized P.g m F (spMap σ' ≫ y) P₁ (β ≫ α) (β₂ ≫ α₂) K ι P₀ φ₀ hm ho (hβ.2.1.comp hα)
    (SiegPull.isSquare_comp hβ₂ hα₂) hΛ₁ hφ₀
  have h₁ : TrLe (F.X.residueField (y (spMap σ' (closedPoint ℂ)))) n := by
    have := trLe_residueField y₀ hK (spMap ι (closedPoint ℂ))
    have e : y₀ (spMap ι (closedPoint ℂ)) = y (spMap σ' (closedPoint ℂ)) :=
      congrArg (fun f : Sp ℂ ⟶ F.X => f (closedPoint ℂ)) hy₀
    exact e ▸ this
  have hs : spMap σ' (closedPoint ℂ) ⤳ spMap r' (closedPoint k) := by
    show PrimeSpectrum.comap σ' (closedPoint ℂ) ⤳ PrimeSpectrum.comap r' (closedPoint k)
    rw [← PrimeSpectrum.le_iff_specializes]
    intro a ha
    have h0 : σ' a ∈ maximalIdeal ℂ := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, map_eq_zero_iff _ hσ'] at h0
    subst h0
    exact zero_mem _
  have h₂ := GlobalTheory.T.transcendence_bound_specializes F.X _ _ n (hs.map y.continuous) h₁
  obtain ⟨k₀, _, _, ι₀, z, h₀, hz⟩ := exists_factor (spMap r' ≫ y) h₂
  have hB := isGrpPullback_pullback F.univ.A z
  have hA := isGrpPullback_pullback ((Over.pullback z).obj F.univ.A) (spMap ι₀)
  have hA' := isGrpPullback_pullback P'.A (spMap r')
  obtain ⟨e, he, -⟩ := grpPullback_iso ((hA.comp hB).congr hz rfl) (hA'.comp hα)
  exact ⟨k₀, inferInstance, inferInstance, ι₀, _, _, h₀, PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hB, _, _, _, _,
    (((isGrpPullback_of_iso e).comp hA').comp hχ.2.1).congr (by rw [Category.id_comp, spMap_comp_spMap]) rfl, hA⟩

end GlobalTheory.BdDim.SiegSpec

end
