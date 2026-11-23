import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem exists_hom_ext_of_grpPullback {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
    [Algebra V F] [IsFractionRing V F] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') {t t' : Over (Sp F)} [GrpObj t] [GrpObj t'] {a : t.left ⟶ G.left}
    {a' : t'.left ⟶ G'.left} (ha : IsGrpPullback t G (spMap (algebraMap V F)) a)
    (ha' : IsGrpPullback t' G' (spMap (algebraMap V F)) a') (β : t ⟶ t') [IsMonHom β] :
    ∃ f : G ⟶ G', IsMonHom f ∧ a ≫ f.left = β.left ≫ a' := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso ha (isGrpPullback_pullback G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso ha' (isGrpPullback_pullback G' _)
  have hφ₁ : e.hom.left ≫ pullback.fst G.hom (spMap (algebraMap V F)) = a := hφ
  have hφ₂ : e'.hom.left ≫ pullback.fst G'.hom (spMap (algebraMap V F)) = a' := hφ'
  obtain ⟨f, ⟨hf, hfβ⟩, -⟩ := semiAbelian_hom_extends_uniquely_dvr V F G G' hG hG' (e.inv ≫ β ≫ e'.hom)
    inferInstance
  refine ⟨f, hf, ?_⟩
  have A : ((Over.pullback (spMap (algebraMap V F))).map f).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ f.left := pullback.lift_fst _ _ _
  have B : β ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap V F))).map f := by
    rw [hfβ]; simp
  rw [← hφ₁, ← hφ₂, Category.assoc, ← A, ← Category.assoc, ← Category.assoc β.left, ← Over.comp_left,
    ← Over.comp_left, B]

theorem pointOver_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [StarRing (𝓞 E)] (T : CDVR) (x₀ : Sp T.Fr ⟶ Xo.X) (k : T.Fr →+* C) (kO kO' : T.V →+* O) (P P' : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left), PointOver P x₀ k kO ψ → PointOver P' x₀ k kO' ψ' → ∃ (α : P.A.A ≅ P'.A.A) (gm : P.G ⟶ P'.G), IsMonHom α.hom ∧ IsMonHom gm ∧ α.hom.left ≫ ψ' = ψ ∧ α.hom.left ≫ P'.gen = P.gen ≫ gm.left ∧ (∀ a, P.oA.act a ≫ α.hom = α.hom ≫ P'.oA.act a) ∧ LBIso P.A.L (P'.A.L.pull α.hom.left) := by
  intro E _ _ _ H Dw l Xo p _ C _ v O _ _ _ T x₀ k kO kO' P P' ψ ψ' h h'
  obtain rfl : kO = kO' := RingHom.ext fun a => P.integers.hom_inj ((h.1 a).trans (h'.1 a).symm)
  obtain ⟨α, hα, hαψ⟩ := grpPullback_iso h.isGrpPullback h'.isGrpPullback
  have hact : ∀ a, P.oA.act a ≫ α.hom = α.hom ≫ P'.oA.act a := fun a =>
    Over.OverMorphism.ext (h'.isGrpPullback.1.hom_ext
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hαψ, h'.act a, h.act a,
        ← Category.assoc, hαψ])
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨-, G, t, m₁, m₂, π, φ, hπ, -, hφ, e₂, e₁, hL⟩ := h
  obtain ⟨-, G', t', n₁, n₂, π', φ', hπ', -, hφ', e₂', e₁', hL'⟩ := h'
  obtain ⟨β, hβ, hβφ⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨f, hf, hfβ⟩ := exists_hom_ext_of_grpPullback G.semi G'.semi m₂.cart n₂.cart β.hom
  have w : (π ≫ f.left) ≫ G'.G.hom = P.G.hom ≫ spMap kO := by rw [Category.assoc, Over.w, hπ.1.w]
  let gm : P.G ⟶ P'.G := Over.homMk (hπ'.1.lift _ _ w) (hπ'.1.lift_snd _ _ w)
  have hgm : gm.left ≫ π' = π ≫ f.left := hπ'.1.lift_fst _ _ w
  have c : α.hom.left ≫ φ' = φ ≫ β.hom.left := n₁.cart.1.hom_ext
    (by rw [Category.assoc, Category.assoc, e₁', hβφ, e₁, hαψ])
    (by rw [Category.assoc, Category.assoc, Over.w, hφ.1.w, hφ'.1.w, Over.w_assoc])
  refine ⟨α, gm, hα, Out.PullGtPf.isMonHom_of_grpPullback hπ hπ' f gm hgm, hαψ, ?_, hact, ?_⟩
  · refine hπ'.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hgm, ← e₂', ← Category.assoc, c, ← Category.assoc, ← e₂,
        Category.assoc, Category.assoc, hfβ]
    · rw [Category.assoc, Category.assoc, Over.w, P.gen_pull.1.w, P'.gen_pull.1.w, Over.w_assoc]
  · refine LBIso.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB ψ) (pull_isLB P'.A.isLB _) hL (LBIso.symm ?_)
    exact LBIso.chartPull (Geo.Tor.chartPullPull P'.A.L _ _ rfl)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => ψ) (fun _ => ψ') (fun _ => 1) _ (fun _ => hαψ.symm)) hL'

end GlobalTheory.CompHt
