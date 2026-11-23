import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CyclotomicRootsOfUnity
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

theorem isDominant_fst {F : Type} [Field F] (V : ValuationSubring F) {X : Scheme.{0}} (s : X ⟶ Sp V) [Flat s] :
    IsDominant (pullback.fst s (spMap V.subtype)) := by
  refine ⟨fun x => ?_⟩
  let g : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  have hg : spMap V.subtype g ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
    show Ideal.comap V.subtype ⊥ ≤ _
    rw [Ideal.comap_bot_of_injective _ V.subtype_injective]
    exact bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg
  refine hy.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨g, e.symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isDominant_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : IsDominant Y.j := by
  have := Y.flat
  have := isDominant_fst V Y.s
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  unfold Model.j
  infer_instance

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := by
  let o := objOfSABMap Y.oF ν
  let n : ObjMap o Y.oF r := objMapOfSABMap Y.oF ν
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

theorem isTransition_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (c : Coeff l) (c₂ : Coeff l₂) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (Y₂ : Model Xo₂ c₂ (c₂.V W).subtype) (b : c.V W →+* c₂.V W) (π π' : Y₂.X ⟶ Y.X), c.F ≤ c₂.F → IsIncl b → IsTransition Y Y₂ b π → IsTransition Y Y₂ b π' → π = π' := by
  intro E _ _ _ H D l l₂ Xo Xo₂ c c₂ W Y Y₂ b π π' _ _ h h'
  obtain ⟨p, mu, r, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  obtain ⟨p', mu', r', h₁', h₂', -, h₃', h₄', h₅'⟩ := h'
  have e : π ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  have e' : π' ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁', ← h₂', Category.assoc, Category.assoc, pullback.condition]
  have := mono_spMap_subtype (c.V W)
  have hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _ := by
    rw [← cancel_mono (spMap (c.V W).subtype), Category.assoc, Category.assoc, ← ModelRelProbe.j_over Y,
      ← Category.assoc, ← Category.assoc, ← h₃, ← h₃', Category.assoc, Category.assoc, e, e']
  obtain ⟨n, hn⟩ := LevelCover.sab_comp Y₂.m mu h₃
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp Y₂.m mu' h₃'
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel Y.m n r rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m n' r' rfl
  have := isReduced_XF Xo₂ c₂
  have hrr : r = r' := map_unique Y ν ν' hr
    (fun a => ⟨_, LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hn]; exact h₄ a),
      LevelCover.sec_cancel ν' Y.m _ _ (by rw [hν', hn']; exact h₄' a)⟩)
    (fun a => ⟨_, LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hn]; exact h₅ a),
      LevelCover.sec_cancel ν' Y.m _ _ (by rw [hν', hn']; exact h₅' a)⟩)
  have : ∀ x : Y₂.X, _root_.IsReduced (Y₂.X.presheaf.stalk x) := fun x ↦
    have := (Y₂.normal x).1
    inferInstance
  have := isReduced_of_isReduced_stalk Y₂.X
  have := projProper _ _ _ Y.proj
  have := isDominant_j Y₂
  exact ext_of_isDominant_of_isSeparated Y.s (e.trans e'.symm) Y₂.j (by rw [h₃, h₃', hrr])

end GlobalTheory.TransitionUnique
