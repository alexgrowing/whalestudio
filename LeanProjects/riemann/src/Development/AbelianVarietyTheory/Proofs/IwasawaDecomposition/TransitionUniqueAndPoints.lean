import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.TransUniq

open GlobalTheory.ModelCompare GlobalTheory.TransitionUnique

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}

theorem phi_eq_on_fibre {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {t : SAB H S'} {r : S' ⟶ S} (ν ν' : SABMap t o.t r)
    (hM : ∀ a, ∃ x : MonoidalCategoryStruct.tensorUnit (Over S') ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (o.eta a).left ∧ x.left ≫ ν'.φ = r ≫ (o.eta a).left)
    (hA : ∀ a, ∃ x : MonoidalCategoryStruct.tensorUnit (Over S') ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (o.etaA a).left ∧ x.left ≫ ν'.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (y : Sp k ⟶ S') {T : Scheme.{0}} (u : T ⟶ Sp k) (g : T ⟶ t.G.left)
    (hg : g ≫ t.G.hom = u ≫ y) : g ≫ ν.φ = g ≫ ν'.φ := by
  let o₁ := objOfSABMap o ν
  let n : ObjMap o₁ o r := objMapOfSABMap o ν
  let n' : ObjMap o₁ o r := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h'⟩
  obtain ⟨o₂, ⟨q⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) _ _ (r ≫ s) (y ≫ r ≫ s) y rfl rfl
    ((Category.comp_id _).symm.trans (congrArg ((y ≫ r ≫ s) ≫ ·) (Spec.map_id _).symm)) o₁
  obtain ⟨m, hm⟩ := ObjComp.objMap_comp n q
  obtain ⟨m', hm'⟩ := ObjComp.objMap_comp n' q
  have e : q.toSABMap.φ ≫ ν.φ = q.toSABMap.φ ≫ ν'.φ :=
    hm.symm.trans ((objMap_unique_of_field firstFiveLaws.1.serre m m').trans hm')
  have hp : IsPullback q.toSABMap.φ o₂.t.G.hom t.G.hom y := q.toSABMap.cart.1
  rw [← hp.lift_fst g u hg]
  exact (Category.assoc _ _ _).trans ((congrArg (hp.lift g u hg ≫ ·) e).trans (Category.assoc _ _ _).symm)

theorem trans_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i i₂ : Idx H p) (τ τ' : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) (mu' : SABMap (Y i₂).t (Y i).t τ'), i.c.F ≤ i₂.c.F → IsTrans i i₂ τ mu → IsTrans i i₂ τ' mu' → τ = τ' ∧ ∀ (k : Type) [Field k] (y : Sp k ⟶ (Xo i₂.l).XF i₂.c) (T : Scheme.{0}) (s : T ⟶ Sp k) (g : T ⟶ (Y i₂).t.G.left), g ≫ (Y i₂).t.G.hom = s ≫ y ≫ (Y i₂).j → g ≫ mu.φ = g ≫ mu'.φ := by
  intro E _ _ _ H Dw Xo p W Y i i₂ τ τ' mu mu' hc h h'
  obtain ⟨b, π, r, hb, h₁, h₂, hf, h₃, h₄, h₅⟩ := h
  obtain ⟨b', π', r', hb', h₁', h₂', hf', h₃', h₄', h₅'⟩ := h'
  obtain rfl : b = b' := RingHom.ext fun x => Subtype.ext (Subtype.ext ((hb x).trans (hb' x).symm))
  obtain rfl : τ = τ' := isTransition_unique E H Dw _ _ _ _ _ _ W (Y i) (Y i₂) b τ τ' hc hb
    ⟨π, mu, r, h₁, h₂, hf, h₃, h₄, h₅⟩ ⟨π', mu', r', h₁', h₂', hf', h₃', h₄', h₅'⟩
  refine ⟨rfl, fun k _ y T s g hg => ?_⟩
  have := mono_spMap_subtype (i.c.V W)
  have := (Y i).jQ_open
  have : Mono (Y i).j := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j
    infer_instance
  obtain rfl : r = r' := by rw [← cancel_mono (Y i).j, ← h₃, ← h₃']
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp (Y i₂).m mu' h₃'
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel (Y i).m n' r rfl
  have hp : IsPullback (Y i₂).m.φ (Y i₂).oF.t.G.hom (Y i₂).t.G.hom (Y i₂).j := (Y i₂).m.cart.1
  have hg' : g ≫ (Y i₂).t.G.hom = (s ≫ y) ≫ (Y i₂).j := by rw [hg, Category.assoc]
  have e := phi_eq_on_fibre (Y i).oF ν ν'
    (fun a => ⟨_, LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a),
      LevelCover.sec_cancel ν' (Y i).m _ _ (by rw [hν', hn']; exact h₄' a)⟩)
    (fun a => ⟨_, LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a),
      LevelCover.sec_cancel ν' (Y i).m _ _ (by rw [hν', hn']; exact h₅' a)⟩)
    y s (hp.lift g (s ≫ y) hg') (hp.lift_snd _ _ _)
  rw [← hp.lift_fst g (s ≫ y) hg', Category.assoc, Category.assoc, ← hn, ← hn', ← hν, ← hν', ← Category.assoc, e,
    Category.assoc]

end GlobalTheory.TransUniq
