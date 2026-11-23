import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagRead

open GlobalTheory.CompanionTheory.Ar.FlagPull

theorem fieldRange_finite {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    FiniteDimensional i.fieldRange Ω ∧
      Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank Ω₁ Ω) := by
  letI := i.toAlgebra
  haveI := hfin
  let e : Ω₁ ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have he : (algebraMap i.fieldRange Ω).comp (e : Ω₁ →+* i.fieldRange) =
      ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap Ω₁ Ω) := by
    ext x
    rfl
  exact ⟨Module.Finite.of_equiv_equiv e (RingEquiv.refl Ω) he,
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) he).symm⟩

theorem span_eq_of_indep {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b' : Fin r → V}
    {W : Submodule Ω V} (hb : LinearIndependent Ω b) (hle : ∀ k, b k ∈ W) (hb' : LinearIndependent Ω b')
    (hs : Submodule.span Ω (Set.range b') = W) : Submodule.span Ω (Set.range b) = W := by
  subst hs
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b')) :=
    FiniteDimensional.span_of_finite Ω (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hle k
  · rw [finrank_span_eq_card hb, finrank_span_eq_card hb']

theorem generic_read : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hfin hd hf hcst hj hpt hρ
  obtain ⟨hfd, hfr⟩ := fieldRange_finite i hfin
  haveI := hfd
  have hgen : genPt A.ξ₀ = genPt B.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt B.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ B.gen₀ hgen
  have hfn : B.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap B.fn ≫ B.ξ₀ = B.ξ ≫ B.f := B.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : B.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (B.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, FlagPull.spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module B.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hemb : ∀ s, B.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, jA w ∈ B.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show jA w ∈ eigSp B.ρ (B.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule B.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← FlagPull.spMap_comp, ← FlagPull.spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  have hspan : ∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s := by
    intro s
    letI := A.fn.toAlgebra
    obtain ⟨cc, u, hcV, -, -, hb, -, -, hfl, -⟩ := Fl.generic
    have hmemc : ∀ k, Fl.j (cc s k) ∈ A.Vgen s := fun k => (Fl.V₀_mem s _).1 (by
      rw [← (hcV s).2]
      exact Submodule.subset_span ⟨k, rfl⟩)
    have hbk : ∀ a, Fl.b s a ∈ A.Vgen s := by
      intro a
      have h1 : Fl.b s a ∈ flagStep Ω₁ (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨a, a.2, rfl⟩
      rw [hfl s] at h1
      refine (Submodule.span_le (p := A.Vgen s).2 ?_) h1
      rintro _ ⟨k, -, rfl⟩
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmemc l)
    obtain ⟨U, hU, b', hb', hfr'⟩ := B.vb s ⟨genPt B.ξ, specializes_rfl⟩ (Set.mem_univ _)
    exact span_eq_of_indep (hj.2 _ _ (hb s)) (fun k => (hVgen s _).2 (hbk k))
      (hfr' _ (Set.mem_univ _) hU).1 hb'
  refine ⟨Fl.Li₀, Fl.acg, mod', transport ψ hψ hs Fl.M₀, jA.comp Fl.j, V₀', hspan, fun e => ?_,
    fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm, ?_⟩
  · show (B.M.pt (jA (Fl.j e))).left ≫ B.m.φ =
      spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
    rw [hpt, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
  · have := genericFlag_pull A.fn B.fn ψ i hfn hs Fl.j jA hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg Fl.generic
    rw [hfr] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.FlagRead
