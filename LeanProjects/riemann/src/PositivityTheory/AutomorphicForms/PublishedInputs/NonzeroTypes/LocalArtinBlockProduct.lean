import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace LocalArtinBlockProduct

theorem prod_blocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (G : Grp k n) {M : Type*} [CommMonoid M] (f : Fin G.s → M) :
    ∏ i, f (G.bl i) = ∏ b, f b ^ G.d b := by
  calc ∏ i, f (G.bl i) = ∏ p : (Σ a, Fin (G.d a)), f (G.bl (G.e p)) := (G.e.prod_comp (fun i => f (G.bl i))).symm
    _ = ∏ p : (Σ a, Fin (G.d a)), f p.1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      show f ((G.e.symm (G.e p)).1) = f p.1
      rw [Equiv.symm_apply_apply]
    _ = ∏ b, f b ^ G.d b := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun b _ => ?_
      show ∏ _y : Fin (G.d b), f b = f b ^ G.d b
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem exists_unit (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    ∃ u, unitIncl (w.adicCompletion E) u = a (ineIncl h t) := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact valuation_eq_one_iff.mp (ord_eq_zero_iff.mp h0)

end LocalArtinBlockProduct

theorem localArtinCharacterProduct_holds : LocalArtinCharacterProduct := by
  intro E Ω _ _ _ _ _ A w h a ha n χ ho μ hμ G σ hG s
  obtain ⟨u, hu⟩ := LocalArtinBlockProduct.exists_unit ha s
  have key : ∀ i, ((χ i (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h s)) : ℂˣ) : ℂ) =
      ((G.chi (σ.symm i) (a (ineIncl h s)) : ℂˣ) : ℂ) := by
    intro i
    have e := DFunLike.congr_fun (hG (σ.symm i)) u
    simp only [MonoidHom.comp_apply, Equiv.apply_symm_apply] at e
    rw [hμ i, ← hu, e]
  simp only [xOf, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd, MonoidHom.comp_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [key i]]
  rw [Equiv.prod_comp σ.symm (fun j => X - C ((G.chi j (a (ineIncl h s)) : ℂˣ) : ℂ))]
  exact LocalArtinBlockProduct.prod_blocks G (fun b => X - C ((G.μ b (a (ineIncl h s)) : ℂˣ) : ℂ))

end UpperTheory.NonzeroTypeTheory
