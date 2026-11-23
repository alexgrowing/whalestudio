import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem modif_genericPoint {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IsIntegral M.X] {η : Y} (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    M.σ (genericPoint M.X) = η ∧ genericPoint M.X ∈ M.opn ∧ IsIso (M.σ.stalkMap (genericPoint M.X)) := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hmem : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  obtain ⟨z, hz⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hz' : M.σ z.1 = η := by rw [← morphismRestrict_base_coe, hz]
  have hsp : M.σ (genericPoint M.X) ⤳ η :=
    hz' ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ z.1)).map M.σ.continuous
  have he : M.σ (genericPoint M.X) = η := (hsp.antisymm (hg.specializes (Set.mem_univ _))).eq
  refine ⟨he, hmem, ?_⟩
  let z0 : (M.σ ⁻¹ᵁ U).toScheme := ⟨genericPoint M.X, hmem⟩
  have h1 : IsIso ((M.σ ∣_ U ≫ U.ι).stalkMap z0) := by
    rw [Scheme.Hom.stalkMap_comp]
    have a := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion U.ι)).2 ((M.σ ∣_ U) z0)
    have b := (IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ∣_ U))).2 z0
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ a b
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    ((IsOpenImmersion.iff_isIso_stalkMap.1 (inferInstance : IsOpenImmersion (M.σ ⁻¹ᵁ U).ι)).2 z0) h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem birational_of_ratGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7}
    (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)
    (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec)
    (k : Consts) (hR : RatGen X Z U P.u₁) : (h.geo f₁ f₂ th k).Birational := by
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  haveI : IsIntegral R.X := HilbertSamuel.Geo.isIntegral (h.geo f₁ f₂ th k)
  obtain ⟨he, hmem, hiso⟩ := modif_genericPoint R.toModif hη hgen
  subst he
  set G := h.geo f₁ f₂ th k with hG
  set η' := genericPoint R.X with hη'
  refine ⟨η', genericPoint_spec _, ?_⟩
  set xp : Sp (R.X.residueField η') ⟶ G.Y := resPt η' with hxp
  set cc := G.chartAt (ptOf xp) with hcc
  have hc : η' ∈ R.Δ₁.moving.U cc := (ptOf_resPt η') ▸ G.mem_chartAt (ptOf xp)
  have hi0 : R.σ η' ∈ (L₀ X Z P.u₁).U (cc.1 PUnit.unit) := mem_pull.1 hc.1
  set φ := (R.σ.residueFieldMap η').hom with hφdef
  have hφ : ∀ a, φ (((Y₀ X Z).residue (R.σ η')).hom a) = (R.X.residue η').hom ((R.σ.stalkMap η').hom a) := fun a => by
    have := congrArg (fun g => g.hom a) (Scheme.residue_residueFieldMap R.σ η')
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this

  let Vf : Cusp Z U P.u₁ → R.X.residueField η' := fun f => G.val xp (toSec (R.Δ₁.lift (h.ext₁.equiv f)))
  have hA : ∀ f, Vf f = ∑ j, G.baseHom xp (f₁.b.equivFun f j) * G.coords xp j := by
    intro f
    have e := R.toModif.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ (f₁.b.equivFun f)
    rw [LinearEquiv.symm_apply_apply] at e
    have e2 : toSec (R.Δ₁.lift (h.ext₁.equiv f)) = G.comb (f₁.b.equivFun f) := by
      apply (bijective_ofSec_top (p := R.str) (B := R.Δ₁.moving)).1
      rw [ofSec_toSec]
      exact e.symm
    exact (congrArg (G.val xp) e2).trans (G.val_comb xp _)
  have hV : ∀ f, Vf f = (R.X.residue η').hom (germ cc η' (memTop η') hc (R.Δ₁.lift (h.ext₁.equiv f))) := by
    intro f
    show valR xp _ _ = _
    refine (projSys.valR_resPt η' _ hc _).trans ?_
    refine (congrArg (fun g => (ConcreteCategory.hom g) ((toSec (R.Δ₁.lift (h.ext₁.equiv f))).f cc))
      (Scheme.germ_residue R.X η' hc).symm).trans ?_
    exact congrArg (R.X.residue η').hom (ger_toSec _ cc η' hc)
  set τ := (R.X.residue η').hom (ger η' hc.2 (R.Δ₁.t.f cc.2)) with hτdef
  have hB : ∀ f, τ * Vf f = φ (((Y₀ X Z).residue (R.σ η')).hom
      (germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f))) := by
    intro f
    have e1 := R.Δ₁.germ_lift (h.ext₁.equiv f) cc η' hc
    have e2 := germ_pull R.σ le_top cc.1 η' (memTop η') hc.1 (h.ext₁.equiv f).1
    have e3 := hφ (germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1)
    have e4 : germ (cc.1 PUnit.unit) (R.σ η') hη hi0 (cuspSec X Z U P.u₁ f) =
        germ (cc.1 PUnit.unit) (R.σ η') (memTop _) hi0 (h.ext₁.equiv f).1 := by
      rw [← h.ext₁.restr_equiv f, germ_restr]
    rw [hV, e4, e3, ← e2, ← e1]
    exact (map_mul _ _ _).symm
  have hτ : τ ≠ 0 := by
    have hu : IsUnit (ger η' hc.2 (R.Δ₁.t.f cc.2)) :=
      (isUnit_ger_iff _ hc.2).2 ((R.Δ₁.mem_nonzeroLocus η').2 (R.notMem_support h.free₁ η' (R.off_eq.ge hmem)))
    exact (hu.map (R.X.residue η').hom).ne_zero
  obtain ⟨j₀, hj₀⟩ : ∃ j, G.coords xp j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact G.geom.alg.bpf.coords_ne_zero xp (funext hn)
  have hmemV : ∀ f f', Vf f / Vf f' ∈ G.ratioField xp := by
    intro f f'
    have key : ∀ g, Vf g = G.coords xp j₀ *
        ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) := by
      intro g
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have hs : ∀ g, ∑ j, G.baseHom xp (f₁.b.equivFun g j) * (G.coords xp j / G.coords xp j₀) ∈ G.ratioField xp :=
      fun g => Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subfield.subset_closure (Or.inr ⟨j, j₀, rfl⟩))
    rw [key, key, mul_div_mul_left _ _ hj₀]
    exact Subfield.div_mem _ (hs f) (hs f')
  have hgen' : ratField (Set.range (cuspSec X Z U P.u₁)) (R.σ η') hη ≤ (G.ratioField xp).comap φ := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨i, hi, _, _, ⟨f, rfl⟩, ⟨f', rfl⟩, rfl⟩
    have htr : ((Y₀ X Z).residue (R.σ η')).hom (tr (L₀ X Z P.u₁) (R.σ η') i (cc.1 PUnit.unit) : _) ≠ 0 :=
      ((Units.isUnit _).map _).ne_zero
    show φ (_ / _) ∈ G.ratioField xp
    rw [germ_change i (cc.1 PUnit.unit) _ hη hi hi0, germ_change i (cc.1 PUnit.unit) _ hη hi hi0, map_mul, map_mul,
      mul_div_mul_left _ _ htr, map_div₀, ← hB f, ← hB f', mul_div_mul_left _ _ hτ]
    exact hmemV f f'
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨a', rfl⟩ := R.X.residue_surjective η' y
  obtain ⟨a, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2 a'
  rw [← hφ]
  exact hgen' (hrat.ge trivial)

example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := @birational_of_ratGen

end GlobalTheory.HSApp
