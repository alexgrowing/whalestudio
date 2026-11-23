import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4

open MeasureTheory

theorem chInt_add_of_continuous : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (f g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, Continuous (f σ)) → (∀ σ, Continuous (g σ)) → chInt (ArInt.comb L n) D (fun σ y => f σ y + g σ y) = chInt (ArInt.comb L n) D f + chInt (ArInt.comb L n) D g := by
  intro H k _ X _ p D hX ι _ L n f g hf hg
  have hu : ∀ (σ : k →+* ℂ) (y : CxPts p σ), CxPts.CInfAt (fun _ : CxPts p σ => (1 : ℝ)) y :=
    fun σ y => CxPts.cInfAt_const 1 y
  have hc : ∀ σ σ' : k →+* ℂ, (Weight.ofFun (fun _ : CxPts p σ => (1 : ℝ))).IsConj
      (Weight.ofFun (fun _ : CxPts p σ' => (1 : ℝ))) := fun _ _ _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := ((H.arExists k X p D hX).2 (Option ι)
    (fun o : Option ι => o.elim (ArInt.fnB (fun σ (_ : CxPts p σ) => (1 : ℝ)) hu hc) L)).1
  have h1 := (H.arMix.fnB H.arExists hX hΦ n).1
  have hfin : ∀ σ (ε : ℤˣ), IsFiniteMeasure (((ArInt.comb L n).φ σ).chernPart D ε) := by
    intro σ ε
    have h1' : Integrable (fun _ : CxPts p σ => (1 : ℝ)) (((ArInt.comb L n).φ σ).chernPart D ε) := by
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact integrableOn_univ.1 (h1 σ).1
      · exact integrableOn_univ.1 (h1 σ).2
    exact (integrable_const_iff.1 h1').resolve_left one_ne_zero
  have hint : ∀ σ (u : CxPts p σ → ℝ), Continuous u → ((ArInt.comb L n).φ σ).ChernIntegrableOn D Set.univ u := by
    intro σ u hu'
    haveI := hX.compactSpace σ
    have hi : ∀ ε : ℤˣ, IntegrableOn u Set.univ (((ArInt.comb L n).φ σ).chernPart D ε) := fun ε => by
      haveI := hfin σ ε
      exact integrableOn_univ.2
        ((BoundedContinuousFunction.mkOfCompact ⟨u, hu'⟩).integrable (((ArInt.comb L n).φ σ).chernPart D ε))
    exact ⟨hi 1, hi (-1)⟩
  have hfs : Finite (k →+* ℂ) := hX.finite_emb
  unfold chInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => Weight.chernInt_add (hint σ _ (hf σ)) (hint σ _ (hg σ))

end GlobalTheory.Mean4
