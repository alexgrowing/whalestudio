import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H
open private UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe

private theorem e_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F)
    (x y : PlacesOver E v) (h : x ≠ y) : x.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two D] at hs
  have hpos : ∀ x : PlacesOver E v, 1 ≤ x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have h1 := Finset.sum_le_sum_of_subset (f := fun x : PlacesOver E v => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F))
    (Finset.subset_univ {x, y})
  rw [Finset.sum_pair h, hs] at h1
  have h2 := hpos x
  have h3 := hpos y
  exact Nat.eq_one_of_mul_eq_one_right (show x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) = 1 by omega)

private theorem map_sg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : P F) (w w' : P E)
    [hl : w.asIdeal.LiesOver v.asIdeal] [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) ∧
      ∀ a b, sg w a * sg w' b = 0 := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc₁, -, -, -, -, hs₁, -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc₂, -, -, -, -, hs₂, -, -⟩ := sgLaws E w'
  refine ⟨Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_), fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)⟩
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs₁ _).1, (hs₂ _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs₂ _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc₁ _).symm
    by_cases h' : u = w'
    · subst h'
      have hb : below F u = v := (below_eq_iff _ _).2 hl'
      subst hb
      rw [(hs₁ _).2 _ h, zero_add]
      exact (congrArg _ (hc x)).trans (hc₂ _).symm
    · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
      rw [(hs x).2 _ hb, map_zero, (hs₁ _).2 _ h, (hs₂ _).2 _ h', add_zero]
  · change (sg w a).1 * (sg w' b).1 = 0
    rw [(hs₁ _).1, zero_mul]
  · change (sg w a).2 u * (sg w' b).2 u = 0
    by_cases h : u = w
    · subst h
      rw [(hs₂ _).2 _ hne, mul_zero]
    · rw [(hs₁ _).2 _ h, zero_mul]

theorem UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∀ ϖ : (H.Kv v)ˣ, H.IsU ϖ → ∃ (ϖ₁ : (H.Kv w)ˣ) (ϖ₂ : (H.Kv w')ˣ), H.IsU ϖ₁ ∧ H.IsU ϖ₂ ∧
            ideleEmbedding ℚ E (H.idl v ϖ) = H.idl w ϖ₁ * H.idl w' ϖ₂ := by
  intro E _ _ D v w w' hne hw hw' _ _ hall ϖ hϖ
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hn : (⟨w, hl⟩ : PlacesOver E v) ≠ ⟨w', hl'⟩ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨-, -, -, hi, -, -, -, -, -, -⟩ := sgLaws ℚ v
  obtain ⟨-, -, -, hi₁, -, -, -, -, -, -⟩ := sgLaws E w
  obtain ⟨-, -, -, hi₂, -, -, -, -, -, -⟩ := sgLaws E w'
  refine ⟨Units.map (completionMap v w : Kv v →* Kv w) ϖ, Units.map (completionMap v w' : Kv v →* Kv w') ϖ, ?_, ?_, Units.ext ?_⟩
  · change Valued.v (completionMap v w (ϖ : Kv v)) = _
    rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota v w (e_one D v _ _ hn)]
    exact hϖ
  · change Valued.v (completionMap v w' (ϖ : Kv v)) = _
    rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota v w' (e_one D v _ _ hn.symm)]
    exact hϖ
  · obtain ⟨h1, h2⟩ := map_sg v w w' hne (fun u hu => hall u (HeightOneSpectrum.ext hu.over.symm)) ((ϖ : Kv v) - 1)
    change adeleMap ℚ E ((idl v ϖ : (A ℚ)ˣ) : A ℚ) = _
    rw [Units.val_mul, hi, hi₁, hi₂, map_add, map_one, h1, map_sub, map_sub, map_one, map_one, add_mul, mul_add, mul_add, h2]
    simp only [one_mul, mul_one, add_zero, Units.coe_map, MonoidHom.coe_coe]
    abel
