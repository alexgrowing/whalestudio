import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightWeightedFiberSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeightOffBoundaryDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSymbolHeightRootSum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatPoint

theorem sum_over_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y)
    (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, GlobalTheory.CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π →
    ∀ (w : V.G), IsClosed ({w} : Set V.G) → ∀ (g : M.Fun) (f : ∀ σ : F →+* ℂ, Pts Y σ → ℝ),
    (∀ a z, under (I.pt a z) = V.π w → g a z = f (I.ε a) (I.pt a z)) →
    ∑ᶠ σ, ∑ᶠ y ∈ {y : GlobalTheory.CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, M.pull ε π g σ y =
      (V.π.residueDegree w : ℝ) * ∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = V.π w), f σ z := by
  intro F _ _ Y V e M I ε π hD w hw g f hgf
  have := GlobalTheory.Mean4O.CoverHt.isPreimmersion_j V
  have inner (σ : F →+* ℂ) :
      ∑ᶠ x ∈ {x : GlobalTheory.CxPts V.p (σ.comp (algebraMap (𝓞 F) F)) | x.1 (IsLocalRing.closedPoint ℂ) = V.j w},
          M.pull ε π g (σ.comp (algebraMap (𝓞 F) F)) x =
        (V.π.residueDegree w : ℝ) * ∑ᶠ (y : Pts Y σ) (_ : under y = V.π w), f σ y := by
    have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
      rw [← Spec.map_comp]
      rfl
    obtain ⟨hε, hπ⟩ := hD (σ.comp (algebraMap (𝓞 F) F))
    have hτ : I.ε (ε (σ.comp (algebraMap (𝓞 F) F))) = σ := (HtModel.bijective_comp F).1 hε
    have hg₂ : ∀ (τ σ : F →+* ℂ) (_ : τ = σ) (p : Pts Y τ) (q : Pts Y σ), p.1 = q.1 → f τ p = f σ q := by
      rintro τ σ rfl p q h
      rw [Subtype.ext h]
    let Φ : {z : {z : Sp ℂ ⟶ V.G // z ≫ V.π ≫ Y.str = spMap σ} // below z.1 = w} →
        ↥{x : GlobalTheory.CxPts V.p (σ.comp (algebraMap (𝓞 F) F)) | x.1 (IsLocalRing.closedPoint ℂ) = V.j w} := fun z =>
      ⟨⟨z.1.1 ≫ V.j, by rw [Category.assoc, V.pb.w, ← Category.assoc, z.1.2, hs]⟩,
        (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.j z.2)⟩
    have hΦ : Function.Bijective Φ := by
      refine ⟨fun a b h => ?_, ?_⟩
      · have h' : a.1.1 ≫ V.j = b.1.1 ≫ V.j := congrArg (fun t => t.1.1) h
        exact Subtype.ext (Subtype.ext (V.pb.hom_ext h' (a.1.2.trans b.1.2.symm)))
      · rintro ⟨x, hx'⟩
        have e1 : x.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := x.2.trans hs
        refine ⟨⟨⟨V.pb.lift x.1 (spMap σ) e1, V.pb.lift_snd _ _ _⟩, ?_⟩, ?_⟩
        · apply V.j.isEmbedding.injective
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp ℂ ⟶ V.X => t (IsLocalRing.closedPoint ℂ)) (V.pb.lift_fst _ _ e1)).trans hx')
        · exact Subtype.ext (Subtype.ext (V.pb.lift_fst _ _ _))
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_eq_of_bijective Φ hΦ (f := fun z => f σ ⟨z.1.1 ≫ V.π, (Category.assoc _ _ _).trans z.1.2⟩) fun z => ?_]
    · rw [GlobalTheory.Mean4O.CoverHt.finsum_lifts σ V.π Y.str w hw (f σ)]
      congr 1
      exact finsum_subtype_eq_finsum_cond (fun y : Pts Y σ => under y = V.π w)
    · obtain ⟨w', h1, h2⟩ := hπ (Φ z).1
      have hb : under (I.pt _ (π _ (Φ z).1)) = V.π w := by
        have e3 : w' = z.1.1 := by
          refine V.pb.hom_ext h1 ?_
          rw [← Category.assoc, h2, (I.pt _ _).2, z.1.2, hτ]
        show below (I.pt _ (π _ (Φ z).1)).1 = V.π w
        rw [← h2, e3]
        exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.π z.2)
      show f σ _ = g _ _
      rw [hgf _ _ hb]
      refine (hg₂ _ _ hτ _ _ ?_).symm
      rw [← h2]
      congr 1
      refine V.pb.hom_ext h1 ?_
      rw [← Category.assoc, h2, (I.pt _ _).2, z.1.2, hτ]
  rw [← finsum_eq_of_bijective _ (HtModel.bijective_comp F) fun σ => (inner σ).symm,
    finsum_eq_sum_of_fintype, ← Finset.mul_sum]

theorem ht_det_eq : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
    ∀ (B : ℝ) (c : O.s.Comp) (τ : D.what₂.Tau) (b : (O.var c).X), IsClosed ({b} : Set (O.var c).X) →
    (O.Φ.C c).π b ∉ GlobalTheory.Toroidal.genBd O.s.T.Z →
    (adlOf (O.Φ.C c) (O.met.hm c) (detSym O.S.Dw (ArIn.ind (Pad.setB O.κ B)) none (DV.tauEmb D τ))).ht b =
      ∑ r : DV.Rt D.what₂.Tau O.N, (if r.1 = τ then (O.root0 c (GlobalTheory.FlagAr.setB O.Y B) r).ht b else 0) +
      (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = b),
          O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z) /
        ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = b} : ℝ)) := by
  intro D O hO A T H h B c τ b hb hbd
  rw [GlobalTheory.T.adelic_height_off_boundary_decomposition D O hO _ c τ b hb hbd, O.setB_eq, GlobalTheory.T.determinant_symbol_height_root_sum D O hO A T H h _ c τ b hb]

theorem exists_algPt_height_zero : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
      (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ'))),
    ∃ x : (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X, ArInt.IsAlgPt x ∧ ∀ hh : (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X → ℝ,
      (comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).IsArithHeight hh → hh x = 0 := by
  intro hP _ _ D O hO _ A T Ht0 h B hB τ c g _ hgZ ε π hd hu hc
  have hE : GlobalTheory.Published.ArExists := hP.p4.arExists
  obtain ⟨hb, hbd⟩ := GlobalTheory.ShFam.KitCheck.innerPt_spec O.Φ c
  have hman := h.an c
  revert π hd hu hc
  generalize h.mdl (GlobalTheory.FlagAr.setB O.Y B) c = W
  intro π hd hu hc
  obtain ⟨w, hw, hwb⟩ := GlobalTheory.Mean4O.OnModel.exists_closed_over W.V hb
  have halg := GlobalTheory.Mean4O.CoverHt.isAlgPt _ w hw
  refine ⟨_, halg, fun hh HH => ?_⟩
  have hF := GlobalTheory.T.point_height_weighted_fiber_sum _ _ W.V _ hu hc w hw hE
  have hR (r : DV.Rt D.what₂.Tau O.N) : IsPtHt (W.gens (GlobalTheory.FlagAr.setB O.Y B) (some r)) (W.V.j w)
      (-(O.root0 c (GlobalTheory.FlagAr.setB O.Y B) r).ht (innerPt O.s O.Φ c)) := by
    have h1 := (GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ _ w hw
      (GlobalTheory.T.lattice_model_induces_root_metric D O hO.dualRef _ c W _ subset_rfl r)).2
    have h2 := (GlobalTheory.T.point_height_dual_and_linear_comb hE _ _ _ _ W.V.ar _ halg).1 _ _ h1
    rw [hwb] at h2
    show IsPtHt (W.root _ r).dual _ _
    convert h2 using 2
    simp [Setup.root0, Setup.adl0, adlOf]
  obtain ⟨Nn, hNn, hcN⟩ := HtTwist.exists_card (O.var c).str (innerPt O.s O.Φ c) hb
  have hNA : Nat.card {y : AlgPt (O.var c) // below y.1 = innerPt O.s O.Φ c} = Nn := hcN _ _
  have hcnt : ∀ σ : D.what₂.LL →+* ℂ, ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = innerPt O.s O.Φ c), (1:ℝ) = Nn := by
    intro σ
    have h1 : Nat.card {z : Pts (O.var c) σ // under z = innerPt O.s O.Φ c} = Nn := hcN ℂ σ
    have : Finite {z : Pts (O.var c) σ // under z = innerPt O.s O.Φ c} := Nat.finite_of_card_ne_zero (h1 ▸ hNn)
    have := Fintype.ofFinite {z : Pts (O.var c) σ // under z = innerPt O.s O.Φ c}
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    simp [← h1, Nat.card_eq_fintype_card]
  have hcard := GlobalTheory.Mean4O.CoverHt.card_emb W.V w hw
  rw [hwb, hNA] at hcard
  have hres : 0 < W.V.π.residueDegree w := by
    let := (W.V.π.residueFieldMap w).hom.toAlgebra
    have : Module.Finite ((O.var c).X.residueField (W.V.π w)) (W.V.G.residueField w) :=
      residueFieldMap_finite_of_locallyQuasiFinite W.V.π _
    exact Module.finrank_pos
  have hdeg : (0 : ℝ) < Module.finrank ℚ D.what₂.LL := Nat.cast_pos.2 Module.finrank_pos
  have hNr : (0 : ℝ) < Nn := Nat.cast_pos.2 (Nat.pos_of_ne_zero hNn)
  have hrr : (0 : ℝ) < W.V.π.residueDegree w := Nat.cast_pos.2 hres
  have hK0 : (Nat.card (W.V.X.residueField (W.V.j w) →+* ℂ) : ℝ) ≠ 0 := by
    rw [hcard]; positivity
  obtain ⟨hA, -⟩ := hE _ W.V.X W.V.p _ W.V.ar
  obtain ⟨ha, Ha⟩ := hA (W.gens (GlobalTheory.FlagAr.setB O.Y B) none)
  have hAm : IsPtHt (W.gens (GlobalTheory.FlagAr.setB O.Y B) none) (W.V.j w)
      (ha (W.V.j w) / Nat.card (W.V.X.residueField (W.V.j w) →+* ℂ)) := by
    refine ⟨ha, Ha, ?_⟩
    field_simp
  have hall := (GlobalTheory.T.point_height_dual_and_linear_comb hE _ _ _ _ W.V.ar _ halg).2 _
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc) (W.gens (GlobalTheory.FlagAr.setB O.Y B)))
    (fun o => o.elim (((∑ᶠ σ, ∑ᶠ y ∈ {y : GlobalTheory.CxPts W.V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = W.V.j w}, (T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ y) /
        (2 * (Nat.card (W.V.X.residueField (W.V.j w) →+* ℂ) : ℝ))))
      fun o' => o'.elim (ha (W.V.j w) / Nat.card (W.V.X.residueField (W.V.j w) →+* ℂ))
        fun r => -(O.root0 c (GlobalTheory.FlagAr.setB O.Y B) r).ht (innerPt O.s O.Φ c))
    (by rintro (_ | _ | r); exacts [hF, hAm, hR r])
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)
  obtain ⟨h', H', e'⟩ := hall
  rw [congrFun (HH.unique W.V.ar H') (W.V.j w), e']
  have hzoff : ∀ a (z : (T.M c).X a), under ((h.man c).pt a z) = W.V.π w → z ∉ (T.M c).Z a := by
    intro a z hz hm
    exact hbd (by rw [← hwb, ← hz]; exact (hman.Z a z).1 hm)
  have hsum := sum_over_cover _ _ W.V _ _ (h.man c) ε π hd w hw ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))
    (fun σ z => 2 * (O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z - O.Y.htDetT B c τ)) (by
      intro a z hz
      have hzZ := hzoff a z hz
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hgZ a z hzZ]
      exact congrArg (fun s => 2 * (s - O.Y.htDetT B c τ)) (hman.ph _ a z hzZ))
  rw [hwb] at hsum
  have hσ (σ : D.what₂.LL →+* ℂ) : ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = innerPt O.s O.Φ c),
      2 * (O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z - O.Y.htDetT B c τ) =
      2 * ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = innerPt O.s O.Φ c), O.chg c none (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ z +
        (-2 * O.Y.htDetT B c τ) * Nn := by
    rw [← hcnt σ, ← finsum_under_mul σ hb, ← finsum_under_mul σ hb, ← finsum_under_add σ hb]
    exact finsum_congr fun z => finsum_congr fun _ => by ring
  simp only [hσ, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul] at hsum
  have hdet := ht_det_eq D O hO A T Ht0 h B c τ _ hb hbd
  have ht : O.Y.htDetT B c τ = (adlOf (O.Φ.C c) (O.met.hm c)
      (detSym O.S.Dw (ArIn.ind (Pad.setB O.κ B)) none (DV.tauEmb D τ))).ht (innerPt O.s O.Φ c) := rfl
  rw [hNA] at hdet
  simp only [Fintype.sum_option, Option.elim, Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero, ite_mul,
    neg_one_mul, zero_mul, neg_neg, one_mul, zero_add]
  rw [hsum, hcard]
  rw [ht, hdet]
  field_simp
  ring

end GlobalTheory.FlatPoint
