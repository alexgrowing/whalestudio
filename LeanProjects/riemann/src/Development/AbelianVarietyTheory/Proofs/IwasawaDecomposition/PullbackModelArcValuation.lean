import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcTorusStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.PolArcExist

theorem j_s {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

instance isDominant_jK (R : Type) [CommRing R] [IsDomain R] : IsDominant (Out.jK R) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hz : (Out.jK R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R (FractionRing R)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (Out.jK R) := ⟨_, hz⟩
  exact closure_mono (Set.singleton_subset_iff.2 hmem)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal R) ≤ y.asIdeal from bot_le))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∃ χV : Sp (PowerSeries O') ⟶ pullback Z.s (spMap bV),
          χV ≫ f = χ₀ ∧ χV ≫ pullback.snd Z.s (spMap bV) = spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ h1 h2 h3 φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hbase hχ₀
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.power_series_arc_abelian_locus E H D l Xo c W Y O' b' χ₀ hχ₀.1 hχ₀.2.1
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.pullback_model_arc_torus E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ h1 h2 h3 φ m BD hhom hpol O' b' ϖ a χ₀
    hbase hχ₀ x₀ hx₀
  have hsub : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← spMap_comp]
    congr 1
    exact RingHom.ext fun x => hbV x

  have hgen : Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' =
      x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype := by
    rw [← hχ₀.1, ← Category.assoc, hx₀, Category.assoc, j_s]
  have hs : χ ≫ Z.s = (spMap (PowerSeries.C (R := O')) ≫ spMap b') ≫ spMap bV := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, j_s, ← hsub]
    simp only [← Category.assoc] at hgen ⊢
    rw [← hgen]
  let aj : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) (by rw [j_s, Category.assoc, hsub])
  have haj : aj ≫ f = Y.j := h2 aj (pullback.lift_fst _ _ _)
  refine ⟨pullback.lift χ _ hs, ?_, pullback.lift_snd _ _ _⟩
  have := isProper_toroidalModel_structureMap Y
  refine ext_of_isDominant_of_isSeparated Y.s ?_ (Out.jK (PowerSeries O')) ?_
  · rw [Category.assoc, h1, pullback.lift_snd, hχ₀.1]
  · have e : Out.jK (PowerSeries O') ≫ pullback.lift χ _ hs = x₀ ≫ aj := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hχ, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hgen]
    rw [← Category.assoc, e, Category.assoc, haj, hx₀]
end GlobalTheory.PolArcExist
