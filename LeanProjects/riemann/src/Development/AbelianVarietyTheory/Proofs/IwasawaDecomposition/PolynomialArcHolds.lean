import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcSectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcValuationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArc

theorem jK_asIdeal {R : Type} [CommRing R] [IsDomain R] (z : Sp (FractionRing R)) : (Out.jK R z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := by haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  change Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)

theorem exists_jK_eq {R : Type} [CommRing R] [IsDomain R] (x : Sp R) (hx : x.asIdeal = ⊥) :
    ∃ z : Sp (FractionRing R), Out.jK R z = x :=
  ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ((jK_asIdeal _).trans hx.symm)⟩

theorem polArc : PolArcSt := by
  intro E _ _ _ H D Xo s l c hg Z BD φ m hhom hdom hpol
  rw [arcChart_iff]
  intro O' _ _ _ b ϖ a hbase
  obtain ⟨p, W, hp, hW, bV, b', hbV, rfl⟩ := GlobalTheory.T.exists_p_adic_arc_base E H l c O' b ϖ hbase
  obtain ⟨f, t, m₁, m₂, h1, h2, h3⟩ := hdom p W hp hW bV hbV
  have hloc := ((s.clauses p W hp hW).2 ⟨l, c, hg p hp⟩).2.2
  rw [arcChart_iff] at hloc
  obtain ⟨χ₀, hχ₀, hspec₀⟩ := hloc O' b' ϖ (moveV bV hbV b' a) hbase
  have hR := GlobalTheory.T.pullback_model_arc_comparison E H D l (Xo l) c p W hp hW Z _ bV hbV f t m₁ m₂ h1 h2 h3
  have hS := GlobalTheory.T.pullback_model_arc_section E H D l (Xo l) c p W hp hW Z _ bV hbV f t m₁ m₂ h1 h2 h3
  have hA := GlobalTheory.T.pullback_model_arc_frame E H D l (Xo l) c p W hp hW Z _ bV hbV f t m₁ m₂ h1 h2 h3 O' b' a
  have hab : ∀ q, pullback.fst Z.s (spMap bV) q ∈ abLocus Z.t.G ↔ f q ∈ abLocus (s.Y p W hp hW ⟨l, c, hg p hp⟩).t.G :=
    fun q => (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 q).trans
      (abLocus_pullback abLocusOne (s.Y p W hp hW ⟨l, c, hg p hp⟩).t.semi m₂.cart.1 q).symm
  have key : ∀ χV : Sp (PowerSeries O') ⟶ pullback Z.s (spMap bV),
      χV ≫ pullback.snd _ _ = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
      (IsArcChart Z a ϖ (χV ≫ pullback.fst _ _) ↔ IsArcChart _ (moveV bV hbV b' a) ϖ (χV ≫ f)) := by
    intro χV h
    constructor
    · rintro ⟨-, k2, k3, k4⟩
      refine ⟨by rw [Category.assoc, h1, h], fun x => ?_, fun x hx => ?_, (hA _ _ _ _ _ h).1 k4⟩
      · rw [← k2 x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hab]
      · rw [Scheme.Hom.comp_apply, ← hR]
        exact k3 x hx
    · rintro ⟨-, k2, k3, k4⟩
      refine ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h, spMap_comp, Category.assoc],
        fun x => ?_, fun x hx => ?_, (hA _ _ _ _ _ h).2 k4⟩
      · rw [← k2 x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hab]
      · rw [Scheme.Hom.comp_apply, hR]
        exact k3 x hx
  obtain ⟨χV, hχV, hsnd⟩ := GlobalTheory.T.pullback_model_arc_valuation E H D l (Xo l) c p W hp hW Z _ bV hbV f t m₁ m₂ h1 h2 h3 φ m BD hhom hpol O' b'
    ϖ a χ₀ hbase ((hχ₀ χ₀).1 rfl)
  have hϖ : ϖ ≠ 0 := by
    rcases hbase with ⟨-, rfl⟩ | ⟨-, hi, -⟩
    · exact one_ne_zero
    · exact hi.ne_zero
  refine ⟨χV ≫ pullback.fst _ _, fun χ' => ⟨?_, ?_⟩, ?_⟩
  · rintro rfl
    exact (key χV hsnd).2 (hχV ▸ (hχ₀ χ₀).1 rfl)
  · intro hc
    have hlift : χ' ≫ Z.s = (spMap (PowerSeries.C (R := O')) ≫ spMap b') ≫ spMap bV := by
      rw [hc.1, spMap_comp, Category.assoc]
    have e : pullback.lift χ' _ hlift ≫ pullback.fst _ _ = χ' := pullback.lift_fst _ _ _
    have hc' := (key _ (pullback.lift_snd _ _ _)).1 (e.symm ▸ hc)
    have h0 : pullback.lift χ' _ hlift ≫ f = χV ≫ f := by rw [hχV]; exact (hχ₀ _).2 hc'
    rw [← e, hS _ _ χV (fun x hx => ?_) h0]
    rw [← Scheme.Hom.comp_apply, e]
    refine hc.2.2.1 x ?_
    rw [hx, Ideal.mem_bot]
    refine mul_ne_zero (fun h => hϖ ?_) PowerSeries.X_ne_zero
    simpa using congrArg (fun q : PowerSeries O' => PowerSeries.coeff 0 q) h
  · intro hirr y' ev hy' hgen hdata hev hevX
    have hl : y' ≫ Z.s = spMap b' ≫ spMap bV := by rw [hy', spMap_comp]
    have ey : pullback.lift y' _ hl ≫ pullback.fst _ _ = y' := pullback.lift_fst _ _ _
    have hsy : pullback.lift y' _ hl ≫ pullback.snd _ _ = spMap (RingHom.id O') ≫ spMap b' := by
      rw [pullback.lift_snd, show spMap (RingHom.id O') = 𝟙 _ from Spec.map_id (CommRingCat.of O'), Category.id_comp]
    have hdata' := (hA O' (Ideal.span {ϖ}) (RingHom.id O') ϖ _ hsy).1 (ey.symm ▸ hdata)
    have hgen' : Set.range (Out.jK O' ≫ pullback.lift y' _ hl ≫ f) ⊆
        Set.range (s.Y p W hp hW ⟨l, c, hg p hp⟩).j := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hR, ← Scheme.Hom.comp_apply, ey, ← Scheme.Hom.comp_apply]
      exact hgen ⟨z, rfl⟩
    have hsp := hspec₀ hirr _ ev (by rw [Category.assoc, h1, pullback.lift_snd]) hgen' hdata' hev hevX
    have e2 := hS O' (pullback.lift y' _ hl) (spMap ev ≫ χV) (fun x hx => ?_) (by rw [Category.assoc, hχV, hsp])
    · rw [← Category.assoc, ← e2, ey]
    · obtain ⟨z, rfl⟩ := exists_jK_eq x hx
      rw [← Scheme.Hom.comp_apply, ey, ← Scheme.Hom.comp_apply]
      exact hgen ⟨z, rfl⟩

end GlobalTheory.PolArc
