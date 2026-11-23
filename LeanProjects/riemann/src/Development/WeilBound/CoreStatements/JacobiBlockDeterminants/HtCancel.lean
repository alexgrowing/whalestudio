import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HodgeCompactPullback
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HcptPullK

noncomputable section

namespace HeightCancellation

theorem ht_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' S'' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m : SABMap t' t f)
    (n : SABMap t'' t k) (e : k = g ≫ f) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n

set_option maxHeartbeats 1000000 in
theorem stHt : SquareStatements.StHt := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' _ _ y y' A A' h i j ⟨hdom, hf, hcst, hext, hjo⟩ hR _ hvb
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y A hmono
  obtain ⟨x, hx⟩ : ∃ x : Sp Ω ⟶ Xo.XF c, A.ξ ≫ A.f = x ≫ Y.j := ⟨spMap A.fn ≫ x₀, by
    rw [Category.assoc, ← hx₀]
    exact A.fn_over⟩
  have hgen := A.tie.gen
  have hgen' := A'.tie.gen
  obtain ⟨mh, hmh⟩ := ht_cancel A.m A'.m hf
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.lie_model_pullback_map A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M hdom mh.cart
  have hjj : ∀ w, j w = j₀ w := fun w => by
    apply A'.M.inj
    apply Over.OverMorphism.ext
    apply A'.m.cart.1.hom_ext
    · refine (hjo w).trans ?_
      show _ = (A'.M.pt (j₀ w)).left ≫ A'.m.φ
      rw [hmh, ← Category.assoc (A'.M.pt (j₀ w)).left, hj₀ w, Category.assoc]
    · rw [Over.w, Over.w]
  have hj : ∀ e, (A'.M.pt (j e)).left ≫ mh.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (A.M.pt e).left :=
    fun e => by rw [hjj e]; exact hj₀ e
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨-, hspan, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M j (𝓞 E) A.t.act.act A'.t.act.act A.ρ A'.ρ
    hdom mh.cart hj A.act A'.act (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li A'.Li j hext hspan
  have hW : ∀ s, eigSp A'.ρ ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li A'.Li j A.ρ A'.ρ (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ A'.X Ω' A'.ξ h i hdom
  have hsp : ∀ p' : Cpt A'.ξ, genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt A'.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt A'.ξ p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt A'.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt A'.ξ p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt A'.ξ), InFibre A'.ξ p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω' A'.ξ ℤ _ _ A'.tie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt A'.ξ, IsIntegrallyClosed (A'.X.presheaf.stalk q.1) := fun q => (A'.normal q.1).2
  have htors : ∀ p ∈ S, FullTorsion A'.t.G A'.ξ (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ _ hdom mh.cart (A.tors p hp)

  have hω : ∀ p ∈ S, ∀ p' : Cpt A'.ξ, 0 < D.p + D.q → A'.M.htOm A'.t.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt A'.ξ p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A'.X A'.f A'.t A'.m Ω' A'.ξ (spMap i ≫ x) (by
      rw [hf, ← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A'.X Ω' A'.ξ s0' o' A'.t m0' A'.Li A'.M (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := PositivityTheory.UnitarySelfGeneration.height_pullback_dominating_map A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq A'.ξ h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  intro p hp s
  have e1 : A'.Vgen s = eigSp A'.ρ ((i.comp A.cst).comp (labelEmb c s)) := by
    rw [← hcst]; rfl
  rw [hR]
  exact GlobalTheory.T.lattice_flag_field_extension A.X A'.X Ω Ω' A.ξ A'.ξ h i A.Li A'.Li j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
    (A'.M.htOm A'.t.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre A'.ξ p q} (labelRk D s) hdom hgen' hext hjd
    (e1.trans (hW s)) (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩

end HeightCancellation
