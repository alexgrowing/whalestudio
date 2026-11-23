import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.Hcptgen
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLev
import Development.WeilBound.CoreStatements.HodgeTatePoints.FamprojAlg

noncomputable section

namespace PositivityTheory.HtPt.Famproj

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem genMap_fromSpecStalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ q)) ≫ X.fromSpecStalk q.1 = ξ := by
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) q.2
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h3 := Spec.map_comp (X.presheaf.stalkSpecializes q.2) (Scheme.stalkClosedPointTo ξ)
  refine Eq.trans (congrArg (· ≫ X.fromSpecStalk q.1) h3) ?_
  exact (Category.assoc _ _ _).trans ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h1).trans h2)

theorem regAt_loc {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] (k₀ : R →+* Ω) (hk : Function.Injective k₀) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom k₀) ≫ x = ξ) (p : PrimeSpectrum R) (hq : genPt ξ ⤳ x p) :
    ∀ r ∈ regAt ξ ⟨x p, hq⟩, ∃ t ∉ p.asIdeal, ∃ a, k₀ t * r = k₀ a := by
  let a₀ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  have hl : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  have hu : ∀ s : p.asIdeal.primeCompl, IsUnit (k₀ s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [hk (h.trans (map_zero k₀).symm)]; exact p.asIdeal.zero_mem)
  let ψ : ((Spec (CommRingCat.of R)).presheaf.stalk p) →+* Ω := IsLocalization.lift hu
  have hψ : ∀ a, ψ (algebraMap R _ a) = k₀ a := fun a => IsLocalization.lift_eq hu a
  have h1 := Scheme.SpecMap_stalkMap_fromSpecStalk x (x := p)
  have h2 : (Spec (CommRingCat.of R)).fromSpecStalk p =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p))) :=
    Spec.fromSpecStalk_eq' (CommRingCat.of R) p
  have h3 := genMap_fromSpecStalk ξ ⟨x p, hq⟩
  have hc : ψ.comp (x.stalkMap p).hom = genMap ξ ⟨x p, hq⟩ := by
    have e1 : Spec.map (CommRingCat.ofHom (ψ.comp (x.stalkMap p).hom)) ≫ X.fromSpecStalk (x p) =
        Spec.map (CommRingCat.ofHom (genMap ξ ⟨x p, hq⟩)) ≫ X.fromSpecStalk (x p) := by
      refine Eq.trans ?_ h3.symm
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      erw [h1]
      rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        show ψ.comp (algebraMap R _) = k₀ from RingHom.ext hψ, hx]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e1))
  rintro _ ⟨g, rfl⟩
  obtain ⟨⟨a, s⟩, hb⟩ := IsLocalization.surj p.asIdeal.primeCompl ((x.stalkMap p).hom g)
  refine ⟨s, s.2, a, ?_⟩
  rw [← hc, ← hψ, ← hψ, ← hb, map_mul, mul_comm]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt_sq_map (H : Host E) (τ : E →+* ℂ) : τ H.rt ^ 2 = -(H.d : ℂ) := by
  simpa using congrArg (fun w : 𝓞 E => τ w) H.rt_sq

theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : starRingEnd ℂ (τ H.rt) = τ H.rt := by
      rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]
    have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := rt_sq_map H τ
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
    rw [hr] at h3
    have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
    have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg r]
  · exact h

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  ext; rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_label {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] (j : c.F →+* Ω) (σ : E →+* Ω) :
    ∃ s, ∀ a : 𝓞 E, j (labelEmb c s (H.bar a)) = σ a := by
  obtain ⟨τ, rfl⟩ := exists_emb E c.F c.conj j σ
  have h3 : τ H.rt ^ 2 = H.rt0 ^ 2 := by rw [H.sqrt_neg_disc_sq, rt_sq_map]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
  · refine ⟨.inr ⟨τ, h⟩, fun a => ?_⟩
    change j (τ.codRestrict c.F (c.conj τ) (H.bar (H.bar a) : 𝓞 E)) = _
    rw [bar_bar]; rfl
  · refine ⟨.inl ⟨τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, fun a => ?_⟩
    · change τ (IsCMField.complexConj E H.rt) = _
      rw [← H.bar_eq, bar_rt]; simp [h]
    · refine congrArg j (Subtype.ext ?_)
      change τ (IsCMField.complexConj E (H.bar a : 𝓞 E)) = τ a
      rw [← H.bar_eq, bar_bar]

end

set_option maxHeartbeats 800000 in
theorem family_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → (∀ s, Module.Projective (chartRing o (mseg y) s.1) (Dc s).om' ∧ ∀ σ : E →+* Ω, Module.Projective (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) ∧ (∀ σ : E →+* Ω, ∃ d : Ω, ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) ∧ ∃ κ : Ω, IsCp p κ ∧ ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, κ ∈ chartRing o (mseg y) s.1 := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS hpq o _ _ ho Dc hF hfree
  obtain ⟨hchar, -, hprop, htate, -, -, hch⟩ := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho

  have hint : ∀ s, mseg y s ≠ 0 → ∀ z : Ω, IsIntegral ℤ z → z ∈ chartRing o (mseg y) s := fun s hs z hz => by
    obtain ⟨-, h1, h2, -⟩ := hch s hs
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := chartRing o (mseg y) s) hz.tower_top
    exact a.2
  have hσ : ∀ s, mseg y s ≠ 0 → ∀ (σ : E →+* Ω) (z : 𝓞 E), σ z ∈ chartRing o (mseg y) s := fun s hs σ z =>
    hint s hs _ (map_isIntegral_int σ (RingOfIntegers.isIntegral_coe z))

  have hunit : ∀ s (r : ℤ), ¬ (p : ℤ) ∣ r → ∃ u : chartRing o (mseg y) s, u * r = 1 := fun s r hr => by
    have hr0 : r ≠ 0 := fun h => hr (h ▸ dvd_zero _)
    obtain ⟨u, hu⟩ := (ho _).2 ⟨r.sign, r.natAbs, fun h => hr (Int.natCast_dvd.2 h), rfl⟩
    refine ⟨⟨_, (chartRing o (mseg y) s).algebraMap_mem u⟩, Subtype.ext ?_⟩
    have h1 : ((r.natAbs : ℕ) : Ω) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.2 hr0
    have h2 : ((r.sign : ℤ) : Ω) * r = (r.natAbs : ℕ) := by
      rw [← Int.cast_mul, Int.sign_mul_self_eq_natAbs, Int.cast_natCast]
    simp only [MulMemClass.coe_mul, hu, SubringClass.coe_intCast, OneMemClass.coe_one]
    rw [div_mul_eq_mul_div, h2, div_self h1]
  have hnm : ∀ s (m : Ideal (chartRing o (mseg y) s)), m.IsPrime → (p : chartRing o (mseg y) s) ∉ m →
      ∀ n : ℤ, n ≠ 0 → (n : chartRing o (mseg y) s) ∉ m := fun s m hm hpm n hn hnm => by
    obtain ⟨k, r, hr, rfl⟩ := WfDvdMonoid.max_power_factor' hn
      (show ¬ IsUnit (p : ℤ) from (Nat.prime_iff_prime_int.1 hp.out).not_isUnit)
    obtain ⟨u, hu⟩ := hunit s r hr
    push_cast at hnm
    rcases hm.mem_or_mem hnm with h | h
    · exact hpm (hm.mem_of_pow_mem _ h)
    · exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (hu ▸ m.mul_mem_left u h))

  have hpt : ∀ s, mseg y s ≠ 0 → ∀ m : Ideal (chartRing o (mseg y) s), m.IsPrime → (p : chartRing o (mseg y) s) ∈ m →
      ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s q ∧ InFibre 𝔐.ξ p q ∧ ∀ r ∈ regAt 𝔐.ξ q, ∃ t ∉ m,
        ∃ a : chartRing o (mseg y) s, algebraMap _ Ω t * r = algebraMap _ Ω a := fun s hs m hm hpm => by
    obtain ⟨-, -, -, x, hx, hr⟩ := hch s hs
    have hl := regAt_loc (algebraMap (chartRing o (mseg y) s) Ω) Subtype.val_injective x hx ⟨m, hm⟩ (𝔐.all _)
    refine ⟨⟨x ⟨m, hm⟩, 𝔐.all _⟩, ((hr _).1 ⟨_, rfl⟩).1, ?_, hl⟩
    rintro ⟨h0, -, h1⟩
    obtain ⟨t, ht, a, ha⟩ := hl _ h1
    refine ht ?_
    have : t = a * p := Subtype.ext (by
      change (t : Ω) * _ = (a : Ω) at ha
      simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, ← ha]
      field_simp)
    exact this ▸ m.mul_mem_left a hpm
  refine ⟨fun s => ?_, fun σ => ?_, ?_⟩
  · have hN := (hch s.1 s.2).1
    refine ⟨projective_of_factor fun m hm => ?_, fun σ => ?_⟩
    · have := hm.isPrime
      by_cases hpm : (p : chartRing o (mseg y) s.1) ∈ m
      · obtain ⟨q, hq, hq', hR⟩ := hpt s.1 s.2 m this hpm
        obtain ⟨U, hU, b, -, hb⟩ := hfree.1 q hq'
        obtain ⟨hb1, hb2⟩ := hb q hq' hU
        exact factor_of_frame Subtype.val_injective m _ hR _ (om'_fg _) b hb1
          ((hF.om'_loc s q hq hq').symm.trans hb2)
      · exact factor_om' _ m hpm
    · obtain ⟨s', hs'⟩ := exists_label c 𝔐.cst σ
      obtain ⟨e⟩ := nonempty_equiv_dual (𝔐.ρ.comp (H.bar : 𝓞 E →+* 𝓞 E)) (Dc s).ρΩ (hF.act s) σ (Dc s).om'
        (𝔐.Vgen s') (by
          ext x
          rw [LatBasic.mem_eigSp]
          simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
            sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
          refine ⟨fun h a => (h (H.bar a)).trans (congrArg (· • x) (hs' a)), fun h a => ?_⟩
          obtain ⟨a, rfl⟩ := H.bar.surjective a
          exact (h a).trans (congrArg (· • x) (hs' a).symm))
      refine projective_of_factor fun m hm => ?_
      have := hm.isPrime
      by_cases hpm : (p : chartRing o (mseg y) s.1) ∈ m
      · obtain ⟨q, hq, hq', hR⟩ := hpt s.1 s.2 m this hpm
        obtain ⟨U, hU, b, -, hb⟩ := hfree.2 s' q hq'
        obtain ⟨hb1, hb2⟩ := hb q hq' hU
        obtain ⟨N, i1, i2, i3, f, g, t, ht, hfg⟩ := factor_of_frame Subtype.val_injective m _ hR
          ((Dc s).om'.map ((𝔐.Vgen s').dualRestrict.restrictScalars _)) ((om'_fg _).map _) b hb1 (by
            rw [← hb2, Lat.map, hF.om'_loc s q hq hq', Submodule.map_span]
            rfl)
        exact ⟨N, i1, i2, i3, f ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ g, t, ht, fun x => by
          change e.symm (g (f (e x))) = _
          rw [hfg, map_smul]
          exact congrArg (t • ·) (e.symm_apply_apply x)⟩
      · obtain ⟨n, hn, hz⟩ := exists_den E
        refine factor_omHT _ m hpm σ n (hnm _ m this hpm n hn) fun k => ?_
        obtain ⟨z, hz⟩ := hz k
        exact ⟨⟨_, hσ s.1 s.2 σ z⟩, by
          change σ z = _
          rw [← hz]; simp⟩
  · obtain ⟨δ, hδ, r, hr, h⟩ := exists_diff_gen E p
    refine ⟨σ δ, fun s => ⟨⟨_, hσ s.1 s.2 σ δ⟩, rfl, le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)⟩⟩
    · rintro _ rfl
      exact ⟨δ, hδ, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := h x hx
      obtain ⟨u, hu⟩ := hunit s.1 r hr
      refine Submodule.mem_span_singleton.2 ⟨u * ⟨_, hσ s.1 s.2 σ z⟩, ?_⟩
      have h1 : (r : Ω) * σ x = σ z * σ δ := by simpa using congrArg (fun w : 𝓞 E => σ w) hz
      have h2 : (u : Ω) * r = 1 := by simpa using congrArg Subtype.val hu
      change (u : Ω) * σ z * σ δ = σ x
      rw [mul_assoc, ← h1, ← mul_assoc, h2, one_mul]
  · unfold IsCp
    split_ifs with h2
    · exact ⟨4, rfl, fun s => ofNat_mem _ 4⟩
    · obtain ⟨-, ζ, hζ, -⟩ := Htat.level_param E H D 𝔐.X 𝔐.t Ω 𝔐.ξ (p ^ 𝔐.R p)
        (Nat.one_le_pow _ _ hp.out.pos) hpq hprop (𝔐.tors p hpS) htate
      have hR := 𝔐.R_ge p hpS
      have h1 : IsPrimitiveRoot ((ζ : Ω) ^ p ^ (𝔐.R p - 1)) p :=
        (IsPrimitiveRoot.coe_units_iff.2 hζ).pow (pow_pos hp.out.pos _)
          (by rw [← pow_succ]; congr 1; omega)
      exact ⟨_, ⟨_, h1, rfl⟩, fun s => sub_mem (hint s.1 s.2 _ (h1.isIntegral hp.out.pos)) (one_mem _)⟩

end PositivityTheory.HtPt.Famproj
