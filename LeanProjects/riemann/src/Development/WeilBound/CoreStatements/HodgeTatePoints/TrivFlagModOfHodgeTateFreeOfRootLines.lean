import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.GeTriv
import Development.WeilBound.CoreStatements.HodgeTatePoints.ChartMonNeZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.Famproj
import Development.WeilBound.CoreStatements.HodgeTatePoints.Hcptgen
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankDualEqOfProjective
import Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInSStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartTransitionIntegralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosedStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem triv_flag_mod_of_hodge_tate_free_of_root_lines (hb : FarguesHodgeTate → PointHT)
    (hl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ) :
    FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) := by
  intro hF E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho Fl xdeg e hfree hroot τ
  have hgen := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  haveI : CharZero Ω := hgen.1
  have hA := hgen.2.2.2.2.2.2
  obtain ⟨Dc, hfam, htest⟩ := hl E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho
  obtain ⟨hproj, hdiff, κ, hκ, hκA⟩ := Famproj.family_proj E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho Dc hfam hfree
  have hPHT : PointHT := hb hF
  have hR : 4 ≤ 𝔐.R p := 𝔐.R_ge p hpS
  have hc : ∀ x : E, cmConj E (cmConj E x) = x := fun x => by simp
  let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
  have hσ : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
  obtain ⟨d, hd⟩ := hdiff σ
  obtain ⟨d', hd'⟩ := hdiff (σ.comp (cmConj E).toRingHom)
  obtain ⟨wW, wM, hb⟩ := Flagb.chart_flag_bases E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc Fl xdeg e τ σ d hfam hfree hroot hσ hd
  choose dd hdd using hd
  choose dd' hdd' using hd'
  choose bW bM hbW hbM using hb
  have hρe : ∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e := by
    intro s t
    refine ⟨?_, hfam.e_eq s t⟩
    ext a w : 2
    rw [hfam.act s, hfam.act t]
  have hint : ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1 := by
    intro s σ' a
    obtain ⟨hN, hIC, hFR, -⟩ := hA s.1 s.2
    obtain ⟨b, hb⟩ := GlobalTheory.T.number_field_integers_in_integrally_closed (chartRing o (mseg y) s.1) Ω E σ' a
    rw [← hb]; exact b.2
  have hcs : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ i, (Dc s).IsDualMap σ (dd s) (𝔐.R p - 2) i ∧ (Dc s).ExactMod σ (𝔐.R p - 2) i ∧ (∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) ∧ ∀ x ∈ (Dc s).om, ((p : Ω) ^ 2) • x ∈ (Dc s).om' := by
    intro s
    obtain ⟨hN, hIC, hFR, -⟩ := hA s.1 s.2
    let κs : chartRing o (mseg y) s.1 := ⟨κ, hκA s⟩
    have hk2 : κs ∣ (p : chartRing o (mseg y) s.1) ^ 2 := GlobalTheory.T.cp_element_divides_prime_sq (chartRing o (mseg y) s.1) Ω p κs hκ
    have hkR : κs * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) ∣ (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) := by
      have : (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) = (p : chartRing o (mseg y) s.1) ^ 2 * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; exact mul_dvd_mul_right hk2 _
    have hcs := chart_sequence (chartRing o (mseg y) s.1) Ω E (cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) (Dc s) κs (𝔐.R p - 2) hkR (htest s κs hPHT hκ) (hproj s).1
    obtain ⟨i, hi1, hi2⟩ := hcs.2 σ (dd s) (dd' s) (hdd s).2 (hdd' s).2 ((hproj s).2 σ) ((hproj s).2 _)
    have hq := Ga.q_surj (chartRing o (mseg y) s.1) Ω Subtype.val_injective E (cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) (Dc s) κs σ (𝔐.R p - 2) (fun a => ⟨⟨_, hint s σ a⟩, rfl⟩) hkR hcs.1.2
    refine ⟨i, hi1, hi2, hq.1, ?_⟩
    intro x hx
    obtain ⟨r, hr⟩ := hk2
    have h1 := (Dc s).om'.smul_mem r (hcs.1.2 x hx)
    have h2 : r • κs • x = ((p : Ω) ^ 2) • x := by
      clear hgen hA hbW hbM hcs hq hi1 hi2 h1 htest hproj
      rw [smul_smul, mul_comm r, ← hr, ← algebraMap_smul Ω]
      simp
    rwa [h2] at h1
  choose i hi using hcs
  have hom : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om :=
    fun s t x hx => GlobalTheory.T.hodge_component_integral_at_prime_in_S E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc hfam s t x
      (fun q hs _ hz => (hfam.om_iff s x).1 hx q hs hz)
  have hh : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ (𝔐.R p)) • w := by
    intro s t x
    have hp0 : ((p : Ω) ^ (𝔐.R p)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    obtain ⟨n, hn⟩ := GlobalTheory.T.hodge_component_integral_at_prime_in_S E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc hfam s t (((p : Ω) ^ (𝔐.R p))⁻¹ • ((Dc s).h x - (Dc t).h x)) (by
      intro q hs ht hz
      obtain ⟨w, hw, he⟩ := hfam.glue s t q hs ht hz x
      rw [he, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul Ω, smul_smul, Nat.cast_pow, inv_mul_cancel₀ hp0, one_smul]
      exact hw)
    refine ⟨n, _, hn, ?_⟩
    rw [smul_comm ((p : Ω) ^ (𝔐.R p)) ((mseg y s.1 / mseg y t.1) ^ n), smul_smul ((p : Ω) ^ (𝔐.R p)) ((p : Ω) ^ (𝔐.R p))⁻¹, mul_inv_cancel₀ hp0, one_smul]
  have hovl1 := GlobalTheory.T.hodge_chart_transition_integral o Ω K J y E (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) Dc hom hh (fun s t => (hρe s t).1) (fun s t a ha => GlobalTheory.T.chart_ring_mem_after_monomial_scaling o Ω K J y s.1 t.1 s.2 t.2 a ha)
  have hovl2 : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ (𝔐.R p - 2)) • z := by
    intro s t σ' x
    obtain ⟨n, w, hw, he⟩ := hh s t x
    refine ⟨n, eigProj (Dc t).ρΩ σ' (((p : Ω) ^ 2) • w), ⟨_, (hi t).2.2.2 w hw, rfl⟩, ?_⟩
    rw [← LinearMap.map_smul, he, ← LinearMap.map_smul, smul_smul, ← pow_add]
    congr 3
    omega
  exact trivflag_charts o Ω K J y E (cmConj E) hc p (𝔐.R p) (𝔐.R p - 2) D.p D.q (Module.Dual Ω 𝔐.Li) Dc σ d dd i bW bM wW wM (fun i => xdeg (τ, i)) (fun s => (hA s.1 s.2).2.2.1) hint (fun s => hdd s) hρe hovl1 hovl2 (fun s => ⟨(hi s).1, (hi s).2.1, (hi s).2.2.1⟩) (Nat.sub_le _ _) (fun s a => hbW s a) (fun s a => hbM s a)

end PositivityTheory.HtPt.Ge
