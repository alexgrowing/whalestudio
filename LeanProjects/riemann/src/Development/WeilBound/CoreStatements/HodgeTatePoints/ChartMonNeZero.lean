import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbGeo

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

section Label

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def prj (σ' : E →+* Ω) : 𝔐.Li →ₗ[Ω] 𝔐.Li := eigProj (𝔐.ρ.comp (H.bar : 𝓞 E →+* 𝓞 E)) σ'

variable {𝔐}

theorem mem_Vgen {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (x : 𝔐.Li) :
    x ∈ HT.eigSp (𝔐.ρ.comp (H.bar : 𝓞 E →+* 𝓞 E)) σ' ↔ x ∈ 𝔐.Vgen s := by
  rw [LatBasic.mem_eigSp]
  simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  refine ⟨fun h a => ?_, fun h a => h _⟩
  obtain ⟨a, rfl⟩ := H.bar.surjective a
  exact h a

theorem prj_mem {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (x : 𝔐.Li) :
    prj 𝔐 σ' x ∈ 𝔐.Vgen s := (mem_Vgen hσ _).1 (LatBasic.eigProj_mem _ _ x)

theorem prj_of_mem {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a))
    {x : 𝔐.Li} (hx : x ∈ 𝔐.Vgen s) : prj 𝔐 σ' x = x := LatBasic.eigProj_of_mem ((mem_Vgen hσ _).2 hx)

theorem eigProj_eq_comp (ρΩ : 𝓞 E →+* Module.End Ω (Module.Dual Ω 𝔐.Li))
    (h : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)) (σ' : E →+* Ω)
    (w : Module.Dual Ω 𝔐.Li) : eigProj ρΩ σ' w = w ∘ₗ prj 𝔐 σ' := by
  ext x
  simp [eigProj, prj, h, LinearMap.sum_apply]

theorem span_flag (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    Submodule.span Ω (Set.range (Fl.b s)) = 𝔐.Vgen s := by
  let q : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  obtain ⟨U, hU, b, hF, hb⟩ := Fl.sub s q trivial
  obtain ⟨U', hU', b', hV, hb'⟩ := 𝔐.vb s q trivial
  have h1 := (hb q trivial hU).2
  have h2 : 𝔐.V s q = _ := (hb' q trivial hU').2
  have h3 := congrArg (fun N : Submodule (regAt 𝔐.ξ q) 𝔐.Li => Submodule.span Ω (N : Set 𝔐.Li)) (h1.symm.trans h2)
  simp only [Submodule.span_span_of_tower] at h3
  rw [← flagStep_top, ← hF, flagStep_top, h3]
  exact hV

theorem li_flag (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) : LinearIndependent Ω (Fl.b s) := by
  obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
  exact h s

theorem charZero (𝔐 : HodgeCpt Y S y) : CharZero Ω :=
  (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance

variable {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]

theorem chart_le (hp : p.Prime)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {t : ∀ k, J k} {q : Cpt 𝔐.ξ} (hq : InChart 𝔐.ξ (mseg y) t q) (hz : OverZp 𝔐 p q) (a : Ω)
    (ha : a ∈ chartRing o (mseg y) t) : a ∈ regAt 𝔐.ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hq.2 j
  | algebraMap r =>
    obtain ⟨a, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    have hu := unitAt_nat q b (by rintro rfl; exact hb (dvd_zero _)) fun r hr hd => by
      by_contra hn
      exact hb (hz r hr hn ▸ hd)
    rw [h, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ a) hu.2.2
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem exists_pt (hp : p.Prime)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {t : ∀ k, J k} (ht : mseg y t ≠ 0) (m : Ideal (chartRing o (mseg y) t)) [hm : m.IsPrime] :
    ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) t q ∧ OverZp 𝔐 p q ∧
      ∀ z ∈ regAt 𝔐.ξ q, ∃ s ∉ m, ∃ a : chartRing o (mseg y) t, (s : Ω) * z = a := by
  haveI := charZero 𝔐
  obtain ⟨q, h1, h2, h3⟩ := exists_point (x := mseg y) 𝔐.tie t ht (chartRing o (mseg y) t)
    (fun j => Algebra.subset_adjoin ⟨j, rfl⟩) m
  refine ⟨q, h1, fun r hr hf => ?_, h2⟩
  by_contra hne
  refine hf (h3 r fun hrm => ?_)
  obtain ⟨u, hu⟩ := (ho ((1 : ℤ) / (r : Ω))).2 ⟨1, r, fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm, rfl⟩
  have : algebraMap o (chartRing o (mseg y) t) u * r = 1 := by
    apply Subtype.ext
    have hr0 : (r : Ω) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    show algebraMap o Ω u * ((r : chartRing o (mseg y) t) : Ω) = 1
    rw [hu]
    simp [hr0]
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (this ▸ m.mul_mem_left _ hrm))

theorem locFrame [Fact p.Prime] (hpS : p ∈ S)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (hfree : HTFree 𝔐 p) (Fl : 𝔐.Flag) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    (s : CMType H ⊕ CMType H) (σ' : E →+* Ω) (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (d : Ω) (hd : d ≠ 0)
    (g : Fin (labelRk D s) → Ω)
    (hfib : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ∀ e, e ∈ 𝔐.HT p s q ↔
      d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q)
    (hoff : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ¬ InFibre 𝔐.ξ p q →
      unitAt 𝔐.ξ q d ∧ ∀ x : E, σ' x ∈ regAt 𝔐.ξ q)
    (hg : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → ∀ i τ, ((𝔐.V s).gr (Fl.b s) i).IsGenAt q τ →
      τ / g i ∈ regAt 𝔐.ξ q ∧ g i / τ ∈ regAt 𝔐.ξ q)
    (m : Ideal (chartRing o (mseg y) t.1)) (hm : m.IsMaximal) :
    LocFrame m (prj 𝔐 σ') (Fl.b s) ((Dc t).omHT σ') d g := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq, hz, hR⟩ := exists_pt (𝔐 := 𝔐) hp ho t.2 m
  obtain ⟨U, hU, b, hF, hb⟩ := Fl.sub s q trivial
  have hb := hb q trivial hU
  have hbV : ∀ i, b i ∈ 𝔐.V s q := fun i => by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩
  have hbG : ∀ i, b i ∈ 𝔐.Vgen s := fun i => by
    rw [← span_flag Fl s, ← flagStep_top, ← hF, flagStep_top]; exact Submodule.subset_span ⟨i, rfl⟩
  have key : (∀ w ∈ (Dc t).om', ∀ i, d * w (b i) ∈ regAt 𝔐.ξ q) ∧
      ∀ w : Module.Dual Ω 𝔐.Li, w ∘ₗ prj 𝔐 σ' = w → (∀ i, d * w (b i) ∈ regAt 𝔐.ξ q) →
        ∃ w₀ ∈ Submodule.span (regAt 𝔐.ξ q) ((Dc t).om' : Set (Module.Dual Ω 𝔐.Li)), w₀ ∘ₗ prj 𝔐 σ' = w := by
    by_cases hf : InFibre 𝔐.ξ p q
    · have hV : 𝔐.V s q = 𝔐.HT p s q :=
        Lat.patch_of_unique S _ _ hpS hf fun p' hp' h => hz p' (𝔐.S_prime p' hp') h
      have hom := hD.om'_loc t q hq hf
      constructor
      · intro w hw i
        have h1 := (hfib q hq hz _).1 (hV ▸ hbV i)
        have h2 := ((𝔐.M.mem_htDual_iff _ _ _ _ q _).1 h1).2 w (by
          show w ∈ omP 𝔐 p q
          rw [hom]; exact Submodule.subset_span hw)
        simpa using h2
      · intro w hw hreg
        obtain ⟨U', hU', f, hfs, hf'⟩ := hfree.2 s q hf
        have hf' := hf' q hf hU'
        haveI : FiniteDimensional Ω (𝔐.Vgen s) := by
          rw [← span_flag Fl s]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range _)
        have h1 := mem_span_of_dual (regAt 𝔐.ξ q) f hf'.1 hfs ((𝔐.Vgen s).dualRestrict w) fun e he => by
          have h2 : (e : 𝔐.Li) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
            refine (𝔐.M.mem_htDual_iff _ _ _ _ q _).2 ⟨e.2, fun w' hw' => ?_⟩
            have h3 : (𝔐.Vgen s).dualRestrict w' ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range f) := by
              rw [← hf'.2]; exact ⟨w', hw', rfl⟩
            exact apply_mem_of_span (regAt 𝔐.ξ q) (Module.Dual.eval Ω _ e) _ (by rintro _ ⟨j, rfl⟩; exact he j) _ h3
          have h4 : d⁻¹ • (e : 𝔐.Li) ∈ 𝔐.V s q := by
            rw [hV, hfib q hq hz, smul_smul, mul_inv_cancel₀ hd, one_smul]; exact h2
          rw [hb.2] at h4
          have h5 := apply_mem_of_span (regAt 𝔐.ξ q) (d • w) _ (by rintro _ ⟨j, rfl⟩; exact hreg j) _ h4
          simpa [inv_mul_cancel_left₀ hd] using h5
        rw [← hf'.2] at h1
        obtain ⟨w₀, hw₀, h2⟩ := h1
        refine ⟨w₀, hom ▸ hw₀, ?_⟩
        rw [← hw]
        ext x
        exact LinearMap.congr_fun h2 ⟨_, prj_mem hσ x⟩
    · have hV : 𝔐.V s q = 𝔐.dR s q :=
        Lat.patch_of_not S _ _ fun p' hp' h => hf (hz p' (𝔐.S_prime p' hp') h ▸ h)
      obtain ⟨hdu, hσR⟩ := hoff q hq hz hf
      have hom := hD.om_loc t q hq hz
      have hpu : unitAt 𝔐.ξ q (p : Ω) := not_not.1 hf
      constructor
      · intro w hw i
        have h1 : (Dc t).om' ≤ (Dc t).om := sup_le (Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (Dc t).h_mem x))
          (by rintro _ ⟨x, hx, rfl⟩; exact (Dc t).om.smul_mem _ hx)
        have h2 : w ∈ 𝔐.M.omLat q := by rw [hom]; exact Submodule.subset_span (h1 hw)
        exact mul_mem hdu.2.1 (h2 _ (hV ▸ hbV i : b i ∈ 𝔐.dR s q).1)
      · intro w hw hreg
        refine ⟨w, ?_, hw⟩
        have h1 : w ∈ 𝔐.M.omLat q := by
          intro e he
          have h2 : prj 𝔐 σ' e ∈ 𝔐.V s q := by
            rw [hV]
            refine ⟨?_, prj_mem hσ e⟩
            simp only [prj, eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
            refine Submodule.sum_mem _ fun k _ => ?_
            haveI := 𝔐.t.act.hom (H.bar (RingOfIntegers.basis E k))
            exact Submodule.smul_mem (𝔐.M.lat q) (⟨_, hσR _⟩ : regAt 𝔐.ξ q)
              (lat_stable 𝔐.M _ _ (𝔐.act (H.bar (RingOfIntegers.basis E k))) q e he)
          rw [hb.2] at h2
          rw [← hw]
          refine apply_mem_of_span (regAt 𝔐.ξ q) w _ ?_ _ h2
          rintro _ ⟨j, rfl⟩
          have := mul_mem hdu.2.2 (hreg j)
          rwa [inv_mul_cancel_left₀ hd] at this
        rw [hom] at h1
        refine Submodule.span_le.2 ?_ h1
        intro x hx
        have h3 : ((p : chartRing o (mseg y) t.1) ^ 𝔐.R p) • x ∈ (Dc t).om' :=
          Submodule.mem_sup_right ⟨x, hx, rfl⟩
        have h4 := Submodule.smul_mem (Submodule.span (regAt 𝔐.ξ q) ((Dc t).om' : Set (Module.Dual Ω 𝔐.Li)))
          (⟨_, pow_mem hpu.2.2 (𝔐.R p)⟩ : regAt 𝔐.ξ q) (Submodule.subset_span h3)
        have h5 : ((p : Ω)⁻¹ ^ 𝔐.R p) • (((p : chartRing o (mseg y) t.1) ^ 𝔐.R p : chartRing o (mseg y) t.1) : Ω) • x
            = x := by
          rw [smul_smul]
          simp [hpu.1]
        exact h5 ▸ h4
  have hP := eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ'
  refine ⟨regAt 𝔐.ξ q, hR, b, hb.1, hF, fun i => ?_, ?_, fun w hw hreg => ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_lead (Fl.b s) b hF i
    have h1 := FlagGrGen.gr_isGenAt _ _ _ _ (𝔐.V s) _ (Fl.b s) b q i τ (li_flag Fl s) hF hb hτ
    exact ⟨τ, hτ, (hg q hq i τ h1).1, (hg q hq i τ h1).2, h1.1⟩
  · rintro _ ⟨w, hw, rfl⟩ i
    show d * eigProj (Dc t).ρΩ σ' w (b i) ∈ _
    rw [hP, LinearMap.comp_apply, prj_of_mem hσ (hbG i)]
    exact key.1 w hw i
  · obtain ⟨w₀, h0, rfl⟩ := key.2 w hw hreg
    refine exists_smul_mem m (regAt 𝔐.ξ q) hR _ _ ?_
    rw [← hP]
    clear hw hreg
    induction h0 using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      have : eigProj (Dc t).ρΩ σ' (c • x) = c • eigProj (Dc t).ρΩ σ' x := map_smul _ (c : Ω) x
      rw [this]; exact Submodule.smul_mem _ c hx

theorem label_basis [Fact p.Prime] (hpS : p ∈ S)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (hfree : HTFree 𝔐 p) (Fl : 𝔐.Flag) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    (s : CMType H ⊕ CMType H) (σ' : E →+* Ω) (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (d : Ω) (hd : d ≠ 0)
    (g : Fin (labelRk D s) → Ω) (hg0 : ∀ i, g i ≠ 0)
    (hfib : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ∀ e, e ∈ 𝔐.HT p s q ↔
      d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q)
    (hoff : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ¬ InFibre 𝔐.ξ p q →
      unitAt 𝔐.ξ q d ∧ ∀ x : E, σ' x ∈ regAt 𝔐.ξ q)
    (hg : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → ∀ i τ, ((𝔐.V s).gr (Fl.b s) i).IsGenAt q τ →
      τ / g i ∈ regAt 𝔐.ξ q ∧ g i / τ ∈ regAt 𝔐.ξ q) :
    ∃ n : Module.Basis (Fin (labelRk D s)) (chartRing o (mseg y) t.1) ((Dc t).omHT σ'),
      ∀ i, (∀ j < i, (n i).1 (Fl.b s j) = 0) ∧ (n i).1 (Fl.b s i) = (d * g i)⁻¹ := by
  refine exists_basis_frames (prj 𝔐 σ') (Fl.b s) (fun e => span_flag Fl s ▸ prj_mem hσ e)
    (fun e he => prj_of_mem hσ (span_flag Fl s ▸ he)) _ ?_ d hd g hg0
    (locFrame hpS ho hD hfree Fl t s σ' hσ d hd g hfib hoff hg)
  rintro _ ⟨w, -, rfl⟩
  show eigProj (Dc t).ρΩ σ' w ∘ₗ _ = eigProj (Dc t).ρΩ σ' w
  rw [eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ']
  ext x
  simp only [LinearMap.comp_apply, prj_of_mem hσ (prj_mem hσ x)]

theorem omHT_comp {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) :
    ∀ w ∈ (Dc t).omHT σ', w ∘ₗ prj 𝔐 σ' = w := by
  rintro _ ⟨w, -, rfl⟩
  show eigProj (Dc t).ρΩ σ' w ∘ₗ _ = eigProj (Dc t).ρΩ σ' w
  rw [eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ']
  ext x
  simp only [LinearMap.comp_apply, prj_of_mem hσ (prj_mem hσ x)]

theorem diff_facts {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) :
    (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∃ a : A, σ δ = a * ds) ∧ (ds : Ω) ≠ 0 ∧
      (ds : Ω) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have h1 : ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∃ a : A, σ δ = a * ds := by
    intro δ hδ
    have : σ δ ∈ Submodule.span A {algebraMap A Ω ds} := by
      rw [h]; exact Submodule.subset_span ⟨δ, hδ, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, ha.symm⟩
  refine ⟨h1, fun h0 => ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
    obtain ⟨a, ha⟩ := h1 x hx
    rw [h0, mul_zero, map_eq_zero] at ha
    exact hx0 (by exact_mod_cast ha)
  · rw [← h]; exact Submodule.mem_span_singleton_self _

theorem off_facts {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) {q : Cpt 𝔐.ξ}
    (hA : ∀ a ∈ A, a ∈ regAt 𝔐.ξ q) (hz : OverZp 𝔐 p q) (hf : ¬ InFibre 𝔐.ξ p q) :
    unitAt 𝔐.ξ q (ds : Ω) ∧ ∀ x : E, σ x ∈ regAt 𝔐.ξ q := by
  obtain ⟨h1, h0, -⟩ := diff_facts h
  have key : ∀ x : E, ∃ u ∈ regAt 𝔐.ξ q, σ x = u * ds := by
    intro x
    obtain ⟨n, hn, δ, hδ, hx⟩ := exists_nat_diff x
    obtain ⟨a, ha⟩ := h1 δ hδ
    have hu := unitAt_nat q n hn fun r hr _ => by
      by_contra hr'
      exact hf (hz r hr hr' ▸ hr')
    refine ⟨(n : Ω)⁻¹ * a, mul_mem hu.2.2 (hA _ a.2), ?_⟩
    rw [_root_.mul_assoc, ← ha, hx, map_mul, map_natCast, inv_mul_cancel_left₀ hu.1]
  refine ⟨⟨h0, hA _ ds.2, ?_⟩, fun x => ?_⟩
  · obtain ⟨u, hu, h2⟩ := key 1
    rw [map_one] at h2
    rwa [← eq_inv_of_mul_eq_one_left h2.symm]
  · obtain ⟨u, hu, h2⟩ := key x
    rw [h2]; exact mul_mem hu (hA _ ds.2)

theorem mem_htW {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) {q : Cpt 𝔐.ξ}
    (hA : ∀ a ∈ A, a ∈ regAt 𝔐.ξ q) (σ₀ : 𝓞 E →+* Ω) (hσ : ∀ a : 𝓞 E, σ (a : E) = σ₀ a) (n : ℕ) (e : 𝔐.Li) :
    e ∈ 𝔐.M.htW 𝔐.t.PP.L n 𝔐.ρ σ₀ (differentIdeal ℤ (𝓞 E)) q ↔
      (ds : Ω) • e ∈ 𝔐.M.htDual 𝔐.t.PP.L n 𝔐.ρ σ₀ q := by
  obtain ⟨h1, h0, h2⟩ := diff_facts h
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx =>
      generalize (ds : Ω) = z at h2
      induction h2 using Submodule.span_induction with
      | mem u hu => obtain ⟨δ, hδ, rfl⟩ := hu; rw [hσ]; exact hx.2 δ hδ
      | zero => rw [zero_smul]; exact zero_mem _
      | add u v _ _ hu hv => rw [add_smul]; exact add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) • x = (⟨a, hA _ a.2⟩ : regAt 𝔐.ξ q) • u • x := mul_smul (a : Ω) u x
        rw [this]; exact Submodule.smul_mem _ _ hu
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (ds : Ω) • a • x = a • (ds : Ω) • x := smul_comm (ds : Ω) (a : Ω) x
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro he
    refine Submodule.subset_span ⟨?_, fun δ hδ => ?_⟩
    · have := (GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ σ₀).smul_mem (ds : Ω)⁻¹ (𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he)
      rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
    · obtain ⟨a, ha⟩ := h1 δ hδ
      rw [← hσ, ha, mul_smul]
      exact Submodule.smul_mem _ (⟨a, hA _ a.2⟩ : regAt 𝔐.ξ q) he

theorem chartMon_ne_zero {t : ∀ k, J k} (ht : mseg y t ≠ 0) (a : K → ℤ) : chartMon y t a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 ht k hk)

theorem rootIdx_left (τ : CMType H) (a : Fin D.p) :
    HodgeCpt.rootIdx D (τ, Fin.castAdd D.q a) = ⟨.inl τ, a⟩ := dif_pos a.2

theorem rootIdx_right (τ : CMType H) (a : Fin D.q) :
    HodgeCpt.rootIdx D (τ, Fin.natAdd D.p a.rev) = ⟨.inr τ, a⟩ := by
  unfold HodgeCpt.rootIdx
  rw [dif_neg (by simp)]
  congr 1
  apply Fin.ext
  have := a.2
  simp only [Fin.val_natAdd, Fin.val_rev]
  omega

end Label

theorem chart_flag_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (σ : E →+* Ω) (d : Ω), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → Fl.RootLines xdeg e → (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) → ∃ (wW : Fin D.p → Module.Dual Ω (Module.Dual Ω 𝔐.Li)) (wM : Fin D.q → Module.Dual Ω 𝔐.Li), ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ (bW : Module.Basis (Fin D.p) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp (cmConj E).toRingHom)))) (bM : Module.Basis (Fin D.q) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)), (∀ a : Fin D.p, ∃ cf : Fin D.p → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (xdeg (τ, Fin.castAdd D.q a)) ∧ ∀ z : (Dc s).omHT (σ.comp (cmConj E).toRingHom), (bW a z).1 = ∑ a', cf a' * wW a' z.1) ∧ ∀ a : Fin D.q, ∃ cf : Fin D.q → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (xdeg (τ, Fin.natAdd D.p a)) ∧ (bM a).1 = ∑ a', cf a' • wM a' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS o _ _ ho Dc Fl xdeg e τ σ d hD hfree hroot hσ hdiff
  have he : ∀ r, e r ≠ 0 := fun r => (hroot r).1
  have hbb : ∀ a : 𝓞 E, H.bar (H.bar a) = a := fun a => by
    apply Subtype.ext
    show ((H.bar (H.bar a) : 𝓞 E) : E) = a
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hσM : ∀ a : 𝓞 E, σ a = 𝔐.emb (.inr τ) (H.bar a) := fun a => by
    rw [hσ]
    show _ = 𝔐.emb (.inl τ) (H.bar (H.bar a))
    rw [hbb]
  have hσW : ∀ a : 𝓞 E, σ.comp (cmConj E).toRingHom a = 𝔐.emb (.inl τ) (H.bar a) := fun a => by
    rw [← hσ, H.bar_eq]; rfl
  obtain ⟨wM, hwM⟩ := shape_M (o := o) (r := D.q) (prj 𝔐 σ) (Fl.b (.inr τ)) (li_flag Fl _)
    (fun x => by have := prj_mem hσM x; rw [← span_flag Fl] at this; exact this)
    (fun a => e (τ, Fin.natAdd D.p a)) (fun a => he _)
  refine ⟨fun a => Module.Dual.eval Ω _ ((d * e (τ, Fin.castAdd D.q a)) • Fl.b (.inl τ) a), wM, fun t => ?_⟩
  obtain ⟨ds, rfl, hds⟩ := hdiff t
  have hd0 := (diff_facts hds).2.1
  have hm := fun r => chartMon_ne_zero t.2 (xdeg r)
  obtain ⟨nW, hnW⟩ := label_basis hpS ho hD hfree Fl t (.inl τ) _ hσW ds hd0
    (fun a : Fin D.p => chartMon y t.1 (xdeg (τ, Fin.castAdd D.q a)) * e (τ, Fin.castAdd D.q a))
    (fun a => mul_ne_zero (hm _) (he _))
    (fun q hq hz x => mem_htW hds (chart_le hp.out ho hq hz) _ hσ _ x)
    (fun q hq hz hf => ⟨(off_facts hds (chart_le hp.out ho hq hz) hz hf).1,
      fun x => (off_facts hds (chart_le hp.out ho hq hz) hz hf).2 _⟩)
    (fun q hq (a : Fin D.p) u hu => by
      have h1 := (hroot (τ, Fin.castAdd D.q a)).2 q trivial t.1 hq
      have h2 : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q a) = 1 := if_pos a.2
      unfold HodgeCpt.Flag.rootLat at h1
      rw [rootIdx_left, h2] at h1
      have h3 := tens_gen _ q 1 (Or.inl rfl) u _ hu h1
      rw [zpow_one] at h3
      exact h3)
  obtain ⟨nM, hnM⟩ := label_basis hpS ho hD hfree Fl t (.inr τ) _ hσM 1 one_ne_zero
    (fun a : Fin D.q => (chartMon y t.1 (xdeg (τ, Fin.natAdd D.p a.rev)) * e (τ, Fin.natAdd D.p a.rev))⁻¹)
    (fun a => inv_ne_zero (mul_ne_zero (hm _) (he _)))
    (fun q hq hz x => by rw [one_smul]; rfl)
    (fun q hq hz hf => ⟨⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩,
      (off_facts hds (chart_le hp.out ho hq hz) hz hf).2⟩)
    (fun q hq (a : Fin D.q) u hu => by
      have h1 := (hroot (τ, Fin.natAdd D.p a.rev)).2 q trivial t.1 hq
      have h2 : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p a.rev) = -1 := if_neg (by simp)
      unfold HodgeCpt.Flag.rootLat at h1
      rw [rootIdx_right, h2] at h1
      have h3 := tens_gen _ q (-1) (Or.inr rfl) u _ hu h1
      rw [zpow_neg_one] at h3
      have e1 : ∀ x : Ω, u / x⁻¹ = x / u⁻¹ := fun x => by rw [div_inv_eq_mul, div_inv_eq_mul, mul_comm]
      have e2 : ∀ x : Ω, x⁻¹ / u = u⁻¹ / x := fun x => by rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm]
      rw [e1, e2]
      exact ⟨h3.2, h3.1⟩)
  obtain ⟨bW, hbW⟩ := shape_alt (r := D.p) (Fl.b (.inl τ)) (fun a => ds * e (τ, Fin.castAdd D.q a))
    (fun a => mul_ne_zero hd0 (he _)) _ (fun a => chartMon y t.1 (xdeg (τ, Fin.castAdd D.q a))) (fun a => hm _) nW
    (fun i => ⟨(hnW i).1, (hnW i).2.trans (by rw [mul_left_comm])⟩)
  obtain ⟨bM, hbM⟩ := hwM _ _ (omHT_comp hD t hσM) (fun a => chartMon y t.1 (xdeg (τ, Fin.natAdd D.p a))) nM
    (fun i => ⟨(hnM i).1, (hnM i).2.trans (by rw [_root_.one_mul, inv_inv])⟩)
  exact ⟨bW, bM, hbW, hbM⟩

end PositivityTheory.HtPt.Flagb
