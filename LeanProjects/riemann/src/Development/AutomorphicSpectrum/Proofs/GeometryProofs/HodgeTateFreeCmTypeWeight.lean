import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeLowerStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeUpperStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTateStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualActionCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralOverRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegralityStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentReductionAtPStatement

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles Module GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

theorem exists_zp (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] : ∃ o : Subring Ω, ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  have hp : p.Prime := Fact.out
  have hmul : ∀ {b b' : ℕ}, ¬ p ∣ b → ¬ p ∣ b' → ¬ p ∣ b * b' := fun h h' hd =>
    (hp.dvd_mul.1 hd).elim h h'
  let o : Subring Ω :=
    { carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
      mul_mem' := by
        rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
        exact ⟨a * a', b * b', hmul hb hb', by push_cast; rw [div_mul_div_comm]⟩
      one_mem' := ⟨1, 1, by simpa using hp.one_lt.ne', by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
        by_cases h0 : (b : Ω) = 0
        · exact ⟨a', b', hb', by simp [h0]⟩
        by_cases h0' : (b' : Ω) = 0
        · exact ⟨a, b, hb, by simp [h0']⟩
        exact ⟨a * b' + a' * b, b * b', hmul hb hb', by push_cast; field_simp⟩
      zero_mem' := ⟨0, 1, by simpa using hp.one_lt.ne', by simp⟩
      neg_mem' := by
        rintro _ ⟨a, b, hb, rfl⟩
        exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩ }
  refine ⟨o, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem dvd_sq (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    (p : ℕ) [Fact p.Prime] (κ : A) (h : IsCp p (algebraMap A K κ)) : κ ∣ (p : A) ^ 2 := by
  have hp : p.Prime := Fact.out
  unfold IsCp at h
  split_ifs at h with h2
  · subst h2
    have : κ = 4 := hinj (by rw [h, map_ofNat])
    rw [this]
    norm_num
  · obtain ⟨ζ, hζ, e⟩ := h
    have e' : algebraMap A K (κ + 1) = ζ := by rw [map_add, e]; simp
    have hz : IsPrimitiveRoot (κ + 1) p := IsPrimitiveRoot.of_map_of_injective (f := algebraMap A K) (by rwa [e']) hinj
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    have hn : 0 < n := by have := hp.one_lt; omega
    have h3 := hz.prod_one_sub_pow_eq_order
    have h4 : (1 - (κ + 1) ^ (0 + 1)) ∣ ∏ k ∈ Finset.range n, (1 - (κ + 1) ^ (k + 1)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
    rw [h3] at h4
    have h5 : κ ∣ ((n + 1 : ℕ) : A) := by
      have : (1 - (κ + 1) ^ (0 + 1)) = -κ := by ring
      rw [this] at h4
      exact (neg_dvd).1 (by push_cast; exact h4)
    exact h5.trans (dvd_pow_self _ two_ne_zero)

theorem ne_zero_of_gen (A K : Type) [CommRing A] [Field K] [Algebra A K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A)
    (h : GeneratesDiff σ d) : algebraMap A K d ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  have h1 : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
    rw [h]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  rw [h0] at h1
  simp only [Set.singleton_zero, Submodule.span_zero, Submodule.mem_bot, map_eq_zero] at h1
  exact hx0 (by exact_mod_cast h1)

theorem emb_mem (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type) [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) : σ (a : E) ∈ (algebraMap A K).range := by
  have h : IsIntegral ℤ (σ (a : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 (h.tower_top (A := A))
  exact ⟨y, hy⟩

theorem div_mem_of_mul (K : Type) [Field K] (B : Subring K) (ϖ : K) (N : ℕ) (G H Z : Matrix (Fin N) (Fin N) K) (hϖ : ϖ ≠ 0)
    (hH : ∀ i j, H i j ∈ B) (hZ : ∀ i j, Z i j ∈ B) (hGH : G * H = 1 + ϖ • Z) (v : Fin N → K) (hv : ∀ l, v l ∈ B)
    (hj : ∀ j, (∑ l, v l * G l j) / ϖ ∈ B) (i : Fin N) : v i / ϖ ∈ B := by
  have e : ∑ j, (∑ l, v l * G l j) * H j i = v i + ϖ * ∑ l, v l * Z l i := by
    have h1 : ∀ l, ∑ j, G l j * H j i = (1 : Matrix (Fin N) (Fin N) K) l i + ϖ * Z l i := fun l => by
      have := congrFun (congrFun hGH l) i
      simpa [Matrix.mul_apply] using this
    calc ∑ j, (∑ l, v l * G l j) * H j i = ∑ l, v l * ∑ j, G l j * H j i := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = v i + ϖ * ∑ l, v l * Z l i := by
          simp only [h1, mul_add, Finset.sum_add_distrib, Matrix.one_apply, Finset.mul_sum]
          simp
          exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : v i / ϖ = ∑ j, ((∑ l, v l * G l j) / ϖ) * H j i - ∑ l, v l * Z l i := by
    have : ∑ j, ((∑ l, v l * G l j) / ϖ) * H j i = (∑ j, (∑ l, v l * G l j) * H j i) / ϖ := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, e]
    field_simp
    ring
  rw [e2]
  exact sub_mem (sum_mem fun j _ => mul_mem (hj j) (hH j i)) (sum_mem fun l _ => mul_mem (hv l) (hZ l i))

end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

theorem exists_unit_smul : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (V : Submodule K Li) (t : K) (B : Subring K), HTL.IsLocIn A B → ∀ e ∈ HTL.latOn D V t B, ∃ u : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ (algebraMap A K u) • e ∈ HTL.latOn D V t (algebraMap A K).range := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact V t B hB e he
  have hle : D.om' ≤ D.om := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨x, rfl⟩
      exact D.h_mem x
    · rintro _ ⟨w, hw, rfl⟩
      exact D.om.smul_mem _ hw
  have hfg : D.om'.FG := Submodule.FG.of_le D.om_lat.fg hle
  obtain ⟨S, hS⟩ := hfg
  have key : ∀ S : Finset (Module.Dual K Li), (∀ w ∈ S, t * w e ∈ B) → ∃ u : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧
      ∀ w ∈ S, algebraMap A K u * (t * w e) ∈ (algebraMap A K).range := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨1, by simp, by simp [one_mem], by simp⟩
    | insert w S _ ih =>
      intro h
      obtain ⟨u, hu0, hui, hu⟩ := ih fun w' hw' => h w' (Finset.mem_insert_of_mem hw')
      obtain ⟨u', a, hu0', hui', ha⟩ := hB.2 _ (h w (Finset.mem_insert_self _ _))
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero hu0 hu0', by rw [map_mul, mul_inv]; exact mul_mem hui hui', ?_⟩
      intro w' hw'
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · refine ⟨u * a, ?_⟩
        rw [map_mul, map_mul, ← ha]
        ring
      · obtain ⟨b, hb⟩ := hu w' hw'
        refine ⟨u' * b, ?_⟩
        rw [map_mul, map_mul, hb]
        ring
  obtain ⟨u, hu0, hui, hu⟩ := key S fun w hw => he.2 w (hS ▸ Submodule.subset_span hw)
  refine ⟨u, hu0, hui, V.smul_mem _ he.1, fun w hw => ?_⟩
  rw [← hS] at hw
  have e1 : ∀ w : Module.Dual K Li, t * w (algebraMap A K u • e) = algebraMap A K u * (t * w e) := fun w => by
    rw [map_smul, smul_eq_mul]
    ring
  rw [e1]
  induction hw using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y _ _ hx hy =>
    have := add_mem hx hy
    simpa [mul_add] using this
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    have : (a • x) e = algebraMap A K a * x e := by
      rw [LinearMap.smul_apply, Algebra.smul_def]
    rw [map_mul, hb, this]
    ring

theorem latOn_smul {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li)) {V : Submodule K Li} {t : K} {B : Subring K} {b : K} (hb : b ∈ B) {e : Li}
    (he : e ∈ latOn D V t B) : b • e ∈ latOn D V t B := by
  refine ⟨V.smul_mem _ he.1, fun w hw => ?_⟩
  have : t * w (b • e) = b * (t * w e) := by
    rw [map_smul, smul_eq_mul]
    ring
  rw [this]
  exact mul_mem hb (he.2 w hw)

theorem latOn_mono {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li)) {V : Submodule K Li} {t : K} {B : Subring K} (hB : IsLocIn A B) {e : Li}
    (he : e ∈ latOn D V t (algebraMap A K).range) : e ∈ latOn D V t B := by
  refine ⟨he.1, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := he.2 w hw
  rw [← ha]
  exact hB.1 a

theorem h_mem_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem chart_pack : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → D.IsDualMap σ d m i → Module.Projective A (D.omHT σ) → ∃ J : Li →ₗ[K] (Fin N → K), ∀ B : Subring K, HTL.IsLocIn A B → (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B, ∀ l, J e l ∈ B) ∧ (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B, ∀ j, ∃ z ∈ B, ∑ l, J e l * D.gram σ d l j = algebraMap A K d * D.h (Pi.single j 1) e + (p : K) ^ m * z) ∧ (∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B, Rr (J e) = e + ((p : K) ^ m) • e') ∧ (∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 B) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 B, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 B, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e') ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) B, ∀ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 B, ∃ z ∈ B, ∑ l, J e l * D.h (Pi.single l 1) e' = (p : K) ^ m * z := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex hdual hproj
  obtain ⟨J, Rr, hJ1, hJ2, hJ3⟩ := GlobalTheory.T.hodge_tate_chart_dual_action A K E c hc p R N Li D ρ hact σ d m i hd hex
  obtain ⟨Rr', hR1, hR2⟩ := GlobalTheory.T.hodge_chart_dual_action_compat A K E c hc p R N Li D ρ hact σ m hproj hex.2.2
  have hσσ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hev : ∀ {e : Li}, e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ → ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e := by
    intro e he w
    exact eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rwa [hσσ]) w
  refine ⟨J, fun B hB => ?_⟩
  have hloc := fun (V : Submodule K Li) (t : K) => exists_unit_smul A K E c hc p R N Li D ρ hact V t B hB
  have hJu : ∀ (u : K) (e : Li) (l : Fin N), J (u • e) l = u * J e l := fun u e l => by
    rw [map_smul]
    rfl
  refine ⟨?_, ?_, ⟨Rr, fun k => latOn_mono D hB (hJ2 k), ?_⟩, ⟨Rr', fun k => latOn_mono D hB (hR1 k), ?_⟩, ?_⟩
  · intro e he l
    obtain ⟨u, hu0, hui, hu⟩ := hloc _ _ e he
    obtain ⟨f, -, hf⟩ := hJ1 _ hu
    have e1 : J e l = (algebraMap A K u)⁻¹ * algebraMap A K (i f l) := by
      rw [← hf l, hJu]
      field_simp
    rw [e1]
    exact mul_mem hui (hB.1 _)
  · intro e he j
    obtain ⟨u, hu0, hui, hu⟩ := hloc _ _ e he
    obtain ⟨f, hf1, hf⟩ := hJ1 _ hu
    let y : D.omHT (σ.comp c.toRingHom) := ⟨eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)), ⟨_, h_mem_om' D _, rfl⟩⟩
    obtain ⟨z, hz⟩ := hdual f j y rfl
    refine ⟨(algebraMap A K u)⁻¹ * algebraMap A K z, mul_mem hui (hB.1 _), ?_⟩
    have e1 : algebraMap A K (f y) = algebraMap A K d * (algebraMap A K u * D.h (Pi.single j 1) e) := by
      rw [hf1 y]
      have : (y : Module.Dual K Li) (algebraMap A K u • e) = D.h (Pi.single j 1) (algebraMap A K u • e) := hev hu.1 _
      rw [this, map_smul, smul_eq_mul]
    have e2 : ∀ l, algebraMap A K (i f l) = algebraMap A K u * J e l := fun l => by
      rw [← hf l, hJu]
    simp only [e2, map_add, map_mul, map_pow, map_natCast, e1] at hz
    have e3 : algebraMap A K u * ∑ l, J e l * D.gram σ d l j =
        algebraMap A K u * (algebraMap A K d * D.h (Pi.single j 1) e + (p : K) ^ m * ((algebraMap A K u)⁻¹ * algebraMap A K z)) := by
      rw [Finset.mul_sum]
      calc _ = ∑ l, algebraMap A K u * J e l * D.gram σ d l j := Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by rw [hz]; field_simp
    exact mul_left_cancel₀ hu0 e3
  · intro e he
    obtain ⟨u, hu0, hui, hu⟩ := hloc _ _ e he
    obtain ⟨e', he', h⟩ := hJ3 _ hu
    refine ⟨(algebraMap A K u)⁻¹ • e', latOn_smul D hui (latOn_mono D hB he'), ?_⟩
    rw [map_smul, map_smul] at h
    have h2 : algebraMap A K u • Rr (J e) = algebraMap A K u • (e + ((p : K) ^ m) • (algebraMap A K u)⁻¹ • e') := by
      rw [h, smul_add, smul_comm (algebraMap A K u) ((p : K) ^ m), smul_smul (algebraMap A K u), mul_inv_cancel₀ hu0, one_smul]
    exact smul_right_injective Li hu0 h2
  · intro e he
    obtain ⟨u, hu0, hui, hu⟩ := hloc _ _ e he
    obtain ⟨e', he', h⟩ := hR2 _ hu
    refine ⟨(algebraMap A K u)⁻¹ • e', latOn_smul D hui (latOn_mono D hB he'), ?_⟩
    have e1 : (fun l => D.h (Pi.single l 1) (algebraMap A K u • e)) = algebraMap A K u • fun l => D.h (Pi.single l 1) e := by
      funext l
      simp
    rw [e1, map_smul] at h
    have h2 : algebraMap A K u • Rr' (fun l => D.h (Pi.single l 1) e) = algebraMap A K u • (e + ((p : K) ^ m) • (algebraMap A K u)⁻¹ • e') := by
      rw [h, smul_add, smul_comm (algebraMap A K u) ((p : K) ^ m), smul_smul (algebraMap A K u), mul_inv_cancel₀ hu0, one_smul]
    exact smul_right_injective Li hu0 h2
  · intro e he e' he'
    obtain ⟨u, hu0, hui, hu⟩ := hloc _ _ e he
    obtain ⟨u', hu0', hui', hu'⟩ := hloc _ _ e' he'
    obtain ⟨f, -, hf⟩ := hJ1 _ hu
    obtain ⟨y, ⟨w, hw, hy⟩, hq⟩ := (hex.2.1 (i f)).2 ⟨f, 0, by simp⟩
    have hy' : eigProj D.ρΩ σ w = y := hy
    obtain ⟨a, ha⟩ := hu'.2 w hw
    rw [one_mul] at ha
    have hev' : ∀ w' : Module.Dual K Li, eigProj D.ρΩ σ w' (algebraMap A K u' • e') = w' (algebraMap A K u' • e') :=
      fun w' => eigProj_apply D ρ hc hact σ hu'.1 w'
    refine ⟨(algebraMap A K u)⁻¹ * (algebraMap A K u')⁻¹ * algebraMap A K a, mul_mem (mul_mem hui hui') (hB.1 _), ?_⟩
    have e1 : (D.q σ (i f)) (algebraMap A K u' • e') = ∑ l, algebraMap A K (i f l) * D.h (Pi.single l 1) (algebraMap A K u' • e') := by
      simp only [HTChart.q, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.smul_apply, hev', Algebra.smul_def]
    have e2 : (D.q σ (i f)) (algebraMap A K u' • e') = (p : K) ^ m * algebraMap A K a := by
      rw [hq, LinearMap.smul_apply, ← hy', hev', ha, Algebra.smul_def]
      simp
    have e3 : ∀ l, algebraMap A K (i f l) = algebraMap A K u * J e l := fun l => by
      rw [← hf l, hJu]
    rw [e1] at e2
    simp only [e3, map_smul, smul_eq_mul] at e2
    have e4 : algebraMap A K u * algebraMap A K u' * ∑ l, J e l * D.h (Pi.single l 1) e' = (p : K) ^ m * algebraMap A K a := by
      rw [← e2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have : ∑ l, J e l * D.h (Pi.single l 1) e' = (algebraMap A K u)⁻¹ * (algebraMap A K u')⁻¹ * ((p : K) ^ m * algebraMap A K a) := by
      rw [← e4]
      field_simp
    rw [this]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat

set_option maxHeartbeats 2000000 in

theorem exactModLat_hodgeTate : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → 0 < D.p + D.q → HTFree 𝔐 p → ∀ τ : CMType H, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q) := by
  intro hF E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq hfree τ
  obtain ⟨o, ho⟩ := HTL.exists_zp Ω p
  obtain ⟨Dc, hfam, htest⟩ := GlobalTheory.T.hodge_tate_free_flag_lattice_lower E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho
  obtain ⟨hproj, hdiff, κ, hκ, hκs⟩ := GlobalTheory.T.hodge_tate_free_flag_lattice_upper E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho Dc hfam hfree
  obtain ⟨hchar, -, -, -, -, -, hcharts⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  haveI := hchar
  have hPt : PointHT := GlobalTheory.T.pointHT_of_fargues_hodge_tate hF
  have hc : ∀ x, cmConj E (cmConj E x) = x := fun x => by
    simp [cmConj]
  let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
  have hσ : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
  obtain ⟨d, hd⟩ := hdiff σ
  obtain ⟨d', hd'⟩ := hdiff (σ.comp (cmConj E).toRingHom)
  have hR := 𝔐.R_ge p hpS
  obtain ⟨m, hm⟩ : ∃ m, 𝔐.R p = m + 2 := ⟨𝔐.R p - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hch : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ (ds κs : chartRing o (mseg y) s.1) (Jc : 𝔐.Li →ₗ[Ω] (Fin (D.p + D.q) → Ω)),
      (ds : Ω) = d ∧ GeneratesDiff σ ds ∧ (κs : Ω) = κ ∧ κs ∣ (p : chartRing o (mseg y) s.1) ^ 2 ∧
      (∀ x ∈ (Dc s).om, κs • x ∈ (Dc s).om') ∧
      (∃ G H Z : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (chartRing o (mseg y) s.1),
        (∀ i j, ((G i j : chartRing o (mseg y) s.1) : Ω) = (Dc s).gram σ ds i j) ∧
        G * H = 1 + ((p : chartRing o (mseg y) s.1) ^ (𝔐.R p)) • Z) ∧
      ∀ B : Subring Ω, HTL.IsLocIn (chartRing o (mseg y) s.1) B →
        (∀ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B, ∀ l, Jc e l ∈ B) ∧
        (∀ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B, ∀ j, ∃ z ∈ B,
          ∑ l, Jc e l * (Dc s).gram σ ds l j = (ds : Ω) * (Dc s).h (Pi.single j 1) e + (p : Ω) ^ m * z) ∧
        (∃ Rr : (Fin (D.p + D.q) → Ω) →ₗ[Ω] 𝔐.Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B) ∧
          ∀ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B, ∃ e' ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B,
            Rr (Jc e) = e + ((p : Ω) ^ m) • e') ∧
        (∃ Rr : (Fin (D.p + D.q) → Ω) →ₗ[Ω] 𝔐.Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 B) ∧
          ∀ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 B, ∃ e' ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 B,
            Rr (fun l => (Dc s).h (Pi.single l 1) e) = e + ((p : Ω) ^ m) • e') ∧
        ∀ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) B, ∀ e' ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 B,
          ∃ z ∈ B, ∑ l, Jc e l * (Dc s).h (Pi.single l 1) e' = (p : Ω) ^ m * z := by
    intro s
    obtain ⟨hN, hI, hFr, -⟩ := hcharts s.1 s.2
    haveI := hN
    haveI := hI
    haveI := hFr
    obtain ⟨ds, hds1, hds2⟩ := hd s
    obtain ⟨ds', -, hds2'⟩ := hd' s
    let κs : chartRing o (mseg y) s.1 := ⟨κ, hκs s⟩
    have hinj : Function.Injective (algebraMap (chartRing o (mseg y) s.1) Ω) := Subtype.val_injective
    have hκd : κs ∣ (p : chartRing o (mseg y) s.1) ^ 2 := HTL.dvd_sq _ Ω hinj p κs hκ
    have hdiv : κs * (p : chartRing o (mseg y) s.1) ^ m ∣ (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) := by
      rw [hm, pow_add, mul_comm ((p : chartRing o (mseg y) s.1) ^ m)]
      exact mul_dvd_mul_right hκd _
    obtain ⟨⟨-, hκ1⟩, hseq⟩ := GlobalTheory.T.chart_sequence_holds (chartRing o (mseg y) s.1) Ω E (cmConj E) hc p (𝔐.R p) (D.p + D.q)
      (Module.Dual Ω 𝔐.Li) (Dc s) κs m hdiv (htest s κs hPt hκ) (hproj s).1
    obtain ⟨i, hi1, hi2⟩ := hseq σ ds ds' hds2 hds2' ((hproj s).2 σ) ((hproj s).2 _)
    have hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), (Dc s).ρΩ a w = w ∘ₗ 𝔐.ρ (RingOfIntegers.mapRingEquiv (cmConj E) a) := fun a w => by
      rw [HT.ModelTest.bar_eq H a]
      exact hfam.act s a w
    obtain ⟨Jc, hJ⟩ := HTL.chart_pack (chartRing o (mseg y) s.1) Ω E (cmConj E) hc p (𝔐.R p) (D.p + D.q) 𝔐.Li (Dc s) 𝔐.ρ hact σ ds m i
      (HTL.ne_zero_of_gen _ Ω E σ ds hds2) hi2 hi1 ((hproj s).2 σ)
    obtain ⟨G, H', Z, -, hG, hGH, -⟩ := GlobalTheory.T.hodge_tate_chart_different_generators (chartRing o (mseg y) s.1) Ω hinj E (cmConj E) hc p (𝔐.R p) (D.p + D.q)
      (Module.Dual Ω 𝔐.Li) (Dc s) σ ds (fun a => HTL.emb_mem _ Ω E σ a) hds2
    exact ⟨ds, κs, Jc, hds1, hds2, rfl, hκd, hκ1, ⟨G, H', Z, hG, hGH⟩, hJ⟩

  choose ds κs Jc hds hgd hκeq hκd hκom hG hpack using hch
  have hcov : ∀ x : Cpt 𝔐.ξ, ∃ s : {s : ∀ k, J k // mseg y s ≠ 0}, InChart 𝔐.ξ (mseg y) s.1 x := fun x => by
    obtain ⟨s, hs⟩ := 𝔐.tie.cover x
    exact ⟨⟨s, hs.1⟩, hs⟩
  choose sx hsx using hcov
  let J' : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, 𝔐.Li →ₗ[Ω] (Fin (D.p + D.q) → Ω) :=
    fun s => LinearMap.pi fun l => (Dc s).h (Pi.single l 1)
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : (p : Ω) ^ m = p * (p : Ω) ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hgram : ∀ s t, (Dc s).gram σ (ds s) = (Dc t).gram σ (ds t) := fun s t => by
    funext i j
    have e1 : algebraMap (chartRing o (mseg y) s.1) Ω (ds s) = d := hds s
    have e2 : algebraMap (chartRing o (mseg y) t.1) Ω (ds t) = d := hds t
    simp only [HTChart.gram, e1, e2, hfam.e_eq s t]
  have hov : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q →
      InChart 𝔐.ξ (mseg y) t.1 q → InFibre 𝔐.ξ p q →
      (∀ e ∈ 𝔐.V (.inl τ) q, ∀ l, (Jc s e l - Jc t e l) / (p : Ω) ∈ regAt 𝔐.ξ q) ∧
      (∀ e ∈ 𝔐.V (.inr τ) q, ∀ l, (J' s e l - J' t e l) / (p : Ω) ∈ regAt 𝔐.ξ q) := by
    intro s t q hs ht hq
    have hZ := HT.ModelTest.overZp_of_inFibre 𝔐 (Fact.out : p.Prime) q hq
    have hls := GlobalTheory.T.hodge_component_integral_over_ring E H D l Xo c O β Y S Ω K J y 𝔐 p o ho s.1 q hs hZ
    have hlt := GlobalTheory.T.hodge_component_integral_over_ring E H D l Xo c O β Y S Ω K J y 𝔐 p o ho t.1 q ht hZ
    obtain ⟨b, hb⟩ := hκd s
    have hb' : (p : Ω) ^ 2 = κ * (b : Ω) := by
      have := congrArg (algebraMap (chartRing o (mseg y) s.1) Ω) hb
      rw [map_pow, map_natCast, map_mul] at this
      rw [this]
      congr 1
      exact hκeq s
    have hbB : (b : Ω) ∈ regAt 𝔐.ξ q := hls.1 b
    have hκw : ∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q := by
      intro w hw
      rw [hfam.om_loc s q hs hZ] at hw
      rw [hfam.om'_loc s q hs hq]
      induction hw using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        have := hκom s x hx
        rwa [show κs s • x = κ • x from by
          rw [← hκeq s]; rfl] at this
      | zero => simp
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
    have hsp : ∀ (u : Ω) (e : 𝔐.Li), (∀ w ∈ (Dc s).om', u * w e ∈ regAt 𝔐.ξ q) →
        ∀ v ∈ omP 𝔐 p q, u * v e ∈ regAt 𝔐.ξ q := by
      intro u e h v hv
      rw [hfam.om'_loc s q hs hq] at hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x y _ _ hx hy =>
        simpa [mul_add] using add_mem hx hy
      | smul a x _ hx =>
        have e1 : u * (a • x) e = (a : Ω) * (u * x e) := by
          have : (a • x) e = (a : Ω) * x e := rfl
          rw [this]; ring
        rw [e1]
        exact mul_mem a.2 hx
    have hrem : ∀ (u : Ω) (e : 𝔐.Li) (w : Module.Dual Ω 𝔐.Li), (∀ v ∈ omP 𝔐 p q, u * v e ∈ regAt 𝔐.ξ q) →
        w ∈ 𝔐.M.omLat q → u * ((p ^ 𝔐.R p) • w) e / (p : Ω) ∈ regAt 𝔐.ξ q := by
      intro u e w h hw
      have h1 := h _ (hκw w hw)
      have e1 : u * ((p ^ 𝔐.R p) • w) e / (p : Ω) = (p : Ω) ^ (m - 1) * (b : Ω) * (u * (κ • w) e) := by
        have e2 : ((p ^ 𝔐.R p) • w) e = (p : Ω) ^ (m + 2) * w e := by
          rw [hm]; simp
        have e3 : (κ • w) e = κ * w e := rfl
        rw [e2, e3, pow_add, hb', hpm]
        field_simp
      rw [e1]
      exact mul_mem (mul_mem (pow_mem (natCast_mem _ p) _) hbB) h1
    constructor
    · intro e he i
      have hes := (GlobalTheory.T.hodge_component_residue_integrality E H D l Xo c O β Y S Ω K J y 𝔐 p o ho Dc hfam hpS τ σ hσ s (ds s) (hgd s) q hs hq e).1 he
      have het := (GlobalTheory.T.hodge_component_residue_integrality E H D l Xo c O β Y S Ω K J y 𝔐 p o ho Dc hfam hpS τ σ hσ t (ds t) (hgd t) q ht hq e).1 he
      obtain ⟨a1, a2, -, -, -⟩ := hpack s _ hls
      obtain ⟨b1, b2, -, -, -⟩ := hpack t _ hlt
      obtain ⟨G, H', Z, hGg, hGH⟩ := hG s
      refine HTL.div_mem_of_mul Ω (regAt 𝔐.ξ q) (p : Ω) (D.p + D.q) (Matrix.of fun i j => (Dc s).gram σ (ds s) i j)
        (Matrix.of fun i j => (H' i j : Ω)) (Matrix.of fun i j => (p : Ω) ^ (𝔐.R p - 1) * (Z i j : Ω)) hp0
        (fun i j => hls.1 _) (fun i j => mul_mem (pow_mem (natCast_mem _ p) _) (hls.1 _)) ?_
        (fun l => Jc s e l - Jc t e l) (fun l => sub_mem (a1 e hes l) (b1 e het l)) ?_ i
      · ext i j
        have h1 := congrArg (algebraMap (chartRing o (mseg y) s.1) Ω) (congrFun (congrFun hGH i) j)
        rw [Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, map_natCast] at h1
        simp only [map_mul] at h1
        simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        have e0 : ∀ k, (Dc s).gram σ (ds s) i k = algebraMap (chartRing o (mseg y) s.1) Ω (G i k) := fun k => (hGg i k).symm
        simp only [e0]
        have e1 : (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Ω) i j =
            algebraMap (chartRing o (mseg y) s.1) Ω ((1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (chartRing o (mseg y) s.1)) i j) := by
          by_cases h : i = j <;> simp [Matrix.one_apply, h]
        have e2 : ∀ x : Ω, (p : Ω) * ((p : Ω) ^ (𝔐.R p - 1) * x) = (p : Ω) ^ 𝔐.R p * x := fun x => by
          rw [← mul_assoc, ← pow_succ']
          congr 2
          omega
        rw [e1, e2]
        exact h1
      · intro j
        obtain ⟨z, hz, h1⟩ := a2 e hes j
        obtain ⟨z', hz', h2⟩ := b2 e het j
        obtain ⟨w, hw, hwe⟩ := hfam.glue s t q hs ht hZ (Pi.single j 1)
        have h3 := hrem d e w (hsp d e (by
          intro w' hw'
          have := hes.2 w' hw'
          rwa [show ((ds s : chartRing o (mseg y) s.1) : Ω) = d from hds s] at this)) hw
        have h2' : ∑ l, Jc t e l * (Dc s).gram σ (ds s) l j = (ds t : Ω) * (Dc t).h (Pi.single j 1) e + (p : Ω) ^ m * z' := by
          rw [hgram s t]
          exact h2
        have e1 : (∑ l, (Jc s e l - Jc t e l) * (Matrix.of fun i j => (Dc s).gram σ (ds s) i j) l j) / (p : Ω) =
            d * ((p ^ 𝔐.R p) • w) e / (p : Ω) + (p : Ω) ^ (m - 1) * (z - z') := by
          simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
          rw [h1, h2', hds s, hds t, hwe, LinearMap.add_apply, hpm]
          field_simp
          ring
        rw [e1]
        exact add_mem h3 (mul_mem (pow_mem (natCast_mem _ p) _) (sub_mem hz hz'))
    · intro e he j
      have hes := (GlobalTheory.T.hodge_component_reduction_at_p E H D l Xo c O β Y S Ω K J y 𝔐 p o ho Dc hfam hpS τ σ hσ s q hs hq e).1 he
      obtain ⟨w, hw, hwe⟩ := hfam.glue s t q hs ht hZ (Pi.single j 1)
      have h1 := hrem 1 e w (hsp 1 e hes.2) hw
      have e1 : J' s e j - J' t e j = 1 * ((p ^ 𝔐.R p) • w) e := by
        show (Dc s).h (Pi.single j 1) e - (Dc t).h (Pi.single j 1) e = _
        rw [hwe, LinearMap.add_apply, one_mul, add_sub_cancel_left]
      rw [e1]
      exact h1
  refine ⟨fun x => Jc (sx x), fun x => J' (sx x), fun x hx => ?_⟩
  obtain ⟨U, -, hU⟩ := 𝔐.tie.affine (sx x).1 (sx x).2
  refine ⟨U, (hU x.1).2 ⟨x.2, hsx x⟩, fun q hqU hq => ?_⟩
  obtain ⟨_, hqc⟩ := (hU q.1).1 hqU
  have hqc' : InChart 𝔐.ξ (mseg y) (sx x).1 q := hqc
  have hqF : InFibre 𝔐.ξ p q := hq
  have hZ := HT.ModelTest.overZp_of_inFibre 𝔐 (Fact.out : p.Prime) q hqF
  have hls := GlobalTheory.T.hodge_component_integral_over_ring E H D l Xo c O β Y S Ω K J y 𝔐 p o ho (sx x).1 q hqc' hZ
  obtain ⟨k1, -, ⟨R1, hR1, hR1'⟩, ⟨R2, hR2, hR2'⟩, k5⟩ := hpack (sx x) _ hls
  have hl := fun e => GlobalTheory.T.hodge_component_residue_integrality E H D l Xo c O β Y S Ω K J y 𝔐 p o ho Dc hfam hpS τ σ hσ (sx x) (ds (sx x)) (hgd _) q hqc' hqF e
  have hr := fun e => GlobalTheory.T.hodge_component_reduction_at_p E H D l Xo c O β Y S Ω K J y 𝔐 p o ho Dc hfam hpS τ σ hσ (sx x) q hqc' hqF e
  obtain ⟨ov1, ov2⟩ := hov (sx x) (sx q) q hqc' (hsx q) hqF
  have hpB : (p : Ω) ^ (m - 1) ∈ regAt 𝔐.ξ q := pow_mem (natCast_mem _ p) _
  refine ⟨⟨fun w hw k => ⟨k1 w ((hl w).1 hw) k, ov1 w hw k⟩, R1, fun k => (hl _).2 (hR1 k), fun w hw => ?_⟩,
    ⟨fun w hw k => ⟨?_, ov2 w hw k⟩, R2, fun k => (hr _).2 (hR2 k), fun w hw => ?_⟩, fun w hw w' hw' => ?_⟩
  · obtain ⟨e', he', h⟩ := hR1' w ((hl w).1 hw)
    refine ⟨(p : Ω) ^ (m - 1) • e', (𝔐.V (.inl τ) q).smul_mem ⟨_, hpB⟩ ((hl e').2 he'), ?_⟩
    rw [h, hpm, smul_smul]
  · have h1 := ((hr w).1 hw).2 ((Dc (sx x)).h (Pi.single k 1)) (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩))
    simpa [J'] using h1
  · obtain ⟨e', he', h⟩ := hR2' w ((hr w).1 hw)
    refine ⟨(p : Ω) ^ (m - 1) • e', (𝔐.V (.inr τ) q).smul_mem ⟨_, hpB⟩ ((hr e').2 he'), ?_⟩
    have : (J' (sx x)) w = fun l => (Dc (sx x)).h (Pi.single l 1) w := rfl
    rw [this, h, hpm, smul_smul]
  · obtain ⟨z, hz, h⟩ := k5 w ((hl w).1 hw) w' ((hr w').1 hw')
    have e1 : dotProduct (Jc (sx x) w) (J' (sx x) w') / (p : Ω) = (p : Ω) ^ (m - 1) * z := by
      have : dotProduct (Jc (sx x) w) (J' (sx x) w') = (p : Ω) ^ m * z := h
      rw [this, hpm]
      field_simp
    rw [e1]
    exact mul_mem hpB hz

end GlobalTheory.CompanionTheory.Ar.Flat
