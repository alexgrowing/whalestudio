import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleChartGenericComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleIntersectionSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBundleIntersectionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelK

section Lat

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ} {Sg : Type}
  {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s)

theorem mem_vanSub {i : ℕ} {g : (Fin n → F) → Ω} : g ∈ vanSub Ω F n i ↔
    ∀ y : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → y j = 0) → g y = 0 := by
  simp [vanSub, Submodule.mem_pi]

theorem mem_kk {τ : Sg} {i : ℕ} {m : Fin (r τ) → Ω} :
    m ∈ D.kk τ i ↔ ∃ g, (g, m) ∈ D.Th τ ∧ g ∈ vanSub Ω F n i := by
  simp only [LieLatticeData.kk, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨⟨g, m'⟩, ⟨h1, h2, -⟩, rfl⟩
    exact ⟨g, h1, h2⟩
  · rintro ⟨g, h1, h2⟩
    exact ⟨(g, m), ⟨h1, h2, AddSubgroup.mem_top _⟩, rfl⟩

theorem mem_xId {χ : F → Ω} {i : Fin n} {c : Ω} : c ∈ D.xId χ i ↔
    ∃ g ∈ D.M, ∃ h ∈ vanSub Ω F n ((i : ℕ) + 1), g + h = c • fun y : Fin n → F => χ (y i) := by
  simp only [LieLatticeData.xId, AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  rfl

theorem mem_stepGraph {τ : Sg} {χ : F → Ω} {i : Fin n} {c : Ω} {m : Fin (r τ) → Ω} :
    (c, m) ∈ D.stepGraph τ χ i ↔ ∃ g h, (g, m) ∈ D.Th τ ∧ h ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
      g + h = c • fun y : Fin n → F => χ (y i) := by
  simp only [LieLatticeData.stepGraph, AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, h1, ⟨h, m''⟩, h2, h3⟩
    have hz : m'' = 0 := (AddSubgroup.mem_prod.1 h2).2
    subst hz
    have e := congrArg Prod.fst h3
    have e' := congrArg Prod.snd h3
    simp at e e'
    subst e'
    exact ⟨g, h, h1, (AddSubgroup.mem_prod.1 h2).1, e⟩
  · rintro ⟨g, h, h1, h2, h3⟩
    refine ⟨(g, m), h1, (h, 0), AddSubgroup.mem_prod.2 ⟨h2, AddSubgroup.mem_bot.2 rfl⟩, ?_⟩
    simp [h3]

theorem mem_mulLat {V : Type} [AddCommGroup V] [Module Ω V] {c : Ω} {L : AddSubgroup V} {v : V} :
    v ∈ mulLat c L ↔ ∃ e ∈ L, v = c • e := by
  simp only [mulLat, AddSubgroup.mem_map, DistribMulAction.toAddMonoidHom_apply]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩

theorem mem_dotDual {R : Subalgebra o Ω} {N : ℕ} {L : AddSubgroup (Fin N → Ω)} {v : Fin N → Ω} :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable [Fintype F] {R : Subalgebra o Ω} {p : ℕ} {w : Ω}

theorem kk_zero (hb : D.Base R p w) (τ : Sg) : D.kk τ 0 = dotDual R (D.lie τ) := by
  ext m
  rw [mem_kk]
  constructor
  · rintro ⟨g, hg, -⟩
    exact ((hb.th τ).2.1 m).1 ⟨g, hg⟩
  · intro hm
    obtain ⟨g, hg⟩ := ((hb.th τ).2.1 m).2 hm
    refine ⟨g, hg, mem_vanSub.2 fun y hy => ?_⟩
    have : y = 0 := funext fun j => hy j (Nat.zero_le _)
    rw [this]
    exact (((hb.th τ).1 g).1 ⟨m, hg⟩).2

theorem kk_top (hb : D.Base R p w) (τ : Sg) : D.kk τ n = mulLat (p : Ω) (dotDual R (D.lie τ)) := by
  ext m
  rw [mem_kk, ← (hb.th τ).2.2 m]
  constructor
  · rintro ⟨g, hg, hv⟩
    have : g = 0 := funext fun y => mem_vanSub.1 hv y fun j hj => absurd j.2 (not_lt.2 hj)
    rwa [this] at hg
  · intro h
    exact ⟨0, h, (vanSub Ω F n n).zero_mem⟩

theorem kk_anti {i j : ℕ} (h : i ≤ j) (τ : Sg) : D.kk τ j ≤ D.kk τ i := by
  intro m hm
  obtain ⟨g, hg, hv⟩ := (mem_kk D).1 hm
  exact (mem_kk D).2 ⟨g, hg, mem_vanSub.2 fun y hy => mem_vanSub.1 hv y fun l hl => hy l (h.trans hl)⟩

theorem smul_mem_kk (hb : D.Base R p w) {τ : Sg} {i j : ℕ} (hi : i ≤ n) {m : Fin (r τ) → Ω}
    (hm : m ∈ D.kk τ j) : (p : Ω) • m ∈ D.kk τ i := by
  have h0 : m ∈ dotDual R (D.lie τ) := by
    rw [← kk_zero D hb τ]
    exact kk_anti D (Nat.zero_le j) τ hm
  exact kk_anti D hi τ (by rw [kk_top D hb τ]; exact mem_mulLat.2 ⟨m, h0, rfl⟩)

end Lat

section Step

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F]
  {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}

theorem mem_of_mem_xId (hb : D.Base R p w) {χ : F → Ω} (h1 : χ 1 = 1) (h01 : (0 : F) ≠ 1)
    {i : Fin n} {c : Ω} (hc : c ∈ D.xId χ i) : c ∈ R := by
  classical
  obtain ⟨g, hg, h, hh, e⟩ := (mem_xId D).1 hc
  let y : Fin n → F := fun j => if j = i then 1 else 0
  have hy : h y = 0 := mem_vanSub.1 hh y fun j hj => by
    have : j ≠ i := fun hji => by
      rw [hji] at hj
      omega
    simp [y, this]
  have e' := congrFun e y
  have hyi : y i = 1 := by simp [y]
  simp only [Pi.add_apply, hy, add_zero, Pi.smul_apply, hyi, h1, smul_eq_mul, mul_one] at e'
  rw [← e']
  have := hb.M_le hg
  exact (AddSubgroup.mem_pi _).1 this y (Set.mem_univ _)

theorem exists_mul_mem_xId (hb : D.Base R p w) {χ : F → Ω} (hχ : ∀ a, χ a ∈ R) (i : Fin n) :
    ∃ m : ℕ, ∀ c ∈ R, (p : Ω) ^ m * c ∈ D.xId χ i := by
  obtain ⟨m, hm⟩ := hb.le_M
  refine ⟨m, fun c hc => (mem_xId D).2 ⟨_, hm (mem_mulLat.2 ⟨fun y => c * χ (y i), ?_, rfl⟩), 0,
    (vanSub Ω F n _).zero_mem, ?_⟩⟩
  · exact (AddSubgroup.mem_pi _).2 fun y _ => R.mul_mem hc (hχ _)
  · funext y
    simp [mul_assoc]

theorem step_facts (hb : D.Base R p w) {τ : Sg} {χ : F → Ω} (h0 : χ 0 = 0) {i : Fin n}
    {X : AddSubgroup Ω} (honto : (D.stepGraph τ χ i).map (AddMonoidHom.snd _ _) = D.kk τ i)
    (hinj : (D.stepGraph τ χ i).comap (AddMonoidHom.inl _ _) = X) :
    (∀ v m, (v, m) ∈ D.stepGraph τ χ i → v ∈ D.xId χ i ∧ m ∈ D.kk τ i) ∧
    (∀ v ∈ D.xId χ i, ∃ m, (v, m) ∈ D.stepGraph τ χ i) ∧
    (∀ m, (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1)) ∧
    (∀ v, (v, 0) ∈ D.stepGraph τ χ i ↔ v ∈ X) ∧
    (∀ m ∈ D.kk τ i, ∃ v, (v, m) ∈ D.stepGraph τ χ i) := by
  refine ⟨fun v m h => ⟨?_, ?_⟩, fun v hv => ?_, fun m => ?_, fun v => ?_, fun m hm => ?_⟩
  · obtain ⟨g, h', hg, hh, e⟩ := (mem_stepGraph D).1 h
    exact (mem_xId D).2 ⟨g, (((hb.th τ).1 g).1 ⟨m, hg⟩).1, h', hh, e⟩
  · rw [← honto]
    exact ⟨(v, m), h, rfl⟩
  · obtain ⟨g, hg, h, hh, e⟩ := (mem_xId D).1 hv
    have hh0 : h 0 = 0 := mem_vanSub.1 hh 0 fun _ _ => rfl
    have e' := congrFun e 0
    simp only [Pi.add_apply, hh0, add_zero, Pi.smul_apply, Pi.zero_apply, h0, smul_zero] at e'
    obtain ⟨m, hm⟩ := ((hb.th τ).1 g).2 ⟨hg, e'⟩
    exact ⟨m, (mem_stepGraph D).2 ⟨g, h, hm, hh, e⟩⟩
  · rw [mem_stepGraph, mem_kk]
    constructor
    · rintro ⟨g, h, hg, hh, e⟩
      have : g = -h := by
        rw [zero_smul] at e
        exact eq_neg_of_add_eq_zero_left e
      exact ⟨g, hg, this ▸ (vanSub Ω F n _).neg_mem hh⟩
    · rintro ⟨g, hg, hv⟩
      exact ⟨g, -g, hg, (vanSub Ω F n _).neg_mem hv, by simp⟩
  · rw [← hinj]
    rfl
  · rw [← honto] at hm
    obtain ⟨⟨v, m'⟩, h, rfl⟩ := hm
    exact ⟨v, h⟩

end Step

section Line

variable {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem chartMon_smul (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (p : ℕ) :
    chartMon x c ((p : ℤ) • a) = chartMon x c a ^ p := by
  simp only [chartMon, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul, zpow_natCast]

theorem powSpan_line {R : Subalgebra O Ω} {p : ℕ} {X Y : AddSubgroup Ω} {e : Ω}
    (hX : ∀ v, v ∈ X ↔ ∃ a ∈ R, v = a * e) (hY : ∀ v, v ∈ Y ↔ ∃ a ∈ R, v = a * e ^ p) :
    Y = powSpan R p X := by
  apply le_antisymm
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := (hY v).1 hv
    refine AddSubgroup.subset_closure ⟨a, ha, e ^ p, ⟨e, (hX e).2 ⟨1, R.one_mem, by simp⟩, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro v ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (hX b).1 hb
    exact (hY _).2 ⟨a * t ^ p, R.mul_mem ha (R.pow_mem ht p), by simp [mul_pow, mul_assoc]⟩

end Line

section Dot

variable {Ω : Type} [Field Ω]

noncomputable def dotB (N : ℕ) : (Fin N → Ω) →ₗ[Ω] (Fin N → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) add_dotProduct smul_dotProduct dotProduct_add dotProduct_smul

theorem dotB_apply (N : ℕ) (a b : Fin N → Ω) : dotB N a b = a ⬝ᵥ b := rfl

theorem dotB_bijective (N : ℕ) : Function.Bijective (dotB (Ω := Ω) N).flip := by
  classical
  constructor
  · intro a b h
    funext i
    have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · intro f
    refine ⟨fun i => f (Pi.single i 1), LinearMap.ext fun v => ?_⟩
    rw [LinearMap.flip_apply, dotB_apply]
    conv_rhs => rw [← Finset.univ_sum_single v]
    simp only [dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Pi.single i (v i) = v i • (Pi.single i 1 : Fin N → Ω) := by
      rw [← Pi.single_smul]
      simp
    rw [e, map_smul, smul_eq_mul]

end Dot

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∀ τ, ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → (k : ℤ) * rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O) = (-1) ^ (k - 1) * ∑ i, (ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmod F _ _ _ n Sg _ r s p hp w χ φ D hfam hG1 hG2 hF hline Xb T hXb
    hT Lie W Om OmHT hB τ k hk1 hk2 q L Q hQ
  have hinj : Function.Injective (algebraMap O Ω) := by
    obtain ⟨-, -, hc, -⟩ := hmod
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have : a ∈ Ideal.comap (C : O →+* _) (mcIdeal O x) := by
      rw [Ideal.mem_comap]
      simp [mcIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap,
        MvPolynomial.algebraMap_apply, ha]
    rw [hc] at this
    simpa using this
  have hfc := GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hfam
  have hbase := hfam.base
  have hch := hfam.char
  have hp0 : (p : O) ≠ 0 := hch.1
  have hpΩ : algebraMap O Ω (p : O) = (p : Ω) := map_natCast _ _
  have hBa := GlobalTheory.T.dvr_bundle_statement_a O Ω K ι
  have hKK : ∀ i : ℕ, ∃ E : ChartBundle O (mseg x) (r (φ τ)) (Fin (r (φ τ)) → Ω),
      ∀ c, mseg x c ≠ 0 → E.lat c = (D c).kk (φ τ) i := fun i =>
    (GlobalTheory.T.lattice_families_glue_to_bundle O Ω K ι x (r (φ τ)) _).1 _ ((hfc.2 (φ τ)).2.2.1 i)
      (fun c hc => (hG2 c hc).kk (φ τ) i)
  choose KK hKK using hKK

  have hSG : ∀ i j, i ≤ n → j ≤ n → SameGeneric O x (KK i) (KK j) := by
    intro i j hi hj c hc
    refine ⟨fun v hv => ⟨p, hp0, ?_⟩, fun v hv => ⟨p, hp0, ?_⟩⟩
    · rw [hKK i c hc] at hv
      rw [hKK j c hc, hpΩ]
      exact smul_mem_kk (D c) (hbase c hc) hj hv
    · rw [hKK j c hc] at hv
      rw [hKK i c hc, hpΩ]
      exact smul_mem_kk (D c) (hbase c hc) hi hv
  have hXT : ∀ (σ : Sg) (i : Fin n), SameGeneric O x (Xb σ i) T := by
    intro σ i c hc
    have hb := hbase c hc
    have hTc : ∀ v, v ∈ T.lat c ↔ v ∈ chartRing O (mseg x) c := by
      intro v
      rw [hT c hc v]
      simp [chartMon]
    have hχR : ∀ a, algebraMap O Ω (χ σ a) ∈ chartRing O (mseg x) c :=
      fun a => Subalgebra.algebraMap_mem _ _
    obtain ⟨m, hm⟩ := exists_mul_mem_xId (D c) hb hχR i
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨(p : O) ^ m, pow_ne_zero _ hp0, ?_⟩⟩
    · rw [hXb σ i c hc] at hv
      rw [map_one, one_smul, hTc]
      exact mem_of_mem_xId (D c) hb (by rw [(hch.2.2.2.2 σ).2, map_one]) hch.2.2.2.1 hv
    · rw [hXb σ i c hc, map_pow, hpΩ, smul_eq_mul]
      exact hm v ((hTc v).1 hv)
  have hstep : ∀ i : Fin n, ck O x d _ (KK i) (KK ((i : ℕ) + 1)) k L Q =
      ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q := by
    intro i
    obtain ⟨u, a, hu, hl⟩ := hline τ i
    obtain ⟨PB, hPB⟩ := (GlobalTheory.T.chart_bundle_product O Ω K ι x).2.2.1 (u ^ (p : ℤ)) ((p : ℤ) • a)
      (zpow_ne_zero _ hu)
    have hA : IsLine O x u a (Xb τ i).lat := fun c hc v => by
      rw [hXb τ i c hc]
      exact hl c hc v
    have hPBlat : ∀ c, mseg x c ≠ 0 → PB.lat c = powSpan (chartRing O (mseg x) c) p
        ((D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
      intro c hc
      refine powSpan_line (e := u * chartMon x c a) (fun v => hl c hc v) (fun v => ?_)
      rw [hPB c hc v, chartMon_smul, zpow_natCast, mul_pow]
    obtain ⟨hPT, hpow⟩ := GlobalTheory.T.line_bundle_chart_generic_comparison O Ω K ι x d hmod (Xb τ i) T PB u a (p : ℤ) hu hA hT
      (hXT τ i) hPB
    have hfacts := fun c (hc : mseg x c ≠ 0) => step_facts (D c) (hbase c hc) (τ := φ τ)
      (χ := fun a => algebraMap O Ω (χ (φ τ) a)) (i := i)
      (by rw [(hch.2.2.2.2 _).1, map_zero]) ((hF c hc).onto (φ τ) i) ((hF c hc).inj τ i)
    have hq : QuotEquiv O x (Xb (φ τ) i).lat PB.lat (KK i).lat (KK ((i : ℕ) + 1)).lat := by
      refine ⟨fun c => (D c).stepGraph (φ τ) (fun a => algebraMap O Ω (χ (φ τ) a)) i,
        ⟨((hfc.2 (φ τ)).2.1 i).2, fun c hc => ?_⟩, fun c hc => ?_⟩
      · obtain ⟨f1, f2, f3, f4, -⟩ := hfacts c hc
        rw [hXb _ i c hc, hKK (i : ℕ) c hc, hKK ((i : ℕ) + 1) c hc, hPBlat c hc]
        exact ⟨f1, f2, f3, fun v hv => (f4 v).2 hv⟩
      · obtain ⟨-, -, -, f4, f5⟩ := hfacts c hc
        rw [hKK (i : ℕ) c hc, hPBlat c hc]
        exact ⟨fun v hv => (f4 v).1 hv, f5⟩
    have hXP : SameGeneric O x (Xb (φ τ) i) PB := by
      intro c hc
      obtain ⟨f1, f2, f3, f4, -⟩ := hfacts c hc
      refine ⟨fun v hv => ⟨p, hp0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · rw [hXb _ i c hc] at hv
        rw [hPBlat c hc, hpΩ, ← f4]
        obtain ⟨m, hm⟩ := f2 v hv
        have hkm := (f1 v m hm).2
        have h1 : ((p : Ω) • v, (p : Ω) • m) ∈
            (D c).stepGraph (φ τ) (fun a => algebraMap O Ω (χ (φ τ) a)) i := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
          exact nsmul_mem hm p
        have h2 := (f3 _).2 (smul_mem_kk (D c) (hbase c hc) (Nat.succ_le_of_lt i.2) hkm)
        have h3 := sub_mem h1 h2
        simpa using h3
      · rw [hPBlat c hc] at hv
        rw [map_one, one_smul, hXb _ i c hc]
        exact (f1 v 0 ((f4 v).2 hv)).1
    have hEq := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d 1 (r (φ τ)) Ω (Fin (r (φ τ)) → Ω) (Xb (φ τ) i) PB (KK i)
      (KK ((i : ℕ) + 1)) hmod hXP (hSG _ _ i.2.le (Nat.succ_le_of_lt i.2)) hq k hk1 hk2 q L Q hQ
    have hsym := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.sameGeneric_symm O hPT
    have hc1 := (hBa x d 1 Ω (Xb (φ τ) i) T PB hmod (hXT _ i) hsym k hk1 hk2 q L Q hQ).1
    have hc2 := (hBa x d 1 Ω PB T PB hmod hPT hsym k hk1 hk2 q L Q hQ).2
    have hpw := hpow k hk1 hk2 q L Q hQ
    rw [← hEq, hc1, hc2, hpw]
    ring
  have htel : ∀ j, j ≤ n → ck O x d _ (KK 0) (KK j) k L Q =
      ∑ i ∈ Finset.range j, ck O x d _ (KK i) (KK (i + 1)) k L Q := by
    intro j
    induction j with
    | zero =>
      intro _
      have h00 := hSG 0 0 (Nat.zero_le _) (Nat.zero_le _)
      have := (hBa x d _ _ (KK 0) (KK 0) (KK 0) hmod h00 h00 k hk1 hk2 q L Q hQ).1
      simp only [Finset.range_zero, Finset.sum_empty]
      omega
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ← ih (by omega)]
      exact (hBa x d _ _ (KK 0) (KK j) (KK (j + 1)) hmod (hSG _ _ (Nat.zero_le _) (by omega))
        (hSG _ _ (by omega) hj) k hk1 hk2 q L Q hQ).1
  have hd : IsDualLat O x (dotB (r (φ τ))) (Lie (φ τ)).lat (KK 0).lat := by
    refine ⟨dotB_bijective _, fun c hc v => ?_⟩
    rw [hKK 0 c hc, kk_zero (D c) (hbase c hc), mem_dotDual, (hB (φ τ) c hc).1]
    rfl
  have hrefl : SameGeneric O x (Lie (φ τ)) (Lie (φ τ)) := fun c _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hdu := (GlobalTheory.T.dual_bundle_intersection O Ω K ι x d (r (φ τ)) _ _ (dotB (r (φ τ))) (Lie (φ τ)) (Lie (φ τ)) (KK 0)
    (KK 0) hmod hrefl hd hd).2 (k - 1) (by omega) q L Q hQ' (p : O) hp0
  have hscale : ∀ c, mseg x c ≠ 0 → ∀ v, v ∈ (KK n).lat c ↔
      ∃ e ∈ (KK 0).lat c, v = algebraMap O Ω (p : O) • e := by
    intro c hc v
    rw [hKK n c hc, hKK 0 c hc, kk_top (D c) (hbase c hc), kk_zero (D c) (hbase c hc), hpΩ, mem_mulLat]
  have hBd := (GlobalTheory.T.dvr_bundle_statement_d O Ω K ι x d (r (φ τ)) _ (KK 0) (KK n) (p : O) hp0 hmod hscale k hk1 hk2
    q L Q hQ).1
  have hsum : ∑ i : Fin n, (ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q) =
      ck O x d _ (KK 0) (KK n) k L Q := by
    rw [htel n le_rfl, ← Fin.sum_univ_eq_sum_range
      (fun i => ck O x d _ (KK i) (KK (i + 1)) k L Q) n]
    exact Finset.sum_congr rfl fun i _ => (hstep i).symm
  have hs : ((-1 : ℤ) ^ (k - 1)) * (-1) ^ (k - 1) = 1 := by
    rw [← mul_pow]
    simp
  rw [hsum, hBd, hdu]
  linear_combination (-(k : ℤ) * rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O)) * hs

end GlobalTheory.CompanionTheory.Ar.Num.RelK
