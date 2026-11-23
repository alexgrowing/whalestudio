import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleFramesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleChartGenericComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquivStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelH

section Chart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat' (R : Subalgebra o Ω) {n : ℕ} {v : Fin n → Ω} :
    v ∈ stdLat R (Fin n) ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual' (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {v : Fin n → Ω} :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)}
    (hL : L ≤ stdLat R (Fin n)) : stdLat R (Fin n) ≤ dotDual R L := by
  intro v hv
  refine (mem_dotDual' R).2 fun l hl => ?_
  have h1 := (mem_stdLat' R).1 (hL hl)
  have h2 := (mem_stdLat' R).1 hv
  exact sum_mem fun i _ => mul_mem (h1 i) (h2 i)

theorem smul_mem_of_dual (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {w : Ω}
    (hL : mulLat w (stdLat R (Fin n)) ≤ L) {v : Fin n → Ω} (hv : v ∈ dotDual R L) :
    w • v ∈ stdLat R (Fin n) := by
  refine (mem_stdLat' R).2 fun i => ?_
  have h1 : w • (Pi.single i 1 : Fin n → Ω) ∈ L := by
    refine hL ⟨Pi.single i 1, (mem_stdLat' R).2 fun j => ?_, rfl⟩
    by_cases h : j = i
    · subst h; simpa using one_mem R
    · simpa [h] using zero_mem R
  have h2 := (mem_dotDual' R).1 hv _ h1
  simpa [dotProduct, Pi.single_apply] using h2

theorem coord_mem_of_le (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)}
    (hL : L ≤ stdLat R (Fin n)) (i : Fin n) {t : Ω}
    (ht : t ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) :
    t ∈ R := by
  obtain ⟨v, hv, rfl⟩ := ht
  exact (mem_stdLat' R).1 (hL hv.1) i

theorem mul_mem_coord (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {w : Ω}
    (hL : mulLat w (stdLat R (Fin n)) ≤ L) (i : Fin n) {a : Ω} (ha : a ∈ R) :
    w * a ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) := by
  refine ⟨w • (Pi.single i a : Fin n → Ω), ⟨hL ⟨Pi.single i a, (mem_stdLat' R).2 fun j => ?_, rfl⟩, ?_⟩, ?_⟩
  · by_cases h : j = i
    · subst h; simpa using ha
    · simpa [h] using zero_mem R
  · show _ ∈ annSub Ω n i
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro j hj
    have : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
    simp [this]
  · simp

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem chart_facts (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω)
    (φ : Equiv.Perm Sg) (hcd : CharData R p w χ) (hb : D.Base R p w) (h1 : D.Good₁ R p χ)
    (h2 : D.Good₂ R p χ) (hf : D.Facts R p w χ φ) (τ : Sg) :
    stdLat R (Fin n) ≤ D.hh R p (χ τ) ∧ (∀ v ∈ D.hh R p (χ τ), w • v ∈ stdLat R (Fin n)) ∧
      ∀ i : Fin n, (∀ t ∈ D.xId (χ τ) i, t ∈ R) ∧ (∀ a ∈ R, w * a ∈ D.xId (χ τ) i) ∧
        ∀ u : Ω, u ≠ 0 → (∀ c, c ∈ D.xId (χ τ) i ↔ ∃ a ∈ R, c = a * u) →
          ∀ t, (∃ v ∈ D.hh R p (χ τ), (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  obtain ⟨hfree, -⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hcd hb h1
  obtain ⟨hLF, -, hle, -⟩ := hfree τ
  have hle' : mulLat w (stdLat R _) ≤ D.af R p (χ τ) := hf.le_af τ
  refine ⟨std_le_dual R hle, fun v hv => smul_mem_of_dual R hle' hv, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro t ht
    rw [← hf.dx τ i] at ht
    exact coord_mem_of_le R hle i ht
  · intro a ha
    rw [← hf.dx τ i]
    exact mul_mem_coord R hle' i ha
  · intro u hu hc t
    refine GlobalTheory.T.dual_lattice_coordinate_generator R n (D.af R p (χ τ)) hLF (h2.ann τ) i u hu (fun c => ?_) t
    have := hc c
    rw [← hf.dx τ i] at this
    exact this

end Chart

section Model

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem coord_ne_zero {x : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : mseg x c ≠ 0) (k : K) :
    x ⟨k, c k⟩ ≠ 0 := fun h => hc (Finset.prod_eq_zero (Finset.mem_univ k) h)

theorem chartMon_ne_zero' {x : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : mseg x c ≠ 0) (b : K → ℤ) :
    chartMon x c b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (coord_ne_zero hc k)

theorem chartMon_neg' (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (b : K → ℤ) :
    chartMon x c (-b) = (chartMon x c b)⁻¹ := by
  simp [chartMon, Finset.prod_inv_distrib, zpow_neg]

theorem chartMon_zero' (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : chartMon x c (0 : K → ℤ) = 1 := by
  simp [chartMon]

theorem inv_line {u : Ω} (hu : u ≠ 0) (v r m : Ω) :
    u⁻¹ * v = r * (u⁻¹ * m) ↔ v = r * (1 * m) := by
  rw [show r * (u⁻¹ * m) = u⁻¹ * (r * (1 * m)) by ring, mul_right_inj' (inv_ne_zero hu)]

theorem inv_line' {u : Ω} (hu : u ≠ 0) (v r m : Ω) :
    u⁻¹ * v = r * (1 * m) ↔ v = r * (u * m) := by
  rw [show r * (u * m) = u * (r * (1 * m)) by ring, inv_mul_eq_iff_eq_mul₀ hu]

end Model

theorem relH_main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ τ (H Tn : ChartBundle O (mseg x) n (Fin n → Ω)), (∀ c, mseg x c ≠ 0 → H.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) ∧ Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n)) → SameGeneric O x H Tn ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d n H Tn k L Q = (-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmodel F _ _ _ n Sg _ r s p hp w χ φ D hfam hg1 hg2 hfacts hline
    Xb T hXb hT τ H Tn hHT
  have hinj : ∀ a : O, algebraMap O Ω a = 0 → a = 0 := by
    intro a ha
    have h1 : (MvPolynomial.C a : MvPolynomial (Σ k, ι k) O) ∈ mcIdeal O x := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (MvPolynomial.C a) = 0
      have h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (MvPolynomial.C a) =
          algebraMap O (MvPolynomial K Ω) a :=
        (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x).commutes a
      rw [h2, MvPolynomial.algebraMap_apply, ha, map_zero]
    have h2 : a ∈ ((mcIdeal O x).comap (MvPolynomial.C : O →+* MvPolynomial (Σ k, ι k) O)) := h1
    rw [hmodel.2.2.1] at h2
    simpa using h2
  obtain ⟨hp0, ⟨u0, hu0, hwu⟩, -, h01, hχ⟩ := hfam.char
  have hp2 : 2 ≤ p := hp.two_le
  have hpΩ : (p : Ω) ≠ 0 := by
    intro h
    exact hp0 (hinj _ (by simpa using h))
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hwu
    rcases mul_eq_zero.1 hwu.symm with h | h
    · exact hu0.ne_zero h
    · exact hp0 h
  obtain ⟨b, hb⟩ : ∃ b : O, (p : O) = b * w := by
    obtain ⟨v, rfl⟩ := hu0
    refine ⟨↑v⁻¹ * w ^ (p - 2), ?_⟩
    have h1 : w ^ (p - 1) = w ^ (p - 2) * w := by
      rw [← pow_succ]
      congr 1
      omega
    calc (p : O) = ↑v⁻¹ * (↑v * (p : O)) := by simp
      _ = _ := by rw [← hwu, h1, mul_assoc]
  have hcd : ∀ c, CharData (chartRing O (mseg x) c) p (algebraMap O Ω w)
      (fun τ a => algebraMap O Ω (χ τ a)) := fun c =>
    ⟨hpΩ, Subalgebra.algebraMap_mem _ w,
      ⟨algebraMap O Ω b, Subalgebra.algebraMap_mem _ b, by rw [← map_mul, ← hb, map_natCast]⟩, h01,
      fun τ => ⟨by simp [(hχ τ).1], by simp [(hχ τ).2], fun a => Subalgebra.algebraMap_mem _ _⟩⟩
  have CF : ∀ c, mseg x c ≠ 0 →
      stdLat (chartRing O (mseg x) c) (Fin n) ≤ H.lat c ∧
      (∀ v ∈ H.lat c, algebraMap O Ω w • v ∈ stdLat (chartRing O (mseg x) c) (Fin n)) ∧
      ∀ i : Fin n, (∀ t ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i, t ∈ chartRing O (mseg x) c) ∧
        (∀ a ∈ chartRing O (mseg x) c,
          algebraMap O Ω w * a ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧
        ∀ u : Ω, u ≠ 0 → (∀ c', c' ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i ↔
            ∃ a ∈ chartRing O (mseg x) c, c' = a * u) →
          ∀ t, (∃ v ∈ H.lat c, (∀ j, i < j → v j = 0) ∧ v i = t) ↔
            ∃ a ∈ chartRing O (mseg x) c, t = a * u⁻¹ := by
    intro c hc
    rw [(hHT c hc).1]
    exact chart_facts (D c) (chartRing O (mseg x) c) p _ _ φ (hcd c) (hfam.base c hc) (hg1 c hc)
      (hg2 c hc) (hfacts c hc) τ
  choose u a hu hl using hline
  have hgR : ∀ (i : Fin n) c, mseg x c ≠ 0 → u τ i * chartMon x c (a τ i) ∈ chartRing O (mseg x) c ∧
      ∃ e ∈ chartRing O (mseg x) c, algebraMap O Ω w = e * (u τ i * chartMon x c (a τ i)) := by
    intro i c hc
    refine ⟨((CF c hc).2.2 i).1 _ ((hl τ i c hc _).2 ⟨1, one_mem _, by simp⟩), ?_⟩
    have h1 := ((CF c hc).2.2 i).2.1 1 (one_mem _)
    rw [mul_one] at h1
    exact (hl τ i c hc _).1 h1
  have hgne : ∀ (i : Fin n) c, mseg x c ≠ 0 → u τ i * chartMon x c (a τ i) ≠ 0 := fun i c hc =>
    mul_ne_zero (hu τ i) (chartMon_ne_zero' hc _)
  have hgm : ∀ (i : Fin n) c, mseg x c ≠ 0 →
      (u τ i * chartMon x c (a τ i)) * chartMon x c (-a τ i) = u τ i := by
    intro i c hc
    rw [chartMon_neg', mul_assoc, mul_inv_cancel₀ (chartMon_ne_zero' hc _), mul_one]
  have hSG : SameGeneric O x H Tn := by
    intro c hc
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [(hHT c hc).2]
      exact (CF c hc).2.1 v hv
    · rw [map_one, one_smul]
      rw [(hHT c hc).2] at hv
      exact (CF c hc).1 hv
  let wB : Module.Basis (Fin n) Ω (Fin n → Ω) :=
    (Pi.basisFun Ω (Fin n)).unitsSMul fun i => Units.mk0 (u τ i)⁻¹ (inv_ne_zero (hu τ i))
  have hrepr : ∀ (v : Fin n → Ω) i, wB.repr v i = u τ i * v i := by
    intro v i
    simp [wB, Units.smul_def]
  have hflagH : IsFlagFrame x H wB (fun i => -a τ i) := by
    refine ⟨fun c hc i => ?_⟩
    have hc' : mseg x c ≠ 0 := hc
    have key := ((CF c hc').2.2 i).2.2 _ (hgne i c hc') (hl τ i c hc')
    ext z
    constructor
    · rintro ⟨v, hv, hz, rfl⟩
      have h0 : ∀ j, i < j → v j = 0 := fun j hj => by
        have h1 := hz j hj
        rw [hrepr] at h1
        exact (mul_eq_zero.1 h1).resolve_left (hu τ j)
      obtain ⟨e, he, hev⟩ := (key (v i)).1 ⟨v, hv, h0, rfl⟩
      refine ⟨e, he, ?_⟩
      show wB.repr v i = e * chartMon x c (-a τ i)
      rw [hrepr, hev, chartMon_neg', mul_inv]
      field_simp [hu τ i]
    · rintro ⟨e, he, rfl⟩
      obtain ⟨v, hv, h0, hvi⟩ := (key (e * (u τ i * chartMon x c (a τ i))⁻¹)).2 ⟨e, he, rfl⟩
      refine ⟨v, hv, fun j hj => by rw [hrepr, h0 j hj, mul_zero], ?_⟩
      show wB.repr v i = e * chartMon x c (-a τ i)
      rw [hrepr, hvi, chartMon_neg', mul_inv]
      field_simp [hu τ i]
  have hflagT : IsFlagFrame x Tn (Pi.basisFun Ω (Fin n)) 0 := by
    refine ⟨fun c hc i => ?_⟩
    have hc' : mseg x c ≠ 0 := hc
    ext z
    constructor
    · rintro ⟨v, hv, -, rfl⟩
      rw [(hHT c hc').2] at hv
      refine ⟨v i, (mem_stdLat' _).1 hv i, ?_⟩
      simp
    · rintro ⟨e, he, rfl⟩
      refine ⟨Pi.single i e, ?_, fun j hj => ?_, ?_⟩
      · rw [(hHT c hc').2]
        refine (mem_stdLat' _).2 fun j => ?_
        by_cases h : j = i
        · subst h
          have he' : e ∈ chartRing O (mseg x) c := he
          simpa using he'
        · simpa [h] using zero_mem (chartRing O (mseg x) c)
      · simp [(ne_of_lt hj).symm]
      · simp
  have htri : ∀ i j : Fin n, i < j → wB.repr (Pi.basisFun Ω (Fin n) i) j = 0 := by
    intro i j hij
    rw [hrepr]
    simp [(ne_of_lt hij).symm]
  have ops := GlobalTheory.T.chart_bundle_product O Ω K ι x
  have e1 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x 1 (-a τ i) A.lat :=
    fun i => ops.2.2.1 1 _ one_ne_zero
  have e2 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x (u τ i) 0 A.lat :=
    fun i => ops.2.2.1 _ _ (hu τ i)
  have e3 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω,
      IsLine O x (u τ i ^ (-1 : ℤ)) ((-1 : ℤ) • a τ i) A.lat :=
    fun i => ops.2.2.1 _ _ (zpow_ne_zero _ (hu τ i))
  choose A1 hA1 using e1
  choose A2 hA2 using e2
  choose A3 hA3 using e3
  have hlX : ∀ i, IsLine O x (u τ i) (a τ i) (Xb τ i).lat := by
    intro i c hc v
    rw [hXb τ i c hc]
    exact hl τ i c hc v
  have hSG12 : ∀ i, SameGeneric O x (A1 i) (A2 i) := by
    intro i c hc
    obtain ⟨hg, e, he, hwe⟩ := hgR i c hc
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · obtain ⟨ρ, hρ, rfl⟩ := (hA1 i c hc v).1 hv
      refine (hA2 i c hc _).2 ⟨ρ * e, mul_mem hρ he, ?_⟩
      rw [chartMon_zero', smul_eq_mul, hwe]
      have h1 := hgm i c hc
      calc e * (u τ i * chartMon x c (a τ i)) * (ρ * (1 * chartMon x c (-a τ i)))
          = ρ * e * ((u τ i * chartMon x c (a τ i)) * chartMon x c (-a τ i)) := by ring
        _ = _ := by rw [h1, mul_one]
    · obtain ⟨ρ, hρ, rfl⟩ := (hA2 i c hc v).1 hv
      rw [map_one, one_smul]
      refine (hA1 i c hc _).2 ⟨ρ * (u τ i * chartMon x c (a τ i)), mul_mem hρ hg, ?_⟩
      rw [chartMon_zero', one_mul, mul_one, mul_assoc, hgm i c hc]
  have hSGX : ∀ i, SameGeneric O x (Xb τ i) T := by
    intro i c hc
    obtain ⟨hg, e, he, hwe⟩ := hgR i c hc
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
    · obtain ⟨ρ, hρ, rfl⟩ := (hlX i c hc v).1 hv
      rw [map_one, one_smul]
      refine (hT c hc _).2 ⟨ρ * (u τ i * chartMon x c (a τ i)), mul_mem hρ hg, ?_⟩
      rw [chartMon_zero']
      ring
    · obtain ⟨ρ, hρ, rfl⟩ := (hT c hc v).1 hv
      refine (hlX i c hc _).2 ⟨ρ * e, mul_mem hρ he, ?_⟩
      rw [chartMon_zero', smul_eq_mul, hwe]
      ring
  refine ⟨hSG, fun k hk1 hk2 q L Q hQ => ?_⟩
  have hsum := GlobalTheory.T.ck_eq_sum_ck_line_summands O Ω K ι x d hmodel n (Fin n → Ω) H Tn hSG wB (Pi.basisFun Ω (Fin n))
    (fun i => -a τ i) 0 hflagH hflagT htri A1 A2
    (fun i => ⟨hA1 i, by
      have h1 : wB.repr (Pi.basisFun Ω (Fin n) i) i = u τ i := by
        rw [hrepr]
        simp
      rw [h1]
      exact hA2 i⟩) k hk1 hk2 q L Q hQ
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP := (GlobalTheory.T.line_bundle_chart_generic_comparison O Ω K ι x d hmodel (Xb τ i) T (A3 i) (u τ i) (a τ i) (-1) (hu τ i) (hlX i)
    hT (hSGX i) (hA3 i)).2 k hk1 hk2 q L Q hQ
  have hTr := (GlobalTheory.T.same_generic_linear_equiv O Ω K ι x d hmodel 1 Ω Ω
    (LinearEquiv.smulOfNeZero Ω Ω (u τ i)⁻¹ (inv_ne_zero (hu τ i))) (A1 i) (A2 i) (A3 i) T (hSG12 i)
    (fun c hc v => ?_)).1 k hk1 hk2 q L Q hQ
  · rw [← hTr, hP]
  · have he : (LinearEquiv.smulOfNeZero Ω Ω (u τ i)⁻¹ (inv_ne_zero (hu τ i))) v = (u τ i)⁻¹ * v := rfl
    rw [he]
    constructor
    · rw [hA3 i c hc, hA1 i c hc]
      simp only [zpow_neg_one, neg_smul, one_smul, inv_line (hu τ i)]
    · rw [hT c hc, hA2 i c hc]
      simp only [inv_line' (hu τ i)]

end GlobalTheory.CompanionTheory.Ar.Num.RelH
