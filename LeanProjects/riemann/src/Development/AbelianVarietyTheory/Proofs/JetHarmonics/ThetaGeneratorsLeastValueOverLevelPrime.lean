import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueTranslatePullbackEqGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartFormStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuationStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChartStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.LevelPrimePoint

theorem crP_mem_harmK_of_disjoint {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ} (k : Type) [Field k]
    (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (cc : T → T) (isX : T → Prop)
    (hβ : ∀ τ i i', β ⟨τ, i⟩ ≠ β ⟨cc τ, i'⟩) :
    Crude.crP r n k β a ∈ harmK r n k cc isX (fun _ => 1) := by
  have hS := Crude.crP_mem_supported (n := n) k β a
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    have key : MvPolynomial.pderiv (⟨τ, i, b⟩ : Letter T r n)
        (MvPolynomial.pderiv (⟨cc τ, i', b⟩ : Letter T r n) (Crude.crP r n k β a)) = 0 := by
      by_cases hg : (⟨cc τ, i', b⟩ : Letter T r n) ∈ Crude.GoodL r n β
      · have hg' : (⟨τ, i, b⟩ : Letter T r n) ∉ Crude.GoodL r n β := by
          rintro ⟨j, hj⟩
          obtain ⟨j', hj'⟩ := hg
          exact hβ τ j j' (hj.trans hj'.symm)
        exact MvPolynomial.pderiv_eq_zero_of_notMem_vars
          (fun hv => hg' (MvPolynomial.mem_supported.1 (Crude.crPderiv_supported _ hS) hv))
      · rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hv => hg (MvPolynomial.mem_supported.1 hS hv)), map_zero]
    simpa using congrArg (fun x => (1 : k) • x) key
  · simp [Matrix.one_apply_ne hb]

open Classical in

theorem exists_minor_harm (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (typ : (E →+* ℂ) → Prop) (htyp : ∀ τ, typ τ ↔ ¬ typ (ComplexEmbedding.conjugate τ))
    (a : (E →+* ℂ) × ℕ → ℕ) (ha : ∀ τ, Antitone fun i => a (τ, i)) (n₁ n₂ : ℕ)
    (h1 : ∀ τ, Dw.mult τ ≤ n₁) (h2 : ∀ τ, Dw.mult τ ≤ n₂) :
    ∃ m : (E →+* ℂ) → ℕ → ℕ, (∀ τ s, m τ s ≠ 0 → 1 ≤ s ∧ s ≤ Dw.mult τ) ∧ degOf Dw m = DF Dw a ∧
      ∃ Ppol ∈ harmA (Dw := Dw) c a (n₁ + n₂), ∀ (K : Type) [CommRing K] (φ : c.F →+* K),
        MvPolynomial.map φ Ppol = minorProd Dw K typ m n₁ (fun i => Fin.castAdd n₂ i) *
          minorProd Dw K (fun τ => ¬ typ τ) m n₂ (fun i => Fin.natAdd n₁ i) := by
  let a' : (E →+* ℂ) → ℕ → ℕ := fun τ i => a (τ, i)
  have hdom : Crude.Dom Dw.mult a' := fun σ i j hij => ha σ hij
  let m : (E →+* ℂ) → ℕ → ℕ := fun τ s =>
    if h : 1 ≤ s ∧ s ≤ Dw.mult τ then Crude.crExp Dw.mult a' τ ⟨s - 1, by omega⟩ else 0
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ Dw.mult τ) → m τ s = 0 := fun τ s h => dif_neg h
  have hm1 : ∀ τ (s : Fin (Dw.mult τ)), m τ (s.val + 1) = Crude.crExp Dw.mult a' τ s := fun τ s =>
    dif_pos ⟨Nat.le_add_left _ _, s.isLt⟩
  let β : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Fin (n₁ + n₂) := fun p =>
    if typ p.1 then Fin.castAdd n₂ (Fin.castLE (h1 p.1) p.2) else Fin.natAdd n₁ (Fin.castLE (h2 p.1) p.2)
  refine ⟨m, fun τ s h => by_contra fun h' => h (hm0 τ s h'), ?_,
    MvPolynomial.map (Int.castRingHom c.F) (Crude.Pmin Dw.mult (n₁ + n₂) β a'), ⟨?_, fun mo => ?_⟩, ?_⟩
  · unfold degOf DF
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range le_rfl (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    have := fun i : Fin (Dw.mult τ) => Crude.crExpSum a' hdom τ i
    change _ = ∑ i : Fin (Dw.mult τ), a' τ i
    simp only [← this, hm1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have : (Finset.univ.filter fun i : Fin (Dw.mult τ) => (i : ℕ) < (s : ℕ) + 1) = Finset.Iic s := by
      ext i; simp [Nat.lt_succ_iff]
    rw [this, Fin.card_Iic]
  · rw [Crude.crP_map]
    refine ⟨crP_mem_harmK_of_disjoint c.F β a' _ _ ?_, Crude.crP_rowInv c.F β a', Crude.crP_rowDeg c.F β a' hdom⟩
    intro τ i i' h
    have h' := congrArg Fin.val h
    have hi := lt_of_lt_of_le i.isLt (h1 τ)
    have hi' := lt_of_lt_of_le i'.isLt (h1 _)
    by_cases ht : typ τ
    · simp only [β, if_pos ht, if_neg ((htyp τ).1 ht), Fin.val_castAdd, Fin.val_castLE, Fin.val_natAdd] at h'
      omega
    · have ht' : typ (ComplexEmbedding.conjugate τ) := by_contra fun h => ht ((htyp τ).2 h)
      simp only [β, if_neg ht, if_pos ht', Fin.val_castAdd, Fin.val_castLE, Fin.val_natAdd] at h'
      omega
  · rw [MvPolynomial.coeff_map]
    exact intCast_mem _ _
  · intro K _ φ
    rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp _) (Int.castRingHom K), Crude.crP_map]
    unfold minorProd Crude.crP
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range le_rfl _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨Nat.succ_le_of_lt s.isLt, (Nat.succ_le_of_lt s.isLt).trans (h1 τ)⟩
      rw [dif_pos hs, hm1]
      unfold GSt.leadMinor
      congr 2
      ext i j : 2
      simp only [Crude.crMinor, β, if_pos h, Matrix.of_apply]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range le_rfl _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨Nat.succ_le_of_lt s.isLt, (Nat.succ_le_of_lt s.isLt).trans (h2 τ)⟩
      rw [dif_pos hs, hm1]
      unfold GSt.leadMinor
      congr 2
      ext i j : 2
      simp only [Crude.crMinor, β, if_neg h, Matrix.of_apply]
      rfl

theorem val_eq_vV (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) (F : Type) [Field F] [Algebra T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (x : T.Fr) (hx : x ≠ 0) :
    v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
  rw [hv x n hn]
  obtain ⟨u, rfl⟩ := hn
  have h1 : valV T.V (algebraMap T.V T.Fr ϖ) = WithZero.exp (-1 : ℤ) := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  have h2 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) u.isUnit
  unfold vV
  rw [map_mul, map_zpow₀, h1, h2, _root_.mul_one, ← WithZero.exp_zsmul, WithZero.log_exp]
  simp

theorem val_nonneg_of_ringOfIntegers (E : Type) [Field E] [NumberField E] (F : Type) [Field F]
    (v : AddValuation F (WithTop ℚ)) (φ : 𝓞 E →+* F) (a : 𝓞 E) : 0 ≤ v (φ a) := by
  have h : IsIntegral ℤ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map φ.toIntAlgHom
  have h' : IsIntegral (AddValuation.toValuation v).integer (φ a) := h.tower_top
  exact (Valuation.integer.integers (AddValuation.toValuation v)).isIntegral_iff_v_le_one.1 h'

theorem exists_val_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {k : ℕ} (a z : Fin k → F)
    (ha : ∀ i, 0 ≤ v (a i)) (ρ : ℚ) (h : v (∑ i, a i * z i) = (ρ : WithTop ℚ)) : ∃ i, v (z i) ≤ (ρ : WithTop ℚ) := by
  by_contra hn
  push Not at hn
  have : (ρ : WithTop ℚ) < v (∑ i, a i * z i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun i _ => ?_
    rw [v.map_mul]
    exact lt_of_lt_of_le (hn i) (le_add_of_nonneg_left (ha i))
  exact this.ne h.symm

theorem nval_add_le (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) (F : Type) [Field F] [Algebra T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (ε : F) (hε : 0 ≤ v ε) (A x : T.Fr) (ρ : ℚ)
    (h : v (ε * algebraMap T.Fr F A * algebraMap T.Fr F x) ≤ (ρ : WithTop ℚ)) (B : ℝ) (hB : (ρ : ℝ) ≤ B) (e : ℕ) :
    nval T.V e x + nval T.V e A ≤ ((B / e : ℝ) : EReal) := by
  rw [_root_.mul_assoc, ← map_mul, v.map_mul] at h
  have h1 : v (algebraMap T.Fr F (A * x)) ≤ (ρ : WithTop ℚ) := (le_add_of_nonneg_left hε).trans h
  have h0 : A * x ≠ 0 := by
    intro h0
    rw [h0, map_zero, v.map_zero] at h1
    exact WithTop.not_top_le_coe _ h1
  rw [val_eq_vV T ϖ hϖ F v hv _ h0, WithTop.coe_le_coe] at h1
  rw [add_comm, ← nval_mul, nval_of_ne h0, EReal.coe_le_coe_iff]
  refine div_le_div_of_nonneg_right (le_trans ?_ hB) (Nat.cast_nonneg e)
  exact_mod_cast h1

theorem exists_sec_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F]
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    {k k' : ℕ} (e : k = k') (r : Fam D'.toPre F k) (σ : U'.toUnifPre.SecGF F k') (h : PS F n (chD C.ch))
    (h1 : U'.toUnifPre.ExpandsG F k' σ (famCast (Dp := D'.toPre) (F := F) e r))
    (h2 : IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F k' σ h) :
    ∃ σ' : U'.toUnifPre.SecGF F k, U'.toUnifPre.ExpandsG F k σ' r ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F k σ' h := by
  subst e
  exact ⟨σ, h1, h2⟩

theorem least_value_le : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → l.M = g' * g → ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) → l.Mb = Ideal.span {π * π'} → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ¬ IsUnit ((g : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → 2 * (Dw.p + Dw.q) ≤ n → 1 ≤ n → 0 < e → DF Dw a < g - 1 → 4 * DF Dw a + 4 ≤ g' → (DF Dw a : ℝ) * M0 < g' → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) + nval T.V e (∏ τ : E →+* ℂ, (io (embK c τ (star π * star π'))) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) ≤ ((((vV T.V ((g : ℕ) : T.Fr) : ℤ) : ℝ) * DF Dw a / (g - 1) + (Dw.p + Dw.q : ℕ) * r * Φ / (4 * g') + 2 * (DF Dw a : ℝ) ^ 2 * Φ / g') / e : ℝ) := by
  intro hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab hTot T io y C hTr P hP hy ϖ hϖ Q hQ Φ M0 r b hΦ hb hM0 g g' hg hg' hgg hM π π' hπ hπ' hMb hcard hnd hnu
    a n e ha hn hn1 he hD1 hD2 hD3
  classical
  have hodd : Odd (g' * g) := hM ▸ l.odd
  have hog : Odd g := (Nat.odd_mul.1 hodd).2
  have hog' : Odd g' := (Nat.odd_mul.1 hodd).1
  obtain ⟨u, u', huu⟩ : ∃ u u' : 𝓞 E, u * (π * π') + u' * (star π * star π') = 1 := by
    have h := l.coprime
    rw [hMb, Ideal.map_span, Set.image_singleton, ← Ideal.span_insert, Ideal.eq_top_iff_one,
      Ideal.mem_span_pair] at h
    obtain ⟨u, u', h⟩ := h
    refine ⟨u, u', ?_⟩
    rw [map_mul] at h
    exact h
  have hc : ∃ u u' : 𝓞 E, u * π + u' * star π = 1 :=
    ⟨u * π', u' * star π', by rw [← huu]; ring⟩
  have hc' : ∃ u u' : 𝓞 E, u * π' + u' * star π' = 1 :=
    ⟨u * π, u' * star π, by rw [← huu]; ring⟩
  haveI : CharZero T.Fr := inferInstance
  obtain ⟨F, _, _, _, _, _, _, v, hv, O, _, _, _, _, hO1, hO2, hO3⟩ := GlobalTheory.T.exists_algClosed_valuedField_over_completeDVR T ϖ hϖ inferInstance
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨n₂, rfl⟩ : ∃ n₂, n = (Dw.p + Dw.q) + n₂ := ⟨n - (Dw.p + Dw.q), by omega⟩
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx1, hx2, -⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 ((Dw.p + Dw.q) + n₂)
  have hmult : ∀ τ, Dw.mult τ ≤ Dw.p + Dw.q := fun τ => by unfold Datum.mult; split_ifs <;> omega
  have hmult2 : ∀ τ, Dw.mult τ ≤ n₂ := fun τ => (hmult τ).trans (by omega)
  have hg0 : ((g : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hg.ne_zero
  have hρg : v ((g : ℕ) : F) = (((vV T.V ((g : ℕ) : T.Fr) : ℤ) : ℚ) : WithTop ℚ) := by
    rw [← val_eq_vV T ϖ hϖ F v hv _ hg0, map_natCast (algebraMap T.Fr F)]
  have hgpos : 0 < v ((g : ℕ) : F) := by
    obtain ⟨d, hd⟩ : ϖ ∣ ((g : ℕ) : T.V) := by
      rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
      exact hnu
    have h1 : v (algebraMap T.Fr F (algebraMap T.V T.Fr ϖ)) = (((1 : ℤ) : ℚ) : WithTop ℚ) :=
      hv _ 1 ⟨1, by simp⟩
    have h2 : 0 ≤ v (algebraMap T.V F d) := (hO2 _).2 ⟨algebraMap T.V O d, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
    rw [← map_natCast (algebraMap T.V F), hd, map_mul, v.map_mul, IsScalarTower.algebraMap_apply T.V T.Fr F ϖ, h1]
    exact lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right h2)
  let φ : (E →+* ℂ) → 𝓞 E →+* F := fun τ => ((algebraMap T.Fr F).comp io).comp (embK c τ)
  have hconj : ∀ τ, embK c (ComplexEmbedding.conjugate τ) (star π) = embK c τ π := by
    intro τ
    apply Subtype.ext
    rw [embK_coe, embK_coe]
    change starRingEnd ℂ (τ ((H.bar π : 𝓞 E) : E)) = _
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  have htyp : ∀ τ, (0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) ↔
      ¬ (0 < v (algebraMap T.Fr F (io (embK c (ComplexEmbedding.conjugate τ) (star π))))) := by
    intro τ
    rw [hconj]
    change 0 < v (φ τ (star π)) ↔ ¬ 0 < v (φ τ π)
    constructor
    · intro h1 h2
      obtain ⟨w, w', hw⟩ := hc
      have h3 : 0 < v (φ τ (w * π + w' * star π)) := by
        rw [map_add (φ τ), map_mul (φ τ), map_mul (φ τ)]
        refine lt_of_lt_of_le (lt_min ?_ ?_) (v.map_add _ _) <;> rw [v.map_mul]
        · exact lt_of_lt_of_le h2 (le_add_of_nonneg_left (val_nonneg_of_ringOfIntegers E F v _ _))
        · exact lt_of_lt_of_le h1 (le_add_of_nonneg_left (val_nonneg_of_ringOfIntegers E F v _ _))
      rw [hw, map_one (φ τ), v.map_one] at h3
      exact lt_irrefl _ h3
    · intro h2
      by_contra h1
      have h3 : v (φ τ (π * star π)) ≤ 0 := by
        rw [map_mul (φ τ), v.map_mul]
        exact add_nonpos (not_lt.1 h2) (not_lt.1 h1)
      rw [hπ, map_natCast (φ τ)] at h3
      exact not_lt.2 h3 hgpos
  obtain ⟨m, hm, hdeg, Ppol, hPpol, hmap⟩ := exists_minor_harm E H Dw l c _ htyp a ha (Dw.p + Dw.q) n₂ hmult hmult2
  obtain ⟨s, s₂, p, w, ζ, x, t₀, t, σ', h, ρ, b1, b2, b3, b4, b5, b6, b7, b8, b9, hval, hρ⟩ :=
    GlobalTheory.T.depthBelowOne_of_hodgeTate_chart_form hHT E H Dw l Xo c (fun _ => rfl) T io y hy C hTr P hP ϖ hϖ Q hQ g g' hg hg' hgg hog hog' π π' hπ hπ'
      hc hc' hcard hnd hnu F v hv O hO1 hO2 (hO3 g hg.ne_zero hnu) I Φ M0 r b hΦ hb hM0 (Dw.p + Dw.q) n₂ hn1
      D' A' G' pD pA pG U' PU oD' hx1 hx2 m
      (fun τ s h => ⟨(hm τ s h).1, (hm τ s h).2, by
        split_ifs
        · exact (hm τ s h).2.trans (hmult τ)
        · exact (hm τ s h).2.trans (hmult2 τ)⟩)
      (hdeg ▸ hD1) (hdeg ▸ hD2) (hdeg ▸ hD3) _ hρg
  obtain ⟨θ, θα, k, aa, hh, c1, c2, c3, haa, hsum, hi⟩ :=
    GlobalTheory.T.pointStatements_on_copies_hold.2.1 E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hgg hog hog' π π' hπ hπ' hc hc' hnu
      F v hv I _ D' A' G' pD pA pG U' PU oD' hx1 hx2 s s₂ p w ζ x t₀ t σ' h ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  letI := io.toAlgebra
  rw [← hmap F ((algebraMap T.Fr F).comp io), hsum,
    (nabJet _ _ _ C.ch.B F _ H.w0 (g' * g) _ _ _ _).2.1] at hval
  obtain ⟨i, hile⟩ := exists_val_le v _ _ haa ρ hval
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hi i
  obtain ⟨σ₃, d8', d9'⟩ := exists_sec_cast C P F pG PU (_root_.one_mul (g' * g)) r₂ σ₂ (hh i) d8 d9
  have hα : (star π * star π') * star (star π * star π') = ((l.M : ℕ) : 𝓞 E) := by
    rw [star_mul, star_star, star_star, hM, Nat.cast_mul, ← hπ, ← hπ']; ring
  have hMb' : l.Mb = Ideal.span {star (star π * star π')} := by
    rw [star_mul, star_star, star_star, hMb, mul_comm]
  have key := GlobalTheory.T.value_translate_pullback_eq_generator' E H Dw l Xo c nab hnab hTot T io y C hTr P hP hy ϖ hϖ Q hQ F v hv _ D' A' G' pD pA pG U' PU
    oD' hx1 hx2 (star π * star π') hα hMb' θ
  rw [hM] at key
  obtain ⟨f, hf, ee, hee, heq⟩ := key θα c1 c2 c3 p₂ w₂ ζ₂ x₂ r₀ r₂ σ₃ (hh i) d3 d4 d5 d1 d2 d6 d7 d8' d9' a Ppol hPpol
  rw [_root_.one_mul] at heq
  rw [heq] at hile
  simp only [← map_pow, ← map_prod] at hile
  refine le_trans (add_le_add (iInf₂_le f hf) le_rfl) (nval_add_le T ϖ hϖ F v hv ee hee _ _ ρ ?_ _ ?_ e)
  · convert hile using 4
    simp only [map_prod, map_pow]
  · rw [hdeg] at hρ
    exact_mod_cast hρ

end GlobalTheory.LevelPrimePoint
