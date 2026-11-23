import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeparableOfNewtonPolygon
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyCoeffValuation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenValuationLtOne

open ValuativeRel Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.mem_iw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin n) k) :
    g ∈ GlobalTheory.SmGL.iwahori k (Fin n) ↔
      (∀ i j, valuation k (g.val i j) ≤ 1) ∧ (∀ i j, valuation k ((g⁻¹).val i j) ≤ 1) ∧
        ∀ i j, j < i → valuation k (g.val i j) < 1 := by
  constructor
  · intro hg
    have key : ∀ h ∈ GlobalTheory.SmGL.iwahori k (Fin n), ∀ i j, valuation k (h.val i j) ≤ 1 := by
      rintro _ ⟨h, -, rfl⟩ i j
      exact (h.val i j).2
    exact ⟨key g hg, key _ (inv_mem hg), (GlobalTheory.SmGL.mem_iwahori.1 hg).2⟩
  · rintro ⟨h1, h2, h3⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
    have inj : Function.Injective
        ((algebraMap 𝒪[k] k).mapMatrix : Matrix (Fin n) (Fin n) 𝒪[k] → Matrix (Fin n) (Fin n) k) :=
      Matrix.map_injective Subtype.val_injective
    let h : GL (Fin n) 𝒪[k] := ⟨A, B, inj (by rw [map_mul, hA, hB, map_one]; exact g.mul_inv),
      inj (by rw [map_mul, hA, hB, map_one]; exact g.inv_mul)⟩
    have hh : GeneralLinearGroup.map (algebraMap 𝒪[k] k) h = g := Units.ext hA
    refine ⟨h, (GlobalTheory.SmGL.mem_borel _).2 fun i j hij => ?_, hh⟩
    show IsLocalRing.residue 𝒪[k] (A i j) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact (h3 i j hij).ne

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.det_iw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ GlobalTheory.SmGL.iwahori k (Fin n)) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, -, rfl⟩ := hg
  have h1 : (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).val.det = algebraMap 𝒪[k] k h.val.det :=
    ((algebraMap 𝒪[k] k).map_det h.val).symm
  rw [h1, ← (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact (GeneralLinearGroup.det h).isUnit

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.sep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (x : Fin n → ℤ)
    (hx : StrictAnti x) {a b : GL (Fin n) k} (ha : a ∈ GlobalTheory.SmGL.iwahori k (Fin n))
    (hb : b ∈ GlobalTheory.SmGL.iwahori k (Fin n)) :
    (a * GlobalTheory.SmGL.diagT k (Fin n) (fun i => ϖ ^ x i) * b).val.charpoly.Separable := by
  have hM := mul_mem hb ha
  obtain ⟨h1, -, h3⟩ := (mem_iw _).1 hM
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hs : StrictMono fun i => valuation k ((ϖ ^ x i : kˣ) : k) := by
    intro i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_lt_zpow_right_of_lt_one₀ h0 hϖ (hx hij)
  rw [Units.val_mul, Units.val_mul, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, ← Units.val_mul,
    GlobalTheory.SmGL.val_diagT]
  exact UpperTheory.separable_of_newton_polygon (valuation k) n _ hs (fun i => (map_ne_zero _).2 (Units.ne_zero _)) _ (Matrix.charpoly_monic _) (by simp)
    (UpperTheory.charpoly_coeff_valuation (valuation k) n _ _ h1 h3 (det_iw hM) hs fun i => Units.ne_zero _)

private theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (hc : IsCompact (I : Set G)) (t : G) (f : G → ℂ)
    (hf : ∀ y, f y ≠ 0 → ∃ a ∈ I, ∃ b ∈ I, y = a * t * b) : HasCompactSupport f := by
  have hK : IsCompact ((fun p : G × G => p.1 * t * p.2) '' ((I : Set G) ×ˢ (I : Set G))) :=
    (hc.prod hc).image (by fun_prop)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra h
  obtain ⟨a, ha, b, hb, rfl⟩ := hf y h
  exact hy ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem UpperTheory.Reformulated.B.DoubleCosetSeparation.dcosSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosSep := by
  intro E _ _ _ n w ϖ hϖ x hx
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  obtain ⟨hop, hc⟩ := UpperTheory.iwahori_subgroup_open (w.adicCompletion E) n
    (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)) fun g => mem_iw g
  have hne : ∀ t y, GlobalTheory.BCT.dcos n w t y ≠ 0 ↔
      ∃ a ∈ GlobalTheory.BCT.iwGL n w, ∃ b ∈ GlobalTheory.BCT.iwGL n w, y = a * t * b := by
    intro t y
    unfold GlobalTheory.BCT.dcos
    split_ifs with h
    · simp [h]
    · simp [h]
  refine ⟨⟨GlobalTheory.BCT.iwGL n w, hop, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨h, -, rfl⟩
    have hO : ∀ z : 𝒪[w.adicCompletion E], (z : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
      intro z
      have hz : valuation (w.adicCompletion E) (z : w.adicCompletion E) ≤ 1 := z.2
      have := (Valuation.vle_one_iff (valuation _)).2 hz
      exact (Valuation.vle_one_iff (Valued.v)).1 this
    let φ : 𝒪[w.adicCompletion E] →+* Formalism.UG.Ov E w := (Subring.subtype _).codRestrict _ hO
    show _ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)
    exact ⟨GeneralLinearGroup.map φ h, Units.ext rfl⟩
  · exact supp (G := GL (Fin n) (w.adicCompletion E)) _ hc (GlobalTheory.BCT.tdiag ϖ x) _ fun y hy => (hne _ y).1 hy
  · intro k hk y
    classical
    unfold GlobalTheory.BCT.dcos
    refine ⟨if_congr ⟨?_, ?_⟩ rfl rfl, if_congr ⟨?_, ?_⟩ rfl rfl⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨k⁻¹ * a, mul_mem (inv_mem hk) ha, b, hb, by rw [mul_assoc, mul_assoc, ← mul_assoc a, ← h]; simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), by rw [← mul_assoc, ← h]; simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hne _ y).1 hy
    refine sep ϖ ?_ x hx ha hb
    have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by simp
    have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
      unfold Formalism.UG.ordL at hϖ
      rw [dif_neg h0] at hϖ
      rw [← WithZero.coe_unzero h0, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt]
      rw [toAdd_one]
      omega
    exact (Valuation.vlt_one_iff (valuation _)).1 ((Valuation.vlt_one_iff Valued.v).2 h1)
