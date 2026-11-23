import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.ContrId
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.OrdLOfVOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.OrdLEqNegLog
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.Hilbert90NormOneUnitsOfUnrOfNotSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.KerConjDiagonalEqSpan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwfLeOneOfPowMul
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.BlockEmbeddingSecondVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteriaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.InertDeltaFirstCaseEqPower
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.MaximalCurveCore
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.UnitaryHeckeOrbitSingleCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.DiagonalConjDistinctValuationsEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.TwistedOrbitalIntegralIndicatorInvIndex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuationsStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.CharpolyConjDiagT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.NrmTwconjPf

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

theorem g0 (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : ∀ p : G, f (p⁻¹ * δ * θ p) = 0) :
    twOrb θ K δ f = 0 := by
  first
    | exact twisted_orbital_integral_eq_zero_of_vanish
    | (apply twisted_orbital_integral_eq_zero_of_vanish <;> assumption)

theorem g1 [IsTopologicalGroup G] [T2Space G] (θ : G →* G) (K I : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hθK : ∀ k ∈ K, θ k ∈ K) (hI : IsLevel θ K I) (δ : G) (X : Set G)
    (hXc : IsCompact X) (hXI : ∀ i ∈ I, ∀ g : G, (i * g ∈ X ↔ g ∈ X) ∧ (g * i ∈ X ↔ g ∈ X))
    (hC : CentOK θ K I δ) (p₀ : G) (h1 : OneCoset θ I δ X p₀) :
    twOrb θ K δ (X.indicator 1) = ((I.relIndex K : ℕ) : ℂ)⁻¹ := by
  first
    | exact twisted_orbital_integral_indicator_inv_index
    | (apply twisted_orbital_integral_indicator_inv_index <;> assumption)

theorem g1prod [IsTopologicalGroup G] [T2Space G] {G' : Type} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K I : Subgroup G) (K' I' : Subgroup G')
    (δ : G) (δ' : G') (X : Set G) (X' : Set G') (p₀ : G) (p₀' : G') :
    (OneCoset θ I δ X p₀ → OneCoset θ' I' δ' X' p₀' →
      OneCoset (θ.prodMap θ') (I.prod I') (δ, δ') (X ×ˢ X') (p₀, p₀')) ∧
    (CentOK θ K I δ → CentOK θ' K' I' δ' → CentOK (θ.prodMap θ') (K.prod K') (I.prod I') (δ, δ')) := by
  first
    | exact g1prod_pf
    | (apply g1prod_pf <;> assumption)

theorem g2 (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ) (δ₀ : G) (c : ℂ) (hS : δ₀ ∈ S)
    (hinv : ∀ δ ∈ S, ∀ g : G, g⁻¹ * δ * θ g ∈ S)
    (hval : ∀ g : G, wt (g⁻¹ * δ₀ * θ g) * twOrb θ K (g⁻¹ * δ₀ * θ g) f = c)
    (hone : ∀ δ ∈ S, wt δ * twOrb θ K δ f ≠ 0 → ∃ g : G, δ = g⁻¹ * δ₀ * θ g) :
    clSum θ K S wt f = c := by
  first
    | exact twisted_class_sum_eq_single_orbit
    | (apply twisted_class_sum_eq_single_orbit <;> assumption)

theorem g2zero (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ)
    (h : ∀ δ ∈ S, wt δ * twOrb θ K δ f = 0) : clSum θ K S wt f = 0 := by
  first
    | exact g2zero_pf
    | (apply g2zero_pf <;> assumption)

theorem g3 (θ : G →* G) (K : Subgroup G) (δ : G) (f₁ f₂ : G → ℂ) (c : ℂ)
    (h : ∀ p : G, f₁ (p⁻¹ * δ * θ p) = c * f₂ (p⁻¹ * δ * θ p)) : twOrb θ K δ f₁ = c * twOrb θ K δ f₂ := by
  first
    | exact twisted_orbital_integral_proportional
    | (apply twisted_orbital_integral_proportional <;> assumption)

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem r1 (w : Pl E) (n : ℕ) (v : Fin n → ℤ) (hv : Function.Injective v) (d d' h : GLw n w)
    (hd : (∀ i j : Fin n, i ≠ j → d.val i j = 0) ∧ ∀ i, ordL (d.val i i) = v i)
    (hd' : (∀ i j : Fin n, i ≠ j → d'.val i j = 0) ∧ ∀ i, ordL (d'.val i i) = v i)
    (hh : h⁻¹ * d * h = d') : d = d' ∧ ∀ i j : Fin n, i ≠ j → h.val i j = 0 := by
  first
    | exact diagonal_conj_distinct_valuations_eq
    | (apply diagonal_conj_distinct_valuations_eq <;> assumption)

theorem r2 (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (x : Fin a → ℤ)
    (hx : StrictAnti x) (τ τ' h : GLw a w) (hτ : τ ∈ TO a w) (hτ' : τ' ∈ TO a w)
    (hh : h⁻¹ * (tdiag ϖ x * τ) * thL a w h = tdiag ϖ x * τ') :
    ∃ z ∈ twCent (thL a w) (tdiag ϖ x * τ), ∃ s ∈ TO a w, h = z * s := by
  first
    | exact le_and_half_le_prod_one_sub_exp_neg_of_bounds
    | (apply le_and_half_le_prod_one_sub_exp_neg_of_bounds <;> assumption)

theorem iw_facts (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (t : GLw a w) :
    IsOpen (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧ IsCompact (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w a, thL a w k ∈ GlobalTheory.LFun.KGL w a) ∧ IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧
    IsLevel (MonoidHom.id _) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 ∧
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  first
    | exact iw_facts_pf
    | (apply iw_facts_pf <;> assumption)

theorem iwU_facts (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧
    IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  first
    | exact iwU_facts_pf
    | (apply iwU_facts_pf <;> assumption)

theorem nrm_twconj (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w) :
    (nrmL a w (g⁻¹ * δ * thL a w g)).val.charpoly = (nrmL a w δ).val.charpoly := by
  first
    | exact nrm_twconj_pf w hw a g δ
    | (apply nrm_twconj_pf w hw a g δ <;> assumption)

namespace S1

section Diag

variable {L : Type} [Field L] {n : ℕ}

def IsDiag (g : GL (Fin n) L) : Prop := ∀ i j, i ≠ j → g.val i j = 0

theorem diag_val {g : GL (Fin n) L} (hg : IsDiag g) : g.val = diagonal fun i => g.val i i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [diagonal_apply_ne _ h, hg i j h]

theorem diag_entry_ne {g : GL (Fin n) L} (hg : IsDiag g) (i : Fin n) : g.val i i ≠ 0 := by
  have h := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rw [diag_val hg, det_diagonal] at h
  exact Finset.prod_ne_zero_iff.mp h.ne_zero i (Finset.mem_univ i)

theorem diag_inv_val {g : GL (Fin n) L} (hg : IsDiag g) :
    (g⁻¹).val = diagonal fun i => (g.val i i)⁻¹ := by
  have h1 : g.val * diagonal (fun i => (g.val i i)⁻¹) = 1 := by
    rw [diag_val hg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [diagonal_apply_eq]
    exact mul_inv_cancel₀ (diag_entry_ne hg i)
  calc (g⁻¹).val = (g⁻¹).val * (g.val * diagonal fun i => (g.val i i)⁻¹) := by rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem diag_mul {g h : GL (Fin n) L} (hg : IsDiag g) (hh : IsDiag h) :
    IsDiag (g * h) ∧ ∀ i, (g * h).val i i = g.val i i * h.val i i := by
  have e : (g * h).val = diagonal fun i => g.val i i * h.val i i := by
    rw [Units.val_mul, diag_val hg, diag_val hh, diagonal_mul_diagonal]
    simp
  refine ⟨fun i j hij => by rw [e, diagonal_apply_ne _ hij], fun i => by rw [e, diagonal_apply_eq]⟩

theorem diag_diagT (s : Fin n → Lˣ) : IsDiag (GlobalTheory.SmGL.diagT L (Fin n) s) ∧
    ∀ i, (GlobalTheory.SmGL.diagT L (Fin n) s).val i i = s i := by
  refine ⟨fun i j hij => by rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_ne _ hij], fun i => by
    rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_eq]⟩

theorem eq_diagT {g : GL (Fin n) L} (hg : IsDiag g) :
    g = GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.mk0 (g.val i i) (diag_entry_ne hg i) := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_diagT]
  conv_lhs => rw [diag_val hg]
  simp

end Diag

section Ord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_of_eq' {x : L} {u : Multiplicative ℤ} (h : Valued.v x = (u : WithZero (Multiplicative ℤ))) :
    ordL x = -Multiplicative.toAdd u := by
  have h0 : Valued.v x ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dif_neg h0]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_unzero, h]

theorem ordL_mul' {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) : ordL (a * b) = ordL a + ordL b := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 ha'
  obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.1 hb'
  have hab : Valued.v (a * b) = ((u * w : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_mul, ← hu, ← hw, WithZero.coe_mul]
  rw [ordL_of_eq' hab, ordL_of_eq' hu.symm, ordL_of_eq' hw.symm, toAdd_mul]
  ring

theorem ordL_congr' {a b : L} (h : Valued.v a = Valued.v b) : ordL a = ordL b := by
  unfold ordL
  simp only [h]

theorem ordL_unit {a : L} (h : Valued.v a = 1) : ordL a = 0 := by
  have h' : Valued.v a = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by rw [h, WithZero.coe_one]
  rw [ordL_of_eq' h']
  simp

theorem ordL_inv' {a : L} (ha : a ≠ 0) : ordL a⁻¹ = -ordL a := by
  have h := ordL_mul' ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, ordL_unit (map_one _)] at h
  omega

theorem ordL_zpow' (ϖ : Lˣ) (hϖ : ordL (ϖ : L) = 1) (k : ℤ) : ordL ((ϖ ^ k : Lˣ) : L) = k := by
  have h0 : Valued.v (ϖ : L) ≠ 0 := (Valuation.ne_zero_iff _).2 ϖ.ne_zero
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
  have h1 := ordL_of_eq' hu.symm
  have h2 : Valued.v ((ϖ ^ k : Lˣ) : L) = ((u ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← hu, WithZero.coe_zpow]
  rw [ordL_of_eq' h2, toAdd_zpow]
  rw [hϖ] at h1
  have : Multiplicative.toAdd u = -1 := by omega
  rw [this]
  ring

end Ord

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_transport {G : Type} [Group G] (θ : G →* G) (δ q z : G) :
    z * δ = δ * θ z ↔ (q⁻¹ * z * q) * (q⁻¹ * δ * θ q) = (q⁻¹ * δ * θ q) * θ (q⁻¹ * z * q) := by
  simp only [map_mul, map_inv]
  constructor
  · intro h
    calc q⁻¹ * z * q * (q⁻¹ * δ * θ q) = q⁻¹ * (z * δ) * θ q := by group
      _ = q⁻¹ * (δ * θ z) * θ q := by rw [h]
      _ = _ := by group
  · intro h
    have h2 := congrArg (fun x => q * x * (θ q)⁻¹) h
    beta_reduce at h2
    calc z * δ = q * (q⁻¹ * z * q * (q⁻¹ * δ * θ q)) * (θ q)⁻¹ := by group
      _ = q * (q⁻¹ * δ * θ q * ((θ q)⁻¹ * θ z * θ q)) * (θ q)⁻¹ := h2
      _ = δ * θ z := by group

theorem mem_twCent' {G : Type} [Group G] (θ : G →* G) (δ z : G) : z ∈ twCent θ δ ↔ z * δ = δ * θ z := Iff.rfl

theorem thL_val (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g : GLw a w) (i j : Fin a) :
    (thL a w g).val i j = (-1) ^ ((i : ℕ) + j) * cj w ((g⁻¹).val j.rev i.rev) := by
  unfold thL
  rw [if_neg hw]
  exact GlobalTheory.ThetaPull.thetaGL_apply _ g i j

theorem thL_diag (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) {g : GLw a w} (hg : IsDiag g) :
    IsDiag (thL a w g) ∧ ∀ i, (thL a w g).val i i = cj w ((g.val i.rev i.rev)⁻¹) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thL_val w hw, diag_inv_val hg, diagonal_apply_ne]
    · simp
    · exact fun h => hij (Fin.rev_injective h).symm
  · rw [thL_val w hw, diag_inv_val hg, diagonal_apply_eq]
    have : (-1 : w.adicCompletion E) ^ ((i : ℕ) + i) = 1 := Even.neg_one_pow ⟨i, rfl⟩
    rw [this, one_mul]

theorem TO_le_iw (w : Pl E) (a : ℕ) {s : GLw a w} (hs : s ∈ TO a w) : s ∈ iwGL a w := by
  have hd : IsDiag s := hs.1
  rw [(GlobalTheory.T.iwahori_and_maximal_compact_criteria E w a s).1]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · by_cases h : i = j
    · subst h; exact (hs.2 i).le
    · rw [hd i j h, map_zero]; exact zero_le
  · rw [diag_inv_val hd]
    by_cases h : i = j
    · subst h; rw [diagonal_apply_eq, map_inv₀, hs.2 i, inv_one]
    · rw [diagonal_apply_ne _ h, map_zero]; exact zero_le
  · rw [hd i j (ne_of_gt hij), map_zero]; exact zero_lt_one

theorem d_diag (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) (y : Fin a → ℤ) {τ : GLw a w} (hτ : τ ∈ TO a w) :
    IsDiag (tdiag ϖ y * τ) ∧ ∀ i, (tdiag ϖ y * τ).val i i = ((ϖ ^ y i : (w.adicCompletion E)ˣ) : _) * τ.val i i := by
  have ht := diag_diagT (L := w.adicCompletion E) (fun i => ϖ ^ y i)
  obtain ⟨h1, h2⟩ := diag_mul (g := tdiag ϖ y) ht.1 hτ.1
  exact ⟨h1, fun i => by rw [h2]; unfold tdiag; rw [ht.2 i]⟩

theorem nrm_d (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ)
    (y : Fin a → ℤ) {τ : GLw a w} (hτ : τ ∈ TO a w) :
    IsDiag (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)) ∧
      ∀ i, (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)).val i i ≠ 0 ∧
        ordL ((tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)).val i i) = nv y i := by
  have hv : ∀ x, Valued.v (cj w x) = Valued.v x := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1
  obtain ⟨hd, hde⟩ := d_diag w ϖ a y hτ
  obtain ⟨hθ, hθe⟩ := thL_diag w hw a hd
  obtain ⟨hN, hNe⟩ := diag_mul hd hθ
  refine ⟨hN, fun i => ⟨diag_entry_ne hN i, ?_⟩⟩
  have hτu : ∀ j, ordL (τ.val j j) = 0 := fun j => ordL_unit (hτ.2 j)
  have hdo : ∀ j, ordL ((tdiag ϖ y * τ).val j j) = y j := fun j => by
    rw [hde j, ordL_mul' (Units.ne_zero _) (diag_entry_ne hτ.1 j), ordL_zpow' ϖ hϖ.1, hτu, add_zero]
  rw [hNe i, ordL_mul' (diag_entry_ne hd i) (diag_entry_ne hθ i), hdo i, hθe i,
    ordL_congr' (hv _), ordL_inv' (diag_entry_ne hd _), hdo]
  unfold nv
  ring

theorem nv_injective {a : ℕ} {y : Fin a → ℤ} (hy : StrictAnti y) : Function.Injective (nv y) := by
  have hs : StrictAnti (nv y) := by
    intro i j hij
    unfold nv
    have h1 := hy hij
    have h2 : j.rev < i.rev := Fin.rev_lt_rev.2 hij
    have h3 := hy h2
    omega
  exact hs.injective

theorem cpt_top {G : Type} [Group G] [TopologicalSpace G] (t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (⟨t, Subgroup.mem_top t⟩ : (⊤ : Subgroup G)) : Set (⊤ : Subgroup G))) := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : (⊤ : Subgroup G) → G) := by
    apply IsClosed.isClosedEmbedding_subtypeVal
    rw [Subgroup.coe_top]
    exact isClosed_univ
  have himg : Subtype.val '' (Subgroup.zpowers (⟨t, Subgroup.mem_top t⟩ : (⊤ : Subgroup G)) : Set (⊤ : Subgroup G)) =
      Subgroup.zpowers t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simp⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨⟨t, Subgroup.mem_top t⟩ ^ k, Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩, by simp⟩
  rw [hemb.isInducing.closure_eq_preimage_closure_image, himg]
  exact hemb.isCompact_preimage h

theorem relIndex_ne_zero_of_isOpen' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K K' : Subgroup G} (hK : IsCompact (K : Set G)) (hK' : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen (K'.subgroupOf K) (hK'.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem continuous_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (x : G) :
    Continuous fun y : G => (MulAut.conj x).toMonoidHom y := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (continuous_const.mul continuous_id).mul continuous_const

end Local

end S1

open S1 in

theorem s1 (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (y : Fin a → ℤ)
    (hy : StrictAnti y) (δ : GLw a w) (hP : ∃ p : GLw a w, dcos a w (tdiag ϖ y) (p⁻¹ * δ * thL a w p) ≠ 0) :
    (∃ p₀, OneCoset (thL a w) (iwGL a w) δ {g | dcos a w (tdiag ϖ y) g ≠ 0} p₀) ∧
      CentOK (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) δ ∧ HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨m, hm, τ, hτ, hmτ⟩ := contr_tw hU w hw ϖ hϖ a y hy _ hp
  obtain ⟨hKo, hKc, -, hIlev, -, -, -⟩ := iw_facts w hw a (tdiag ϖ y)
  have hIo : IsOpen (iwGL a w : Set (GLw a w)) := hIlev.1
  have hIc : IsCompact (iwGL a w : Set (GLw a w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) hIlev.2.1
  have hθI : ∀ k ∈ iwGL a w, thL a w k ∈ iwGL a w := hIlev.2.2

  have h0 : (p * m)⁻¹ * δ * thL a w (p * m) = tdiag ϖ y * τ := by
    rw [← hmτ, map_mul]; group

  have hcent : ∀ z, z ∈ twCent (thL a w) δ ↔ (p * m)⁻¹ * z * (p * m) ∈ twCent (thL a w) (tdiag ϖ y * τ) := by
    intro z
    rw [mem_twCent', mem_twCent', tw_transport (thL a w) δ (p * m) z, h0]

  have hTI : ∀ s ∈ TO a w, s ∈ iwGL a w := fun s hs => TO_le_iw w a hs

  obtain ⟨hNd, hNe⟩ := nrm_d hU w hw ϖ hϖ a y hτ
  have hcdiag : ∀ c ∈ twCent (thL a w) (tdiag ϖ y * τ), IsDiag c := by
    intro c hc
    rw [mem_twCent'] at hc
    have hc2 : thL a w c * thL a w (tdiag ϖ y * τ) = thL a w (tdiag ϖ y * τ) * c := by
      have := congrArg (thL a w) hc
      rwa [map_mul (thL a w) c, map_mul (thL a w) (tdiag ϖ y * τ), GlobalTheory.BCT.TwistInvol.thL_involutive] at this
    have hcN : c * (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)) = tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ) * c := by
      rw [← mul_assoc, hc, mul_assoc, hc2, ← mul_assoc]
    have hcomm : c⁻¹ * (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)) * c =
        tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ) := by
      rw [mul_assoc, ← hcN]; group
    have hN : (∀ i j : Fin a, i ≠ j → (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)).val i j = 0) ∧
        ∀ i, ordL ((tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)).val i i) = nv y i :=
      ⟨hNd, fun i => (hNe i).2⟩
    exact (r1 w a (nv y) (nv_injective hy) _ _ c hN hN hcomm).2
  have hcpt : cptPart (twCent (thL a w) δ) ≤ (iwGL a w).map (MulAut.conj (p * m)).toMonoidHom := by
    unfold cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hcpt⟩
    have hc := (hcent t).1 ht
    have hcd := hcdiag _ hc
    set c := (p * m)⁻¹ * t * (p * m) with hcdef
    have htc : t = (p * m) * GlobalTheory.SmGL.diagT _ (Fin a) (fun i => Units.mk0 (c.val i i) (diag_entry_ne hcd i)) *
        (p * m)⁻¹ := by
      rw [← eq_diagT hcd, hcdef]; group
    have hu := GlobalTheory.T.compact_element_eigenvalues_units E w a ⊤ ⟨t, Subgroup.mem_top t⟩ (p * m) _ htc (cpt_top t hcpt)
    have hcTO : c ∈ TO a w := ⟨hcd, fun i => by simpa using hu i⟩
    refine Subgroup.mem_map.2 ⟨c, hTI c hcTO, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcdef]
    group
  refine ⟨⟨p * m, ⟨fun q => ?_, hcpt⟩⟩, fun x => ⟨?_, ?_⟩, ?_⟩
  ·
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hq
      obtain ⟨m', hm', τ', hτ', e'⟩ := contr_tw hU w hw ϖ hϖ a y hy _ hq
      have hh : ((p * m)⁻¹ * q * m')⁻¹ * (tdiag ϖ y * τ) * thL a w ((p * m)⁻¹ * q * m') = tdiag ϖ y * τ' := by
        rw [← e', ← h0]
        simp only [map_mul, map_inv]
        group
      obtain ⟨c, hc, s, hs, hcs⟩ := r2 hU w hw ϖ hϖ a y hy τ τ' _ hτ hτ' hh
      refine ⟨(p * m) * c * (p * m)⁻¹, (hcent _).2 ?_, s * m'⁻¹, mul_mem (hTI s hs) (inv_mem hm'), ?_⟩
      · have : (p * m)⁻¹ * ((p * m) * c * (p * m)⁻¹) * (p * m) = c := by group
        rw [this]; exact hc
      · calc q = (p * m) * ((p * m)⁻¹ * q * m') * m'⁻¹ := by group
          _ = _ := by rw [hcs]; group
    · rintro ⟨z, hz, i, hi, rfl⟩
      rw [mem_twCent'] at hz
      have hz' : z⁻¹ * δ * thL a w z = δ := by rw [mul_assoc, ← hz]; group
      have e : (z * (p * m) * i)⁻¹ * δ * thL a w (z * (p * m) * i) =
          i⁻¹ * tdiag ϖ y * (τ * thL a w i) := by
        calc (z * (p * m) * i)⁻¹ * δ * thL a w (z * (p * m) * i)
            = i⁻¹ * ((p * m)⁻¹ * (z⁻¹ * δ * thL a w z) * thL a w (p * m)) * thL a w i := by
              simp only [map_mul]; group
          _ = _ := by rw [hz', h0]; group
      rw [e]
      unfold dcos
      rw [if_pos ⟨i⁻¹, inv_mem hi, τ * thL a w i, mul_mem (hTI τ hτ) (hθI i hi), rfl⟩]
      exact one_ne_zero
  ·
    rintro g ⟨hg1, hg2⟩
    apply Subgroup.subset_closure
    refine ⟨hg1, ?_⟩
    have hC : IsCompact ((GlobalTheory.LFun.KGL w a).map (MulAut.conj x).toMonoidHom : Set (GLw a w)) := by
      rw [Subgroup.coe_map]
      exact hKc.image (continuous_conj x)
    have hsub : (Subgroup.zpowers g : Set (GLw a w)) ⊆ ((GlobalTheory.LFun.KGL w a).map (MulAut.conj x).toMonoidHom : Set _) :=
      Subgroup.zpowers_le.2 hg2
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  ·
    have hCT : cptPart (twCent (thL a w) δ) ≤ twCent (thL a w) δ := (Subgroup.closure_le _).2 fun t ht => ht.1
    have hUo : IsOpen ((iwGL a w).map (MulAut.conj x).toMonoidHom : Set (GLw a w)) := by
      rw [Subgroup.coe_map]
      have e : (⇑(MulAut.conj x).toMonoidHom : GLw a w → GLw a w) = (· * x⁻¹) ∘ (x * ·) := by
        funext y; simp [MulAut.conj_apply]
      rw [e]
      exact ((isOpenMap_mul_right x⁻¹).comp (isOpenMap_mul_left x)) _ hIo
    have hC'c : IsCompact ((iwGL a w).map (MulAut.conj (p * m)).toMonoidHom : Set (GLw a w)) := by
      rw [Subgroup.coe_map]; exact hIc.image (continuous_conj _)
    have h1 := relIndex_ne_zero_of_isOpen' hC'c hUo
    have h2 : ((iwGL a w).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL a w) δ)) ≠ 0 :=
      fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right hcpt h)
    have h3 : ((iwGL a w).map (MulAut.conj x).toMonoidHom ⊓ cptPart (twCent (thL a w) δ)).relIndex
        (cptPart (twCent (thL a w) δ)) ≠ 0 := by
      rwa [Subgroup.inf_relIndex_right]
    have hle : (iwGL a w).map (MulAut.conj x).toMonoidHom ⊓ cptPart (twCent (thL a w) δ) ≤
        twCent (thL a w) δ ⊓ (iwGL a w).map (MulAut.conj x).toMonoidHom := fun g hg => ⟨hCT hg.2, hg.1⟩
    intro h
    have hd := Subgroup.relIndex_dvd_of_le_left (cptPart (twCent (thL a w) δ)) hle
    rw [h] at hd
    exact h3 (Nat.eq_zero_of_zero_dvd hd)
  ·
    refine ⟨fun i => (tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ)).val i i, ?_, fun i => hNe i⟩
    rw [← nrm_twconj w hw a (p * m) δ, h0]
    have : nrmL a w (tdiag ϖ y * τ) = tdiag ϖ y * τ * thL a w (tdiag ϖ y * τ) := by
      unfold nrmL thL; rw [if_neg hw, if_neg hw]
    rw [this, diag_val hNd, charpoly_diagonal]
    simp only [diagonal_apply_eq]

theorem s2 (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) :
    (∃ p₀, OneCoset (MonoidHom.id (UL n w)) (iwU n w b) γ {g | fU n w b ϖ l g ≠ 0} p₀) ∧
      CentOK (MonoidHom.id (UL n w)) (KL n w) (iwU n w b) γ ∧ HasVals γ.1.val.charpoly (wexp n l) := by
  first
    | exact unitary_hecke_orbit_single_coset
    | (apply unitary_hecke_orbit_single_coset <;> assumption)

theorem k1 (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (hQ : γ.1.val.charpoly = Q₁ * Q₂) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic) (hc₁ : IsCsr w Q₁) (hc₂ : IsCsr w Q₂) :
    kapSign n w Q₁ γ.1 = 1 := by
  obtain ⟨-, -, hV⟩ := s2 hU w hw n b hb ϖ hϖ l hl γ hP
  obtain ⟨hanti, hrev⟩ := GlobalTheory.T.weight_exponent_strictly_antitone n l hl
  refine Kap.kapSign_eq_one_of_vals hU w n γ.1 γ.2 (wexp n l) hanti.injective ?_ hV Q₁
  intro i j h
  exact hanti.injective (h.trans (hrev i).symm)

theorem v1 (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    delta w 1 Q₁ Q₂ = (-qh w) ^ (-vRes n a (lOf x) s) := by
  first
    | exact inert_delta_first_case_eq_power
    | (apply inert_delta_first_case_eq_power <;> assumption)

theorem ext (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ)
    (y : Fin a → ℤ) (hy : StrictAnti y) (Q : (w.adicCompletion E)[X]) (hm : Q.Monic) (hQ : IsCsr w Q)
    (hv : HasVals Q (nv y)) :
    ∃ δ : GLw a w, dcos a w (tdiag ϖ y) δ ≠ 0 ∧ (nrmL a w δ).val.charpoly = Q := by
  first
    | exact ext_pf
    | (apply ext_pf <;> assumption)

theorem exu (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (Q : (w.adicCompletion E)[X])
    (hm : Q.Monic) (hQ : IsCsr w Q) (hv : HasVals Q (wexp n l)) :
    ∃ γ : UL n w, fU n w b ϖ l γ ≠ 0 ∧ γ.1.val.charpoly = Q := by
  first
    | exact exu_pf
    | (apply exu_pf <;> assumption)

theorem combine_caseA (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    HasVals (Q₁ * Q₂) (wexp n (lOf x)) := by
  first
    | exact combine_caseA_pf
    | (apply combine_caseA_pf <;> assumption)

theorem split_caseA (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic) (hd₁ : Q₁.natDegree = a)
    (hd₂ : Q₂.natDegree = n - a) (hc₁ : IsCsr w Q₁) (hc₂ : IsCsr w Q₂) (hv : HasVals (Q₁ * Q₂) (wexp n (lOf x))) :
    ∃ s, CaseA w n a x Q₁ Q₂ s := by
  first
    | exact split_caseA_pf
    | (apply split_caseA_pf <;> assumption)

theorem aL_relIndex_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem aL_cancel (K A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) : K * A * B * (A * B)⁻¹ = K := by
  rw [mul_assoc K A B, mul_assoc, mul_inv_cancel₀ (mul_ne_zero hA hB), mul_one]

theorem aL_restr_anti {n m : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) := fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem aL_symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) (j : Fin n) :
    j.rev ∈ symIdx n mid s ↔ j ∈ symIdx n mid s := by
  have hj := j.isLt
  have key : ∀ (p q : ℕ) (hp : p < n / 2) (hq : q < n / 2), p = q →
      ((⟨p, hp⟩ : Fin (n / 2)) ∈ s ↔ (⟨q, hq⟩ : Fin (n / 2)) ∈ s) := by
    rintro p q hp hq rfl; rfl
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev]
  constructor
  · rintro (⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩)
    · exact Or.inr (Or.inl ⟨by omega, (key _ _ _ _ (by omega)).mp hs⟩)
    · exact Or.inl ⟨by omega, (key _ _ _ _ (by omega)).mp hs⟩
    · exact Or.inr (Or.inr ⟨hm, ho, by omega⟩)
  · rintro (⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩)
    · exact Or.inr (Or.inl ⟨by omega, (key _ _ _ _ (by omega)).mp hs⟩)
    · exact Or.inl ⟨by omega, (key _ _ _ _ (by omega)).mp hs⟩
    · exact Or.inr (Or.inr ⟨hm, ho, by omega⟩)

theorem aL_emb_rev {n m : ℕ} (S : Finset (Fin n)) (hS : ∀ j : Fin n, j.rev ∈ S ↔ j ∈ S) (h : S.card = m)
    (i : Fin m) : S.orderEmbOfFin h i.rev = (S.orderEmbOfFin h i).rev := by
  have hf : (fun i : Fin m => (S.orderEmbOfFin h i.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro i
      rw [hS]
      exact Finset.orderEmbOfFin_mem S h _
    · intro i i' hii
      rw [Fin.rev_lt_rev]
      exact (S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hii)
  have := congrFun hf i.rev
  rw [Fin.rev_rev] at this
  exact this.symm

theorem aL_lOf_pos {n : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) (k : Fin (n / 2)) : 0 < lOf x k := by
  have hk := k.isLt
  have : x ⟨n - 1 - k.val, by omega⟩ < x ⟨k.val, by omega⟩ := hx (Fin.mk_lt_mk.mpr (by omega))
  unfold lOf
  linarith

theorem aL_lOf_inj {n : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) : Function.Injective (lOf x) := by
  have : StrictAnti (lOf x) := by
    intro k k' hkk
    have hk := k.isLt
    have hk' := k'.isLt
    have hkk' : k.val < k'.val := hkk
    have h1 : x ⟨k'.val, by omega⟩ < x ⟨k.val, by omega⟩ := hx (Fin.mk_lt_mk.mpr hkk')
    have h2 : x ⟨n - 1 - k.val, by omega⟩ < x ⟨n - 1 - k'.val, by omega⟩ := hx (Fin.mk_lt_mk.mpr (by omega))
    unfold lOf
    linarith
  exact this.injective

theorem aL_diff_eq {n : ℕ} (x : Fin n → ℤ) (p q r t : Fin n) (h1 : p.val = r.val) (h2 : q.val = t.val) :
    x p - x q = x r - x t := by
  rw [Fin.ext h1, Fin.ext h2]

theorem aL_mem_iff {n m : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) (mid : Prop) [Decidable mid]
    (s : Finset (Fin (n / 2))) (h : (symIdx n mid s).card = m) (k : Fin (n / 2)) :
    k ∈ s ↔ lOf x k ∈ Set.range (nv (restr x _ h)) := by
  have hrev : ∀ j : Fin n, j.rev ∈ symIdx n mid s ↔ j ∈ symIdx n mid s := aL_symIdx_rev n mid s
  have hnv : ∀ i, nv (restr x _ h) i =
      x (Finset.orderEmbOfFin _ h i) - x (Finset.orderEmbOfFin _ h i).rev := by
    intro i
    simp only [nv, restr]
    rw [aL_emb_rev _ hrev h i]
  have hk := k.isLt
  constructor
  · intro hks
    have hj : (⟨k.val, by omega⟩ : Fin n) ∈ symIdx n mid s := by
      simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨hk, hks⟩
    obtain ⟨i, hi⟩ : ∃ i, Finset.orderEmbOfFin _ h i = (⟨k.val, by omega⟩ : Fin n) := by
      rw [← Set.mem_range, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hj
    refine ⟨i, ?_⟩
    rw [hnv, hi]
    unfold lOf
    exact aL_diff_eq x _ _ _ _ rfl (by simp only [Fin.val_rev]; omega)
  · rintro ⟨i, hi⟩
    rw [hnv] at hi
    have hjS : Finset.orderEmbOfFin _ h i ∈ symIdx n mid s := Finset.orderEmbOfFin_mem _ h i
    generalize Finset.orderEmbOfFin _ h i = j at hi hjS
    have hpos := aL_lOf_pos x hx k
    have hj := j.isLt
    by_cases hjl : j.val < n / 2
    · have hjs : (⟨j.val, hjl⟩ : Fin (n / 2)) ∈ s := by
        simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
        rcases hjS with ⟨_, hs⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
        · exact hs
        · omega
        · omega
      have e : lOf x ⟨j.val, hjl⟩ = lOf x k := by
        rw [← hi]
        unfold lOf
        exact aL_diff_eq x _ _ _ _ rfl (by simp only [Fin.val_rev]; omega)
      rw [← aL_lOf_inj x hx e]
      exact hjs
    · exfalso
      have hle : j.rev ≤ j := by
        rw [Fin.le_def, Fin.val_rev]
        omega
      have := hx.antitone hle
      linarith

theorem aL_hasVals_range {w : Pl E} {m : ℕ} (Q : (w.adicCompletion E)[X]) (v v' : Fin m → ℤ)
    (h : HasVals Q v) (h' : HasVals Q v') : Set.range v ⊆ Set.range v' := by
  obtain ⟨u, hQ, hu⟩ := h
  obtain ⟨u', hQ', hu'⟩ := h'
  rintro _ ⟨i, rfl⟩
  have h0 : Q.eval (u i) = 0 := by
    rw [hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [hQ', eval_prod] at h0
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h0
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  exact ⟨j, by rw [← (hu' j).2, ← hj, (hu i).2]⟩

theorem aL_s_eq {n a : ℕ} {w : Pl E} (x : Fin n → ℤ) (hx : StrictAnti x) (mid mid' : Prop) [Decidable mid]
    [Decidable mid'] (s s' : Finset (Fin (n / 2))) (h : (symIdx n mid s).card = a)
    (h' : (symIdx n mid' s').card = a) (Q : (w.adicCompletion E)[X]) (hv : HasVals Q (nv (restr x _ h)))
    (hv' : HasVals Q (nv (restr x _ h'))) : s = s' := by
  have e : Set.range (nv (restr x _ h)) = Set.range (nv (restr x _ h')) :=
    (aL_hasVals_range Q _ _ hv hv').antisymm (aL_hasVals_range Q _ _ hv' hv)
  ext k
  rw [aL_mem_iff x hx mid s h k, aL_mem_iff x hx mid' s' h' k, e]

theorem aL_dcos_ne {n : ℕ} {w : Pl E} (t g : GLw n w) :
    dcos n w t g ≠ 0 ↔ ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, g = x * t * z := by
  unfold dcos
  split_ifs with h <;> simp [h]

theorem aL_dcos_left {n : ℕ} {w : Pl E} (t i g : GLw n w) (hi : i ∈ iwGL n w) :
    dcos n w t (i * g) ≠ 0 ↔ dcos n w t g ≠ 0 := by
  rw [aL_dcos_ne, aL_dcos_ne]
  constructor
  · rintro ⟨x, hx, z, hz, he⟩
    refine ⟨i⁻¹ * x, mul_mem (inv_mem hi) hx, z, hz, ?_⟩
    calc g = i⁻¹ * (i * g) := by group
      _ = _ := by rw [he]; group
  · rintro ⟨x, hx, z, hz, he⟩
    exact ⟨i * x, mul_mem hi hx, z, hz, by rw [he]; group⟩

theorem aL_dcos_right {n : ℕ} {w : Pl E} (t i g : GLw n w) (hi : i ∈ iwGL n w) :
    dcos n w t (g * i) ≠ 0 ↔ dcos n w t g ≠ 0 := by
  rw [aL_dcos_ne, aL_dcos_ne]
  constructor
  · rintro ⟨x, hx, z, hz, he⟩
    refine ⟨x, hx, z * i⁻¹, mul_mem hz (inv_mem hi), ?_⟩
    calc g = (g * i) * i⁻¹ := by group
      _ = _ := by rw [he]; group
  · rintro ⟨x, hx, z, hz, he⟩
    exact ⟨x, hx, z * i, mul_mem hz hi, by rw [he]; group⟩

theorem aL_dcos_mul {a b : ℕ} {w : Pl E} (t₁ : GLw a w) (t₂ : GLw b w) (y : GLw a w × GLw b w) :
    dcos a w t₁ y.1 * dcos b w t₂ y.2 =
      ({g | dcos a w t₁ g ≠ 0} ×ˢ {g | dcos b w t₂ g ≠ 0} : Set (GLw a w × GLw b w)).indicator 1 y := by
  by_cases h1 : dcos a w t₁ y.1 = 0
  · rw [h1, zero_mul, Set.indicator_of_notMem]
    simp [h1]
  · by_cases h2 : dcos b w t₂ y.2 = 0
    · rw [h2, mul_zero, Set.indicator_of_notMem]
      simp [h2]
    · rw [Set.indicator_of_mem (by exact ⟨h1, h2⟩)]
      have e1 : dcos a w t₁ y.1 = 1 := by unfold dcos at h1 ⊢; split_ifs at h1 ⊢ <;> simp_all
      have e2 : dcos b w t₂ y.2 = 1 := by unfold dcos at h2 ⊢; split_ifs at h2 ⊢ <;> simp_all
      rw [e1, e2, Pi.one_apply, mul_one]

theorem aL_orb_val (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (a b : ℕ) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : IsUnifAt ϖ) (y₁ : Fin a → ℤ) (y₂ : Fin b → ℤ) (hy₁ : StrictAnti y₁) (hy₂ : StrictAnti y₂)
    (δ : GLw a w × GLw b w)
    (hP : ∃ p : GLw a w × GLw b w, p⁻¹ * δ * (thL a w).prodMap (thL b w) p ∈
      ({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} : Set (GLw a w × GLw b w))) :
    twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) δ
      (({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} :
        Set (GLw a w × GLw b w)).indicator 1) =
      (((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) * (iwGL b w).relIndex (GlobalTheory.LFun.KGL w b) : ℕ) : ℂ)⁻¹ := by
  obtain ⟨δ₁, δ₂⟩ := δ
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := hP
  have hp₁ : dcos a w (tdiag ϖ y₁) (p₁⁻¹ * δ₁ * thL a w p₁) ≠ 0 := hp.1
  have hp₂ : dcos b w (tdiag ϖ y₂) (p₂⁻¹ * δ₂ * thL b w p₂) ≠ 0 := hp.2
  obtain ⟨⟨q₁, hq₁⟩, hC₁, -⟩ := s1 hU w hw ϖ hϖ a y₁ hy₁ δ₁ ⟨p₁, hp₁⟩
  obtain ⟨⟨q₂, hq₂⟩, hC₂, -⟩ := s1 hU w hw ϖ hϖ b y₂ hy₂ δ₂ ⟨p₂, hp₂⟩
  obtain ⟨ho₁, hk₁, hθ₁, hI₁, -, -, hX₁⟩ := iw_facts w hw a (tdiag ϖ y₁)
  obtain ⟨ho₂, hk₂, hθ₂, hI₂, -, -, hX₂⟩ := iw_facts w hw b (tdiag ϖ y₂)
  have hpr := g1prod (thL a w) (thL b w) (GlobalTheory.LFun.KGL w a) (iwGL a w) (GlobalTheory.LFun.KGL w b) (iwGL b w) δ₁ δ₂
    {g | dcos a w (tdiag ϖ y₁) g ≠ 0} {g | dcos b w (tdiag ϖ y₂) g ≠ 0} q₁ q₂
  have hKo : IsOpen (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]; exact ho₁.prod ho₂
  have hKc : IsCompact (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) :
      Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]; exact hk₁.prod hk₂
  have hθK : ∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b),
      (thL a w).prodMap (thL b w) k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := fun k hk =>
    Subgroup.mem_prod.mpr ⟨hθ₁ _ (Subgroup.mem_prod.mp hk).1, hθ₂ _ (Subgroup.mem_prod.mp hk).2⟩
  have hI : IsLevel ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
      ((iwGL a w).prod (iwGL b w)) := by
    refine ⟨?_, Subgroup.prod_mono hI₁.2.1 hI₂.2.1, fun k hk =>
      Subgroup.mem_prod.mpr ⟨hI₁.2.2 _ (Subgroup.mem_prod.mp hk).1, hI₂.2.2 _ (Subgroup.mem_prod.mp hk).2⟩⟩
    rw [Subgroup.coe_prod]; exact hI₁.1.prod hI₂.1
  have hXI : ∀ i ∈ (iwGL a w).prod (iwGL b w), ∀ g : GLw a w × GLw b w,
      (i * g ∈ ({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} :
          Set (GLw a w × GLw b w)) ↔
        g ∈ ({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} :
          Set (GLw a w × GLw b w))) ∧
      (g * i ∈ ({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} :
          Set (GLw a w × GLw b w)) ↔
        g ∈ ({g | dcos a w (tdiag ϖ y₁) g ≠ 0} ×ˢ {g | dcos b w (tdiag ϖ y₂) g ≠ 0} :
          Set (GLw a w × GLw b w))) := by
    intro i hi g
    rw [Subgroup.mem_prod] at hi
    simp only [Set.mem_prod, Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul]
    exact ⟨and_congr (aL_dcos_left _ _ _ hi.1) (aL_dcos_left _ _ _ hi.2),
      and_congr (aL_dcos_right _ _ _ hi.1) (aL_dcos_right _ _ _ hi.2)⟩
  rw [g1 ((thL a w).prodMap (thL b w)) _ _ hKo hKc hθK hI (δ₁, δ₂) _ (hX₁.prod hX₂) hXI (hpr.2 hC₁ hC₂) (q₁, q₂)
    (hpr.1 hq₁ hq₂), aL_relIndex_prod]

theorem aL_phiX_val (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2)))
    (hsh : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2)
    (h₁ : (symIdx n (a % 2 = 1) s).card = a) (h₂ : (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a)
    (hv₁ : HasVals Q₁ (nv (restr x _ h₁))) (y : GLw a w × GLw (n - a) w)
    (hy : (nrmL a w y.1).val.charpoly = Q₁) :
    phiX n w b ϖ x a y =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ *
        ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) * ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) *
        (dcos a w (tdiag ϖ (restr x _ h₁)) y.1 * dcos (n - a) w (tdiag ϖ (restr x _ h₂)) y.2) := by
  unfold phiX
  rw [Finset.sum_eq_single s]
  · rw [dif_pos hsh, dif_pos h₁, dif_pos h₂]
    ring
  · intro s' _ hne
    split_ifs with hsh' h₁' h₂' <;> try rfl
    have hd : dcos a w (tdiag ϖ (restr x _ h₁')) y.1 = 0 := by
      by_contra hne1
      have hv := (s1 hU w hw ϖ hϖ a _ (aL_restr_anti x hx _ h₁') y.1 ⟨1, by simpa using hne1⟩).2.2
      rw [hy] at hv
      exact hne (aL_s_eq x hx _ _ s' s h₁' h₁ Q₁ hv hv₁)
    rw [hd, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem aL_unqT (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ)
    (y : Fin a → ℤ) (hy : StrictAnti y) (δ δ' : GLw a w) (h : dcos a w (tdiag ϖ y) δ ≠ 0)
    (h' : dcos a w (tdiag ϖ y) δ' ≠ 0)
    (hQ : (nrmL a w δ').val.charpoly = (nrmL a w δ).val.charpoly) :
    ∃ g : GLw a w, δ' = g⁻¹ * δ * thL a w g := by
  obtain ⟨m, -, τ, hτ, hmτ⟩ := contr_tw hU w hw ϖ hϖ a y hy δ h
  obtain ⟨m', -, τ', hτ', hmτ'⟩ := contr_tw hU w hw ϖ hϖ a y hy δ' h'
  have hc : (nrmL a w (tdiag ϖ y * τ)).val.charpoly = (nrmL a w (tdiag ϖ y * τ')).val.charpoly := by
    rw [← hmτ, ← hmτ', nrm_twconj w hw, nrm_twconj w hw, hQ]
  obtain ⟨g, -, hg⟩ := unq_diag hU w hw ϖ hϖ a y hy τ τ' hτ hτ' hc
  refine ⟨m * g * m'⁻¹, ?_⟩
  rw [← hmτ, ← hmτ'] at hg
  have e : δ' = m' * (m'⁻¹ * δ' * thL a w m') * (thL a w m')⁻¹ := by group
  rw [e, ← hg]
  simp only [map_mul, map_inv]
  group

theorem asmL_A (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    stTw2 a (n - a) w Q₁ Q₂ (phiX n w b ϖ x a) =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := by
  obtain ⟨hsh1, hsh2, hsh3, h₁, h₂, hv₁, hv₂⟩ := hA
  have hy₁ := aL_restr_anti x hx _ h₁
  have hy₂ := aL_restr_anti x hx _ h₂
  obtain ⟨δ₁, hδ₁, hQδ₁⟩ := ext hU w hw ϖ hϖ a _ hy₁ Q₁ hm₁ hc₁ hv₁
  obtain ⟨δ₂, hδ₂, hQδ₂⟩ := ext hU w hw ϖ hϖ (n - a) _ hy₂ Q₂ hm₂ hc₂ hv₂
  obtain ⟨-, -, -, -, -, hr₁, -⟩ := iw_facts w hw a (tdiag ϖ (restr x _ h₁))
  obtain ⟨-, -, -, -, -, hr₂, -⟩ := iw_facts w hw (n - a) (tdiag ϖ (restr x _ h₂))
  set X : Set (GLw a w × GLw (n - a) w) :=
    {g | dcos a w (tdiag ϖ (restr x _ h₁)) g ≠ 0} ×ˢ {g | dcos (n - a) w (tdiag ϖ (restr x _ h₂)) g ≠ 0}
    with hXdef
  set θ := (thL a w).prodMap (thL (n - a) w) with hθ
  set S : Set (GLw a w × GLw (n - a) w) :=
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL (n - a) w y.2).val.charpoly = Q₂} with hS
  have hinv : ∀ δ ∈ S, ∀ g : GLw a w × GLw (n - a) w, g⁻¹ * δ * θ g ∈ S := by
    rintro δ ⟨e1, e2⟩ g
    exact ⟨(nrm_twconj w hw a g.1 δ.1).trans e1, (nrm_twconj w hw (n - a) g.2 δ.2).trans e2⟩
  have hval : ∀ y ∈ S, phiX n w b ϖ x a y =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ *
        ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) *
        ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) * X.indicator 1 y := by
    intro y hy
    rw [aL_phiX_val hU w hw n a b ϖ hϖ x hx Q₁ s ⟨hsh1, hsh2, hsh3⟩ h₁ h₂ hv₁ y hy.1, aL_dcos_mul]
  have horb : ∀ δ ∈ S, (∃ p, p⁻¹ * δ * θ p ∈ X) →
      twOrb θ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) δ (phiX n w b ϖ x a) =
        (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := by
    intro δ hδ hP
    rw [g3 _ _ δ _ (X.indicator 1) _ (fun p => hval _ (hinv δ hδ p)),
      aL_orb_val hU w hw a (n - a) ϖ hϖ _ _ hy₁ hy₂ δ hP, Nat.cast_mul]
    exact aL_cancel _ _ _ (Nat.cast_ne_zero.mpr hr₁) (Nat.cast_ne_zero.mpr hr₂)
  have hδ₀ : ((δ₁, δ₂) : GLw a w × GLw (n - a) w) ∈ S := ⟨hQδ₁, hQδ₂⟩
  unfold stTw2
  apply g2 θ _ S 1 (phiX n w b ϖ x a) (δ₁, δ₂) _ hδ₀ hinv
  · intro g
    rw [Pi.one_apply, one_mul]
    apply horb _ (hinv _ hδ₀ g)
    refine ⟨g⁻¹, ?_⟩
    have e : (g⁻¹)⁻¹ * (g⁻¹ * (δ₁, δ₂) * θ g) * θ g⁻¹ = (δ₁, δ₂) := by
      rw [map_inv]; group
    rw [e]
    exact ⟨hδ₁, hδ₂⟩
  · intro δ hδ hne
    rw [Pi.one_apply, one_mul] at hne
    obtain ⟨p, hp⟩ : ∃ p, phiX n w b ϖ x a (p⁻¹ * δ * θ p) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne (g0 θ _ δ _ hcon)
    have hyS := hinv δ hδ p
    rw [hval _ hyS] at hp
    have hyX : p⁻¹ * δ * θ p ∈ X := by
      by_contra hn
      rw [Set.indicator_of_notMem hn, mul_zero] at hp
      exact hp rfl
    obtain ⟨g₁, hg₁⟩ := aL_unqT hU w hw ϖ hϖ a _ hy₁ δ₁ _ hδ₁ hyX.1 (hyS.1.trans hQδ₁.symm)
    obtain ⟨g₂, hg₂⟩ := aL_unqT hU w hw ϖ hϖ (n - a) _ hy₂ δ₂ _ hδ₂ hyX.2 (hyS.2.trans hQδ₂.symm)
    refine ⟨(g₁, g₂) * p⁻¹, ?_⟩
    have hy : p⁻¹ * δ * θ p = (g₁, g₂)⁻¹ * (δ₁, δ₂) * θ (g₁, g₂) := Prod.ext hg₁ hg₂
    calc δ = p * (p⁻¹ * δ * θ p) * (θ p)⁻¹ := by group
      _ = ((g₁, g₂) * p⁻¹)⁻¹ * (δ₁, δ₂) * θ ((g₁, g₂) * p⁻¹) := by
        rw [hy, map_mul, map_inv]; group

theorem aLB_restr_anti {n m : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) := fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem asmL_B (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (hB : ∀ s, ¬ CaseA w n a x Q₁ Q₂ s) :
    stTw2 a (n - a) w Q₁ Q₂ (phiX n w b ϖ x a) = 0 := by
  unfold stTw2
  apply g2zero
  intro δ hδ
  rw [Pi.one_apply, one_mul]
  apply g0
  intro p
  have hy1 : (nrmL a w (p⁻¹ * δ * (thL a w).prodMap (thL (n - a) w) p).1).val.charpoly = Q₁ :=
    (nrm_twconj w hw a p.1 δ.1).trans hδ.1
  have hy2 : (nrmL (n - a) w (p⁻¹ * δ * (thL a w).prodMap (thL (n - a) w) p).2).val.charpoly = Q₂ :=
    (nrm_twconj w hw (n - a) p.2 δ.2).trans hδ.2
  unfold phiX
  apply Finset.sum_eq_zero
  intro s' _
  split_ifs with hsh h₁ h₂ <;> try rfl
  by_contra hne
  have hd2 := right_ne_zero_of_mul hne
  have hd1 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have v1 := (s1 hU w hw ϖ hϖ a _ (aLB_restr_anti x hx _ h₁)
    (p⁻¹ * δ * (thL a w).prodMap (thL (n - a) w) p).1 ⟨1, by simpa using hd1⟩).2.2
  have v2 := (s1 hU w hw ϖ hϖ (n - a) _ (aLB_restr_anti x hx _ h₂)
    (p⁻¹ * δ * (thL a w).prodMap (thL (n - a) w) p).2 ⟨1, by simpa using hd2⟩).2.2
  rw [hy1] at v1
  rw [hy2] at v2
  exact hB s' ⟨hsh.1, hsh.2.1, hsh.2.2, h₁, h₂, v1, v2⟩

section
variable {G : Type} [Group G] [TopologicalSpace G]

theorem meets_of_ne (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb (MonoidHom.id G) K δ f ≠ 0) :
    ∃ p : G, f (p⁻¹ * δ * p) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact h (g0 (MonoidHom.id G) K δ f (fun p => by simpa using hcon p))

end

theorem isCsr_mul (w : Pl E) {Q₁ Q₂ : (w.adicCompletion E)[X]} (h₁ : IsCsr w Q₁) (h₂ : IsCsr w Q₂) :
    IsCsr w (Q₁ * Q₂) := by
  rcases h₁ with h | h₁
  · exact Or.inl h
  rcases h₂ with h | h₂
  · exact Or.inl h
  right
  rw [Polynomial.mul_coeff_zero, map_mul, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h₁, ← h₂,
    C_mul]
  ring

theorem charpoly_conj (w : Pl E) (n : ℕ) (g δ : UL n w) :
    (g⁻¹ * δ * g).1.val.charpoly = δ.1.val.charpoly := by
  rw [show (g⁻¹ * δ * g).1.val = ((g : GLw n w)⁻¹).val * (δ : GLw n w).val * (g : GLw n w).val from rfl]
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem fU_ne_iff (w : Pl E) (n : ℕ) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ)
    (g : UL n w) :
    fU n w b ϖ l g ≠ 0 ↔ ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, g.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
  unfold fU
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_ne_zero⟩
  · exact ⟨fun h' => (h' rfl).elim, fun h' => (h h').elim⟩

theorem fU_biinv (w : Pl E) (n : ℕ) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ)
    (i : UL n w) (hi : i ∈ iwU n w b) (g : UL n w) :
    (fU n w b ϖ l (i * g) ≠ 0 ↔ fU n w b ϖ l g ≠ 0) ∧ (fU n w b ϖ l (g * i) ≠ 0 ↔ fU n w b ϖ l g ≠ 0) := by
  simp only [fU_ne_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨i⁻¹ * x, mul_mem (inv_mem hi) hx, z, hz, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    calc (g : GLw n w) = (i : GLw n w)⁻¹ * ((i : GLw n w) * g) := by group
      _ = _ := by rw [h]; group
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨i * x, mul_mem hi hx, z, hz, ?_⟩
    simp only [Subgroup.coe_mul] at h ⊢
    rw [h]; group
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨x, hx, z * i⁻¹, mul_mem hz (inv_mem hi), ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    calc (g : GLw n w) = ((g : GLw n w) * i) * (i : GLw n w)⁻¹ := by group
      _ = _ := by rw [h]; group
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨x, hx, z * i, mul_mem hz hi, ?_⟩
    simp only [Subgroup.coe_mul] at h ⊢
    rw [h]; group

theorem fU_eq_ind (w : Pl E) (n : ℕ) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) :
    fU n w b ϖ l = {g | fU n w b ϖ l g ≠ 0}.indicator 1 := by
  funext g
  have h01 : fU n w b ϖ l g = 0 ∨ fU n w b ϖ l g = 1 := by
    unfold fU; split_ifs <;> simp
  rcases h01 with h | h <;> simp [Set.indicator, h]

theorem orbR (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) :
    twOrb (MonoidHom.id (UL n w)) (KL n w) γ (fU n w b ϖ l) = (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := by
  obtain ⟨⟨p₀, h1⟩, hC, -⟩ := s2 hU w hw n b hb ϖ hϖ l hl γ hP
  obtain ⟨hKo, hKc, hI, -, hXc⟩ := iwU_facts w hw n b hb ϖ l
  rw [fU_eq_ind w n b ϖ l]
  exact g1 (MonoidHom.id _) (KL n w) (iwU n w b) hKo hKc (fun k hk => hk) hI γ _ hXc
    (fun i hi g => fU_biinv w n b ϖ l i hi g) hC p₀ h1

theorem uniqR (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ γ' : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) (hP' : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ' * p) ≠ 0)
    (hQ : γ.1.val.charpoly = γ'.1.val.charpoly) : ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  obtain ⟨p₀, u, hu, hγ, -, -, hQγ⟩ := s2raw hU w hw n b hb ϖ hϖ l hl γ hP
  obtain ⟨p₁, u', hu', hγ', -, -, hQγ'⟩ := s2raw hU w hw n b hb ϖ hϖ l hl γ' hP'
  have hinj : Function.Injective (wexp n l) := (GlobalTheory.T.weight_exponent_strictly_antitone n l hl).1.injective
  have huu : (fun i => (u i : w.adicCompletion E)) = fun i => (u' i : w.adicCompletion E) :=
    GlobalTheory.T.roots_eq_of_distinct_valuations (w.adicCompletion E) n (wexp n l) hinj (fun i => (u i : w.adicCompletion E))
      (fun i => (u' i : w.adicCompletion E)) hu hu' (by rw [← hQγ, ← hQγ', hQ])
  have hu_eq : u = u' := funext fun i => Units.ext (congrFun huu i)
  subst hu_eq
  have heq : p₀⁻¹ * γ * p₀ = p₁⁻¹ * γ' * p₁ := Subtype.ext (hγ.trans hγ'.symm)
  refine ⟨p₀ * p₁⁻¹, ?_⟩
  calc γ' = p₁ * (p₁⁻¹ * γ' * p₁) * p₁⁻¹ := by group
    _ = p₁ * (p₀⁻¹ * γ * p₀) * p₁⁻¹ := by rw [heq]
    _ = (p₀ * p₁⁻¹)⁻¹ * γ * (p₀ * p₁⁻¹) := by group

theorem asmR_A (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s) :
    delta w 1 Q₁ Q₂ * kapOrb n w Q₁ Q₂ (fU n w b ϖ (lOf x)) =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := by
  have hdel := v1 w hw n a ha x hx Q₁ Q₂ s hA
  have hvals := combine_caseA w hw n a ha x hx Q₁ Q₂ s hA
  obtain ⟨γ₀, hγ₀, hγ₀Q⟩ :=
    exu hU w hw n b hb ϖ hϖ (lOf x) hc (Q₁ * Q₂) (hm₁.mul hm₂) (isCsr_mul w hc₁ hc₂) hvals
  have key : ∀ γ : UL n w, γ.1.val.charpoly = Q₁ * Q₂ → (∃ p : UL n w, fU n w b ϖ (lOf x) (p⁻¹ * γ * p) ≠ 0) →
      kapSign n w Q₁ γ.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) γ (fU n w b ϖ (lOf x)) =
        1 * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := fun γ hQ hP => by
    rw [k1 hU w hw n b hb ϖ hϖ (lOf x) hc γ hP Q₁ Q₂ hQ hm₁ hm₂ hc₁ hc₂,
      orbR hU w hw n b hb ϖ hϖ (lOf x) hc γ hP]
  have hkap : kapOrb n w Q₁ Q₂ (fU n w b ϖ (lOf x)) = 1 * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ := by
    unfold kapOrb
    refine g2 (MonoidHom.id _) (KL n w) _ _ _ γ₀ _ hγ₀Q ?_ ?_ ?_
    · intro δ hδ g
      have hδ' : δ.1.val.charpoly = Q₁ * Q₂ := hδ
      show (g⁻¹ * δ * (MonoidHom.id _) g).1.val.charpoly = Q₁ * Q₂
      rw [MonoidHom.id_apply, charpoly_conj, hδ']
    · intro g
      refine key _ (by rw [MonoidHom.id_apply, charpoly_conj, hγ₀Q]) ⟨g⁻¹, ?_⟩
      rw [MonoidHom.id_apply, show (g⁻¹)⁻¹ * (g⁻¹ * γ₀ * g) * g⁻¹ = γ₀ by group]
      exact hγ₀
    · intro δ hδ hne
      have hδ' : δ.1.val.charpoly = Q₁ * Q₂ := hδ
      obtain ⟨g, hg⟩ := uniqR hU w hw n b hb ϖ hϖ (lOf x) hc γ₀ δ ⟨1, by simpa using hγ₀⟩
        (meets_of_ne _ _ _ (right_ne_zero_of_mul hne)) (by rw [hγ₀Q, hδ'])
      exact ⟨g, by simpa using hg⟩
  rw [hdel, hkap, one_mul]

theorem asmR_B (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (hB : ∀ s, ¬ CaseA w n a x Q₁ Q₂ s) :
    kapOrb n w Q₁ Q₂ (fU n w b ϖ (lOf x)) = 0 := by
  unfold kapOrb
  refine g2zero (MonoidHom.id _) (KL n w) _ _ _ ?_
  intro δ hδ
  by_contra hne
  have hδ' : δ.1.val.charpoly = Q₁ * Q₂ := hδ
  obtain ⟨-, -, hv⟩ := s2 hU w hw n b hb ϖ hϖ (lOf x) hc δ (meets_of_ne _ _ _ (right_ne_zero_of_mul hne))
  rw [hδ'] at hv
  obtain ⟨s, hs⟩ := split_caseA w hw n a ha x hx Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hc₁ hc₂ hv
  exact hB s hs

theorem asmReg_mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {k : Fin n} :
    k ∈ symIdx n mid s ↔
      (∃ j ∈ s, (j : ℕ) = k ∨ (j : ℕ) = n - 1 - k) ∨ (mid ∧ n % 2 = 1 ∧ (k : ℕ) = n / 2) := by
  simp only [symIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h, hm⟩ | ⟨h, hm⟩ | hmid)
    · exact Or.inl ⟨_, hm, Or.inl rfl⟩
    · exact Or.inl ⟨_, hm, Or.inr rfl⟩
    · exact Or.inr hmid
  · rintro (⟨j, hj, hjk | hjk⟩ | hmid)
    · have hj' := j.isLt
      refine Or.inl ⟨by omega, ?_⟩
      rwa [show (⟨k.val, by omega⟩ : Fin (n / 2)) = j from Fin.ext hjk.symm]
    · have hj' := j.isLt
      refine Or.inr (Or.inl ⟨by omega, ?_⟩)
      rwa [show (⟨n - 1 - k.val, by omega⟩ : Fin (n / 2)) = j from Fin.ext hjk.symm]
    · exact Or.inr (Or.inr hmid)

theorem asmReg_symIdx_rev {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {k : Fin n}
    (hk : k ∈ symIdx n mid s) : k.rev ∈ symIdx n mid s := by
  rw [asmReg_mem_symIdx] at hk ⊢
  have hr : (k.rev : ℕ) = n - (k + 1) := Fin.val_rev k
  have hkn := k.isLt
  rcases hk with ⟨j, hj, hjk⟩ | ⟨hm, hn, hkm⟩
  · exact Or.inl ⟨j, hj, by omega⟩
  · exact Or.inr ⟨hm, hn, by omega⟩

theorem asmReg_disj {n : ℕ} {s : Finset (Fin (n / 2))} {m1 m2 : Prop} [Decidable m1] [Decidable m2]
    (hm : ¬ (m1 ∧ m2)) : Disjoint (symIdx n m1 s) (symIdx n m2 sᶜ) := by
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  rw [asmReg_mem_symIdx] at hk1 hk2
  have hkn := k.isLt
  rcases hk1 with ⟨j, hj, hjk⟩ | ⟨hm1, hn, hkm⟩ <;> rcases hk2 with ⟨j', hj', hjk'⟩ | ⟨hm2, hn', hkm'⟩
  · rw [Finset.mem_compl] at hj'
    have h1 := j.isLt
    have h2 := j'.isLt
    have hjj : j = j' := Fin.ext (by omega)
    exact hj' (hjj ▸ hj)
  · have h1 := j.isLt
    omega
  · have h2 := j'.isLt
    omega
  · exact hm ⟨hm1, hm2⟩

theorem asmReg_oe_rev {n m : ℕ} {S : Finset (Fin n)} (hS : ∀ k ∈ S, k.rev ∈ S) (h : S.card = m) (i : Fin m) :
    S.orderEmbOfFin h i.rev = (S.orderEmbOfFin h i).rev := by
  have key : (fun i : Fin m => (S.orderEmbOfFin h i.rev).rev) = S.orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h (fun i => hS _ (S.orderEmbOfFin_mem h _))
      (fun i j hij => Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij)))
  have hi : (S.orderEmbOfFin h i.rev).rev = S.orderEmbOfFin h i := congrFun key i
  exact (Fin.rev_rev _).symm.trans (congrArg Fin.rev hi)

theorem asmReg_nv_restr {n m : ℕ} (x : Fin n → ℤ) {S : Finset (Fin n)} (hS : ∀ k ∈ S, k.rev ∈ S)
    (h : S.card = m) (i : Fin m) :
    nv (restr x S h) i = x (S.orderEmbOfFin h i) - x (S.orderEmbOfFin h i).rev := by
  simp only [nv, restr]
  rw [asmReg_oe_rev hS h i]

theorem asmReg_F_inj {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun k : Fin n => x k - x k.rev := by
  intro k k' hkk
  simp only at hkk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hx hlt
    have h2 := hx (Fin.rev_lt_rev.mpr hlt)
    omega
  · have h1 := hx hlt
    have h2 := hx (Fin.rev_lt_rev.mpr hlt)
    omega

theorem asmReg_sep {w : Pl E} {n a b : ℕ} (x : Fin n → ℤ) (hx : StrictAnti x) (S₁ S₂ : Finset (Fin n))
    (hS₁ : ∀ k ∈ S₁, k.rev ∈ S₁) (hS₂ : ∀ k ∈ S₂, k.rev ∈ S₂) (hdis : Disjoint S₁ S₂) (h₁ : S₁.card = a)
    (h₂ : S₂.card = b) (P₁ P₂ : (w.adicCompletion E)[X]) (hP₁ : HasVals P₁ (nv (restr x S₁ h₁)))
    (hP₂ : HasVals P₂ (nv (restr x S₂ h₂))) : (P₁ * P₂).Separable := by
  obtain ⟨u, rfl, hu⟩ := hP₁
  obtain ⟨v, rfl, hv⟩ := hP₂
  have e : (∏ i, (X - C (u i))) * (∏ j, (X - C (v j))) =
      ∏ p : Fin a ⊕ Fin b, (X - C (Sum.elim u v p)) := by
    rw [Fintype.prod_sum_type]
    rfl
  rw [e, separable_prod_X_sub_C_iff]
  have hF := asmReg_F_inj hx
  have key : ∀ p, ordL (Sum.elim u v p) =
      (fun k : Fin n => x k - x k.rev) (Sum.elim (S₁.orderEmbOfFin h₁) (S₂.orderEmbOfFin h₂) p) := by
    rintro (i | j)
    · simp only [Sum.elim_inl]
      rw [(hu i).2, asmReg_nv_restr x hS₁ h₁]
    · simp only [Sum.elim_inr]
      rw [(hv j).2, asmReg_nv_restr x hS₂ h₂]
  intro p q hpq
  have h1 := hF ((key p).symm.trans ((congrArg ordL hpq).trans (key q)))
  rcases p with i | i <;> rcases q with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr] at h1
  · exact congrArg _ ((S₁.orderEmbOfFin h₁).injective h1)
  · exact (Finset.disjoint_left.mp hdis (S₁.orderEmbOfFin_mem h₁ i)
      (by rw [h1]; exact S₂.orderEmbOfFin_mem h₂ j)).elim
  · exact (Finset.disjoint_left.mp hdis (S₁.orderEmbOfFin_mem h₁ j)
      (by rw [← h1]; exact S₂.orderEmbOfFin_mem h₂ i)).elim
  · exact congrArg _ ((S₂.orderEmbOfFin h₂).injective h1)

theorem asmReg (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) : RegAt2 a (n - a) w (phiX n w b ϖ x a) := by
  intro y hy
  unfold phiX at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  split_ifs at hs with h h₁ h₂ <;> try exact absurd rfl hs
  have hd₂ := right_ne_zero_of_mul hs
  have hd₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hs)
  have hv₁ := (s1 hU w hw ϖ hϖ a (restr x _ h₁)
    (fun i j hij => hx ((Finset.orderEmbOfFin _ h₁).strictMono hij)) y.1
    ⟨1, by rw [inv_one, one_mul, map_one, mul_one]; exact hd₁⟩).2.2
  have hv₂ := (s1 hU w hw ϖ hϖ (n - a) (restr x _ h₂)
    (fun i j hij => hx ((Finset.orderEmbOfFin _ h₂).strictMono hij)) y.2
    ⟨1, by rw [inv_one, one_mul, map_one, mul_one]; exact hd₂⟩).2.2
  exact asmReg_sep x hx _ _ (fun k hk => asmReg_symIdx_rev hk) (fun k hk => asmReg_symIdx_rev hk)
    (asmReg_disj (fun hm => by omega)) h₁ h₂ _ _ hv₁ hv₂

theorem m4 : M4 := by
  intro E _ _ _ hU w hw n a ha b hb ϖ hϖ x hx hc
  refine ⟨?_, asmReg hU w hw n a ha b hb ϖ hϖ x hx hc⟩
  intro Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hs hc₁ hc₂
  by_cases hA : ∃ s, CaseA w n a x Q₁ Q₂ s
  · obtain ⟨s, hA⟩ := hA
    rw [asmL_A hU w hw n a ha b hb ϖ hϖ x hx hc Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hs hc₁ hc₂ s hA,
      asmR_A hU w hw n a ha b hb ϖ hϖ x hx hc Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hs hc₁ hc₂ s hA]
  · push_neg at hA
    rw [asmL_B hU w hw n a ha b hb ϖ hϖ x hx hc Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hs hc₁ hc₂ hA,
      asmR_B hU w hw n a ha b hb ϖ hϖ x hx hc Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hs hc₁ hc₂ hA, mul_zero]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
