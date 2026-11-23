import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffMoreColumns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsBetaUnitBlock
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ShortSeriesBlockProduct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSimInducing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StandardCoverShortValueEqThetaValueStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortTimesTheta

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.FormTies GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

theorem card_quot (Dw : Datum H) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    Nat.card (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) = Ideal.absNorm I ^ (Dw.p + Dw.q) := by
  haveI := Dw.fin
  haveI := Dw.proj
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  rw [natCard_quot_smul_top_of_projective, Dw.rank, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem mb_ne_bot (l : Level H) : l.Mb ≠ ⊥ ∧ Mfr l ≠ ⊥ := by
  have hM : (l.M : 𝓞 E) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have h : l.Mb * Mfr l ≠ ⊥ := by
    rw [Mfr, l.prod, Ne, Ideal.span_singleton_eq_bot]; exact hM
  exact ⟨fun e => h (by rw [e, Ideal.bot_mul]), fun e => h (by rw [e, Ideal.mul_bot])⟩

theorem finite_conjQ (Dw : Datum H) (l : Level H) : Finite (ConjQ Dw l) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_quot Dw (mb_ne_bot l).2]
    exact pow_ne_zero _ (fun h => (mb_ne_bot l).2 (Ideal.absNorm_eq_zero_iff.1 h)))

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem card_cover {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) :
    Nat.card (LevQ Dw d.l₂) = Nat.card (ConjQ Dw l) * Nat.card (LaI Xo c d) := by
  have hI : d.I ≠ ⊥ := fun e => (mb_ne_bot d.l₂).1 (by rw [hd.2.2.2.1, e, Ideal.mul_bot])
  have h1 : Ideal.absNorm (Mfr l) = Ideal.absNorm l.Mb := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv).symm
  rw [card_quot Dw (mb_ne_bot d.l₂).1, card_quot Dw (mb_ne_bot l).2, card_quot Dw hI, hd.2.2.2.1, map_mul, mul_pow, h1]

theorem pd_mem {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) : (d.pd : 𝓞 E) ∈ d.I ∧ l.Mb ⊔ d.I = ⊤ := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h2 := d.l₂.prod
  rw [hd.2.2.2.1, hd.2.1, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
    ← Ideal.span_singleton_mul_span_singleton] at h2
  have h3 := mul_left_cancel₀ (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM) h2
  have h4 : (d.pd : 𝓞 E) ∈ d.I := by
    have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I := h3 ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have h5 : (l.M : 𝓞 E) ∈ l.Mb := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  refine ⟨h4, ?_⟩
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := 𝓞 E) hd.2.2.1
  rw [Ideal.eq_top_iff_one, ← huv, add_comm]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ h5) (Ideal.mul_mem_left _ _ h4)

theorem eq_mk_iff {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) (x : Dw.La) (q : LevQ Dw d.l₂) :
    q = Submodule.Quotient.mk ((d.pd : 𝓞 E) • x) ↔ levRep q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧
      levRep q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨h1, h2⟩ := pd_mem d hd
  have hq : Submodule.Quotient.mk (levRep q) = q := Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have hp : (d.pd : 𝓞 E) • x ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul h1 trivial
  conv_lhs => rw [← hq, Submodule.Quotient.eq, hd.2.2.2.1]
  constructor
  · intro h
    refine ⟨?_, Submodule.smul_mono_left Ideal.mul_le_left h⟩
    simpa using add_mem (Submodule.smul_mono_left Ideal.mul_le_right h) hp
  · rintro ⟨ha, hb⟩
    have hc := sub_mem ha hp
    generalize levRep q - (d.pd : 𝓞 E) • x = v at hb hc
    obtain ⟨a, ha, b, hb', hab⟩ := Submodule.mem_sup.1 (h2 ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ d.I)
    have e : v = a • v + b • v := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul ha hc
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hb' hb

theorem sum_char [inst : Fintype (ConjQ Dw l)] (c : Coeff l) {m : ℕ} (u v : Fin m → Dw.La) :
    ∑ x : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) u) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x b)) v =
      if ∀ b, v b - u b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (ConjQ Dw l) : c.F) ^ m else 0 := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have hz := LevelPairing.zetaM_prim c
  have h0 : zetaM c ≠ 0 := hz.ne_zero hM.ne'
  have h1 : ∀ x : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) u) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x b)) v =
      ∏ b, zetaM c ^ Dw.EF (qRep (x b)) (cSep l • (v b - u b)) := fun x => by
    rw [← zpow_add₀ h0, ← MoreColumns.zpow_sum h0]
    congr 1
    simp only [pairL, smul_sub, map_sub, Finset.sum_sub_distrib]
    ring
  have h2 : ∀ w : Dw.La, ∑ a : ConjQ Dw l, zetaM c ^ Dw.EF (qRep a) (cSep l • w) =
      if w ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (ConjQ Dw l) : c.F) else 0 := fun w =>
    @MoreColumns.char_sum E _ _ _ H Dw l.M hM l.Mb l.prod l.coprime c.F _ _ hz inst w
  simp only [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun b (a : ConjQ Dw l) => zetaM c ^ Dw.EF (qRep a) (cSep l • (v b - u b)))]
  simp only [h2]
  rw [Finset.prod_ite_zero]
  simp

theorem sum_new_columns [Fintype (ConjQ Dw l)] {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) {m : ℕ} (x : Fin m → Dw.La)
    (q : Fin m → LevQ Dw d.l₂) :
    (∑ x' : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b)) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x' b)) (fun b => levRep (q b))) *
      (if ∀ b : Fin m, levRep (q b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) =
      if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then (Nat.card (Fin m → LevQ Dw d.l₂) : c.F) else 0 := by
  rw [sum_char, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, card_cover d hd]
  simp only [funext_iff, eq_mk_iff d hd, forall_and]
  by_cases h1 : ∀ b, levRep (q b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) <;>
    by_cases h2 : ∀ b, levRep (q b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) <;>
    simp [h1, h2, mul_pow]

theorem weighted_sum {K S ι Q : Type} [Field K] [CommRing S] [Algebra K S] [Fintype ι] [Finite Q] (cf : ι → K)
    (w : ι → Q → K) (w₀ : Q → K) (t : K) (hw : ∀ q, ∑ i, cf i * w i q = t * w₀ q) (A : S) (B : Q → S) :
    ∑ i, algebraMap K S (cf i) * (A * ∑ᶠ q, algebraMap K S (w i q) * B q) =
      algebraMap K S t * (A * ∑ᶠ q, algebraMap K S (w₀ q) * B q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_left_comm, ← mul_assoc (algebraMap K S t), ← map_mul, ← hw, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

theorem shortVal_sum (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab : NabV Xo c} (hn : IsNab Xo c nab) {n : ℕ}
    {Λ : GenLat E n} {N : ℕ} (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hL : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) {ι : Type} [Fintype ι] (cf : ι → c.F)
    (w : ι → (Fin n → LevQ Dw l) → c.F) (w₀ : (Fin n → LevQ Dw l) → c.F) (t : c.F)
    (hw : ∀ q, ∑ i, cf i * w i q = t * w₀ q) (β : c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) (u : ι → S) (hv : ShortValAt Xo c nab w₀ Λ β N P y v)
    (hu : ∀ i, ShortValAt Xo c nab (w i) Λ β N P y (u i)) :
    ∑ i, algebraMap c.F S (cf i) * u i = algebraMap c.F S t * v := by
  haveI := ShortValue.finite_levelQuotient Dw l
  obtain ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  have hinj : Function.Injective φ := h1.injective
  apply hinj
  have key := fun i => (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hn n
    Λ N hU hT hL a P hP.1 (w i) β).2 S S' φ y y' h2 (u i) _ (hu i)
    ⟨S', _, _, AlgHom.id c.F S', y', z, tp, F, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      FramedBaseChange.refl y', h3, h4, h5, h6, rfl⟩
  rw [map_sum, map_mul, h7]
  simp only [map_mul φ, AlgHom.commutes, key]
  exact weighted_sum cf w w₀ t hw _ _

theorem admissibleColumns_append {n m nV : ℕ} (h : n = nV → m = 0) (x0 : Fin n → Dw.La) (x : Fin m → Dw.La)
    (hx : AdmX (l := l) (decide (n = nV)) x0) : AdmX (l := l) (decide (n + m = nV)) (Fin.append x0 x) := by
  unfold AdmX at hx ⊢
  refine eq_top_iff.2 (hx.ge.trans (sup_le_sup_right (Submodule.span_mono ?_) _))
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨Fin.castAdd m b, ?_, Fin.append_left _ _ _⟩
  rcases hb with hb | hb
  · have h1 : n = nV := of_decide_eq_true hb
    exact Or.inl (decide_eq_true (by have := h h1; omega))
  · exact Or.inr hb

theorem trivAt_of_dvd {n a b : ℕ} {Λ : GenLat E n} (h : Λ.TrivAt b) (hab : a ∣ b) : Λ.TrivAt a := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk.coprime_dvd_right hab, h⟩

theorem isBeta_betaH {n : ℕ} {Λ : GenLat E n}
    (h : ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) :
    IsBeta Dw c Λ (betaH (Dw := Dw) c Λ) := by
  unfold betaH
  rw [dif_pos h]
  exact h.choose_spec

theorem map_blockPoly {K K' : Type} [Field K] [Field K'] (f : K →+* K') {n m : ℕ} (P : MvPolynomial (LtN Dw n) K)
    (Q : MvPolynomial (LtN Dw m) K) :
    MvPolynomial.map f (blockPoly P Q) = blockPoly (MvPolynomial.map f P) (MvPolynomial.map f Q) := by
  simp only [blockPoly, map_mul, MvPolynomial.map_rename]

theorem isIntegral_zpow {K : Type} [Field K] {ζ : K} (h : IsOfFinOrder ζ) (t : ℤ) : IsIntegral ℤ (ζ ^ t) := by
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine IsIntegral.of_pow hk ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, e, one_zpow]
  exact isIntegral_one

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem sum_data [Fintype (ConjQ Dw l)] {n m : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev)
    (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F) (ζ : c.F)
    (hφ : ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) *
      (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then
        (Nat.card (LaI Xo c d) : c.F) ^ m else 0))
    (x0 : Fin n → Dw.La) (x : Fin m → Dw.La) (q : Fin (n + m) → LevQ Dw d.l₂) :
    ∑ x' : Fin m → ConjQ Dw l,
        d.eF (zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b))) *
          d.eF (zetaM c ^ pairL (l := l) (Fin.append x0 fun b => qRep (x' b)) (fun b => levRep (q b)) * φ' q) =
      d.eF ζ * blockDat (d.w x0) (fun q : Fin m → LevQ Dw d.l₂ =>
        if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F)
        else 0) q := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have h0 : zetaM c ≠ 0 := (LevelPairing.zetaM_prim c).ne_zero hM.ne'
  have h1 : ∀ y : Fin m → Dw.La, zetaM c ^ pairL (l := l) (Fin.append x0 y) (fun b => levRep (q b)) =
      zetaM c ^ pairL (l := l) x0 (fun b => levRep (q (Fin.castAdd m b))) *
        zetaM c ^ pairL (l := l) y (fun b => levRep (q (Fin.natAdd n b))) := fun y => by
    rw [← zpow_add₀ h0]
    congr 1
    simp [pairL, Fin.sum_univ_add]
  have h2 := congrArg d.eF (sum_new_columns d hd x (fun b => q (Fin.natAdd n b)))
  rw [apply_ite d.eF, map_natCast, map_zero] at h2
  unfold blockDat
  refine Eq.trans ?_ (congrArg (fun t => d.eF ζ * (d.w x0 (fun i => q (Fin.castAdd m i)) * t)) (h2.trans (by congr)))
  simp only [h1, hφ, DeltaDat.w, ← map_mul, ← map_sum]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

theorem mul_mem_span (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab : NabV Xo c} (hn : IsNab Xo c nab) {n m : ℕ}
    (d : DeltaDat Xo c n) (hd : d.IsLev) (hn₂ : IsNab d.Xo₂ d.c₂ d.nab₂) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F)
    (ζ : c.F) (hζ : IsOfFinOrder ζ)
    (hφ : ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) *
      (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then
        (Nat.card (LaI Xo c d) : c.F) ^ m else 0))
    (bad nV : ℕ) (hV : n = nV → m = 0)
    (hβ : ∀ (k : ℕ) (Λ : GenLat E k), Λ.Unimod → Λ.TrivAt bad →
      ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (hT : ShortValTot Xo c nab bad nV (a + a') (n + m) (withCoeff d φ'))
    {g f : Rul Xo c} (hg : g ∈ shortGen Xo c nab bad nV a n d) (hf : f ∈ thGen Xo c nab a' m) :
    g * f ∈ Submodule.span (𝓞 c.F) (shortGen Xo c nab bad nV (a + a') (n + m) (withCoeff d φ')) := by
  haveI := finite_conjQ Dw l
  haveI := Fintype.ofFinite (ConjQ Dw l)
  have hLaws := GlobalTheory.abelianSchemeLaws_all.1
  have hM : 0 < l.M := by have := l.three_le; omega
  have hfs := GlobalTheory.thetaRule_mem_sec hLaws hC E H Dw l Xo c nab hn a' m f hf
  obtain ⟨hgs, Λ, N, x0, P', hU, hb, hT₂, hL₂, hx0, hP', hgr⟩ := hg
  obtain ⟨x, P, hP, hfr⟩ := hf
  have hdv : l.M ∣ d.l₂.M := hd.1.1
  have hPL : P ∈ harmL c (unitLat E m) a' := (StdHarm.harmL_std c m a').ge hP
  have hA : LatAdm l bad Λ := ⟨hU, hb, trivAt_of_dvd hT₂ hdv⟩
  have hA₂ : LatAdm d.l₂ bad Λ := ⟨hU, hb, hT₂⟩
  have hu₂ : (unitLat E m).LevOK N d.l₂.M :=
    ⟨hL₂.1, hL₂.2.1, by simpa [GenLat.Ln, unitLat] using Submodule.smul_le_right⟩
  have hQ := ((GlobalTheory.shortSeries_blockProduct hC E H Dw l Xo c nab hn bad n m Λ _ hA (Survey.BaseClassMove.latAdm_unit l bad m) N
    ⟨hL₂.1, hdv.trans hL₂.2.1, hL₂.2.2⟩ ⟨hu₂.1, hdv.trans hu₂.2.1, hu₂.2.2⟩).2 a a' P' P hP' hPL).1
  obtain ⟨⟨hB, hBL⟩, hprod⟩ := GlobalTheory.shortSeries_blockProduct hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn₂ bad n m Λ _ hA₂
    (Survey.BaseClassMove.latAdm_unit d.l₂ bad m) N hL₂ hu₂
  have b₁ := isBeta_betaH (hβ n Λ hU hb)
  have b₂ := isBeta_betaH (hβ _ _ hB.1 hB.2.1)
  obtain ⟨ζ', hζ', eβ⟩ := ((BetaOfSum.blockBeta E H Dw l c bad).1 n m Λ _ hA (Survey.BaseClassMove.latAdm_unit l bad m) _ 1 _ b₁
    (Survey.BaseClassMove.isBeta_unit c m)).1 b₂
  have hadm := fun x' : Fin m → ConjQ Dw l => admissibleColumns_append hV x0 (fun b => qRep (x' b)) hx0
  choose F hFs hFr using fun x' : Fin m → ConjQ Dw l =>
    (hT (blockLat Λ (unitLat E m)) N _ _ hB.1 hB.2.1 hB.2.2 hBL (hadm x') hQ).2
  have hζ0 : ζ ≠ 0 := hζ.isUnit.ne_zero
  let cf : (Fin m → ConjQ Dw l) → c.F := fun x' =>
    zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b))
  have hcf : ∀ x', IsIntegral ℤ (ζ' * ζ⁻¹ * cf x') := fun x' =>
    ((by simpa using isIntegral_zpow hζ' 1 : IsIntegral ℤ ζ').mul
      (by simpa using isIntegral_zpow hζ (-1) : IsIntegral ℤ ζ⁻¹)).mul
      (isIntegral_zpow (isOfFinOrder_iff_pow_eq_one.2 ⟨l.M, hM, (LevelPairing.zetaM_prim c).pow_eq_one⟩) _)
  have main : g * f = ∑ x', (ζ' * ζ⁻¹ * cf x') • F x' := by
    refine ClassSumUnique.sec_eq_of_geometric (sec_mul Xo c a a' n m hgs hfs)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hFs i)) fun k _ _ _ y => ?_
    letI iA : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t := fun t => by
      show algebraMap c.F k (d.eF.symm (d.eF t)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
    obtain ⟨v₁, hv₁, e₁⟩ := hgr k hk y y₂ hy
    choose u hu eu using fun x' => @hFr x' k _ _ _ iA hk y y₂ hy
    have hP₁ := ((PlaceInt.eF_transfer E H Dw l Xo c n d Λ).2.1 a P' hP').1
    have hP₂ : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ (unitLat E m) a' :=
      ((PlaceInt.eF_transfer E H Dw l Xo c m (withCoeff d fun _ => 0) (unitLat E m)).2.1 a' P hPL).1
    obtain ⟨v₂, hv₂, -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn₂ m
      (unitLat E m) N (Survey.BaseClassMove.latAdm_unit d.l₂ bad m).1 (Survey.BaseClassMove.latAdm_unit d.l₂ bad m).2.2 hu₂ a' _ hP₂.1
      (fun q : Fin m → LevQ Dw d.l₂ => if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then
        (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) 1).1 k y₂
    have e₂ : v₂ = evR Xo c f y :=
      GlobalTheory.T.standardCover_shortValue_eq_thetaValue hC E H Dw l Xo c nab n d hd hn hn₂ m N a' x P _ hu₂ hP
        (fun b => (eq_mk_iff d hd (x b) _).1 rfl) k hk y y₂ hy v₂ _ hv₂
        ((GlobalTheory.thetaRule_exists_and_eval hC E H Dw l Xo c nab hn a' m x P hP).2 f hfr k y)
    have n₁ : d.eF (betaH (Dw := Dw) c Λ) ≠ 0 := (map_ne_zero _).2 b₁.1
    have n₂ : d.eF (betaH (Dw := Dw) c (blockLat Λ (unitLat E m))) ≠ 0 := (map_ne_zero _).2 b₂.1
    obtain ⟨hQ₂, hval⟩ := hprod a a' _ _ hP₁ hP₂
    have hv := (hval _ _ k y₂ _ _ _ ((Survey.BaseClassMove.shortValAt_beta _ _ _ _ _ _ n₁ _ _ _ _).1 hv₁) hv₂).2 rfl
    have hlin := shortVal_sum hC hn₂ hB.1 hB.2.2 hBL hQ₂ (fun x' => d.eF (cf x'))
      (fun x' q => d.eF (zetaM c ^ pairL (l := l) (Fin.append x0 fun b => qRep (x' b)) (fun b => levRep (q b)) * φ' q))
      _ (d.eF ζ)
      (sum_data d hd φ' ζ hφ x0 x) 1 y₂ _
      (fun x' => algebraMap d.c₂.F k (d.eF (betaH (Dw := Dw) c (blockLat Λ (unitLat E m)))) * u x') hv
      (fun x' => by
        rw [← map_blockPoly]
        exact (Survey.BaseClassMove.shortValAt_beta _ _ _ _ _ _ n₂ _ _ _ _).1 (hu x'))
    simp only [hk] at hlin
    let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
    have hm : evR Xo c (g * f) y = evR Xo c g y * evR Xo c f y := evalAt_mul _ _ g f y
    have eu' : ∀ x', evR Xo c (F x') y = evR d.Xo₂ d.c₂ d.cδ y₂ * u x' := eu
    rw [hm, ← hL (∑ x', _), map_sum, e₁, ← e₂]
    simp only [map_smul]
    simp only [hL, eu', Algebra.smul_def]
    have n₃ : algebraMap c.F k (betaH (Dw := Dw) c Λ) ≠ 0 := (map_ne_zero _).2 b₁.1
    have n₄ : algebraMap c.F k ζ ≠ 0 := (map_ne_zero _).2 hζ0
    refine mul_left_cancel₀ (mul_ne_zero n₄ n₃) ?_
    have e₃ : ∀ x', algebraMap c.F k ζ * algebraMap c.F k (betaH (Dw := Dw) c Λ) *
        (algebraMap c.F k (ζ' * ζ⁻¹ * cf x') * (evR d.Xo₂ d.c₂ d.cδ y₂ * u x')) = evR d.Xo₂ d.c₂ d.cδ y₂ *
        (algebraMap c.F k (cf x') * (algebraMap c.F k (betaH (Dw := Dw) c (blockLat Λ (unitLat E m))) * u x')) := by
      intro x'
      rw [eβ]
      simp only [map_mul, map_inv₀, map_one]
      field_simp
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x' _ => e₃ x']
    rw [← Finset.mul_sum, hlin]
    ring
  rw [main]
  refine Submodule.sum_mem _ fun x' _ => ?_
  exact (Submodule.span (𝓞 c.F) _).smul_mem (⟨_, hcf x'⟩ : 𝓞 c.F) (Submodule.subset_span
    ⟨hFs x', _, N, _, _, hB.1, hB.2.1, hB.2.2, hBL, hadm x', hQ, hFr x'⟩)

end General

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem short_mul_theta_mem_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL)) := by
  intro hC D T h j hj hS h1 hA w wL hr hV g hg f hf
  obtain ⟨s, hn⟩ := h.nabPin j hj
  obtain ⟨s₂, hn₂⟩ := hS.dNab j hj w.n
  obtain rfl : s = s₂ := starRing_eq _ _ fun a => (hn.1 a).trans (hn₂.1 a).symm
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
    have h1 := hj.1
    have h2 := hj.2
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hd := hS.dLev j hj w.n
  by_cases hpt : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T.Q.c.F k),
      Nonempty (FrPt (T.Q.Xo j) T.Q.c k)
  swap
  · have e : g * f = 0 := GlobalTheory.ClassSumUnique.sec_eq_of_geometric
      (sec_mul _ _ _ _ _ _ hg.1 (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hn _ _ f hf))
      (Submodule.zero_mem _) fun k _ _ _ y => absurd ⟨k, _, ‹_›, _, ⟨y⟩⟩ hpt
    rw [e]
    exact Submodule.zero_mem _
  obtain ⟨k, _, _, _, ⟨y⟩⟩ := hpt
  obtain ⟨φ', e⟩ := h1.eq_withCoeff w.n (w.n + wL.n)
  obtain ⟨φ₀, e₀⟩ := h1 w.n
  have hA' : (T.dδ j w.n).l₂.A = 1 := by rw [e₀]; exact hA
  obtain ⟨ph, ψ, x₀, -, hp, ht⟩ := hS.dPhi j hj w.n hr
  have h2 := hS.dPhi j hj (w.n + wL.n) (hr.trans (Nat.le_add_right _ _))
  have h3 := hS.shTot j hj _ (w.n + wL.n) (dom_wtA (WeightAlgebra.wadd w wL))
  change g * f ∈ Submodule.span (𝓞 T.Q.c.F) (shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV
    (wtA (WeightAlgebra.wadd w wL)) (w.n + wL.n) (T.dδ j (w.n + wL.n)))
  rw [e] at h2 h3 ⊢
  rw [wtA_wadd] at h3 ⊢
  obtain ⟨ph', ψ', x₀', -, hp', ht'⟩ := h2
  letI : Algebra (T.dδ j w.n).c₂.F k :=
    ((algebraMap T.Q.c.F k).comp ((T.dδ j w.n).eF.symm : (T.dδ j w.n).c₂.F →+* T.Q.c.F)).toAlgebra
  obtain ⟨y₂, -⟩ := hd.2.2.2.2.2.2.1 k (fun t => by
    show algebraMap T.Q.c.F k ((T.dδ j w.n).eF.symm ((T.dδ j w.n).eF t)) = _
    rw [AlgEquiv.symm_apply_apply]) y
  obtain rfl : ψ = ψ' := GlobalTheory.CoverCharacter.psi_unique _ _ _ _ _ _ _ (T.dδ j w.n) (hpq ▸ hr1) hd hA' k ⟨y₂⟩ ψ ψ' ht ht'
  obtain ⟨ζ, hζ, hφ⟩ := GlobalTheory.MoreColumns.coeff_more_columns _ _ _ _ _ _ _ _ (T.dδ j w.n) φ' hd (hpq ▸ hr) ψ ph x₀ ph' x₀'
    hp hp'
  exact mul_mem_span hC hn (T.dδ j w.n) hd hn₂ φ' ζ hζ hφ (badN D) D.R.nV hV
    (fun k Λ => hS.beta j hj k (h.kPsi j hj) Λ) _ _ h3 hg hf

end GlobalTheory.ShortTimesTheta
