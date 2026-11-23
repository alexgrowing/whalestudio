import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.CompTieA

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAlg (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

theorem intAlg_zero : IntAlg (0 : Rul Xo c) := by
  intro la v hv
  simp only [valSet, Set.mem_setOf_eq] at hv
  obtain ⟨y, rfl⟩ := hv
  unfold vAtV
  obtain ⟨⟨w, q⟩, T, io, e, ho, z, hz, eta, -, hw⟩ := y
  unfold profI at hw
  obtain ⟨rfl, -⟩ := Prod.mk.inj hw
  simp [evI, evR, evalAt, nval]

theorem intAlg_add {f g : Rul Xo c} (hf : IntAlg f) (hg : IntAlg g) : IntAlg (f + g) := fun la v hv =>
  (le_min (hf la v hv) (hg la v hv)).trans ((isVal_valSet la v hv).add f g)

theorem intAlg_smul (a : 𝓞 c.F) {f : Rul Xo c} (hf : IntAlg f) : IntAlg (a • f) := fun la v hv => by
  have e : (a • f : Rul Xo c) = (a : c.F) • f := rfl
  rw [e]
  by_cases ha : (a : c.F) = 0
  · rw [ha, zero_smul, (isVal_valSet la v hv).zero]; exact le_top
  · rw [(isVal_valSet la v hv).smul _ _ ha]
    exact add_nonneg (by exact_mod_cast vAdd_int_nonneg la ha) (hf la v hv)

theorem intAlg_span {s : Set (Rul Xo c)} (hs : ∀ f ∈ s, IntAlg f) {f : Rul Xo c}
    (hf : f ∈ Submodule.span (𝓞 c.F) s) : IntAlg f := by
  induction hf using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact intAlg_zero
  | add x y _ _ hx hy => exact intAlg_add hx hy
  | smul a x _ hx => exact intAlg_smul a hx

variable (Xo c) in

def RegularityR1ValuedPoints (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, IntAlg f →
    ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f

theorem ramIdx_nonneg {Ω : Type} [Field Ω] [Algebra c.F Ω] {v : AddValuation Ω (WithTop ℤ)}
    {la : HeightOneSpectrum (𝓞 c.F)} (ho : IsOver (K := c.F) v la) : 0 ≤ ramIdx (K := c.F) v la := by
  unfold ramIdx
  have hpos : ∀ n ∈ {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n}, 0 ≤ n := by
    rintro n ⟨a, ha, -, hv⟩
    have h := (ho a).mpr ha
    rw [hv] at h
    exact_mod_cast h.le
  rcases Set.eq_empty_or_nonempty
      {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v ((algebraMap c.F Ω) ↑a) = ↑n} with he | hne
  · rw [he, Int.csInf_empty]
  · exact hpos _ (Int.csInf_mem hne ⟨0, hpos⟩)

variable (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
  (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
  (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)

theorem ord_nonneg_of [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c} (hFs : F ∈ sec Xo c a n) (hFC : F ∈ C a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR1 a n F hFC hF la y)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      obtain ⟨la⟩ := ‹Nonempty (HeightOneSpectrum (𝓞 c.F))›
      exact hR1Q a n F hFC ⟨la, hF la⟩ q
  exact_mod_cast key

theorem mem_of_mem_span_int (S : Submodule c.F (Rul Xo c)) {s : Set (Rul Xo c)} (hs : s ⊆ S) {F : Rul Xo c}
    (hF : F ∈ Submodule.span (𝓞 c.F) s) : F ∈ S := by
  induction hF using Submodule.span_induction with
  | mem x h => exact hs h
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul a x _ hx => exact S.smul_mem (a : c.F) hx

omit δ C cls PY lies in

theorem exists_of_mem_span_valG {u : WtR E} {ι : Type} {R : ι → Rul Xo c} {x : ∀ Z : Comp Xo c, AC Z}
    (hx : x ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun _ => Algebra.toModule
      Submodule.span (𝓞 c.F) (Set.range fun k => valG h u (R k)))) :
    ∃ F ∈ Submodule.span (𝓞 c.F) (Set.range R), x = valG h u F := by
  try dsimp only at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact ⟨R k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  | zero => exact ⟨0, zero_mem _, funext fun Z => (valC_zero h u.1 u.2 Z).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨F, hF, rfl⟩ := hy
    obtain ⟨G, hG, rfl⟩ := hz
    exact ⟨F + G, add_mem hF hG, funext fun Z => (valC_add h u.1 u.2 F G Z).symm⟩
  | smul a y _ hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    refine ⟨a • F, Submodule.smul_mem _ a hF, funext fun Z => ?_⟩
    refine (Algebra.smul_def a (valG h u F Z)).trans ?_
    rw [IsScalarTower.algebraMap_apply (𝓞 c.F) c.F (AC Z)]
    exact (valC_smul_ct h u.1 u.2 (a : c.F) F Z).symm

section LawA2Of

variable [Fintype (Comp Xo c)]
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem lawA2_of_data [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwC : ∀ k, wR k ∈ C uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpC : ∀ k, thpR k ∈ C uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heS : etR ∈ sec Xo c uet.1 uet.2) (heC : etR ∈ C uet.1 uet.2) (heI : IntAlg etR) (heN : NZAt h etR)
    (h1S : ta1R ∈ sec Xo c uta1.1 uta1.2) (h1C : ta1R ∈ C uta1.1 uta1.2) (h1I : IntAlg ta1R) (h1N : NZAt h ta1R)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2C : ta2R ∈ C uta2.1 uta2.2) (h2I : IntAlg ta2R) (h2N : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) :
    A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) := by
  have cases' : ∀ {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)},
      (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu
        ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).admitted Z v →
      IsNormDiscrete v ∧ ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) := by
    intro Z v hA
    obtain ⟨hd, hc⟩ := hA
    exact ⟨hd, hc.imp (fun h' => let ⟨la, ho, _⟩ := h'; ⟨la, ho⟩) (fun h' => h'.1)⟩
  refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
    fun Z v hA => ?_⟩
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q
      (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwS) hF) (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwC) hF)
      (intAlg_span (Set.forall_mem_range.2 hwI) hF) hd hc (evC_ne_zero_of_valC hx0)
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q
      (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpS) hF) (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpC) hF)
      (intAlg_span (Set.forall_mem_range.2 hpI) hF) hd hc (evC_ne_zero_of_valC hx0)
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q heS heC heI hd hc (heN Z)
    rw [huet] at h0
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q h1S h1C h1I hd hc (h1N Z)
    rw [huta1] at h0
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q h2S h2C h2I hd hc (h2N Z)
    rw [huta2] at h0
    exact h0

end LawA2Of

end Formalism.L2.Pj
