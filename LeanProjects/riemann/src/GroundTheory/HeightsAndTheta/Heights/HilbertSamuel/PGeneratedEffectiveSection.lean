import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedEffectiveSection

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver F ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add {p q : MRingOver F ι} {a : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

theorem isMultiHomog_smul {p : MRingOver F ι} {a : K → ℕ} (r : F) (hp : IsMultiHomog p a) :
    IsMultiHomog (r • p) a :=
  fun m hm k => hp m (MvPolynomial.support_smul hm) k

variable {V : Ideal (MRingOver F ι)}

theorem quotPart_eq_mk {c : K → ℤ} {m : MRingOver F ι ⧸ V} (hm : m ∈ KH.quotPart F V c) (h0 : m ≠ 0) :
    (∀ k, 0 ≤ c k) ∧ ∃ p, IsMultiHomog p (fun k => (c k).toNat) ∧ Ideal.Quotient.mk V p = m := by
  by_cases hc : ∀ k, 0 ≤ c k
  · refine ⟨hc, ?_⟩
    have hm' : m ∈ Submodule.map (Ideal.Quotient.mkₐ F V).toLinearMap
        (Submodule.span F {p : MRingOver F ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)}) := by
      rw [← Submodule.span_image]
      exact hm
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm'
    refine ⟨p, ?_, rfl⟩
    clear hm h0 hm'
    induction hp using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => exact isMultiHomog_zero _
    | add x y _ _ hx hy => exact isMultiHomog_add hx hy
    | smul r x _ hx => exact isMultiHomog_smul r hx
  · exfalso
    apply h0
    have e : {p : MRingOver F ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp => hc hp.1
    unfold KH.quotPart at hm
    rw [e, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    exact hm

theorem smul_quot (r : MRingOver F ι) (a : MRingOver F ι ⧸ V) : r • a = Ideal.Quotient.mk V r * a :=
  Algebra.smul_def r a

theorem locPart_eq_mk {T : Submonoid (MRingOver F ι)} {c : K → ℤ}
    {x : LocalizedModule T (MRingOver F ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart F V) T c) :
    ∃ (m : MRingOver F ι ⧸ V) (t : T) (β : K → ℕ), IsMultiHomog (t : MRingOver F ι) β ∧
      m ∈ KH.quotPart F V (c + fun k => (β k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 1, 0, GenTwistGenerated.isMultiHomog_one 0 fun _ => rfl, Submodule.zero_mem _,
      (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', β', ht', hm', rfl⟩ := hy
    refine ⟨t' • m + t • m', t * t', β + β', GenTwistGenerated.isMultiHomog_mul ht ht', ?_,
      LocalizedModule.mk_add_mk⟩
    have deg : ∀ (s : T) (γ : K → ℕ), IsMultiHomog (s : MRingOver F ι) γ →
        Ideal.Quotient.mk V (s : MRingOver F ι) ∈ KH.quotPart F V (fun k => (γ k : ℤ)) := by
      intro s γ hs
      exact Submodule.subset_span ⟨s, ⟨fun k => Int.natCast_nonneg _, by simpa using hs⟩, rfl⟩
    have h1 := GenTwistGenerated.quotPart_mul hm (deg t' β' ht')
    have h2 := GenTwistGenerated.quotPart_mul hm' (deg t β ht)
    have e1 : ((c + fun k => (β k : ℤ)) + fun k => (β' k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    have e2 : ((c + fun k => (β' k : ℤ)) + fun k => (β k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [e1] at h1
    rw [e2] at h2
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_quot, smul_quot, mul_comm _ m, mul_comm _ m']
    exact add_mem h1 h2
  | smul r x _ hx =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    exact ⟨r • m, t, β, ht, Submodule.smul_mem _ r hm, LocalizedModule.smul'_mk r m t⟩

theorem cellMon_le_primeCompl {P : Ideal (MRingOver F ι)} [P.IsPrime] {I : ∀ k, Finset (ι k)}
    (h : ∀ k, ∀ j ∈ I k, (X ⟨k, j⟩ : MRingOver F ι) ∉ P) : KH.cellMon F I ≤ P.primeCompl := by
  refine Submonoid.closure_le.mpr ?_
  rintro _ ⟨k, j, hj, rfl⟩
  exact h k j hj

section Frac

variable [V.IsPrime]

def toFrac (T : Submonoid (MRingOver F ι)) (hT : T ≤ V.primeCompl)
    (x : LocalizedModule T (MRingOver F ι ⧸ V)) : FractionRing (MRingOver F ι ⧸ V) :=
  x.liftOn (fun p => algebraMap _ (FractionRing (MRingOver F ι ⧸ V)) p.1 /
      algebraMap _ (FractionRing (MRingOver F ι ⧸ V)) (Ideal.Quotient.mk V (p.2 : MRingOver F ι))) (by
    rintro ⟨m, t⟩ ⟨m', t'⟩ ⟨u, hu⟩
    have nz : ∀ s : T, Ideal.Quotient.mk V (s : MRingOver F ι) ≠ 0 := fun s h =>
      hT s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have nz' : ∀ s : T, algebraMap (MRingOver F ι ⧸ V) (FractionRing (MRingOver F ι ⧸ V))
        (Ideal.Quotient.mk V (s : MRingOver F ι)) ≠ 0 := fun s =>
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nz s)
    simp only [Submonoid.smul_def, smul_quot] at hu
    have h := mul_left_cancel₀ (nz u) hu
    simp only
    rw [div_eq_div_iff (nz' t) (nz' t'), ← map_mul, ← map_mul, mul_comm m, h, mul_comm])

theorem toFrac_mk (T : Submonoid (MRingOver F ι)) (hT : T ≤ V.primeCompl) (m : MRingOver F ι ⧸ V) (t : T) :
    toFrac T hT (LocalizedModule.mk m t) = algebraMap _ (FractionRing (MRingOver F ι ⧸ V)) m /
      algebraMap _ (FractionRing (MRingOver F ι ⧸ V)) (Ideal.Quotient.mk V (t : MRingOver F ι)) :=
  LocalizedModule.liftOn_mk _ _ _

theorem toFrac_cellRes {J I : ∀ k, Finset (ι k)} (h : KH.cellMon F J ≤ KH.cellMon F I)
    (hI : KH.cellMon F I ≤ V.primeCompl) (x : LocalizedModule (KH.cellMon F J) (MRingOver F ι ⧸ V)) :
    toFrac _ hI (KH.cellRes F (MRingOver F ι ⧸ V) J I x) = toFrac _ (h.trans hI) x := by
  induction x using LocalizedModule.induction_on with
  | h m t => rw [GenTwistGenerated.cellRes_mk h, toFrac_mk, toFrac_mk]

end Frac

def chart (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩

def pairCell (c : ∀ k, ι k) (k : K) (j : ι k) (hj : j ≠ c k) : KH.Cell K ι 1 :=
  ⟨Function.update (fun l => ({c l} : Finset (ι l))) k {c k, j}, fun l => by
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Function.update_of_ne hl], by
      rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair hj.symm]
      · intro l _ hl
        simp [Function.update_of_ne hl]
      · simp⟩

theorem chart_le {P : Ideal (MRingOver F ι)} [P.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ l, (X ⟨l, c l⟩ : MRingOver F ι) ∉ P) : KH.cellMon F (chart c).1 ≤ P.primeCompl :=
  cellMon_le_primeCompl fun l j hj => by
    simp only [chart, Finset.mem_singleton] at hj
    subst hj
    exact hc l

theorem res_eq_of_pair {M : Type*} [AddCommGroup M] [Module (MRingOver F ι) M] (c : ∀ k, ι k) (k : K)
    (j : ι k) (hj : j ≠ c k) (f : KH.CechC F ι M 0) (hf : KH.cechD F ι M 0 f = 0) :
    KH.cellRes F M (chart c).1 (pairCell c k j hj).1 (f (chart c)) =
      KH.cellRes F M (chart (Function.update c k j)).1 (pairCell c k j hj).1
        (f (chart (Function.update c k j))) := by
  classical
  have h := congrFun hf (pairCell c k j hj)
  have hIk : (pairCell c k j hj).1 k = {c k, j} := by simp [pairCell]
  have hIl : ∀ l, l ≠ k → (pairCell c k j hj).1 l = {c l} := fun l hl => by
    simp [pairCell, Function.update_of_ne hl]
  generalize pairCell c k j hj = I at h hIk hIl ⊢
  have hne : ∀ l, (I.1 l).Nonempty := I.2.1
  have hxy : c k ≠ j := hj.symm
  have hx : c k ∈ I.1 k := by rw [hIk]; simp
  have hy : j ∈ I.1 k := by rw [hIk]; simp
  have hcard₀ : (I.1 k).card = 2 := by rw [hIk]; exact Finset.card_pair hxy
  have hother : ∀ l, l ≠ k → (I.1 l).card = 1 := fun l hl => by rw [hIl l hl]; rfl
  have hface : ∀ i ∈ I.1 k, (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have hsign : KH.faceSign I.1 k j = -KH.faceSign I.1 k (c k) := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hxy with h' | h'
    · have e₁ : ((I.1 k).filter (· < c k)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      have e₂ : ((I.1 k).filter (· < j)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k).filter (· < c k)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      have e₂ : ((I.1 k).filter (· < j)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  have key : ∀ (c₀ : ∀ k, ι k) (a : ∀ l, Finset (ι l)) (p : (∀ l, (a l).Nonempty) ∧ ∑ l, ((a l).card - 1) = 0),
      a = (chart c₀).1 →
      KH.cellRes F M a I.1 (f ⟨a, p⟩) = KH.cellRes F M (chart c₀).1 I.1 (f (chart c₀)) := by
    rintro c₀ a p rfl
    rfl
  have f₁ : Function.update I.1 k ((I.1 k).erase (c k)) = (chart (Function.update c k j)).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      simp [chart, hxy]
    · rw [Function.update_of_ne hl, hIl l hl]
      simp [chart, Function.update_of_ne hl]
  have f₂ : Function.update I.1 k ((I.1 k).erase j) = (chart c).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      ext x
      simp only [chart, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · rintro rfl
        exact ⟨hxy, Or.inl rfl⟩
    · rw [Function.update_of_ne hl, hIl l hl]
      rfl
  change (∑ l : K, ∑ i ∈ I.1 l, _ :
    KH.CechC F ι M 0 →ₗ[MRingOver F ι] LocalizedModule (KH.cellMon F I.1) M) f = 0 at h
  rw [Finset.sum_eq_single k, Finset.sum_eq_add_of_mem (c k) j hx hy hxy, dif_pos (hface (c k) hx),
    dif_pos (hface j hy)] at h
  · rw [hsign, LinearMap.add_apply] at h
    change KH.faceSign I.1 k (c k) • (KH.cellRes F M _ I.1 (f _)) +
      (-KH.faceSign I.1 k (c k)) • (KH.cellRes F M _ I.1 (f _)) = 0 at h
    rw [key _ _ _ f₁, key _ _ _ f₂, neg_smul, ← sub_eq_add_neg] at h
    have h' := sub_eq_zero.mp h
    have hs2 : KH.faceSign I.1 k (c k) * KH.faceSign I.1 k (c k) = 1 := by
      unfold KH.faceSign
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h'' := congrArg (fun x => KH.faceSign I.1 k (c k) • x) h'
    simp only [smul_smul, hs2, one_smul] at h''
    exact h''.symm
  · intro i hi _
    have : i = c k ∨ i = j := by rw [hIk] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h' => ?_
    have := h'.1 l
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h'
    exact absurd (Finset.mem_univ k) h'

section Chain

variable [V.IsPrime]

theorem toFrac_adj {z : KH.CechC F ι (MRingOver F ι ⧸ V) 0}
    (hz : KH.cechD F ι (MRingOver F ι ⧸ V) 0 z = 0) (c c' : ∀ k, ι k) (k : K) (j : ι k)
    (hc' : c' = Function.update c k j) (hc : ∀ l, (X ⟨l, c l⟩ : MRingOver F ι) ∉ V)
    (hj : (X ⟨k, j⟩ : MRingOver F ι) ∉ V) (h₁ : KH.cellMon F (chart c).1 ≤ V.primeCompl)
    (h₂ : KH.cellMon F (chart c').1 ≤ V.primeCompl) :
    toFrac _ h₁ (z (chart c)) = toFrac _ h₂ (z (chart c')) := by
  by_cases hjc : j = c k
  · have e : c' = c := by rw [hc', hjc, Function.update_eq_self]
    subst e
    rfl
  · subst hc'
    have hP : KH.cellMon F (pairCell c k j hjc).1 ≤ V.primeCompl := by
      refine cellMon_le_primeCompl fun l i hi => ?_
      by_cases hl : l = k
      · subst hl
        simp only [pairCell, Function.update_self, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hc _
        · exact hj
      · simp only [pairCell, Function.update_of_ne hl, Finset.mem_singleton] at hi
        subst hi
        exact hc l
    have hle₁ : KH.cellMon F (chart c).1 ≤ KH.cellMon F (pairCell c k j hjc).1 := by
      refine GenTwistGenerated.cellMon_mono fun l => ?_
      by_cases hl : l = k
      · subst hl
        simp [chart, pairCell]
      · simp [chart, pairCell, Function.update_of_ne hl]
    have hle₂ : KH.cellMon F (chart (Function.update c k j)).1 ≤ KH.cellMon F (pairCell c k j hjc).1 := by
      refine GenTwistGenerated.cellMon_mono fun l => ?_
      by_cases hl : l = k
      · subst hl
        simp [chart, pairCell]
      · simp [chart, pairCell, Function.update_of_ne hl]
    have e := congrArg (toFrac _ hP) (res_eq_of_pair c k j hjc z hz)
    rwa [toFrac_cellRes hle₁, toFrac_cellRes hle₂] at e

theorem toFrac_chain {z : KH.CechC F ι (MRingOver F ι ⧸ V) 0}
    (hz : KH.cechD F ι (MRingOver F ι ⧸ V) 0 z = 0) (i : ∀ k, ι k)
    (hi : ∀ l, (X ⟨l, i l⟩ : MRingOver F ι) ∉ V) (c : ∀ k, ι k)
    (hc : ∀ l, (X ⟨l, c l⟩ : MRingOver F ι) ∉ V) :
    toFrac _ (chart_le hc) (z (chart c)) = toFrac _ (chart_le hi) (z (chart i)) := by
  classical
  suffices H : ∀ s : Finset K, ∀ (c : ∀ k, ι k) (hc : ∀ l, (X ⟨l, c l⟩ : MRingOver F ι) ∉ V), (∀ l ∉ s, c l = i l) →
      toFrac _ (chart_le hc) (z (chart c)) = toFrac _ (chart_le hi) (z (chart i)) from
    H Finset.univ c hc fun l hl => (hl (Finset.mem_univ l)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro c hc h
    have e : c = i := funext fun l => h l (Finset.notMem_empty l)
    subst e
    rfl
  | insert k s _ ih =>
    intro c hc h
    have hc' : ∀ l, (X ⟨l, Function.update c k (i k) l⟩ : MRingOver F ι) ∉ V := by
      intro l
      by_cases hl : l = k
      · subst hl
        rw [Function.update_self]
        exact hi l
      · rw [Function.update_of_ne hl]
        exact hc l
    rw [toFrac_adj hz c _ k (i k) rfl hc (hi k) (chart_le hc) (chart_le hc')]
    refine ih _ hc' fun l hl => ?_
    by_cases hlk : l = k
    · subst hlk
      rw [Function.update_self]
    · rw [Function.update_of_ne hlk]
      exact h l (by simp [hlk, hl])

end Chain

end GeneratedEffectiveSection

theorem GeneratedEffectiveSection.proof : GeneratedEffectiveSection.Statement := by
  intro F _ K _ _ ι _ _ V a hV hgen
  classical
  have : V.IsPrime := hV.1
  choose i hi using hV.2.2
  obtain ⟨r, z, u, hz, -, hsum⟩ := hgen (GeneratedEffectiveSection.chart i)
  have hne : (1 : LocalizedModule (KH.cellMon F (GeneratedEffectiveSection.chart i).1)
      (MRingOver F ι ⧸ V)) ≠ 0 := by
    intro h
    have h1 := congrArg (GeneratedEffectiveSection.toFrac _ (GeneratedEffectiveSection.chart_le hi)) h
    rw [show (1 : LocalizedModule (KH.cellMon F (GeneratedEffectiveSection.chart i).1) (MRingOver F ι ⧸ V)) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], ← LocalizedModule.zero_mk 1,
      GeneratedEffectiveSection.toFrac_mk, GeneratedEffectiveSection.toFrac_mk] at h1
    simp at h1
  rw [← hsum] at hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hzj : z j (GeneratedEffectiveSection.chart i) ≠ 0 := fun h => hj (by rw [h]; exact mul_zero (u j))
  have hd : KH.cechD F ι (MRingOver F ι ⧸ V) 0 (z j) = 0 := LinearMap.mem_ker.mp (hz j).2
  have hloc : ∀ c, z j (GeneratedEffectiveSection.chart c) ∈
      KH.locPart ι (KH.quotPart F V) (KH.cellMon F (GeneratedEffectiveSection.chart c).1) a :=
    fun c => Submodule.mem_pi.mp (hz j).1 (GeneratedEffectiveSection.chart c) (Set.mem_univ _)
  obtain ⟨m, t, β, ht, hm, he⟩ := GeneratedEffectiveSection.locPart_eq_mk (hloc i)
  have hm0 : m ≠ 0 := fun h => hzj (by rw [he, h, LocalizedModule.zero_mk])
  obtain ⟨hnn, f, hf, rfl⟩ := GeneratedEffectiveSection.quotPart_eq_mk hm hm0
  have hfV : f ∉ V := fun h => hm0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have htV : (t : MRingOver F ι) ∉ V := GeneratedEffectiveSection.chart_le hi t.2
  refine ⟨f, t, ⟨fun k => ((a + fun k => (β k : ℤ)) k).toNat, β, hf, ht, hfV, htV, fun k => ?_⟩,
    fun W => ?_⟩
  · rw [Int.toNat_of_nonneg (hnn k)]
    simp
  · simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, sub_nonneg]
    by_cases hW : W ∈ divSupp V (t : MRingOver F ι)
    · have hWp : W.IsPrime := hW.1.1.1
      have hVW : V ≤ W := le_sup_left.trans hW.1.1.2
      choose c hc using hW.2
      have hcV : ∀ l, (X ⟨l, c l⟩ : MRingOver F ι) ∉ V := fun l h => hc l (hVW h)
      obtain ⟨m', t', -, -, -, he'⟩ := GeneratedEffectiveSection.locPart_eq_mk (hloc c)
      obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective m'
      have hch := GeneratedEffectiveSection.toFrac_chain hd i hi c hcV
      rw [he', he, GeneratedEffectiveSection.toFrac_mk, GeneratedEffectiveSection.toFrac_mk] at hch
      have ht'W : (t' : MRingOver F ι) ∉ W := GeneratedEffectiveSection.chart_le hc t'.2
      have ht'V : (t' : MRingOver F ι) ∉ V := fun h => ht'W (hVW h)
      have nz : ∀ s : MRingOver F ι, s ∉ V → algebraMap (MRingOver F ι ⧸ V)
          (FractionRing (MRingOver F ι ⧸ V)) (Ideal.Quotient.mk V s) ≠ 0 := fun s hs =>
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr fun h =>
          hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
      rw [div_eq_div_iff (nz _ ht'V) (nz _ htV)] at hch
      replace hch : Ideal.Quotient.mk V (f' * t) = Ideal.Quotient.mk V (f * t') := by
        apply IsFractionRing.injective (MRingOver F ι ⧸ V) (FractionRing (MRingOver F ι ⧸ V))
        simpa only [map_mul] using hch
      rw [Ideal.Quotient.eq] at hch
      have hf'V : f' ∉ V := by
        intro h
        have h2 : f * t' ∈ V := by
          have := V.sub_mem (V.mul_mem_right (t : MRingOver F ι) h) hch
          simpa using this
        rcases hV.1.mem_or_mem h2 with h3 | h3
        · exact hfV h3
        · exact ht'V h3
      have one_W : (1 : MRingOver F ι) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
      have e1 := NumbersDVR.divCycle_eq_of_mul_sub_mem (P := V) (W := W) (u := 1) (v := 1)
        (f := f * t') (g := f' * t) one_W one_W
        (by rw [one_mul, one_mul, ← neg_sub]; exact V.neg_mem hch)
      have e2 := congrFun (NumbersDVR.DivCycleMul.full F K ι V f t' hV.1 hfV ht'V) W
      have e3 := congrFun (NumbersDVR.DivCycleMul.full F K ι V f' t hV.1 hf'V htV) W
      have e4 := NumbersDVR.divCycle_eq_zero_of_form_not_mem V ht'W
      have e5 := NumbersDVR.divCycle_nonneg V f' W
      rw [NumbersDVR.VocabDivCycle.proof F K ι V t W, NumbersDVR.VocabDivCycle.proof F K ι V f W]
      simp only [Pi.add_apply] at e2 e3
      linarith
    · have h0 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V (t : MRingOver F ι) W = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
        simp [Finsupp.ofSupportFinite_coe, hW]
      rw [h0]
      simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
