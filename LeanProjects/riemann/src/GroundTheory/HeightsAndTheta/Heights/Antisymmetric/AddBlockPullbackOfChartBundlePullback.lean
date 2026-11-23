import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.LocallyFreeSpreadHyp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

section Rings

variable {Ω : Type} [Field Ω]

theorem locAtIntPrime_eq_locPrimeTo (p : ℕ) (A : Subalgebra ℤ Ω) :
    locAtIntPrime p A.toSubring = (IndefiniteRowSideFullHecke.Antisym.locPrimeTo A p).toSubring := by
  rw [IndefiniteRowSideFullHecke.Antisym.locPrimeTo, Algebra.adjoin_int]
  show locAtIntPrime p A.toSubring = Subring.closure _
  apply le_antisymm
  · refine Subring.closure_le.2 (Set.union_subset (fun a ha => Subring.subset_closure (Or.inl ha)) ?_)
    rintro u ⟨s, hs, rfl⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg s
    · exact Subring.subset_closure
        (Or.inr ⟨n, fun h => hs (Int.natCast_dvd_natCast.2 h), by simp⟩)
    · have hmem : ((n : ℕ) : Ω)⁻¹ ∈ Subring.closure ((A : Set Ω) ∪
          {u | ∃ s : ℕ, ¬ p ∣ s ∧ u = (s : Ω)⁻¹}) :=
        Subring.subset_closure (Or.inr ⟨n, fun h => hs (by
          rw [Int.dvd_neg]; exact Int.natCast_dvd_natCast.2 h), rfl⟩)
      simpa [inv_neg] using neg_mem hmem
  · refine Subring.closure_le.2 (Set.union_subset (fun a ha => Subring.subset_closure (Or.inl ha)) ?_)
    rintro u ⟨s, hs, rfl⟩
    exact Subring.subset_closure (Or.inr ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩)

theorem invertNat_eq (m : ℕ) (A : Subalgebra ℤ Ω) :
    invertNat m A.toSubring = (IndefiniteRowSideFullHecke.Antisym.invertNat A m).toSubring := by
  rw [IndefiniteRowSideFullHecke.Antisym.invertNat, Algebra.adjoin_int]
  rfl

theorem exists_eq_div_of_mem_locAtIntPrime [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω) {u : Ω}
    (hu : u ∈ locAtIntPrime p A.toSubring) :
    ∃ a ∈ A, ∃ t : ℕ, ¬ p ∣ t ∧ u = a * (t : Ω)⁻¹ := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, hs, rfl⟩
    · exact ⟨x, hx, 1, hp.not_dvd_one, by simp⟩
    · obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg s
      · exact ⟨1, one_mem _, n, fun h => hs (Int.natCast_dvd_natCast.2 h), by simp⟩
      · refine ⟨-1, neg_mem (one_mem _), n, fun h => hs (by
          rw [Int.dvd_neg]; exact Int.natCast_dvd_natCast.2 h), by simp [inv_neg]⟩
  | zero => exact ⟨0, zero_mem _, 1, hp.not_dvd_one, by simp⟩
  | one => exact ⟨1, one_mem _, 1, hp.not_dvd_one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    obtain ⟨b, hb, t', ht', rfl⟩ := hy
    have h0 : (t : Ω) ≠ 0 := by
      rintro h; exact ht (by rw [show t = 0 by exact_mod_cast h]; exact dvd_zero p)
    have h0' : (t' : Ω) ≠ 0 := by
      rintro h; exact ht' (by rw [show t' = 0 by exact_mod_cast h]; exact dvd_zero p)
    refine ⟨a * t' + b * t, add_mem (mul_mem ha (A.natCast_mem _)) (mul_mem hb (A.natCast_mem _)),
      t * t', fun h => (hp.dvd_mul.1 h).elim ht ht', ?_⟩
    push_cast
    field_simp
  | neg x _ hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, t, ht, by ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    obtain ⟨b, hb, t', ht', rfl⟩ := hy
    refine ⟨a * b, mul_mem ha hb, t * t', fun h => (hp.dvd_mul.1 h).elim ht ht', ?_⟩
    push_cast
    rw [mul_inv]
    ring

theorem mem_span_locAtIntPrime_iff [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (L' : AddSubgroup E)
    (hL' : ∀ a ∈ A, ∀ e ∈ L', a • e ∈ L') (e : E) :
    e ∈ Submodule.span (locAtIntPrime p A.toSubring) (L' : Set E) ↔
      ∃ s : ℕ, ¬ p ∣ s ∧ (s : Ω) • e ∈ L' := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using hx⟩
    | zero => exact ⟨1, hp.not_dvd_one, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, fun h => (hp.dvd_mul.1 h).elim hs ht, ?_⟩
      rw [smul_add, Nat.cast_mul, mul_comm, mul_smul, mul_comm, mul_smul]
      exact add_mem (by simpa using hL' _ (A.natCast_mem t) _ hsx)
        (by simpa using hL' _ (A.natCast_mem s) _ hty)
    | smul u x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨a, ha, t, ht, hu⟩ := exists_eq_div_of_mem_locAtIntPrime hp A u.2
      have h0 : (t : Ω) ≠ 0 := by
        rintro h; exact ht (by rw [show t = 0 by exact_mod_cast h]; exact dvd_zero p)
      refine ⟨t * s, fun h => (hp.dvd_mul.1 h).elim ht hs, ?_⟩
      rw [Subring.smul_def, hu, smul_smul, Nat.cast_mul,
        show (t : Ω) * s * (a * (t : Ω)⁻¹) = a * s by field_simp, ← smul_smul]
      exact hL' a ha _ hsx
  · rintro ⟨s, hs, hse⟩
    have h0 : (s : Ω) ≠ 0 := by
      rintro h; exact hs (by rw [show s = 0 by exact_mod_cast h]; exact dvd_zero p)
    have hinv : (s : Ω)⁻¹ ∈ locAtIntPrime p A.toSubring :=
      Subring.subset_closure (Or.inr ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩)
    have : e = (⟨_, hinv⟩ : locAtIntPrime p A.toSubring) • ((s : Ω) • e) := by
      rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hse)

end Rings

section Join

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem joinPt_eq_segreJoin (x : ι → Ω) (z : κ → Ω') :
    joinPt x z = segreJoin (fun i => algebraMap Ω Ω' (x i)) z := rfl

theorem pullbackLat_eq_pullLat {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {x : ι → Ω}
    (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    pullbackLat B z q = IndefiniteRowSideFullHecke.Antisym.pullLat x z B.lat q := rfl

theorem addBlockPullback_of_chartBundlePullback (h : ChartBundlePullback.Statement) :
    IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement := by
  intro Ω Ω' _ _ _ _ ι κ _ _ x z r E _ _ B
  exact h Ω Ω' ι κ x z r E B

end Join

section AddBlock

variable {K : Type} {ι : K → Type} {κ : Type}

def addBlockToSum : Option K → K ⊕ Unit
  | none => Sum.inr ()
  | some k => Sum.inl k

def addBlockIdxToSigma :
    (Σ o, addBlockIdx ι κ o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k)
  | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩

def sigmaToAddBlockIdx :
    (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) → (Σ o, addBlockIdx ι κ o)
  | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  | ⟨Sum.inl k, i⟩ => ⟨some k, i⟩

def addBlockIdxEquiv :
    (Σ o, addBlockIdx ι κ o) ≃ (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) where
  toFun := addBlockIdxToSigma
  invFun := sigmaToAddBlockIdx
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | ⟨⟩, i⟩ <;> rfl

theorem addBlockToSum_fst (q : Σ o, addBlockIdx ι κ o) :
    (addBlockIdxEquiv q).1 = addBlockToSum q.1 := by
  rcases q with ⟨_ | k, i⟩ <;> rfl

theorem addBlockPt_eq_joinPt {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω']
    (y : (Σ k, ι k) → Ω) (z : κ → Ω') :
    addBlockPt (Ω := Ω) (Ω' := Ω') y z =
      IndefiniteRowSideFullHecke.Antisym.joinPt (fun q => algebraMap Ω Ω' (y q))
        (fun q : (Σ _ : Unit, κ) => z q.2) ∘ addBlockIdxEquiv := by
  funext q
  rcases q with ⟨_ | k, i⟩ <;> rfl

theorem addBlockDeg_eq_sumElim (a : K → ℤ) :
    addBlockDeg a = Sum.elim a 0 ∘ addBlockToSum := by
  funext o
  rcases o with _ | k <;> rfl

end AddBlock

section Readings

open IndefiniteRowSideFullHecke.Antisym

def ratsInReal : Subfield ℝ := (Rat.castHom ℝ).fieldRange

abbrev chartOne : Subalgebra ℤ ℝ := chartRing ℤ (fun _ : Unit => (1 : ℝ)) ()

theorem mem_ratsInReal_of_mem_locPrimeTo {u : ℝ} (hu : u ∈ locPrimeTo chartOne 2) :
    u ∈ ratsInReal := by
  have hA : chartOne ≤ subalgebraOfSubring ratsInReal.toSubring :=
    Algebra.adjoin_le (by
      rintro _ ⟨_, rfl⟩
      exact mem_subalgebraOfSubring.2 (by simp [one_mem]))
  have hB : locPrimeTo chartOne 2 ≤ subalgebraOfSubring ratsInReal.toSubring := by
    refine Algebra.adjoin_le (Set.union_subset hA ?_)
    rintro _ ⟨s, -, rfl⟩
    exact mem_subalgebraOfSubring.2 (ratsInReal.inv_mem (natCast_mem ratsInReal s))
  exact mem_subalgebraOfSubring.1 (hB hu)

theorem sqrt_two_not_mem_ratsInReal : √2 ∉ ratsInReal := by
  rintro ⟨q, hq⟩
  exact irrational_sqrt_two ⟨q, hq⟩

abbrev zTwo : Subring ℝ := locAtIntPrime 2 chartOne.toSubring

theorem mem_ratsInReal_of_mem_zTwo {u : ℝ} (hu : u ∈ zTwo) : u ∈ ratsInReal := by
  rw [zTwo, locAtIntPrime_eq_locPrimeTo] at hu
  exact mem_ratsInReal_of_mem_locPrimeTo hu

theorem linearIndependent_one_sqrtTwo : LinearIndependent zTwo ![(1 : ℝ), √2] := by
  refine LinearIndependent.pair_iffₛ.2 fun s t s' t' h => ?_
  simp only [Subring.smul_def, smul_eq_mul, mul_one] at h
  have hs := mem_ratsInReal_of_mem_zTwo (s - s').2
  have ht := mem_ratsInReal_of_mem_zTwo (t - t').2
  push_cast at hs ht
  by_cases htt : (t : ℝ) - t' = 0
  · refine ⟨Subtype.ext ?_, Subtype.ext (by linarith)⟩
    have : (t : ℝ) = t' := by linarith
    rw [this] at h
    linarith
  · exfalso
    apply sqrt_two_not_mem_ratsInReal
    have : √2 = ((s' : ℝ) - s) / ((t : ℝ) - t') := by
      field_simp
      linarith
    rw [this]
    exact div_mem (by simpa using neg_mem hs) ht

def sqrtTwoLattice : Submodule zTwo ℝ := Submodule.span zTwo (Set.range ![(1 : ℝ), √2])

theorem one_mem_sqrtTwoLattice : (1 : ℝ) ∈ sqrtTwoLattice :=
  Submodule.subset_span ⟨0, rfl⟩

theorem sqrtTwo_mem_sqrtTwoLattice : √2 ∈ sqrtTwoLattice :=
  Submodule.subset_span ⟨1, rfl⟩

theorem sqrtTwoLattice_firstReading :
    Module.Finite zTwo sqrtTwoLattice ∧ Module.Projective zTwo sqrtTwoLattice ∧
      Submodule.span ℝ (sqrtTwoLattice : Set ℝ) = ⊤ := by
  have b := Module.Basis.span linearIndependent_one_sqrtTwo
  have : Module.Free zTwo sqrtTwoLattice := Module.Free.of_basis b
  have : Module.Finite zTwo sqrtTwoLattice := Module.Finite.of_basis b
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [eq_top_iff]
  intro v _
  simpa using Submodule.smul_mem _ v (Submodule.subset_span one_mem_sqrtTwoLattice :
    (1 : ℝ) ∈ Submodule.span ℝ (sqrtTwoLattice : Set ℝ))

theorem not_isLocFreeLattice_sqrtTwo (r : ℕ) :
    ¬ IsLocFreeLattice (locPrimeTo chartOne 2) r sqrtTwoLattice.toAddSubgroup := by
  rintro ⟨-, k, f, c, hf, -, hsum, hfr⟩
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hsum
  obtain ⟨b, hli, -, hiff⟩ := hfr l
  have hr : r ≤ 1 := by simpa using hli.fintype_card_le_finrank
  have hrat : ∀ a : ℝ, (∃ n : ℕ, f l ^ n * a ∈ locPrimeTo chartOne 2) → a ∈ ratsInReal := by
    rintro a ⟨n, hn⟩
    have hfn : f l ^ n ≠ 0 := pow_ne_zero _ hl
    have : a = f l ^ n * a / f l ^ n := by field_simp
    rw [this]
    exact div_mem (mem_ratsInReal_of_mem_locPrimeTo hn)
      (pow_mem (mem_ratsInReal_of_mem_locPrimeTo (hf l)) n)
  obtain ⟨a, ha, h1⟩ := (hiff 1).1 ⟨0, by simpa using one_mem_sqrtTwoLattice⟩
  obtain ⟨a', ha', h2⟩ := (hiff √2).1 ⟨0, by simpa using sqrtTwo_mem_sqrtTwoLattice⟩
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · simp at h1
  · simp only [Fin.sum_univ_one, smul_eq_mul] at h1 h2
    have ha0 : a 0 ≠ 0 := by rintro h; rw [h, zero_mul] at h1; exact one_ne_zero h1
    apply sqrt_two_not_mem_ratsInReal
    have : √2 = a' 0 / a 0 := by
      rw [eq_div_iff ha0, h2, mul_assoc, mul_comm (b 0), ← h1, mul_one]
    rw [this]
    exact div_mem (hrat _ (ha' 0)) (hrat _ (ha 0))

theorem locFreeLattice_readings_differ :
    ∃ L : Submodule zTwo ℝ,
      (Module.Finite zTwo L ∧ Module.Projective zTwo L ∧ Submodule.span ℝ (L : Set ℝ) = ⊤) ∧
      ∀ r, ¬ IsLocFreeLattice (locPrimeTo chartOne 2) r L.toAddSubgroup :=
  ⟨sqrtTwoLattice, sqrtTwoLattice_firstReading, not_isLocFreeLattice_sqrtTwo⟩

end Readings

end GroundTheory.Heights₂.Heights
