import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenOnFibres

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Homog

variable {R : Type} [CommRing R]

theorem homog_monomial (m : (Σ k, ι k) →₀ ℕ) (r : R) (a : K → ℕ) (h : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    IsMultiHomog (monomial m r : MRingOver R ι) a := by
  intro m' hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact h k

theorem homog_one : IsMultiHomog (1 : MRingOver R ι) 0 :=
  homog_monomial 0 1 0 fun k => by simp

theorem homog_C (r : R) : IsMultiHomog (C r : MRingOver R ι) 0 :=
  homog_monomial 0 r 0 fun k => by simp

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by
  intro m hm
  simp at hm

theorem homog_mul {f g : MRingOver R ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_add {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_sub {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine homog_add hf fun m hm k => hg m ?_ k
  rwa [MvPolynomial.support_neg] at hm

open Classical in
theorem homog_X (k : K) (i : ι k) : IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by
  classical
  refine homog_monomial _ _ _ fun k' => ?_
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem homog_pow {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (R := R) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

theorem homog_map {S : Type} [CommRing S] (φ : R →+* S) {f : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsMultiHomog (MvPolynomial.map φ f) a :=
  fun m hm k => hf m (MvPolynomial.support_map_subset φ f hm) k

end Homog

def cmon (c : ∀ k, ι k) (e : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ e k

theorem homog_cmon (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (cmon c e) e := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (R := ℤ) (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (c k)) _) ih
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

theorem cmon_add (c : ∀ k, ι k) (e f : K → ℕ) : cmon c (e + f) = cmon c e * cmon c f := by
  simp only [cmon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

section Chart

variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)

theorem aeval_cmon (c : ∀ k, ι k) (e : K → ℕ) : aeval y (cmon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [cmon, map_prod, map_pow, aeval_X]

theorem prod_pow_add (c : ∀ k, ι k) (e f : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e + f) k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def FracData (c : ∀ k, ι k) (s : Ω) (a : K → ℤ) (e : K → ℕ) (F : MRing ι) : Prop :=
  ∃ d : K → ℕ, IsMultiHomog F d ∧ (∀ k, (d k : ℤ) = e k + a k) ∧ aeval y F = s * ∏ k, y ⟨k, c k⟩ ^ e k

theorem exists_fracData_of_mem_chartRingZ (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Ω}
    (hs : s ∈ chartRingZ y c) : ∃ e F, FracData y c s 0 e F := by
  classical
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, X ⟨k, i⟩, Pi.single k 1, homog_X k i, fun _ => by simp, ?_⟩
    have hprod : ∏ k', y ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k' = y ⟨k, c k⟩ := by
      rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [Pi.single_apply, hk'])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    rw [hprod, aeval_X]
    field_simp [hc k]
  | algebraMap r =>
    exact ⟨0, C r, 0, homog_C r, fun _ => by simp, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨e1, F1, d1, hF1, hd1, hv1⟩ := hx
    obtain ⟨e2, F2, d2, hF2, hd2, hv2⟩ := hz
    have h1 : d1 = e1 := funext fun k => by have := hd1 k; simp only [Pi.zero_apply, add_zero] at this; omega
    have h2 : d2 = e2 := funext fun k => by have := hd2 k; simp only [Pi.zero_apply, add_zero] at this; omega
    subst h1 h2
    refine ⟨d1 + d2, F1 * cmon c d2 + F2 * cmon c d1, d1 + d2, ?_, fun k => by simp, ?_⟩
    · refine homog_add (homog_mul hF1 (homog_cmon c d2)) ?_
      rw [add_comm d1 d2]
      exact homog_mul hF2 (homog_cmon c d1)
    · rw [map_add, map_mul, map_mul, hv1, hv2, aeval_cmon, aeval_cmon, prod_pow_add]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨e1, F1, d1, hF1, hd1, hv1⟩ := hx
    obtain ⟨e2, F2, d2, hF2, hd2, hv2⟩ := hz
    refine ⟨e1 + e2, F1 * F2, d1 + d2, homog_mul hF1 hF2, fun k => ?_, ?_⟩
    · have h1 := hd1 k
      have h2 := hd2 k
      simp only [Pi.zero_apply, add_zero] at h1 h2 ⊢
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [map_mul, hv1, hv2, prod_pow_add]
      ring

theorem fracData_shift (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Ω} (b : K → ℤ) {e : K → ℕ}
    {F : MRing ι} (h : FracData y c (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) 0 e F) :
    FracData y c s b (e + fun k => (-b k).toNat) (F * cmon c fun k => (b k).toNat) := by
  obtain ⟨d, hF, hd, hv⟩ := h
  have hde : d = e := funext fun k => by have := hd k; simp only [Pi.zero_apply, add_zero] at this; omega
  subst hde
  refine ⟨d + fun k => (b k).toNat, homog_mul hF (homog_cmon c _), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    omega
  · rw [map_mul, hv, aeval_cmon, prod_pow_add]
    have hk : ∀ k, y ⟨k, c k⟩ ^ (-b k) * y ⟨k, c k⟩ ^ (b k).toNat = y ⟨k, c k⟩ ^ (-b k).toNat := by
      intro k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      omega
    calc s * (∏ k, y ⟨k, c k⟩ ^ (-b k)) * (∏ k, y ⟨k, c k⟩ ^ d k) * ∏ k, y ⟨k, c k⟩ ^ (b k).toNat
        = s * (∏ k, y ⟨k, c k⟩ ^ d k) * ∏ k, (y ⟨k, c k⟩ ^ (-b k) * y ⟨k, c k⟩ ^ (b k).toNat) := by
          rw [Finset.prod_mul_distrib]; ring
      _ = _ := by simp only [hk]; ring

theorem exists_fracData_of_mem_chartLat {a : K → ℤ} {s : Ω} (hs : s ∈ chartLat y a 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ∃ e F, FracData y c s a e F := by
  have h := hs c hc
  simp only [Nat.cast_one, one_mul] at h
  obtain ⟨e, F, hF⟩ := exists_fracData_of_mem_chartRingZ y c hc h
  exact ⟨_, _, fracData_shift y c hc a hF⟩

theorem prod_zpow_neg_mul (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ (-b k)) * ∏ k, y ⟨k, c k⟩ ^ (b k) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ => by rw [← zpow_add₀ (hc k), neg_add_cancel, zpow_zero]

end Chart

section Loc

variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (S : Type) [CommRing S]

abbrev idealOver : Ideal (MRingOver S ι) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom S))

def IsRep (T : Submonoid (MRingOver S ι)) (x : LocalizedModule T (MRingOver S ι ⧸ idealOver y S))
    (c : ∀ k, ι k) (s : Ω) (a : K → ℤ) : Prop :=
  ∃ e F, FracData y c s a e F ∧ ∃ h : MvPolynomial.map (Int.castRingHom S) (cmon c e) ∈ T,
    x = LocalizedModule.mk (Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom S) F)) ⟨_, h⟩

variable {y S}

theorem smul_mk (r x : MRingOver S ι) :
    r • Ideal.Quotient.mk (idealOver y S) x = Ideal.Quotient.mk (idealOver y S) (r * x) := rfl

theorem mem_idealOver {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) (h0 : aeval y f = 0) :
    MvPolynomial.map (Int.castRingHom S) f ∈ idealOver y S := by
  apply Ideal.mem_map_of_mem
  show mConeMap y f = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y hf, h0, map_zero, zero_mul]

theorem mk_eq_of_aeval {T : Submonoid (MRingOver S ι)} {F1 F2 t1 t2 : MRing ι}
    (h1 : MvPolynomial.map (Int.castRingHom S) t1 ∈ T) (h2 : MvPolynomial.map (Int.castRingHom S) t2 ∈ T)
    {d : K → ℕ} (hd1 : IsMultiHomog (t2 * F1) d) (hd2 : IsMultiHomog (t1 * F2) d)
    (hv : aeval y (t2 * F1) = aeval y (t1 * F2)) :
    (LocalizedModule.mk (Ideal.Quotient.mk (idealOver y S) (MvPolynomial.map (Int.castRingHom S) F1)) ⟨_, h1⟩ :
      LocalizedModule T _) =
      LocalizedModule.mk (Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom S) F2)) ⟨_, h2⟩ := by
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_mk, ← map_mul]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact mem_idealOver (homog_sub hd1 hd2) (by rw [map_sub, hv, sub_self])

theorem IsRep.congr_val {T : Submonoid (MRingOver S ι)} {x : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)}
    {c : ∀ k, ι k} {s s' : Ω} {a : K → ℤ} (h : IsRep y S T x c s a) (hs : s = s') : IsRep y S T x c s' a :=
  hs ▸ h

theorem IsRep.unique {T : Submonoid (MRingOver S ι)} {x x' : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)}
    {c c' : ∀ k, ι k} {s : Ω} {a : K → ℤ} (hx : IsRep y S T x c s a) (hx' : IsRep y S T x' c' s a) : x = x' := by
  obtain ⟨e1, F1, ⟨d1, hF1, hd1, hv1⟩, h1, rfl⟩ := hx
  obtain ⟨e2, F2, ⟨d2, hF2, hd2, hv2⟩, h2, rfl⟩ := hx'
  have hdeg : e1 + d2 = e2 + d1 := funext fun k => by
    have := hd1 k
    have := hd2 k
    simp only [Pi.add_apply]
    omega
  refine mk_eq_of_aeval h1 h2 (d := e2 + d1) (homog_mul (homog_cmon c' e2) hF1) ?_ ?_
  · rw [← hdeg]
    exact homog_mul (homog_cmon c e1) hF2
  · rw [map_mul, map_mul, aeval_cmon, aeval_cmon, hv1, hv2]
    ring

theorem cmon_mem_of_mul {T : Submonoid (MRingOver S ι)} {c : ∀ k, ι k} {e1 e2 : K → ℕ}
    (h1 : MvPolynomial.map (Int.castRingHom S) (cmon c e1) ∈ T)
    (h2 : MvPolynomial.map (Int.castRingHom S) (cmon c e2) ∈ T) :
    MvPolynomial.map (Int.castRingHom S) (cmon c (e1 + e2)) ∈ T := by
  rw [cmon_add, map_mul]
  exact T.mul_mem h1 h2

theorem IsRep.add {T : Submonoid (MRingOver S ι)} {x x' : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)}
    {c : ∀ k, ι k} {s s' : Ω} {a : K → ℤ} (hx : IsRep y S T x c s a) (hx' : IsRep y S T x' c s' a) :
    IsRep y S T (x + x') c (s + s') a := by
  obtain ⟨e1, F1, ⟨d1, hF1, hd1, hv1⟩, h1, rfl⟩ := hx
  obtain ⟨e2, F2, ⟨d2, hF2, hd2, hv2⟩, h2, rfl⟩ := hx'
  have hdeg : e1 + d2 = e2 + d1 := funext fun k => by
    have := hd1 k
    have := hd2 k
    simp only [Pi.add_apply]
    omega
  have hT := cmon_mem_of_mul h1 h2
  refine ⟨e1 + e2, cmon c e2 * F1 + cmon c e1 * F2,
    ⟨e2 + d1, homog_add (homog_mul (homog_cmon c e2) hF1) ?_, fun k => ?_, ?_⟩, hT, ?_⟩
  · rw [← hdeg]
    exact homog_mul (homog_cmon c e1) hF2
  · have := hd1 k
    simp only [Pi.add_apply, Nat.cast_add]
    omega
  · rw [map_add, map_mul, map_mul, aeval_cmon, aeval_cmon, hv1, hv2, prod_pow_add]
    ring
  · rw [LocalizedModule.mk_add_mk]
    have hs : (⟨_, h1⟩ * ⟨_, h2⟩ : T) = ⟨_, hT⟩ :=
      Subtype.ext (by simp only [Submonoid.coe_mul, cmon_add, map_mul])
    rw [hs]
    congr 1
    simp only [Submonoid.smul_def, smul_mk, map_add, map_mul]

theorem IsRep.mul {T : Submonoid (MRingOver S ι)} {x x' : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)}
    {c : ∀ k, ι k} {s s' : Ω} {a b : K → ℤ} (hx : IsRep y S T x c s a) (hx' : IsRep y S T x' c s' b) :
    IsRep y S T (x * x') c (s * s') (a + b) := by
  obtain ⟨e1, F1, ⟨d1, hF1, hd1, hv1⟩, h1, rfl⟩ := hx
  obtain ⟨e2, F2, ⟨d2, hF2, hd2, hv2⟩, h2, rfl⟩ := hx'
  have hT := cmon_mem_of_mul h1 h2
  refine ⟨e1 + e2, F1 * F2, ⟨d1 + d2, homog_mul hF1 hF2, fun k => ?_, ?_⟩, hT, ?_⟩
  · have := hd1 k
    have := hd2 k
    simp only [Pi.add_apply, Nat.cast_add]
    omega
  · rw [map_mul, hv1, hv2, prod_pow_add]
    ring
  · rw [LocalizedModule.mk_mul_mk]
    have hs : (⟨_, h1⟩ * ⟨_, h2⟩ : T) = ⟨_, hT⟩ :=
      Subtype.ext (by simp only [Submonoid.coe_mul, cmon_add, map_mul])
    rw [hs]
    congr 1
    simp only [map_mul]

theorem IsRep.one {T : Submonoid (MRingOver S ι)} {c : ∀ k, ι k} :
    IsRep y S T (1 : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)) c 1 0 := by
  have hT : MvPolynomial.map (Int.castRingHom S) (cmon c 0) ∈ T := by
    simp only [cmon, Pi.zero_apply, pow_zero, Finset.prod_const_one, map_one]
    exact T.one_mem
  refine ⟨0, 1, ⟨0, homog_one, fun k => by simp, by simp⟩, hT, ?_⟩
  rw [show (1 : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)) = LocalizedModule.mk 1 1 by
    rw [OreLocalization.one_def],
    LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp [cmon]

theorem IsRep.zero {T : Submonoid (MRingOver S ι)} {c : ∀ k, ι k} :
    IsRep y S T (0 : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)) c 0 0 := by
  have hT : MvPolynomial.map (Int.castRingHom S) (cmon c 0) ∈ T := by
    simp only [cmon, Pi.zero_apply, pow_zero, Finset.prod_const_one, map_one]
    exact T.one_mem
  refine ⟨0, 0, ⟨0, homog_zero 0, fun k => by simp, by simp⟩, hT, ?_⟩
  rw [map_zero, map_zero, LocalizedModule.zero_mk]

theorem IsRep.sum {T : Submonoid (MRingOver S ι)} {c : ∀ k, ι k} {β : Type} (t : Finset β)
    (x : β → LocalizedModule T (MRingOver S ι ⧸ idealOver y S)) (v : β → Ω)
    (h : ∀ j ∈ t, IsRep y S T (x j) c (v j) 0) : IsRep y S T (∑ j ∈ t, x j) c (∑ j ∈ t, v j) 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (IsRep.zero (y := y) (S := S) (T := T) (c := c))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j t)).add (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj'))

theorem IsRep.lift {T T' : Submonoid (MRingOver S ι)} (hle : T ≤ T')
    {x : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)} {c : ∀ k, ι k} {s : Ω} {a : K → ℤ}
    (hx : IsRep y S T x c s a) : IsRep y S T' (LocalizedModule.liftOfLE T T' hle x) c s a := by
  obtain ⟨e, F, hF, h, rfl⟩ := hx
  refine ⟨e, F, hF, hle h, ?_⟩
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

theorem IsRep.mem_locPart {T : Submonoid (MRingOver S ι)}
    {x : LocalizedModule T (MRingOver S ι ⧸ idealOver y S)} {c : ∀ k, ι k} {s : Ω} {a : K → ℤ}
    (hx : IsRep y S T x c s a) : x ∈ KH.locPart ι (KH.quotPart S (idealOver y S)) T a := by
  obtain ⟨e, F, ⟨d, hF, hd, -⟩, h, rfl⟩ := hx
  refine Submodule.subset_span ⟨_, ⟨_, h⟩, e, homog_map _ (homog_cmon c e), ?_, rfl⟩
  refine Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
  · have := hd k
    simp only [Pi.add_apply]
    omega
  · have hd' : (fun k => ((a + fun k => (e k : ℤ)) k).toNat) = d := funext fun k => by
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [hd']
    exact homog_map _ hF

theorem subsingleton_loc {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k) (hy : y ⟨k, i⟩ = 0) :
    Subsingleton (LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ idealOver y S)) := by
  have hX : (X ⟨k, i⟩ : MRingOver S ι) ∈ idealOver y S := by
    have e : (X ⟨k, i⟩ : MRingOver S ι) = MvPolynomial.map (Int.castRingHom S) (X ⟨k, i⟩) := (map_X _ _).symm
    rw [e]
    exact mem_idealOver (homog_X k i) (by rw [aeval_X, hy])
  have hmem : (X ⟨k, i⟩ : MRingOver S ι) ∈ KH.cellMon S I := Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have h0 : ∀ x : LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ idealOver y S), x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨_, hmem⟩, ?_⟩
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      simp only [smul_zero, Submonoid.smul_def, smul_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ hX)
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

end Loc

section Cells

def cellChart (J : KH.Cell K ι 0) : ∀ k, ι k := fun k => (J.2.1 k).choose

theorem cellChart_mem (J : KH.Cell K ι 0) (k : K) : cellChart J k ∈ J.1 k := (J.2.1 k).choose_spec

variable (S : Type) [CommRing S]

theorem cmon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (e : K → ℕ) :
    MvPolynomial.map (Int.castRingHom S) (cmon c e) ∈ KH.cellMon S I := by
  simp only [cmon, map_prod, map_pow, map_X]
  exact Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _
    (Submonoid.subset_closure (s := {f : MRingOver S ι | ∃ k, ∃ i ∈ I k, f = X ⟨k, i⟩}) ⟨k, c k, hc k, rfl⟩) _

variable {S}

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : KH.cellMon S J ≤ KH.cellMon S I :=
  Submonoid.closure_mono (by
    rintro f ⟨k, j, hj, rfl⟩
    simp only [Set.mem_setOf_eq]
    exact ⟨k, j, h k hj, rfl⟩)

theorem cellRes_of_le {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : KH.cellMon S J ≤ KH.cellMon S I) : KH.cellRes S M J I = LocalizedModule.liftOfLE _ _ h := by
  unfold KH.cellRes
  rw [dif_pos h]

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem cechD_zero_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0)
    (I : KH.Cell K ι 1)
    (hz : ∀ J J' : KH.Cell K ι 0, (∀ k, J.1 k ⊆ I.1 k) → (∀ k, J'.1 k ⊆ I.1 k) →
      KH.cellRes S M J.1 I.1 (z J) = KH.cellRes S M J'.1 I.1 (z J')) :
    KH.cechD S ι M 0 z I = 0 := by
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have hsum : ∑ k, ((I.1 k).card - 1) = 1 := I.2.2
  obtain ⟨k0, hk0ne⟩ : ∃ k0, (I.1 k0).card - 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [Finset.sum_eq_zero fun k _ => hc k] at hsum
    exact absurd hsum (by norm_num)
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => (I.1 k).card - 1) (Finset.mem_univ k0)
  rw [hsum] at hsplit
  replace hsplit : (I.1 k0).card - 1 + ∑ k ∈ Finset.univ.erase k0, ((I.1 k).card - 1) = 1 := hsplit
  have hk0 := Finset.card_pos.mpr (hne k0)
  have hrest0 : ∑ k ∈ Finset.univ.erase k0, ((I.1 k).card - 1) = 0 := by
    by_contra h
    have : 1 ≤ ∑ k ∈ Finset.univ.erase k0, ((I.1 k).card - 1) := Nat.one_le_iff_ne_zero.mpr h
    omega
  have hrest : ∀ k ≠ k0, (I.1 k).card = 1 := by
    intro k hk
    have h1 := (Finset.sum_eq_zero_iff.mp hrest0) k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    have h2 := Finset.card_pos.mpr (hne k)
    omega
  have h2 : (I.1 k0).card = 2 := by
    omega
  obtain ⟨i1, i2, hlt, hI⟩ : ∃ i1 i2, i1 < i2 ∧ I.1 k0 = {i1, i2} := by
    obtain ⟨a, b, hab, h⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hab with h' | h'
    · exact ⟨a, b, h', h⟩
    · exact ⟨b, a, h', by rw [h, Finset.pair_comm]⟩
  have hface : ∀ i ∈ I.1 k0, (∀ l, (Function.update I.1 k0 ((I.1 k0).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k0 ((I.1 k0).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k0).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, h2]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self]
        exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]
        exact hne l
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self, hc]
        rfl
      · rw [Function.update_of_ne hl, hrest l hl]
        rfl
  have hsub : ∀ i l, Function.update I.1 k0 ((I.1 k0).erase i) l ⊆ I.1 l := by
    intro i l
    by_cases hl : l = k0
    · subst hl
      rw [Function.update_self]
      exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hl]
  have hsumsign : ∑ l ∈ Finset.univ.filter (· < k0), ((I.1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hrest l (ne_of_lt (Finset.mem_filter.mp hl).2)]; rfl
  have hs : KH.faceSign I.1 k0 i1 + KH.faceSign I.1 k0 i2 = 0 := by
    have f1 : (({i1, i2} : Finset (ι k0)).filter (· < i1)).card = 0 := by
      simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hlt.le, hlt.le]
    have f2 : (({i1, i2} : Finset (ι k0)).filter (· < i2)).card = 1 := by
      simp [Finset.filter_insert, Finset.filter_singleton, hlt]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f1, f2]
    norm_num
  have hi1 : i1 ∈ I.1 k0 := by rw [hI]; simp
  have hi2 : i2 ∈ I.1 k0 := by rw [hI]; simp
  have e : KH.cellRes S M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1 (z ⟨_, hface i1 hi1⟩) =
      KH.cellRes S M (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩) :=
    hz ⟨_, hface i1 hi1⟩ ⟨_, hface i2 hi2⟩ (hsub i1) (hsub i2)
  show (KH.cechD S ι M 0 z) I = 0
  rw [KH.cechD]
  erw [LinearMap.pi_apply]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single k0]
  · rw [Finset.sum_eq_add_of_mem i1 i2 hi1 hi2 (ne_of_lt hlt)]
    · rw [dif_pos (hface i1 hi1), dif_pos (hface i2 hi2)]
      show KH.faceSign I.1 k0 i1 • KH.cellRes S M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1
          (z ⟨_, hface i1 hi1⟩) + KH.faceSign I.1 k0 i2 • KH.cellRes S M
          (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩) = 0
      rw [e, ← add_smul, hs, zero_smul]
    · intro i hi hne'
      rw [hI] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact absurd rfl hne'.1
      · exact absurd rfl hne'.2
  · intro k _ hk
    refine Finset.sum_eq_zero fun i hi => ?_
    split_ifs with hc
    · exfalso
      obtain ⟨hn, -⟩ := hc
      have h3 := hn k
      rw [Function.update_self] at h3
      have h4 := Finset.card_erase_of_mem hi
      rw [hrest k hk] at h4
      have h5 := Finset.card_pos.mpr h3
      omega
    · rfl
  · intro h
    exact absurd (Finset.mem_univ k0) h

end Cells

section Main

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {S : Type} [CommRing S]
variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

variable (y S) in
open Classical in

def secCoch (s : Ω) (a : K → ℤ) : KH.CechC S ι (MRingOver S ι ⧸ idealOver y S) 0 := fun J =>
  if h : ∃ x, IsRep y S (KH.cellMon S J.1) x (cellChart J) s a then h.choose else 0

theorem secCoch_spec {s : Ω} {a : K → ℤ} (hs : s ∈ chartLat y a 1) (J : KH.Cell K ι 0)
    (hc : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0) :
    IsRep y S (KH.cellMon S J.1) (secCoch y S s a J) (cellChart J) s a := by
  have hex : ∃ x, IsRep y S (KH.cellMon S J.1) x (cellChart J) s a := by
    obtain ⟨e, F, hF⟩ := exists_fracData_of_mem_chartLat y hs (cellChart J) hc
    exact ⟨_, e, F, hF, cmon_mem S (cellChart_mem J) e, rfl⟩
  unfold secCoch
  rw [dif_pos hex]
  exact hex.choose_spec

theorem secCoch_mem {s : Ω} {a : K → ℤ} (hs : s ∈ chartLat y a 1) :
    secCoch y S s a ∈ KH.cechZc ι (KH.quotPart S (idealOver y S)) a 0 := by
  refine Submodule.mem_inf.mpr ⟨fun J _ => ?_, ?_⟩
  · unfold secCoch
    split_ifs with h
    · exact h.choose_spec.mem_locPart
    · exact zero_mem _
  · rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    funext I
    refine cechD_zero_eq_zero _ I fun J J' hJ hJ' => ?_
    by_cases hz : ∃ k, ∃ i ∈ I.1 k, y ⟨k, i⟩ = 0
    · obtain ⟨k, i, hi, h0⟩ := hz
      haveI := subsingleton_loc (S := S) hi h0
      exact Subsingleton.elim _ _
    · push_neg at hz
      have hJc : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0 := fun k => hz k _ (hJ k (cellChart_mem J k))
      have hJc' : ∀ k, y ⟨k, cellChart J' k⟩ ≠ 0 := fun k => hz k _ (hJ' k (cellChart_mem J' k))
      rw [cellRes_of_le (cellMon_mono hJ), cellRes_of_le (cellMon_mono hJ')]
      exact ((secCoch_spec hs J hJc).lift _).unique ((secCoch_spec hs J' hJc').lift _)

variable (S) in

theorem generatedV_idealOver {a : K → ℤ} {n : ℕ} {w : Fin n → Ω} (hw : ∀ j, w j ∈ chartLat y a 1)
    (hg : KH.GeneratesOn y a w) : KH.GeneratedV S (idealOver y S) a := by
  intro I
  by_cases hz : ∃ k, y ⟨k, cellChart I k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    haveI := subsingleton_loc (S := S) (cellChart_mem I k) h0
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, Subsingleton.elim _ _⟩
  · push_neg at hz
    obtain ⟨u, hu, hsum⟩ := hg (cellChart I) hz
    have hU : ∀ j, ∃ x, IsRep y S (KH.cellMon S I.1) x (cellChart I)
        (u j * ∏ k, y ⟨k, cellChart I k⟩ ^ (-a k)) (-a) := by
      intro j
      obtain ⟨e, F, hF⟩ := exists_fracData_of_mem_chartRingZ y _ hz (hu j)
      have hval : (u j * ∏ k, y ⟨k, cellChart I k⟩ ^ (-a k)) * ∏ k, y ⟨k, cellChart I k⟩ ^ (-(-a) k) = u j := by
        simp only [Pi.neg_apply, neg_neg]
        rw [mul_assoc, prod_zpow_neg_mul y _ hz a, mul_one]
      refine ⟨_, _, _, fracData_shift y _ hz (-a) (hval ▸ hF), cmon_mem S (cellChart_mem I) _, rfl⟩
    choose U hU using hU
    refine ⟨n, fun j => secCoch y S (w j) a, U, fun j => secCoch_mem (hw j), fun j => (hU j).mem_locPart, ?_⟩
    have hterm : ∀ j ∈ Finset.univ, IsRep y S (KH.cellMon S I.1) (U j * secCoch y S (w j) a I) (cellChart I)
        (u j * (w j * ∏ k, y ⟨k, cellChart I k⟩ ^ (-a k))) 0 := by
      intro j _
      have h := (hU j).mul (secCoch_spec (hw j) I hz)
      rw [neg_add_cancel] at h
      exact h.congr_val (by ring)
    have h := IsRep.sum Finset.univ _ _ hterm
    rw [hsum] at h
    exact h.unique (IsRep.one (c := cellChart I))

end Main

end GenOnFibres

theorem GenOnFibres.proof : GenOnFibres.Statement := by
  intro K _ _ ι _ _ Ω _ y a n w hw hg
  exact ⟨GenOnFibres.generatedV_idealOver ℚ hw hg,
    fun ℓ _ => GenOnFibres.generatedV_idealOver (ZMod ℓ) hw hg⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
