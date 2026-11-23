import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenTwistGenerated

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem isMultiHomog_mul {p q : MRingOver S ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k

theorem isMultiHomog_one (a : K → ℕ) (ha : ∀ k, a k = 0) : IsMultiHomog (1 : MRingOver S ι) a := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply]
  exact isMultiHomog_monomial 0 1 a fun k => by simp [ha k]

variable {V : Ideal (MRingOver S ι)}

theorem quotPart_mul {c d : K → ℤ} {x y : MRingOver S ι ⧸ V} (hx : x ∈ KH.quotPart S V c)
    (hy : y ∈ KH.quotPart S V d) : x * y ∈ KH.quotPart S V (c + d) := by
  have h := Submodule.mul_mem_mul hx hy
  unfold KH.quotPart at h ⊢
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨p, ⟨hc, hp⟩, rfl⟩, _, ⟨q, ⟨hd, hq⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨p * q, ⟨fun k => add_nonneg (hc k) (hd k), ?_⟩, map_mul _ _ _⟩
  have e : (fun k => ((c + d) k).toNat) = (fun k => (c k).toNat) + fun k => (d k).toNat := by
    funext k
    simp [Int.toNat_add (hc k) (hd k)]
  rw [e]
  exact isMultiHomog_mul hp hq

theorem mk_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : MRingOver S ι ⧸ V) (t : T)
    (a : K → ℕ) (ht : IsMultiHomog (t : MRingOver S ι) a)
    (hm : m ∈ KH.quotPart S V (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι (KH.quotPart S V) T c :=
  Submodule.subset_span ⟨m, t, a, ht, hm, rfl⟩

theorem smul_mul_loc {T : Submonoid (MRingOver S ι)} (s : S)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (s • x) * y = s • (x * y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.mk_mul_mk,
        LocalizedModule.smul'_mk, smul_mul_assoc]

theorem mul_smul_loc {T : Submonoid (MRingOver S ι)} (s : S)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : x * (s • y) = s • (x * y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.mk_mul_mk,
        LocalizedModule.smul'_mk, mul_smul_comm]

theorem locPart_mul {T : Submonoid (MRingOver S ι)} {c d : K → ℤ}
    {x y : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c)
    (hy : y ∈ KH.locPart ι (KH.quotPart S V) T d) : x * y ∈ KH.locPart ι (KH.quotPart S V) T (c + d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
      obtain ⟨m', t', a', ht', hm', rfl⟩ := hy
      rw [LocalizedModule.mk_mul_mk]
      refine mk_mem_locPart _ _ (a + a') (by simpa using isMultiHomog_mul ht ht') ?_
      have e : (c + fun k => (a k : ℤ)) + (d + fun k => (a' k : ℤ)) =
          (c + d) + fun k => ((a + a') k : ℤ) := by
        funext k
        simp only [Pi.add_apply, Nat.cast_add]
        ring
      rw [← e]
      exact quotPart_mul hm hm'
    | zero => convert Submodule.zero_mem _ using 1; exact mul_zero x
    | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
    | smul s y _ h => rw [mul_smul_loc]; exact Submodule.smul_mem _ s h
  | zero => convert Submodule.zero_mem _ using 1; exact zero_mul y
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul s x _ h => rw [smul_mul_loc]; exact Submodule.smul_mem _ s h

theorem cellRes_mk {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : KH.cellMon S J ≤ KH.cellMon S I) (m : M) (t : KH.cellMon S J) :
    KH.cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold KH.cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

theorem cellRes_mul {J I : ∀ k, Finset (ι k)} (x y : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ V)) :
    KH.cellRes S (MRingOver S ι ⧸ V) J I (x * y) =
      KH.cellRes S (MRingOver S ι ⧸ V) J I x * KH.cellRes S (MRingOver S ι ⧸ V) J I y := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      induction y using LocalizedModule.induction_on with
      | h m' t' =>
        rw [LocalizedModule.mk_mul_mk, cellRes_mk h, cellRes_mk h, cellRes_mk h, LocalizedModule.mk_mul_mk]
        rfl
  · unfold KH.cellRes
    rw [dif_neg h]
    exact (zero_mul (0 : LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ V))).symm

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : KH.cellMon S J ≤ KH.cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

theorem cechD_zero_apply {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] (I : KH.Cell K ι 1) :
    ∃ J₁ J₂ : KH.Cell K ι 0, (∀ k, J₁.1 k ⊆ I.1 k) ∧ (∀ k, J₂.1 k ⊆ I.1 k) ∧ ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      ∀ f : KH.CechC S ι M 0, KH.cechD S ι M 0 f I =
        σ • (KH.cellRes S M J₁.1 I.1 (f J₁) - KH.cellRes S M J₂.1 I.1 (f J₂)) := by
  classical
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have hsum : ∑ k, ((I.1 k).card - 1) = 1 := I.2.2

  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun k => (I.1 k).card - 1) (by rw [hsum]; exact one_ne_zero)
  have hle : ∀ k, (I.1 k).card - 1 ≤ 1 := fun k =>
    (Finset.single_le_sum (f := fun k => (I.1 k).card - 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)).trans hsum.le
  have hpos : ∀ k, 1 ≤ (I.1 k).card := fun k => Finset.card_pos.mpr (hne k)
  have hcard₀ : (I.1 k₀).card = 2 := by have := hle k₀; have := hpos k₀; omega
  have hother : ∀ l, l ≠ k₀ → (I.1 l).card = 1 := by
    intro l hl
    have h2 := Finset.sum_le_sum_of_subset (f := fun k => (I.1 k).card - 1) (Finset.subset_univ {l, k₀})
    rw [Finset.sum_pair hl] at h2
    have h3 := h2.trans hsum.le
    have := hpos l
    omega
  obtain ⟨x, y, hxy, hI⟩ := Finset.card_eq_two.mp hcard₀

  have hface : ∀ i ∈ I.1 k₀, (∀ l, (Function.update I.1 k₀ ((I.1 k₀).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k₀ ((I.1 k₀).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k₀).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have hx : x ∈ I.1 k₀ := by rw [hI]; simp
  have hy : y ∈ I.1 k₀ := by rw [hI]; simp
  have hsub : ∀ i, ∀ l, Function.update I.1 k₀ ((I.1 k₀).erase i) l ⊆ I.1 l := by
    intro i l
    by_cases hl : l = k₀
    · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hl]
  have hsign : KH.faceSign I.1 k₀ y = -KH.faceSign I.1 k₀ x := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hxy with h | h
    · have e₁ : ((I.1 k₀).filter (· < x)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      have e₂ : ((I.1 k₀).filter (· < y)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k₀).filter (· < x)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      have e₂ : ((I.1 k₀).filter (· < y)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  refine ⟨⟨_, hface x hx⟩, ⟨_, hface y hy⟩, hsub x, hsub y, KH.faceSign I.1 k₀ x,
    by unfold KH.faceSign; exact neg_one_pow_eq_or ℤ _, fun f => ?_⟩
  change (∑ k : K, ∑ i ∈ I.1 k, _ :
    KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) M) f = _
  rw [Finset.sum_eq_single k₀, Finset.sum_eq_add_of_mem x y hx hy hxy, dif_pos (hface x hx),
    dif_pos (hface y hy)]
  · rw [hsign, LinearMap.add_apply]
    change KH.faceSign I.1 k₀ x • (KH.cellRes S M _ I.1 (f _)) +
      (-KH.faceSign I.1 k₀ x) • (KH.cellRes S M _ I.1 (f _)) = _
    rw [neg_smul, ← sub_eq_add_neg]
    exact (zsmul_sub _ _ _).symm
  · intro i hi hne'
    have : i = x ∨ i = y := by rw [hI] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have := (h.1 l)
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h; exact absurd (Finset.mem_univ k₀) h

theorem mem_cechZc_zero {c : K → ℤ} {z : KH.CechC S ι (MRingOver S ι ⧸ V) 0}
    (hz : ∀ J, z J ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S J.1) c)
    (hd : KH.cechD S ι (MRingOver S ι ⧸ V) 0 z = 0) : z ∈ KH.cechZc ι (KH.quotPart S V) c 0 :=
  ⟨Submodule.mem_pi.mpr fun J _ => hz J, LinearMap.mem_ker.mpr hd⟩

theorem res_eq_of_cechD {I : KH.Cell K ι 1} {J₁ J₂ : KH.Cell K ι 0} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] {f : KH.CechC S ι M 0}
    (hd : KH.cechD S ι M 0 f I = σ • (KH.cellRes S M J₁.1 I.1 (f J₁) - KH.cellRes S M J₂.1 I.1 (f J₂)))
    (h0 : KH.cechD S ι M 0 f = 0) : KH.cellRes S M J₁.1 I.1 (f J₁) = KH.cellRes S M J₂.1 I.1 (f J₂) := by
  have h := congrFun h0 I
  rw [hd] at h
  rw [← sub_eq_zero]
  rcases hσ with rfl | rfl
  · simp only [one_smul] at h
    exact h
  · simp only [neg_smul, one_smul] at h
    exact neg_eq_zero.mp h

theorem cechD_mul {z z' : KH.CechC S ι (MRingOver S ι ⧸ V) 0}
    (hz : KH.cechD S ι _ 0 z = 0) (hz' : KH.cechD S ι _ 0 z' = 0) :
    KH.cechD S ι (MRingOver S ι ⧸ V) 0 (fun J => z J * z' J) = 0 := by
  funext I
  obtain ⟨J₁, J₂, -, -, σ, hσ, hd⟩ := cechD_zero_apply (S := S) (M := MRingOver S ι ⧸ V) I
  rw [hd]
  rw [cellRes_mul, cellRes_mul, res_eq_of_cechD hσ (hd z) hz, res_eq_of_cechD hσ (hd z') hz']
  exact (congrArg (σ • ·) (sub_self _)).trans (zsmul_zero σ)

theorem cechD_const (m : MRingOver S ι ⧸ V) :
    KH.cechD S ι (MRingOver S ι ⧸ V) 0 (fun _ => LocalizedModule.mk m 1) = 0 := by
  funext I
  obtain ⟨J₁, J₂, h₁, h₂, σ, -, hd⟩ := cechD_zero_apply (S := S) (M := MRingOver S ι ⧸ V) I
  rw [hd, cellRes_mk (cellMon_mono h₁), cellRes_mk (cellMon_mono h₂)]
  exact (congrArg (σ • ·) (sub_self _)).trans (zsmul_zero σ)

theorem generated_add {a b : K → ℤ} (ha : KH.GeneratedV S V a) (hb : KH.GeneratedV S V b) :
    KH.GeneratedV S V (a + b) := by
  intro I
  obtain ⟨r, z, u, hz, hu, h1⟩ := ha I
  obtain ⟨r', z', u', hz', hu', h1'⟩ := hb I
  refine ⟨r * r', fun p J => z (finProdFinEquiv.symm p).1 J * z' (finProdFinEquiv.symm p).2 J,
    fun p => u (finProdFinEquiv.symm p).1 * u' (finProdFinEquiv.symm p).2, fun p => ?_, fun p => ?_, ?_⟩
  · refine mem_cechZc_zero (fun J => locPart_mul ?_ ?_) (cechD_mul ?_ ?_)
    · exact Submodule.mem_pi.mp (hz _).1 J (Set.mem_univ _)
    · exact Submodule.mem_pi.mp (hz' _).1 J (Set.mem_univ _)
    · exact LinearMap.mem_ker.mp (hz _).2
    · exact LinearMap.mem_ker.mp (hz' _).2
  · rw [neg_add]
    exact locPart_mul (hu _) (hu' _)
  · refine (Equiv.sum_comp finProdFinEquiv.symm
      (fun q : Fin r × Fin r' => u q.1 * u' q.2 * (z q.1 I * z' q.2 I))).trans ?_
    refine (Fintype.sum_prod_type _).trans ?_
    calc ∑ j, ∑ l, u j * u' l * (z j I * z' l I) = ∑ j, ∑ l, u j * z j I * (u' l * z' l I) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
            mul_mul_mul_comm (u j) (u' l) (z j I) (z' l I)
      _ = (∑ j, u j * z j I) * ∑ l, u' l * z' l I := (Finset.sum_mul_sum _ _ _ _).symm
      _ = 1 := (congrArg₂ (· * ·) h1 h1').trans
          (mul_one (1 : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)))

def chartExp (c : ∀ k, ι k) (n : ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n else 0

theorem generated_diag (n : ℕ) : KH.GeneratedV S V (fun _ => (n : ℤ)) := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let p : MRingOver S ι := monomial (chartExp c n) 1
  have hph : IsMultiHomog p (fun _ => n) := by
    refine isMultiHomog_monomial _ _ _ fun k => ?_
    simp [chartExp]
  have hpm : p ∈ KH.cellMon S I.1 := by
    change monomial (chartExp c n) 1 ∈ _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
    refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
    have hq' : q.2 = c q.1 := by
      by_contra h
      simp [chartExp, h] at hq
    obtain ⟨k, i⟩ := q
    simp only at hq'
    subst hq'
    exact ⟨k, c k, hc k, rfl⟩
  have hpq : Ideal.Quotient.mk V p ∈ KH.quotPart S V (fun _ => (n : ℤ)) :=
    Submodule.subset_span ⟨p, ⟨fun _ => Int.natCast_nonneg n, by simpa using hph⟩, rfl⟩
  have h1q : (1 : MRingOver S ι ⧸ V) ∈ KH.quotPart S V 0 :=
    Submodule.subset_span ⟨1, ⟨fun _ => le_rfl, isMultiHomog_one _ fun _ => rfl⟩, map_one _⟩
  refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk V p) 1,
    fun _ => LocalizedModule.mk 1 ⟨p, hpm⟩, fun _ => mem_cechZc_zero (fun J => ?_) (cechD_const _),
    fun _ => ?_, ?_⟩
  · refine mk_mem_locPart _ _ 0 (isMultiHomog_one _ fun _ => rfl) ?_
    convert hpq using 2
    funext k
    simp
  · refine mk_mem_locPart _ _ (fun _ => n) hph ?_
    convert h1q using 2
    funext k
    simp
  · have e : Ideal.Quotient.mk V p = (⟨p, hpm⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V) :=
      ((Algebra.smul_def p (1 : MRingOver S ι ⧸ V)).trans (mul_one _)).symm
    refine (Fin.sum_univ_one _).trans ?_
    refine LocalizedModule.mk_mul_mk.trans ?_
    calc LocalizedModule.mk (1 * Ideal.Quotient.mk V p) (⟨p, hpm⟩ * 1)
        = LocalizedModule.mk ((⟨p, hpm⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) ⟨p, hpm⟩ := by
          rw [one_mul, mul_one, e]
      _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
      _ = 1 := OreLocalization.one_def.symm

end GenTwistGenerated

theorem GenTwistGenerated.proof : GenTwistGenerated.Statement := by
  intro S _ K _ _ ι _ _ V α m n hα
  induction m with
  | zero => simpa using GenTwistGenerated.generated_diag (V := V) n
  | succ m ih =>
    have e : (((m + 1 : ℕ) : ℤ) • α + fun _ => (n : ℤ)) = α + ((m : ℤ) • α + fun _ => (n : ℤ)) := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e]
    exact GenTwistGenerated.generated_add hα ih

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
