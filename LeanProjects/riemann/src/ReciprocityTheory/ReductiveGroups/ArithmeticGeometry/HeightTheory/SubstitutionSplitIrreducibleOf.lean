import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PowFirstVarDvdSubstitution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvalOneBilinearSubstitution

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

namespace LinearSubstitution

variable {K : Type} [Field K] {D N : ℕ}

abbrev isX (v : V D N) : Prop := v.isRight = true

abbrev isU (v : V D N) : Prop := v.isLeft = true

theorem wt_isX (s : V D N →₀ ℕ) : WH.wt isX s = ∑ i, s (Sum.inr i) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isX]

theorem wt_isU (s : V D N →₀ ℕ) : WH.wt isU s = ∑ p, s (Sum.inl p) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isU]

noncomputable def gImg (t : TVar D N) : MvPolynomial (V D N) K :=
  X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))

theorem weightGrading_substitution (p : V D N → Prop) [DecidablePred p]
    (hp : ∀ t : TVar D N, WH.psiP p (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X)
    (F : KTp K D N) (d0 : ℕ) (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F) :
    WH.psiP p (bilinearSubstitution F) = Polynomial.C (bilinearSubstitution F) * Polynomial.X ^ ((D + 1) * d0) := by
  classical
  have hw : ∀ s ∈ F.support, WH.wt (fun _ : TVar D N => True) s = (D + 1) * d0 := by
    intro s hs
    simp only [WH.wt, ↓reduceIte]
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hmh s hs b]
    simp
  have e := WH.psiP_eq_of_isWeightedHomogeneous (K := K) (fun _ : TVar D N => True) ((D + 1) * d0) F hw
  have e2 := congrArg (Polynomial.mapAlgHom (aeval fun t : TVar D N => gImg (K := K) t)) e
  have h1 : WH.psiP p (bilinearSubstitution F) =
      aeval (fun t => Polynomial.C (gImg (K := K) t) * Polynomial.X) F := by
    rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl, MvPolynomial.comp_aeval_apply]
    simp only [hp]
  rw [h1]
  unfold WH.psiP at e2
  rw [MvPolynomial.comp_aeval_apply] at e2
  convert e2 using 1
  · refine congrArg (fun f => aeval f F) (funext fun t => ?_)
    simp
  · rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl]
    simp

theorem psiX_g (t : TVar D N) :
    WH.psiP isX (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isX]
  try ring

theorem psiU_g (t : TVar D N) :
    WH.psiP isU (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isU]
  try ring

theorem eq_monomial_of_dehomog_const (A : MvPolynomial (V D N) K) (m : ℕ) (hA : ∀ s ∈ A.support, WH.wt isX s = m)
    (k : K) (h1 : ev1 A = C k) : A = C k * X (Sum.inr 0) ^ m := by
  classical
  have hev1x0 : ev1 (X (Sum.inr 0) : MvPolynomial (V D N) K) = 1 := by simp [ev1]
  have hmono : ∀ (s : V D N →₀ ℕ) (a : K),
      ev1 (monomial s a) = monomial (s.erase (Sum.inr 0)) a := by
    intro s a
    have hs : monomial s a =
        monomial (s.erase (Sum.inr 0)) a * X (Sum.inr 0) ^ (s (Sum.inr 0)) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [hs, map_mul, map_pow, hev1x0, one_pow, mul_one, ev1, aeval_monomial, monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    apply Finsupp.prod_congr
    intro v hv
    rw [if_neg]
    rintro rfl
    simp at hv
  have hcoeff : ∀ u, coeff u (ev1 A) =
      ∑ s ∈ A.support, if s.erase (Sum.inr 0) = u then coeff s A else 0 := by
    intro u
    conv_lhs => rw [A.as_sum]
    rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hmono, coeff_monomial]
  have hwt : ∀ s : V D N →₀ ℕ,
      WH.wt isX s = WH.wt isX (s.erase (Sum.inr 0)) + s (Sum.inr 0) := by
    intro s
    conv_lhs => rw [← Finsupp.erase_add_single (Sum.inr 0) s]
    rw [WH.wt_add, WH.wt_single, if_pos (show isX (Sum.inr 0 : V D N) from rfl)]
  have hwt0 : WH.wt isX (0 : V D N →₀ ℕ) = 0 := by simp [WH.wt]
  have hinj : ∀ s ∈ A.support, ∀ s' ∈ A.support,
      s.erase (Sum.inr 0) = s'.erase (Sum.inr 0) → s = s' := by
    intro s hs s' hs' he
    have h2 := hwt s
    have h3 := hwt s'
    rw [hA s hs] at h2
    rw [hA s' hs', ← he] at h3
    have h4 : s (Sum.inr 0) = s' (Sum.inr 0) := by omega
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, ← Finsupp.erase_add_single (Sum.inr 0) s', he, h4]
  have hsingle : ∀ s ∈ A.support, s.erase (Sum.inr 0) = 0 → s = Finsupp.single (Sum.inr 0) m := by
    intro s hs hs0
    have h2 := hwt s
    rw [hA s hs, hs0, hwt0, zero_add] at h2
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, hs0, zero_add, ← h2]
  ext u
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hu : u ∈ A.support
  · have e := hcoeff (u.erase (Sum.inr 0))
    rw [Finset.sum_eq_single u (fun s hs hne => if_neg (fun h => hne (hinj s hs u hu h)))
      (fun h => absurd hu h), if_pos rfl, h1, coeff_C] at e
    rw [← e]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · have h0 : 0 = u.erase (Sum.inr 0) := by
        rw [← h]
        simp
      rw [if_pos h0, if_pos h, mul_one]
    · have h0 : ¬ 0 = u.erase (Sum.inr 0) := fun h0 => h (hsingle u hu h0.symm).symm
      rw [if_neg h0, if_neg h, mul_zero]
  · have hu0 : coeff u A = 0 := by simpa using hu
    rw [hu0]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · rw [if_pos h, mul_one]
      have e := hcoeff 0
      rw [h1, coeff_C, if_pos rfl] at e
      rw [e]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      intro hs0
      apply hu
      rw [← h, ← hsingle s hs hs0]
      exact hs
    · rw [if_neg h, mul_zero]

end LinearSubstitution

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem substitution_split_irreducible_of (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := by
  classical
  have hF0 : F0 ≠ 0 := hirr.ne_zero
  have hirr1 : Irreducible (LinearSubstitution.ev1 (bilinearSubstitution F0)) := by
    rw [LinearSubstitution.evalOne_bilinearSubstitution]
    exact LinearSubstitution.irreducible_theta_rename F0 hirr
  have hg0 : bilinearSubstitution F0 ≠ 0 := fun h => hirr1.ne_zero (by rw [h, map_zero])
  have hX : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isX s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isX _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isX LinearSubstitution.psiX_g F0 d0 hmh)
  have hU : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isU s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isU _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isU LinearSubstitution.psiU_g F0 d0 hmh)
  have hev : LinearSubstitution.ev1 (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) = 1 := by simp [LinearSubstitution.ev1]
  have hbound : ∀ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 →
      a ≤ (bilinearSubstitution F0).totalDegree := by
    rintro a ⟨h, hh⟩
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hh, mul_zero])
    rw [hh, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) hh0, totalDegree_X_pow]
    omega
  obtain ⟨a, hPa, hle, hnot⟩ : ∃ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 ∧
      d.D * d0 ≤ a ∧ ¬ (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ (a + 1) ∣ bilinearSubstitution F0 := by
    have hP0 := d.pow_first_var_dvd_substitution c F0 hF0 hker d0 hmh
    exact ⟨Nat.findGreatest (fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
      (bilinearSubstitution F0).totalDegree,
      Nat.findGreatest_spec (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      Nat.le_findGreatest (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      fun h => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h⟩
  obtain ⟨F1, hF1⟩ := hPa
  have hF10 : F1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hF1, mul_zero])
  have hev1 : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 F1 := by
    rw [hF1, map_mul, map_pow, hev, one_pow, one_mul]
  have hdvdF1 : F1 ∣ bilinearSubstitution F0 := ⟨X (Sum.inr 0) ^ a, by rw [hF1, mul_comm]⟩
  obtain ⟨deF, hdeF⟩ := WH.hom_of_dvd LinearSubstitution.isX ((d.D + 1) * d0) (bilinearSubstitution F0) F1 hg0 hX hdvdF1
  have hshift : ∀ s ∈ F1.support, s + Finsupp.single (Sum.inr 0) a ∈ (bilinearSubstitution F0).support := by
    intro s hs
    rw [mem_support_iff, hF1, mul_comm, X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    exact mem_support_iff.1 hs
  refine ⟨a, F1, deF, hF1, ⟨fun hu => ?_, fun G H hGH => ?_⟩, ?_, ?_, ?_⟩
  · exact hirr1.not_isUnit (by rw [hev1]; exact hu.map _)
  · have hmul : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 G * LinearSubstitution.ev1 H := by rw [hev1, hGH, map_mul]
    have key : ∀ G' : MvPolynomial (LinearSubstitution.V d.D d.N) K, G' ∣ F1 → IsUnit (LinearSubstitution.ev1 G') → IsUnit G' := by
      intro G' hG' hu
      obtain ⟨k, hk, hkG⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
      obtain ⟨m, hm⟩ := WH.hom_of_dvd LinearSubstitution.isX _ (bilinearSubstitution F0) G' hg0 hX (hG'.trans hdvdF1)
      have hG'eq := LinearSubstitution.eq_monomial_of_dehomog_const G' m hm k hkG
      cases m with
      | zero =>
        rw [hG'eq, pow_zero, mul_one]
        exact hk.map C
      | succ m =>
        exfalso
        apply hnot
        obtain ⟨Q, hQ⟩ := hG'
        refine ⟨C k * X (Sum.inr 0) ^ m * Q, ?_⟩
        rw [hF1, hQ, hG'eq]
        ring
    rcases hirr1.isUnit_or_isUnit hmul with h | h
    · exact Or.inl (key G ⟨H, hGH⟩ h)
    · exact Or.inr (key H ⟨G, by rw [hGH, mul_comm]⟩ h)
  · intro s hs
    rw [← LinearSubstitution.wt_isX]
    exact hdeF s hs
  · obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hF10
    have hs' : s ∈ F1.support := mem_support_iff.2 hs
    have h := hX _ (hshift s hs')
    rw [WH.wt_add, WH.wt_single, if_pos (show LinearSubstitution.isX (Sum.inr 0 : LinearSubstitution.V d.D d.N) from rfl),
      hdeF s hs'] at h
    have h2 : (d.D + 1) * d0 = d.D * d0 + d0 := by ring
    linarith
  · intro s hs
    have h := hU _ (hshift s hs)
    rw [WH.wt_add, WH.wt_single, if_neg (by simp [LinearSubstitution.isU]), add_zero] at h
    rw [← LinearSubstitution.wt_isU]
    exact h.le

end Data

end ReciprocityTheory.ChartRestriction.G.T0
