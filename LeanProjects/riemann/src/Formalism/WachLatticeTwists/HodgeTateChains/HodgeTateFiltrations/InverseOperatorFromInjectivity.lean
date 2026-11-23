import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
import Formalism.GaloisCohomology.GaloisCohomologyProofs.DevTorsion

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem t2 : InjectivityOnLayerOfPower := by
  intro R _ Xm _ _ g k z α h hz
  have e1 : (g - 1) * (∑ j ∈ Finset.range k, g ^ j) = g ^ k - 1 := mul_geom_sum g k
  have e2 : (∑ j ∈ Finset.range k, g ^ j) * (g - 1) = g ^ k - 1 := geom_sum_mul g k
  constructor
  · intro x hx
    have h1 : (g ^ k - 1) x = 0 := by
      rw [← e2, Module.End.mul_apply]
      simp [hx]
    have h2 : z • α x = 0 := by
      rw [← h x]; simpa using h1
    exact α.map_eq_zero_iff.1 (hz _ h2)
  · intro x
    refine ⟨(∑ j ∈ Finset.range k, g ^ j) (α.symm x), ?_⟩
    have h1 : (g ^ k - 1) (α.symm x) = z • x := by
      have := h (α.symm x)
      simpa using this
    rw [← h1, ← e1, Module.End.mul_apply]
    simp

section padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma tf_pow {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    (htf : ∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) (k : ℕ) (x : V)
    (h : ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) : x = 0 := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply htf
    rw [smul_smul, ← pow_succ']
    exact h

lemma unit_of_not_dvd {d : ℕ} (h : ¬ ℓ ∣ d) : IsUnit (d : ℤ_[ℓ]) := by
  rw [PadicInt.isUnit_iff]
  apply le_antisymm (PadicInt.norm_le_one _)
  by_contra hc
  push Not at hc
  have h1 : ‖((d : ℤ) : ℤ_[ℓ])‖ < 1 := by simpa using hc
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact h (by exact_mod_cast h1)

lemma index_smul_mem {A : Type} [AddCommGroup A] [Module ℤ_[ℓ] A] (S : Submodule ℤ_[ℓ] A) (d : ℕ)
    (hd : d ≠ 0) (x : A) (h : d • x ∈ S) : ((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • x ∈ S := by
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := ℓ) (n := d)
  have hnd : ¬ ℓ ∣ d' := by
    intro ⟨t, ht⟩
    apply pow_succ_padicValNat_not_dvd (p := ℓ) hd
    refine ⟨t, ?_⟩
    rw [pow_succ, mul_assoc, ← ht]
    exact hd'
  obtain ⟨c, hc⟩ := unit_of_not_dvd hnd
  have h1 : d • x = (c : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • x) := by
    rw [smul_smul, hc, ← Nat.cast_smul_eq_nsmul ℤ_[ℓ] d x]
    congr 1
    conv_lhs => rw [hd']
    push_cast
    ring
  have h2 : ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (d • x) ∈ S := S.smul_mem _ h
  rw [h1, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

lemma poly_split (R : Polynomial ℤ_[ℓ]) : ∃ R' : Polynomial ℤ_[ℓ], R = C (R.eval 1) + (X - 1) * R' := by
  obtain ⟨R', hR'⟩ : (X - C (1 : ℤ_[ℓ])) ∣ R - C (R.eval 1) := X_sub_C_dvd_sub_C_eval
  refine ⟨R', ?_⟩
  rw [map_one] at hR'
  rw [← hR']; ring

lemma aeval_split {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + (g (aeval g R' x) - aeval g R' x) := by
  conv_lhs => rw [h]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

lemma aeval_split' {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + aeval g R' (g x - x) := by
  conv_lhs => rw [h, mul_comm]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

end padic

theorem eigen : StatEigen := by
  intro ℓ _ w m hm h2 hw U i V _ _ g htf hkill k x x' hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  have h1 : aeval g (Rpoly ℓ w U i) (g x' - x') = 0 := by
    have h0 : aeval g ((X - 1) * Rpoly ℓ w U i) x' = 0 := by rw [hkill]; rfl
    rw [mul_comm, map_mul, Module.End.mul_apply] at h0
    simpa using h0
  have h3 : aeval g (Rpoly ℓ w U i) x = 0 := by
    apply tf_pow htf k
    rw [← map_smul, hx, h1]
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split g _ R' hR' x
  rw [h3] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  set c := PadicInt.unitCoeff hne with hc
  refine ⟨-(((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • aeval g R' x), ?_⟩
  have h5 : ((Rpoly ℓ w U i).eval 1) • x = -(g (aeval g R' x) - aeval g R' x) :=
    eq_neg_of_add_eq_zero_left h4.symm
  have h6 : ((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x
      = ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((Rpoly ℓ w U i).eval 1) • x) := by
    rw [smul_smul]
    conv_rhs => rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h6, h5]
  simp only [map_neg, map_smul, smul_neg, smul_sub]
  abel

theorem htpoly : StatHTpoly := by
  intro ℓ _ w U i
  by_cases hi : i ∈ U
  · refine ⟨?_, fun h => absurd hi h⟩
    have : HTpoly ℓ w U i = (X - 1) * Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [← Finset.mul_prod_erase U _ hi]
      simp
    rw [this]
  · have : HTpoly ℓ w U i = Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [Finset.erase_eq_of_notMem hi]
    exact ⟨this ▸ dvd_mul_left _ _, fun _ => this⟩

theorem eigenInj : StatEigenInj := by
  intro ℓ _ w m hm h2 hw U i hi V _ _ g htf hkill x hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  rw [(htpoly ℓ w U i).2 hi] at hkill
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split' g _ R' hR' x
  rw [hkill, hx, sub_self, map_zero, add_zero] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  apply tf_pow htf (rI ℓ m U i)
  have h5 : ((PadicInt.unitCoeff hne : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x) = 0 := by
    rw [smul_smul, ← hu]; exact h4.symm
  have h6 := congrArg (fun y => (((PadicInt.unitCoeff hne)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • y) h5
  simpa [smul_smul] using h6

theorem devSum : StatDevSum := by
  intro ℓ _ H Gr _ _ _ _ f p c h0 hex hker hGr n
  induction n with
  | zero => intro x _; rw [h0 x, smul_zero]
  | succ n ih =>
    intro x hx
    rw [Finset.sum_range_succ, add_comm (∑ k ∈ Finset.range n, c k) (c n)]
    exact Formalism.GaloisCohomology.devTorsion ℤ_[ℓ] (Gr n) (H (n + 1)) (H n) (f n) (p n) (ℓ : ℤ_[ℓ]) (c n) _
      (hex n) (hker n) (hGr n) ih x hx

theorem killSum : StatKillSum := by
  intro ℓ _ H Gr _ _ _ _ f p c n h0
  induction n with
  | zero => intro _ _ x; rw [h0 x, smul_zero]
  | succ n ih =>
    intro hex hGr x
    have h1 : p n (((ℓ : ℤ_[ℓ]) ^ (∑ k ∈ Finset.range n, c k)) • x) = 0 := by
      rw [map_smul]
      exact ih (fun k hk => hex k (by omega)) (fun k hk => hGr k (by omega)) _
    obtain ⟨y, hy⟩ := (hex n (by omega) _).1 h1
    rw [Finset.sum_range_succ, add_comm (∑ k ∈ Finset.range n, c k) (c n), pow_add, mul_smul, ← hy,
      ← map_smul, hGr n (by omega) y, map_zero]

theorem cores : StatCores := by
  intro ℓ _ A B _ _ _ _ res cor d c hd hcr hB x ⟨k, hk⟩
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c) • res x = 0 := hB _ ⟨k, by rw [← map_smul, hk, map_zero]⟩
  have h2 : d • (((ℓ : ℤ_[ℓ]) ^ c) • x) = 0 := by
    rw [← hcr, map_smul, h1, map_zero]
  have h3 := index_smul_mem (⊥ : Submodule ℤ_[ℓ] A) d hd _ (by simpa using h2)
  rw [pow_add, mul_smul]
  simpa using h3

theorem reindex : StatReindex := by
  intro ℓ m U a n
  unfold cM
  symm
  apply Finset.sum_bij (fun (k : ℕ) _ => a + (k : ℤ))
  · intro k hk
    have := Finset.mem_range.1 hk
    rw [Finset.mem_Ico]; omega
  · intro k1 _ k2 _ h
    simpa using h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    refine ⟨(b - a).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · intro k _; rfl

theorem bkSubspace : StatBKSubspace := by
  intro O F _ _ _ _ _ hO HV HV' _ _ _ _ pair Hf Hf' hann a
  constructor
  · intro h
    rw [hann]
    intro b hb
    by_contra hne
    obtain ⟨t, ht0, htu⟩ := Ring.exists_not_isUnit_of_not_isField hO
    have hinj := IsFractionRing.injective O F
    have ht : algebraMap O F t ≠ 0 := by
      intro h0; exact ht0 (hinj (by rw [h0, map_zero]))
    obtain ⟨o, ho⟩ := h (((algebraMap O F t)⁻¹ / pair a b) • b) (Hf'.smul_mem _ hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at ho
    apply htu
    refine IsUnit.of_mul_eq_one o (hinj ?_)
    rw [map_mul, ho, map_one, mul_inv_cancel₀ ht]
  · intro h b hb
    exact ⟨0, by rw [map_zero, (hann a).1 h b hb]⟩

theorem bkc : StatBKc := by
  intro O _ ϖ r Hr HD HV Z H0 _ _ _ _ _ _ _ _ _ _ io pr j q dl Hf hsq hkill hlift hker hdl b ⟨β, hβ, hb⟩
  obtain ⟨z, hz⟩ := hlift β (by rw [← hb, ← map_smul, hkill, map_zero])
  obtain ⟨h, hh⟩ := hker (b - q z) (by rw [map_sub, hsq, hz, hb, sub_self])
  refine ⟨z + dl h, ?_, ?_⟩
  · rw [map_add, hdl, add_zero, hz]; exact hβ
  · rw [map_add, ← hh]; abel

theorem lemmaA : StatLemmaA := by
  intro ℓ Bm _ Am T hsat hcl hT hstep x hx
  apply hcl
  intro n
  induction n with
  | zero => exact ⟨0, Am.zero_mem, x, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, b, hab⟩ := ih
    have hsatn : ∀ (k : ℕ) (y : Bm), (ℓ ^ k) • y ∈ Am → y ∈ Am := by
      intro k
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ihk =>
        intro y hy
        apply hsat
        apply ihk
        rw [smul_smul, ← pow_succ]; exact hy
    have h1 : (ℓ ^ n) • T b ∈ Am := by
      have : (ℓ ^ n) • T b = T x - T a := by rw [hab, map_add, map_nsmul]; abel
      rw [this]; exact Am.sub_mem hx (hT a ha)
    obtain ⟨a', ha', b', hab'⟩ := hstep b ⟨T b, hsatn n _ h1, 0, by simp⟩
    refine ⟨a + (ℓ ^ n) • a', Am.add_mem ha (Am.nsmul_mem ha' _), b', ?_⟩
    rw [hab, hab', smul_add, smul_smul, ← pow_succ, add_assoc]

theorem inverse_operator_from_injectivity : InverseOperatorFromInjectivity := by
  intro R _ Xm _ _ g z hinj hsur
  choose S hS using hsur
  have huniq : ∀ a b : Xm, g a - a = g b - b → a = b := by
    intro a b h
    have : g (a - b) = a - b := by
      rw [map_sub]
      have h' : g a - g b = a - b := by
        have := sub_eq_sub_iff_add_eq_add.1 h
        rw [sub_eq_sub_iff_add_eq_add, this, add_comm]
      exact h'
    exact sub_eq_zero.1 (hinj _ this)
  refine ⟨{ toFun := S, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro a b
    apply huniq
    rw [← hS, map_add, smul_add, hS a, hS b]; abel
  · intro c a
    apply huniq
    rw [← hS, RingHom.id_apply, map_smul, ← smul_sub, ← hS a, smul_comm]
  · intro x; exact (hS x).symm
  · intro x
    apply huniq
    show g (S (g x - x)) - S (g x - x) = _
    rw [← hS, map_smul, smul_sub]

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
