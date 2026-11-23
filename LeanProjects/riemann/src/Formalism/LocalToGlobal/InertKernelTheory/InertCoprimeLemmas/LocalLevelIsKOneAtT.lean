import Formalism.LocalToGlobal.InertKernelTheory.StatementLoc

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

namespace Formalism.L2.KerInert.Loc

section Res

variable {ι κ R : Type} [CommRing R]

theorem resV_coeff (f : κ → ι) (a : MvPowerSeries ι R) (n : κ →₀ ℕ) :
    MvPowerSeries.coeff n (resV f a) = MvPowerSeries.coeff (n.mapDomain f) a := rfl

theorem degree_mapDomain (f : κ → ι) (n : κ →₀ ℕ) : (n.mapDomain f).degree = n.degree := by
  classical
  refine Finsupp.induction n ?_ ?_
  · simp
  · intro a b g _ _ ih
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, map_add, Finsupp.degree_single,
      Finsupp.degree_single, ih]

def resFam (f : κ → ι) (i : ι) : MvPowerSeries κ R := by
  classical exact if h : ∃ k, f k = i then MvPowerSeries.X h.choose else 0

theorem resFam_apply {f : κ → ι} (hf : Function.Injective f) (k : κ) :
    resFam (R := R) f (f k) = MvPowerSeries.X k := by
  have h : ∃ k', f k' = f k := ⟨k, rfl⟩
  unfold resFam
  rw [dif_pos h, hf h.choose_spec]

theorem resFam_off (f : κ → ι) (i : ι) (hi : ∀ k, f k ≠ i) : resFam (R := R) f i = 0 := by
  unfold resFam
  rw [dif_neg]
  rintro ⟨k, hk⟩
  exact hi k hk

theorem cc_resFam (f : κ → ι) (i : ι) : MvPowerSeries.constantCoeff (resFam (R := R) f i) = 0 := by
  unfold resFam
  split_ifs <;> simp

theorem hasSubst_resFam [Finite ι] (f : κ → ι) : MvPowerSeries.HasSubst (resFam (R := R) f) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => cc_resFam f i)

private theorem prod_X_pow_lemma {σ : Type} (d : σ →₀ ℕ) :
    (d.prod fun k m => (MvPowerSeries.X k : MvPowerSeries σ R) ^ m) = MvPowerSeries.monomial d 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp
  · intro a b g _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun k m => (MvPowerSeries.X k : MvPowerSeries σ R) ^ m) (pow_zero _), ih,
      MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, one_mul]

theorem resV_eq_subst [Finite ι] {f : κ → ι} (hf : Function.Injective f) (g : MvPowerSeries ι R) :
    resV f g = MvPowerSeries.subst (resFam f) g := by
  classical
  ext e
  rw [resV_coeff, MvPowerSeries.coeff_subst (hasSubst_resFam f), finsum_eq_single _ (e.mapDomain f)]
  · beta_reduce
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [resFam_apply hf]
    rw [prod_X_pow_lemma, MvPowerSeries.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    beta_reduce
    by_cases hsub : ↑d.support ⊆ Set.range f
    · obtain ⟨d', rfl⟩ : ∃ d', Finsupp.mapDomain f d' = d :=
        ⟨_, Finsupp.mapDomain_comapDomain f hf d hsub⟩
      rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      simp only [resFam_apply hf]
      rw [prod_X_pow_lemma, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
      rintro rfl
      exact hd rfl
    · rw [Set.not_subset] at hsub
      obtain ⟨s, hs, hsf⟩ := hsub
      have hz : (d.prod fun s m => resFam (R := R) f s ^ m) = 0 := by
        rw [Finsupp.prod]
        apply Finset.prod_eq_zero (Finset.mem_coe.mp hs)
        rw [resFam_off f s (fun k hk => hsf ⟨k, hk⟩), zero_pow (Finsupp.mem_support_iff.mp hs)]
      rw [hz, map_zero, smul_zero]

theorem resV_mul [Finite ι] {f : κ → ι} (hf : Function.Injective f) (a b : MvPowerSeries ι R) :
    resV f (a * b) = resV f a * resV f b := by
  rw [resV_eq_subst hf, resV_eq_subst hf a, resV_eq_subst hf b, MvPowerSeries.subst_mul (hasSubst_resFam f)]

private theorem resV_one_lemma [Finite ι] {f : κ → ι} (hf : Function.Injective f) :
    resV f (1 : MvPowerSeries ι R) = 1 := by
  classical
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
  by_cases h : n = 0
  · rw [if_pos h, if_pos (by rw [h, Finsupp.mapDomain_zero])]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    apply Finsupp.mapDomain_injective hf
    rw [h', Finsupp.mapDomain_zero]

theorem resV_pow [Finite ι] {f : κ → ι} (hf : Function.Injective f) (a : MvPowerSeries ι R) (k : ℕ) :
    resV f (a ^ k) = resV f a ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, resV_one_lemma hf]
  | succ k ih => rw [pow_succ, pow_succ, resV_mul hf, ih]

theorem resV_one [Finite ι] {f : κ → ι} (hf : Function.Injective f) :
    resV f (1 : MvPowerSeries ι R) = 1 :=
  resV_one_lemma hf

theorem resV_add (f : κ → ι) (a b : MvPowerSeries ι R) : resV f (a + b) = resV f a + resV f b := rfl

theorem resV_neg (f : κ → ι) (a : MvPowerSeries ι R) : resV f (-a) = -resV f a := rfl

theorem resV_sub (f : κ → ι) (a b : MvPowerSeries ι R) : resV f (a - b) = resV f a - resV f b := rfl

theorem resV_sum {α : Type} (f : κ → ι) (s : Finset α) (a : α → MvPowerSeries ι R) :
    resV f (∑ x ∈ s, a x) = ∑ x ∈ s, resV f (a x) := by
  ext n
  simp only [resV_coeff, map_sum]

theorem cc_resV (f : κ → ι) (a : MvPowerSeries ι R) :
    MvPowerSeries.constantCoeff (resV f a) = MvPowerSeries.constantCoeff a := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    resV_coeff, Finsupp.mapDomain_zero]

theorem resV_map {S : Type} [CommRing S] (f : κ → ι) (φ : R →+* S) (a : MvPowerSeries ι R) :
    resV f (MvPowerSeries.map φ a) = MvPowerSeries.map φ (resV f a) := by
  ext n
  simp only [resV_coeff, MvPowerSeries.coeff_map]

theorem resV_X [Finite ι] {f : κ → ι} (hf : Function.Injective f) (k : κ) :
    resV f (MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.X k := by
  classical
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  by_cases h : n = Finsupp.single k 1
  · rw [if_pos h, if_pos (by rw [h, Finsupp.mapDomain_single])]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    apply Finsupp.mapDomain_injective hf
    rw [h', Finsupp.mapDomain_single]

theorem resV_X_off [Finite ι] {f : κ → ι} (hf : Function.Injective f) (i : ι) (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  classical
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_X, map_zero, if_neg]
  intro h
  have h2 := congrArg (fun d => d i) h
  simp only [Finsupp.single_eq_same] at h2
  rw [Finsupp.mapDomain_notin_range] at h2
  · exact zero_ne_one h2
  · rintro ⟨k, hk⟩
    exact hi k hk

theorem resV_subst [Finite ι] {σ : Type} {f : κ → ι} (hf : Function.Injective f) {a : σ → MvPowerSeries ι R}
    (ha : MvPowerSeries.HasSubst a) (g : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a g) = MvPowerSeries.subst (fun s => resV f (a s)) g := by
  rw [resV_eq_subst hf, MvPowerSeries.subst_comp_subst_apply ha (hasSubst_resFam f)]
  congr 1
  funext s
  rw [resV_eq_subst hf]

theorem resV_subst_diag [Finite ι] {f : κ → ι} (hf : Function.Injective f) {a : ι → MvPowerSeries ι R}
    (ha : MvPowerSeries.HasSubst a) {a' : κ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (f k)) = a' k) (h0 : ∀ i, (∀ k, f k ≠ i) → resV f (a i) = 0)
    (g : MvPowerSeries ι R) :
    resV f (MvPowerSeries.subst a g) = MvPowerSeries.subst a' (resV f g) := by
  rw [resV_subst hf ha, resV_eq_subst hf g, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam f) ha']
  congr 1
  funext i
  by_cases hi : ∃ k, f k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [resFam_apply hf, MvPowerSeries.subst_X ha', h1]
  · push_neg at hi
    rw [resFam_off f i hi, h0 i hi, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem subst_psubst {σ τ : Type} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b)
    {c : MvPowerSeries σ R} (hc : MvPowerSeries.constantCoeff c = 0) (L : PowerSeries R) :
    MvPowerSeries.subst b (PowerSeries.subst c L) = PowerSeries.subst (MvPowerSeries.subst b c) L := by
  have hc' : MvPowerSeries.HasSubst (fun _ : Unit => c) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hc)
  rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hc' hb]

private theorem cc_psubst_lemma {τ : Type} {c : MvPowerSeries τ R} (hc : MvPowerSeries.constantCoeff c = 0)
    {L : PowerSeries R} (hL : PowerSeries.constantCoeff L = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst c L) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases d with _ | d
  · simp [hL]
  · simp [hc]

theorem hasSubst_diag [Finite ι] (L : PowerSeries R) (hL : PowerSeries.constantCoeff L = 0) :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι R) L) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => cc_psubst_lemma (MvPowerSeries.constantCoeff_X i) hL)

theorem resV_diag [Finite ι] [Finite κ] {f : κ → ι} (hf : Function.Injective f) (L : PowerSeries R)
    (hL : PowerSeries.constantCoeff L = 0) (g : MvPowerSeries ι R) :
    resV f (MvPowerSeries.subst (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι R) L) g) =
      MvPowerSeries.subst (fun k => PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ R) L) (resV f g) := by
  have hc : ∀ i : ι, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries ι R)) :=
    fun i => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)
  refine resV_subst_diag hf (hasSubst_diag L hL) (hasSubst_diag L hL) (fun k => ?_) (fun i hi => ?_) g
  · rw [PowerSeries.subst, PowerSeries.subst, resV_subst hf (hc (f k)), resV_X hf]
  · obtain ⟨L', hL'⟩ := PowerSeries.X_dvd_iff.mpr hL
    have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
    rw [hL', PowerSeries.subst_mul hs, PowerSeries.subst_X hs, resV_mul hf, resV_X_off hf i hi, zero_mul]

theorem hasSubst_negX [Finite ι] :
    MvPowerSeries.HasSubst (fun i : ι => -(MvPowerSeries.X i : MvPowerSeries ι R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by simp)

theorem resV_negX [Finite ι] [Finite κ] {f : κ → ι} (hf : Function.Injective f) (g : MvPowerSeries ι R) :
    resV f (MvPowerSeries.subst (fun i => -(MvPowerSeries.X i : MvPowerSeries ι R)) g) =
      MvPowerSeries.subst (fun k => -(MvPowerSeries.X k : MvPowerSeries κ R)) (resV f g) := by
  refine resV_subst_diag hf hasSubst_negX hasSubst_negX (fun k => ?_) (fun i hi => ?_) g
  · rw [resV_neg, resV_X hf]
  · rw [resV_neg, resV_X_off hf i hi, neg_zero]

end Res

variable {p : ℕ} [Fact p.Prime]

private theorem cc_logF_lemma : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk]
  simp

theorem cc_logF' (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap (K0 p) K1) (logF p)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF_lemma, map_zero]

theorem resV_inParamK {ι κ : Type} [Finite ι] [Finite κ] {f : κ → ι} (hf : Function.Injective f)
    (K1 : Type) [Field K1] [Algebra (K0 p) K1] (g : MvPowerSeries ι K1) :
    resV f (inParamK p K1 g) = inParamK p K1 (resV f g) := by
  rw [inParamK, inParamK]
  exact resV_diag hf _ (cc_logF' K1) g

theorem resV_inParam {ι κ : Type} [Finite ι] [Finite κ] {f : κ → ι} (hf : Function.Injective f)
    (g : MvPowerSeries ι (K0 p)) : resV f (inParam p g) = inParam p (resV f g) := by
  rw [inParam, inParam]
  exact resV_diag hf _ cc_logF_lemma g

theorem resV_expS {ι κ : Type} [Finite ι] {f : κ → ι} (hf : Function.Injective f) (g : MvPowerSeries ι (K0 p)) :
    resV f (expS p g) = expS p (resV f g) := by
  ext n
  rw [resV_coeff]
  show expS p g (n.mapDomain f) = expS p (resV f g) n
  rw [expS, expS, degree_mapDomain]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← resV_pow hf, resV_coeff]

theorem simeq_resV {ι κ : Type} [Finite ι] [Finite κ] {f : κ → ι} (hf : Function.Injective f)
    {a b : MvPowerSeries ι (K0 p)} (h : Simeq p a b) : Simeq p (resV f a) (resV f b) := by
  rw [Simeq] at h ⊢
  obtain ⟨h0, c, hc0, hc⟩ := h
  refine ⟨by rw [← resV_sub, cc_resV, h0], resV f c, by rw [cc_resV, hc0], ?_⟩
  rw [← resV_sub, ← resV_inParam hf, ← resV_expS hf, hc, resV_add, resV_one hf, resV_map]

theorem hasSubst_pair {τ : Type} {x y : MvPowerSeries τ (K0 p)} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.HasSubst ![x, y] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hx, hy])

theorem restrict_formalSum {ι κ : Type} [Finite ι] {f : κ → ι} (hf : Function.Injective f) (be : MvPowerSeries (Fin 2) (K0 p))
    {x y : MvPowerSeries ι (K0 p)} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    resV f (sub2 p be x y) = sub2 p be (resV f x) (resV f y) := by
  rw [sub2, sub2, resV_subst hf (hasSubst_pair hx hy)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem formalSum_zero_zero {τ : Type} {be : MvPowerSeries (Fin 2) (K0 p)} (hbe : BeProp p be) :
    sub2 p be (0 : MvPowerSeries τ (K0 p)) 0 = 0 := by
  have hcc : MvPowerSeries.constantCoeff be = 0 := by
    by_contra hne
    have h1 := hbe.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    simp at h1
  have h00 : (![0, 0] : Fin 2 → MvPowerSeries τ (K0 p)) = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  rw [sub2, h00]
  ext e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)), map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcc, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    have hz : (d.prod fun s m => (fun _ => (0 : MvPowerSeries τ (K0 p))) s ^ m) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      exact zero_pow hs
    rw [hz, map_zero, smul_zero]

theorem resV_beSum {ι κ : Type} [Fintype ι] [Fintype κ] {g : κ → ι} (hg : Function.Injective g)
    {be : MvPowerSeries (Fin 2) (K0 p)} (hbe : BeProp p be) :
    resV (Sum.map g g) (∑ i : ι, sub2 p be (MvPowerSeries.X (Sum.inl i)) (MvPowerSeries.X (Sum.inr i))) =
      ∑ k : κ, sub2 p be (MvPowerSeries.X (Sum.inl k)) (MvPowerSeries.X (Sum.inr k)) := by
  have hgg : Function.Injective (Sum.map g g) := Sum.map_injective.mpr ⟨hg, hg⟩
  rw [resV_sum]
  symm
  apply Fintype.sum_of_injective g hg
  · intro i hi
    have hl : ∀ k, Sum.map g g k ≠ Sum.inl i := by
      rintro (k | k) hk
      · simp only [Sum.map_inl, Sum.inl.injEq] at hk
        exact hi ⟨k, hk⟩
      · simp at hk
    have hr : ∀ k, Sum.map g g k ≠ Sum.inr i := by
      rintro (k | k) hk
      · simp at hk
      · simp only [Sum.map_inr, Sum.inr.injEq] at hk
        exact hi ⟨k, hk⟩
    rw [restrict_formalSum hgg _ (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
      resV_X_off hgg _ hl, resV_X_off hgg _ hr, formalSum_zero_zero hbe]
  · intro k
    have hl := resV_X (R := K0 p) hgg (Sum.inl k)
    have hr := resV_X (R := K0 p) hgg (Sum.inr k)
    simp only [Sum.map_inl, Sum.map_inr] at hl hr
    rw [restrict_formalSum hgg _ (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _), hl, hr]

theorem K1gen_resV {ι κ : Type} [Fintype ι] [Fintype κ] {K1 : Type} [Field K1] [Algebra (K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (K0 p)} {g : κ → ι} (hg : Function.Injective g) {Th : MvPowerSeries (ι ⊕ ι) K1}
    (h : ExtensionGeneratorCondition p K1 R1 be Th) : ExtensionGeneratorCondition p K1 R1 be (resV (Sum.map g g) Th) := by
  have hgg : Function.Injective (Sum.map g g) := Sum.map_injective.mpr ⟨hg, hg⟩
  rw [ExtensionGeneratorCondition] at h ⊢
  obtain ⟨Ph, U, hTh, hU, hneg, hbe, hPh⟩ := h
  refine ⟨resV (Sum.map g g) Ph, resV (Sum.map g g) U, ?_, ?_, ?_, hbe, ?_⟩
  · rw [hTh, resV_mul hgg, resV_map, resV_expS hgg, resV_neg]
  · rw [← resV_inParamK hgg K1 U]
    rw [IntR] at hU ⊢
    intro n
    rw [resV_coeff]
    exact hU _
  · rw [← resV_negX hgg]
    exact simeq_resV hgg hneg
  · rw [← resV_beSum hg hbe]
    exact simeq_resV hgg hPh

end Formalism.L2.KerInert.Loc

namespace Formalism.L2.KerInert

open Formalism.L2.KerInert.Loc Formalism.L2.G.Pend

theorem first_kernel_local_of_general : FirstKernelLocalOfGeneral := by
  intro p _ X _ E hfin be T pos F H v j hj L0 hL0 La' hL' φ
  let _ := wittFractionAlgebraCp p
  exact K1gen_resV (g := fun e => (⟨v, e⟩ : X.EA j)) (fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2)
    (H j hj L0 hL0 La' hL' φ)

theorem admissible_second_of_variant (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p}
    (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.MainNotions.FormalGroupSystem.adm2b D X (pendT X E hfin hst hLT pos F) → Formalism.MainNotions.FormalGroupSystem.adm2 D X (pendT X E hfin hst hLT pos F) :=
  fun h => (adm_two_iff_local_representative D X E hfin hst hLT pos F).2
    (first_kernel_local_of_general X E hfin _ pos F ((adm_two_pendant_iff_representative D X E hfin hst hLT pos F).1 h))

end Formalism.L2.KerInert
