import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section Forms

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F]

def linForm : (σ → F) →ₗ[F] MvPolynomial σ F :=
  Fintype.linearCombination F (fun p => (X p : MvPolynomial σ F))

theorem linForm_apply (c : σ → F) : linForm c = ∑ p, c p • (X p : MvPolynomial σ F) := by
  simp [linForm, Fintype.linearCombination_apply]

def lin (U : Submodule F (σ → F)) : Ideal (MvPolynomial σ F) :=
  Ideal.span (linForm '' (U : Set (σ → F)))

theorem linForm_mem {U : Submodule F (σ → F)} {c : σ → F} (h : c ∈ U) : linForm c ∈ lin U :=
  Ideal.subset_span ⟨c, h, rfl⟩

variable [DecidableEq σ]

theorem linForm_single (p : σ) : linForm (Pi.single p (1 : F)) = (X p : MvPolynomial σ F) := by
  rw [linForm_apply, Finset.sum_eq_single p]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem eq_sum_single (c : σ → F) : c = ∑ p, c p • (Pi.single p (1 : F) : σ → F) := by
  ext q
  simp [Finset.sum_apply, Pi.single_apply]

theorem eval_linForm (l : (σ → F) →ₗ[F] F) (c : σ → F) :
    eval (fun q => l (Pi.single q 1)) (linForm c) = l c := by
  conv_rhs => rw [eq_sum_single c, map_sum]
  rw [linForm_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [smul_eval]

theorem lin_le_ker {U : Submodule F (σ → F)} (l : (σ → F) →ₗ[F] F) (h : U ≤ LinearMap.ker l) :
    lin U ≤ RingHom.ker (eval fun q => l (Pi.single q 1)) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  change eval _ _ = 0
  rw [eval_linForm]
  exact h hc

theorem X_notMem_lin {U : Submodule F (σ → F)} {p : σ} (h : (Pi.single p (1 : F) : σ → F) ∉ U) :
    (X p : MvPolynomial σ F) ∉ lin U := by
  obtain ⟨l, hl, hU⟩ := Submodule.exists_le_ker_of_notMem h
  intro hX
  have := lin_le_ker l hU hX
  rw [RingHom.mem_ker, eval_X] at this
  exact hl this

theorem single_notMem {U : Submodule F (σ → F)} {p : σ} (h : (X p : MvPolynomial σ F) ∉ lin U) :
    (Pi.single p (1 : F) : σ → F) ∉ U := fun h' => h (linForm_single (F := F) p ▸ linForm_mem h')

theorem lin_sup (U : Submodule F (σ → F)) (p : σ) :
    lin (U ⊔ Submodule.span F {(Pi.single p (1 : F) : σ → F)}) = lin U ⊔ Ideal.span {X p} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (sup_le (Ideal.span_mono (Set.image_mono ?_)) ?_)
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_add, map_smul, linForm_single, smul_eq_C_mul]
    exact add_mem (Ideal.mem_sup_left (linForm_mem hu))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  · exact SetLike.coe_subset_coe.2 le_sup_left
  · rw [Ideal.span_singleton_le_iff_mem, ← linForm_single (F := F) p]
    exact linForm_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem finrank_quot_succ (U : Submodule F (σ → F)) {e : σ → F} (h : e ∉ U) :
    Module.finrank F ((σ → F) ⧸ (U ⊔ Submodule.span F {e})) + 1 =
      Module.finrank F ((σ → F) ⧸ U) := by
  have he : e ≠ 0 := fun h0 => h (h0 ▸ U.zero_mem)
  have h1 := Submodule.finrank_quotient_add_finrank U
  have h2 := Submodule.finrank_quotient_add_finrank (U ⊔ Submodule.span F {e})
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span F {e})
  have h4 : U ⊓ Submodule.span F {e} = ⊥ :=
    ((Submodule.disjoint_span_singleton' he).2 h).eq_bot
  rw [h4, finrank_bot, finrank_span_singleton he] at h3
  omega

end Forms

section Quot

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {F : Type*} [Field F]
  (U : Submodule F (σ → F))

def qb : Module.Basis (Fin (Module.finrank F ((σ → F) ⧸ U))) F ((σ → F) ⧸ U) :=
  Module.finBasis F _

def toY : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin (Module.finrank F ((σ → F) ⧸ U))) F :=
  aeval fun p => linForm ((qb U).equivFun (U.mkQ (Pi.single p 1)))

theorem toY_linForm (c : σ → F) : toY U (linForm c) = linForm ((qb U).equivFun (U.mkQ c)) := by
  rw [linForm_apply c, map_sum]
  conv_rhs => rw [eq_sum_single c]
  simp only [map_sum, map_smul, toY, aeval_X]

theorem toY_kill : ∀ a ∈ lin U, toY U a = 0 := by
  intro a ha
  have : lin U ≤ RingHom.ker (toY U) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    change toY U _ = 0
    have h0 : U.mkQ c = 0 := by simpa using hc
    rw [toY_linForm, h0]
    simp
  exact this ha

def sec (t : Fin (Module.finrank F ((σ → F) ⧸ U))) : σ → F :=
  Function.surjInv (Submodule.mkQ_surjective U) (qb U t)

theorem mkQ_sec (t : Fin (Module.finrank F ((σ → F) ⧸ U))) : U.mkQ (sec U t) = qb U t :=
  Function.surjInv_eq _ _

def fromY : MvPolynomial (Fin (Module.finrank F ((σ → F) ⧸ U))) F →ₐ[F] MvPolynomial σ F ⧸ lin U :=
  aeval fun t => Ideal.Quotient.mkₐ F (lin U) (linForm (sec U t))

theorem fromY_linForm (w : Fin (Module.finrank F ((σ → F) ⧸ U)) → F) :
    fromY U (linForm w) = Ideal.Quotient.mkₐ F (lin U) (linForm (∑ t, w t • sec U t)) := by
  rw [linForm_apply w, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_smul, fromY, aeval_X]

def quotEquiv :
    (MvPolynomial σ F ⧸ lin U) ≃ₐ[F] MvPolynomial (Fin (Module.finrank F ((σ → F) ⧸ U))) F :=
  AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ (lin U) (toY U) (toY_kill U)) (fromY U)
    (by
      apply MvPolynomial.algHom_ext
      intro t
      rw [AlgHom.comp_apply, fromY, aeval_X, AlgHom.id_apply]
      change toY U (linForm (sec U t)) = X t
      have h : (qb U).equivFun (qb U t) = Pi.single t 1 := by
        ext j
        simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
      rw [toY_linForm, mkQ_sec, h, linForm_single])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro p
      change fromY U (toY U (X p)) = Ideal.Quotient.mk (lin U) (X p)
      rw [show toY U (X p) = linForm ((qb U).equivFun (U.mkQ (Pi.single p 1))) by simp [toY],
        fromY_linForm]
      change Ideal.Quotient.mk (lin U) _ = _
      rw [Ideal.Quotient.eq, ← linForm_single (F := F) p, ← map_sub]
      refine linForm_mem ((Submodule.Quotient.eq U).1 ?_)
      change U.mkQ _ = U.mkQ _
      rw [map_sum]
      simp only [map_smul, mkQ_sec]
      exact (qb U).sum_equivFun _)

instance lin_isPrime : (lin U).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (quotEquiv U).toRingEquiv.toMulEquiv.isDomain

theorem lin_dim :
    ringKrullDim (MvPolynomial σ F ⧸ lin U) = (Module.finrank F ((σ → F) ⧸ U) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (quotEquiv U).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  simp

end Quot

section Block

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem homog_linForm (k₀ : K) (hK : ∀ a : K, a = k₀) (c : (Σ k, ι k) → F) :
    IsMultiHomog (linForm c : MRingOver F ι) fun _ => 1 := by
  classical
  intro m hm k
  rw [linForm_apply] at hm
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  have hq' : m ∈ (X q : MRingOver F ι).support := support_smul hq
  have := inh_homog_X (F := F) q m hq' k
  rw [this, (hK k).trans (hK q.1).symm]
  simp

theorem eq_linForm (k₀ : K) (hK : ∀ a : K, a = k₀) {f : MRingOver F ι}
    (hf : IsMultiHomog f fun _ => 1) :
    f = linForm fun p => coeff (Finsupp.single p 1) f := by
  classical
  have hsupp : ∀ m ∈ f.support, ∃ q : Σ k, ι k, m = Finsupp.single q 1 := by
    intro m hm
    have hs : ∑ i, m ⟨k₀, i⟩ = 1 := hf m hm k₀
    obtain ⟨a, -, ha0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i => m ⟨k₀, i⟩) (by rw [hs]; exact one_ne_zero)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => m ⟨k₀, i⟩) (Finset.mem_univ a)
    have ha : m ⟨k₀, a⟩ = 1 := by omega
    have hrest : ∑ x ∈ Finset.univ.erase a, m ⟨k₀, x⟩ = 0 := by omega
    have h0 : ∀ b, b ≠ a → m ⟨k₀, b⟩ = 0 := fun b hb =>
      Finset.sum_eq_zero_iff.1 hrest b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩)
    refine ⟨⟨k₀, a⟩, ?_⟩
    ext ⟨k, b⟩
    have hk := hK k
    subst hk
    by_cases hb : b = a
    · subst hb; simp [ha]
    · rw [h0 b hb, Finsupp.single_apply, if_neg]
      intro h
      exact hb (sigma_mk_injective h).symm
  ext m
  rw [linForm_apply, coeff_sum]
  simp only [coeff_smul, coeff_X', smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hm : m ∈ f.support
  · obtain ⟨q, rfl⟩ := hsupp m hm
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Finsupp.single_left_injective one_ne_zero h)
    · simp
  · rw [notMem_support_iff.1 hm]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    split_ifs with h
    · subst h
      exact notMem_support_iff.1 hm
    · rfl

theorem ptDeg_eq_one [DecidableEq (Σ k, ι k)] (k₀ : K) (hK : ∀ a : K, a = k₀)
    (U : Submodule F ((Σ k, ι k) → F))
    (hd : Module.finrank F (((Σ k, ι k) → F) ⧸ U) = 1) (i : ∀ k, ι k) (hi : IsChart (lin U) i) :
    ptDeg (lin U) i = 1 := by
  set p0 : Σ k, ι k := ⟨k₀, i k₀⟩ with hp0
  set e0 : (Σ k, ι k) → F := Pi.single p0 1 with he0
  have h0 : e0 ∉ U := single_notMem (hi k₀)
  obtain ⟨l, hl, hU⟩ := Submodule.exists_le_ker_of_notMem h0
  set l' : ((Σ k, ι k) → F) →ₗ[F] F := (l e0)⁻¹ • l with hl'
  have hl1 : l' e0 = 1 := by simp [hl', inv_mul_cancel₀ hl]
  have hU' : U ≤ LinearMap.ker l' := fun u hu => by
    have : l u = 0 := hU hu
    simp [hl', this]
  have hne : U.mkQ e0 ≠ 0 := by simpa using h0
  have hq : ∀ q : Σ k, ι k, ∃ c : F, c • e0 - Pi.single q 1 ∈ U := by
    intro q
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hd (U.mkQ (Pi.single q 1))
    refine ⟨c, (Submodule.Quotient.eq U).1 ?_⟩
    change U.mkQ _ = U.mkQ _
    rw [map_smul, hc]
  have hrange : (X p0 - 1 : MRingOver F ι) ∈ chartIdeal (lin U) i :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨k₀, rfl⟩)
  refine inh_finrank_quot (chartIdeal (lin U) i) (fun q => l' (Pi.single q 1)) ?_ ?_
  · refine sup_le (lin_le_ker l' hU') (Ideal.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk := hK k
    subst hk
    change eval _ _ = 0
    simpa [map_sub, eval_X] using sub_eq_zero.2 hl1
  · intro q
    obtain ⟨c, hc⟩ := hq q
    have hlc : l' (Pi.single q 1) = c := by
      have : l' (c • e0 - Pi.single q 1) = 0 := hU' hc
      rw [map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero] at this
      exact this.symm
    rw [hlc]
    have hmem : (linForm (c • e0 - Pi.single q 1) : MRingOver F ι) ∈ chartIdeal (lin U) i :=
      Ideal.mem_sup_left (linForm_mem hc)
    have heq : (X q - C c : MRingOver F ι) =
        C c * (X p0 - 1) - linForm (c • e0 - Pi.single q 1) := by
      rw [map_sub, map_smul, linForm_single, linForm_single, smul_eq_C_mul]
      ring
    rw [heq]
    exact sub_mem (Ideal.mul_mem_left _ _ hrange) hmem

theorem exists_single_notMem [DecidableEq (Σ k, ι k)] (U : Submodule F ((Σ k, ι k) → F))
    (hd : 0 < Module.finrank F (((Σ k, ι k) → F) ⧸ U)) :
    ∃ q : Σ k, ι k, (Pi.single q (1 : F) : (Σ k, ι k) → F) ∉ U := by
  by_contra hcon
  push_neg at hcon
  have htop : U = ⊤ := by
    refine (Submodule.eq_top_iff').2 fun c => ?_
    rw [eq_sum_single c]
    exact U.sum_mem fun p _ => U.smul_mem _ (hcon p)
  subst htop
  have : Subsingleton (((Σ k, ι k) → F) ⧸ (⊤ : Submodule F ((Σ k, ι k) → F))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  rw [Module.finrank_zero_of_subsingleton] at hd
  exact lt_irrefl _ hd

theorem degree_lin (k₀ : K) (hK : ∀ a : K, a = k₀) (J : IFamily F ι) (hJ : IsFieldIntersection J) :
    ∀ (r : ℕ) (U : Submodule F ((Σ k, ι k) → F)), IsProjVarF (lin U) r →
      J (lin U) r (fun _ _ => 1) = 1 := by
  classical
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.2 ⟨k₀, hK⟩
  have hdim : ∀ (r : ℕ) (U : Submodule F ((Σ k, ι k) → F)), IsProjVarF (lin U) r →
      Module.finrank F (((Σ k, ι k) → F) ⧸ U) = r + 1 := by
    intro r U hV
    have h := hV.2
    rw [lin_dim, hcard] at h
    exact_mod_cast h
  intro r
  induction r with
  | zero =>
    intro U hV
    have hd := hdim 0 U hV
    choose i hi using hV.1.2.2
    rw [hJ.1 (lin U) _ i hV hi, ptDeg_eq_one k₀ hK U (by simpa using hd) i hi]
    rfl
  | succ r ih =>
    intro U hV
    have hd := hdim (r + 1) U hV
    obtain ⟨i0, hi0⟩ := hV.1.2.2 k₀
    set p : Σ k, ι k := ⟨k₀, i0⟩ with hp
    have he : (Pi.single p (1 : F) : (Σ k, ι k) → F) ∉ U := single_notMem hi0
    set U' := U ⊔ Submodule.span F {(Pi.single p (1 : F) : (Σ k, ι k) → F)} with hU'
    have hd' : Module.finrank F (((Σ k, ι k) → F) ⧸ U') = r + 1 := by
      have h1 : Module.finrank F (((Σ k, ι k) → F) ⧸ U') + 1 = _ := finrank_quot_succ U he
      omega
    have hsup : lin U ⊔ Ideal.span {(X p : MRingOver F ι)} = lin U' := (lin_sup U p).symm
    have hrel : IsRelevant (lin U') := by
      obtain ⟨q, hq⟩ := exists_single_notMem U' (by omega)
      obtain ⟨k', j⟩ := q
      intro k
      have hk : k = k' := (hK k).trans (hK k').symm
      subst hk
      exact ⟨j, X_notMem_lin hq⟩
    have hV' : IsProjVarF (lin U') r := by
      refine ⟨⟨inferInstance, ⟨_, ?_, rfl⟩, hrel⟩, ?_⟩
      · rintro _ ⟨c, -, rfl⟩
        exact ⟨_, homog_linForm k₀ hK c⟩
      · rw [lin_dim, hd', hcard]
    have hrat : IsRatSection (lin U) (fun _ => 1) (X p) 1 := by
      refine ⟨fun _ => 1, 0, ?_, inh_homog_one, hi0, ?_, fun k => by simp⟩
      · have := inh_homog_X (F := F) p
        have h1 : (Pi.single p.1 1 : K → ℕ) = fun _ => 1 := by
          ext k
          rw [(hK k).trans (hK p.1).symm]
          simp
        rwa [h1] at this
      · exact (Ideal.ne_top_iff_one _).1 hV.1.1.ne_top
    have hb := hJ.2 (lin U) r (fun _ _ => 1) (fun _ => 1) (X p) 1 hV hrat
    have hsn : Fin.snoc (α := fun _ => K → ℤ) (fun _ _ => (1 : ℤ)) (fun _ => 1) =
        fun (_ : Fin (r + 1)) _ => 1 := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hsn] at hb
    rw [hb, ratDiv, inh_divCycle_prime (lin U) (X p) (lin U') hsup hrel, inh_divCycle_one]
    simp [Finsupp.mapRange_single, inh_cycEval_single, ih U' hV']

end Block

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.LinDeg

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem linear_subspace_degree_one : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (k₀ : K), (∀ a : K, a = k₀) → ∀ (J : IFamily F ι), IsFieldIntersection J →
    ∀ (S : Set (MRingOver F ι)), (∀ f ∈ S, IsMultiHomog f fun _ => 1) → ∀ r : ℕ,
    IsProjVarF (Ideal.span S) r → J (Ideal.span S) r (fun _ _ => 1) = 1 := by
  intro F _ K _ ι _ k₀ hK J hJ S hS r hV
  set U : Submodule F ((Σ k, ι k) → F) :=
    ((Ideal.span S).restrictScalars F).comap LinDeg.linForm with hU
  have hlin : Ideal.span S = LinDeg.lin U := by
    refine le_antisymm (Ideal.span_le.2 fun f hf => ?_) (Ideal.span_le.2 ?_)
    · rw [LinDeg.eq_linForm k₀ hK (hS f hf)]
      refine LinDeg.linForm_mem ?_
      change LinDeg.linForm _ ∈ Ideal.span S
      rw [← LinDeg.eq_linForm k₀ hK (hS f hf)]
      exact Ideal.subset_span hf
    · rintro _ ⟨c, hc, rfl⟩
      exact hc
  rw [hlin] at hV ⊢
  exact LinDeg.degree_lin k₀ hK J hJ r U hV

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
