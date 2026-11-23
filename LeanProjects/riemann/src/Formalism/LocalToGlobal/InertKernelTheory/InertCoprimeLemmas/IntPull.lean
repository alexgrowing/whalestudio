import Formalism.LocalToGlobal.InertKernelTheory.DefsInt

noncomputable section

namespace Formalism.L2.KerInert.PullbackComparison

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MvPolynomial Classical

variable (D : D7) {N N' : ℕ}

def cz (z : VC D N N') (k : D.what₂.Tau × Fin N' × Fin N) : ℂ := z k.1 k.2.1 k.2.2

theorem sum_coordV (z : VC D N N') : ∑ k, cz D z k • coordV D k = z := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordV, cz, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp
  · intro b _ hb
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hb (Prod.ext h1.symm (Prod.ext h2.symm h3.symm))
  · simp

theorem iter_expand (G : VC D N N' → ℂ) (n : ℕ) (z : VC D N N') :
    iteratedFDeriv ℂ n G 0 (fun _ => z) =
      ∑ κ : Fin n → D.what₂.Tau × Fin N' × Fin N,
        (∏ j, cz D z (κ j)) * iteratedFDeriv ℂ n G 0 (fun j => coordV D (κ j)) := by
  have h : (fun _ : Fin n => z) = fun _ => ∑ k, cz D z k • coordV D k := by
    funext _; exact (sum_coordV D z).symm
  rw [h, (iteratedFDeriv ℂ n G 0).map_sum (fun (_ : Fin n) k => cz D z k • coordV D k)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

theorem exists_perm_of_map_eq {β : Type*} {m : ℕ} (g g' : Fin m → β)
    (h : Multiset.map g Finset.univ.val = Multiset.map g' Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin m), ∀ j, g (σ j) = g' j := by
  have h1 : ∀ (f : Fin m → β) (b : β),
      Fintype.card {j // f j = b} = Multiset.count b (Multiset.map f Finset.univ.val) := by
    intro f b
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro x _
    exact eq_comm
  have hc : ∀ b, Fintype.card {j // g' j = b} = Fintype.card {j // g j = b} := by
    intro b; rw [h1, h1, h]
  let e : ∀ b, {j // g' j = b} ≃ {j // g j = b} := fun b => Fintype.equivOfCardEq (hc b)
  refine ⟨(Equiv.sigmaFiberEquiv g').symm.trans ((Equiv.sigmaCongrRight e).trans
    (Equiv.sigmaFiberEquiv g)), fun j => ?_⟩
  exact (e (g' j) ⟨j, rfl⟩).2

theorem iter_eq_taylor (G : VC D N N' → ℂ) (hG : AnalyticOnNhd ℂ G Set.univ) {m : ℕ}
    (g : Fin m → D.what₂.Tau × Fin N' × Fin N) (α : Mono D N N')
    (h : Multiset.map g Finset.univ.val = Finsupp.toMultiset α) :
    iteratedFDeriv ℂ m G 0 (fun j => coordV D (g j)) =
      (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α := by
  have hm : m = Multiset.card (Finsupp.toMultiset α) := by
    rw [← h, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  subst hm
  have hL : Multiset.map (fun i : Fin (Multiset.card (Finsupp.toMultiset α)) =>
      (Finsupp.toMultiset α).toList.get ⟨i, by simpa using i.2⟩) Finset.univ.val = Finsupp.toMultiset α := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset α)]
    congr 1
    apply List.ext_get (by simp)
    intro i h1 h2
    simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq _ g (hL.trans h.symm)
  have h0 : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold taylor
  rw [mul_div_cancel₀ _ h0]
  have e1 : (fun j => coordV D (g j)) = (fun i : Fin (Multiset.card (Finsupp.toMultiset α)) =>
      coordV D ((Finsupp.toMultiset α).toList.get ⟨i, by simpa using i.2⟩)) ∘ σ := by
    funext j; simp only [Function.comp_apply]; rw [hσ j]
  rw [e1, hG.analyticOn.iteratedFDeriv_comp_perm]

def ak {m : ℕ} (κ : Fin m → D.what₂.Tau × Fin N' × Fin N) : Mono D N N' := ∑ j, Finsupp.single (κ j) 1

theorem toMultiset_ak {m : ℕ} (κ : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    Finsupp.toMultiset (ak D κ) = Multiset.map κ Finset.univ.val := by
  unfold ak
  rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [Finset.sum_eq_multiset_sum]
  conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map κ Finset.univ.val), Multiset.map_map]
  rfl

theorem prod_X_eq {m : ℕ} (κ : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    (∏ j, X (κ j) : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ) = monomial (ak D κ) 1 := by
  unfold ak
  rw [monomial_sum_one]
  rfl

def RP (G : VC D N N' → ℂ) (n : ℕ) : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ :=
  ∑ κ : Fin n → D.what₂.Tau × Fin N' × Fin N,
    C (iteratedFDeriv ℂ n G 0 (fun j => coordV D (κ j))) * ∏ j, X (κ j)

theorem eval_RP (G : VC D N N' → ℂ) (n : ℕ) (z : VC D N N') :
    eval (cz D z) (RP D G n) = iteratedFDeriv ℂ n G 0 (fun _ => z) := by
  rw [iter_expand, RP, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp [map_prod, mul_comm]

theorem coeff_RP (G : VC D N N' → ℂ) (hG : AnalyticOnNhd ℂ G Set.univ) (n : ℕ) (β : Mono D N N') :
    coeff β (RP D G n) =
      if (β.sum fun _ m => m) = n then (n.factorial : ℂ) * taylor D G β else 0 := by
  have h2 : coeff β (RP D G n) = ∑ κ : Fin n → D.what₂.Tau × Fin N' × Fin N,
      (if ak D κ = β then (1 : ℂ) else 0) * ((β.prod fun _ n => (n.factorial : ℂ)) * taylor D G β) := by
    rw [RP, coeff_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [prod_X_eq, coeff_C_mul, coeff_monomial]
    split_ifs with h
    · rw [iter_eq_taylor D G hG κ β (by rw [← h, toMultiset_ak]), mul_one, one_mul]
    · rw [mul_zero, zero_mul]
  have h3 : (∑ κ : Fin n → D.what₂.Tau × Fin N' × Fin N, (if ak D κ = β then (1 : ℂ) else 0)) =
      coeff β ((∑ k, X k : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ) ^ n) := by
    rw [← Fin.prod_const n (∑ k, X k : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ),
      Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [prod_X_eq, coeff_monomial]
  rw [h2, ← Finset.sum_mul, h3, coeff_sum_X_pow_of_fintype]
  split_ifs with h
  · rw [← mul_assoc]
    congr 1
    subst h
    have := Nat.multinomial_spec β.support β
    rw [Finsupp.multinomial_eq]
    unfold Finsupp.prod Finsupp.sum
    rw [mul_comm]
    show (∏ a ∈ β.support, ((β a).factorial : ℂ)) * ((Nat.multinomial β.support β : ℕ) : ℂ) =
      (((∑ a ∈ β.support, β a).factorial : ℕ) : ℂ)
    exact_mod_cast this
  · simp

theorem RP_eq (G : VC D N N' → ℂ) (hG : AnalyticOnNhd ℂ G Set.univ) (n : ℕ) :
    RP D G n = ∑ β ∈ Finset.finsuppAntidiag Finset.univ n, monomial β ((n.factorial : ℂ) * taylor D G β) := by
  ext β
  rw [coeff_RP D G hG, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  have hiff : ((β.sum fun _ m => m) = n) ↔ β ∈ Finset.finsuppAntidiag Finset.univ n := by
    rw [Finset.mem_finsuppAntidiag, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp
  by_cases h : (β.sum fun _ m => m) = n
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (mt hiff.2 h)]

theorem eval_aeval' {ι : Type*} (x : ι → ℂ) (ℓ : ι → MvPolynomial ι ℂ) (P : MvPolynomial ι ℂ) :
    eval x (aeval ℓ P) = eval (fun s => eval x (ℓ s)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, eval_X]

theorem RP_comp (H : VC D N N' → ℂ) (hH : AnalyticOnNhd ℂ H Set.univ)
    (A : VC D N N' →L[ℂ] VC D N N') (n : ℕ) :
    RP D (H ∘ A) n = aeval (fun s => ∑ k, cz D (A (coordV D k)) s • X k) (RP D H n) := by
  apply MvPolynomial.funext
  intro x
  have hx : x = cz D (fun τ i j => x (τ, i, j)) := rfl
  set z : VC D N N' := fun τ i j => x (τ, i, j)
  rw [hx, eval_RP, eval_aeval',
    A.iteratedFDeriv_comp_right (hH.contDiff (n := ⊤)) 0 le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  have hz : (fun s => eval (cz D z) (∑ k, cz D (A (coordV D k)) s • X k : MvPolynomial _ ℂ)) =
      cz D (A z) := by
    funext s
    conv_rhs => rw [← sum_coordV D z]
    simp only [map_sum, map_smul, smul_eval, eval_X, cz, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hz, eval_RP]

theorem taylor_comp (H : VC D N N' → ℂ) (hH : AnalyticOnNhd ℂ H Set.univ)
    (A : VC D N N' →L[ℂ] VC D N N') (α : Mono D N N') :
    taylor D (H ∘ A) α = ∑ β ∈ Finset.finsuppAntidiag Finset.univ (α.sum fun _ m => m),
      taylor D H β * coeff α (β.prod fun s e => (∑ k, cz D (A (coordV D k)) s • X k) ^ e) := by
  have hHA : AnalyticOnNhd ℂ (H ∘ A) Set.univ :=
    hH.comp (A.analyticOnNhd _) (Set.mapsTo_univ _ _)
  have h1 := congrArg (coeff α) (RP_comp D H hH A (α.sum fun _ m => m))
  rw [coeff_RP D (H ∘ A) hHA, if_pos rfl, RP_eq D H hH, map_sum, coeff_sum] at h1
  simp only [aeval_monomial, algebraMap_eq, coeff_C_mul] at h1
  have h0 : ((α.sum fun _ m => m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  apply mul_left_cancel₀ h0
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

end Formalism.L2.KerInert.PullbackComparison

noncomputable section

namespace Formalism.L2.KerInert.PullbackComparison

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

variable (D : D7) {N N' : ℕ}

theorem lamC_alg {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (q : Qbar) :
    lamC lam (algebraMap Qbar ℂ q) = lam q := by
  unfold lamC
  rw [dif_pos (show algebraMap Qbar ℂ q ∈ Qbar from q.2)]
  rfl

theorem isHom_prodQ {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R] (c : σ → σ → R) (d : σ →₀ ℕ) :
    (d.prod fun s e => (∑ k, c s k • MvPolynomial.X k : MvPolynomial σ R) ^ e).IsHomogeneous d.degree := by
  have h1 : ∀ s, (∑ k, c s k • MvPolynomial.X k : MvPolynomial σ R).IsHomogeneous 1 := by
    intro s
    apply MvPolynomial.IsHomogeneous.sum
    intro k _
    rw [MvPolynomial.smul_eq_C_mul]
    exact (MvPolynomial.isHomogeneous_X R k).C_mul _
  have := MvPolynomial.IsHomogeneous.prod d.support
    (fun s => (∑ k, c s k • MvPolynomial.X k : MvPolynomial σ R) ^ d s) (fun s => 1 * d s)
    (fun s _ => (h1 s).pow (d s))
  rw [Finsupp.degree_apply]
  simpa [Finsupp.prod] using this

theorem mem_S_iff (d : Mono D N N') (n : ℕ) :
    d ∈ Finset.finsuppAntidiag Finset.univ n ↔ d.degree = n := by
  rw [Finset.mem_finsuppAntidiag]
  rw [Finsupp.degree_eq_sum]
  simp

theorem coe_prodQ {σ : Type*} {R : Type*} [CommSemiring R] (Q : σ → MvPolynomial σ R) (d : σ →₀ ℕ) :
    (d.prod fun s e => ((Q s : MvPolynomial σ R) : MvPowerSeries σ R) ^ e) =
      ((d.prod fun s e => Q s ^ e : MvPolynomial σ R) : MvPowerSeries σ R) := by
  have := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))
    (fun s => Q s ^ d s) d.support
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow] at this
  simp only [Finsupp.prod]
  exact this.symm

theorem pSer_comp (H : VC D N N' → ℂ) (hH : AnalyticOnNhd ℂ H Set.univ)
    (hq : ∀ β, taylor D H β ∈ Qbar)
    (A : VC D N N' →L[ℂ] VC D N N') (hA : ∀ s k, cz D (A (coordV D k)) s ∈ Qbar)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    pSer D lam (H ∘ A) = MvPowerSeries.subst
      (fun s => ((∑ k, lamC lam (cz D (A (coordV D k)) s) • MvPolynomial.X k :
         MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
           MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) (pSer D lam H) := by
  let a' : (D.what₂.Tau × Fin N' × Fin N) → (D.what₂.Tau × Fin N' × Fin N) → Qbar :=
    fun s k => ⟨cz D (A (coordV D k)) s, hA s k⟩
  let t' : Mono D N N' → Qbar := fun β => ⟨taylor D H β, hq β⟩
  let Q' : Mono D N N' → MvPolynomial (D.what₂.Tau × Fin N' × Fin N) Qbar :=
    fun β => β.prod fun s e => (∑ k, a' s k • MvPolynomial.X k) ^ e
  have hmapC : ∀ β, MvPolynomial.map (algebraMap Qbar ℂ) (Q' β) =
      β.prod fun s e => (∑ k, cz D (A (coordV D k)) s • MvPolynomial.X k) ^ e := by
    intro β
    simp only [Q', Finsupp.prod, map_prod, map_pow, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_X]
    rfl
  have hmapP : ∀ β, MvPolynomial.map lam (Q' β) =
      β.prod fun s e => (∑ k, lamC lam (cz D (A (coordV D k)) s) • MvPolynomial.X k) ^ e := by
    intro β
    simp only [Q', Finsupp.prod, map_prod, map_pow, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_X]
    refine Finset.prod_congr rfl fun s _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← lamC_alg lam (a' s k)]
    rfl
  have hB : MvPowerSeries.HasSubst (fun s => ((∑ k, lamC lam (cz D (A (coordV D k)) s) •
      MvPolynomial.X k : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
        MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_X, smul_zero,
        Finset.sum_const_zero])
  ext α
  rw [MvPowerSeries.coeff_subst hB]
  show lamC lam (taylor D (H ∘ A) α) = _
  rw [taylor_comp D H hH A α]
  have e1 : (∑ β ∈ Finset.finsuppAntidiag Finset.univ (α.sum fun _ m => m),
      taylor D H β * MvPolynomial.coeff α (β.prod fun s e =>
        (∑ k, cz D (A (coordV D k)) s • MvPolynomial.X k) ^ e)) =
      algebraMap Qbar ℂ (∑ β ∈ Finset.finsuppAntidiag Finset.univ (α.sum fun _ m => m),
        t' β * MvPolynomial.coeff α (Q' β)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, ← MvPolynomial.coeff_map, hmapC β]
    rfl
  rw [e1, lamC_alg, map_sum]
  have hsupp : Function.support (fun d : Mono D N N' => MvPowerSeries.coeff d (pSer D lam H) •
      MvPowerSeries.coeff α (d.prod fun s e => ((∑ k, lamC lam (cz D (A (coordV D k)) s) •
        MvPolynomial.X k : MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
          MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) ^ e)) ⊆
      ((Finset.finsuppAntidiag (Finset.univ : Finset (D.what₂.Tau × Fin N' × Fin N)) (α.sum fun _ m => m) :
        Finset (Mono D N N')) : Set (Mono D N N')) := by
    intro d hd
    by_contra hdS
    apply hd
    show _ • _ = 0
    rw [coe_prodQ, MvPolynomial.coeff_coe, (isHom_prodQ _ d).coeff_eq_zero, smul_zero]
    intro h
    apply hdS
    rw [Finset.mem_coe, mem_S_iff]
    exact h.symm
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, coe_prodQ, MvPolynomial.coeff_coe, ← hmapP β, MvPolynomial.coeff_map, smul_eq_mul]
  congr 1
  rw [← lamC_alg lam (t' β)]
  rfl

end Formalism.L2.KerInert.PullbackComparison

noncomputable section

namespace Formalism.L2.KerInert.PullbackComparison

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem emb_star (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (star x) = starRingEnd ℂ (φ x) := by
  have := D.host.isCMField_hostE
  change φ (NumberField.IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj]

theorem conj_eq_star (x : D.host.E) : D.host.conj x = star x := by
  apply D.host.φ₀.injective
  rw [emb_star, Formalism.HC.HostAx.conjE_apply]

theorem emb_mem (φ : D.host.E →+* ℂ) (x : D.host.E) : φ x ∈ Qbar :=
  (IsIntegral.of_finite ℚ x).map φ.toRatAlgHom

theorem sum_mul_star_conj {R : Type*} [CommRing R] [StarRing R] {n m : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (g' : Matrix (Fin m) (Fin m) R) (hg : g * g.conjTranspose = 1)
    (hg' : g' * g'.conjTranspose = 1) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, (g'.conjTranspose * x * g) i j * star ((g'.conjTranspose * y * g) i j) =
      ∑ i, ∑ j, x i j * star (y i j) := by
  have key : ∀ X Y : Matrix (Fin m) (Fin n) R,
      ∑ i, ∑ j, X i j * star (Y i j) = Matrix.trace (X * Y.conjTranspose) := by
    intro X Y
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [key, key, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc g g.conjTranspose, hg, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hg', Matrix.mul_one]

theorem map_star (φ : D.host.E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) :
    star (γ.map φ) = (star γ).map φ := by
  ext i j
  simp only [Matrix.star_apply, Matrix.map_apply]
  rw [emb_star, starRingEnd_apply]

theorem map_mul_star (φ : D.host.E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hγ : γ * star γ = 1) : γ.map φ * star (γ.map φ) = 1 := by
  rw [map_star, ← Matrix.map_mul, hγ, Matrix.map_one _ (map_zero φ) (map_one φ)]

variable {D}

theorem tPull_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (z w : VC D N N') :
    tPull D (tor0 D cc δ) γ γ' (z + w) = tPull D (tor0 D cc δ) γ γ' z + tPull D (tor0 D cc δ) γ γ' w := by
  funext τ i j
  have h1 : ∀ x : VC D N N', tPull D (tor0 D cc δ) γ γ' x τ i j = ∑ d, (∑ c,
      star ((tor0 D cc δ).emb τ (γ' c i)) * x τ c d) * (tor0 D cc δ).emb τ (γ d j) := by
    intro x
    simp only [tPull, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, h1, h1, h1]
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem tPull_smul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) (z : VC D N N') :
    tPull D (tor0 D cc δ) γ γ' (c • z) = c • tPull D (tor0 D cc δ) γ γ' z := by
  funext τ i j
  have h1 : ∀ x : VC D N N', tPull D (tor0 D cc δ) γ γ' x τ i j = ∑ d, (∑ c,
      star ((tor0 D cc δ).emb τ (γ' c i)) * x τ c d) * (tor0 D cc δ).emb τ (γ d j) := by
    intro x
    simp only [tPull, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, h1, h1]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  ring

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →L[ℂ] VC D N N' :=
  LinearMap.toContinuousLinearMap
    { toFun := tPull D (tor0 D cc δ) γ γ'
      map_add' := tPull_add cc δ γ γ'
      map_smul' := tPull_smul cc δ γ γ' }

theorem tPullL_apply (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') :
    tPullL cc δ γ γ' z = tPull D (tor0 D cc δ) γ γ' z := rfl

theorem tPull_entry_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (s k : D.what₂.Tau × Fin N' × Fin N) :
    cz D (tPullL cc δ γ γ' (coordV D k)) s ∈ Qbar := by
  rw [tPullL_apply]
  show ((Matrix.conjTranspose (γ'.map (embT D s.1)) * Matrix.of (coordV D k s.1) * γ.map (embT D s.1)
    : Matrix _ _ ℂ)) s.2.1 s.2.2 ∈ Qbar
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply]
  refine IntermediateField.sum_mem _ fun d _ => IntermediateField.mul_mem _ ?_ (emb_mem D _ _)
  refine IntermediateField.sum_mem _ fun c _ => IntermediateField.mul_mem _ ?_ ?_
  · rw [← starRingEnd_apply, ← emb_star]
    exact emb_mem D _ _
  · unfold coordV
    split_ifs
    · exact IntermediateField.one_mem _
    · exact IntermediateField.zero_mem _

theorem tPull_embV (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (B : Matrix (Fin N') (Fin N) D.host.E) :
    tPull D (tor0 D cc δ) γ γ' (embV D (tor0 D cc δ) B) = embV D (tor0 D cc δ) (star γ' * B * γ) := by
  funext τ
  show (Matrix.conjTranspose (γ'.map (embT D τ)) * Matrix.of (fun i j => embT D τ (B i j)) *
    γ.map (embT D τ) : Matrix _ _ ℂ) = Matrix.of (fun i j => embT D τ ((star γ' * B * γ) i j))
  rw [← Matrix.star_eq_conjTranspose, map_star]
  have h1 : Matrix.of (fun i j => embT D τ (B i j)) = B.map (embT D τ) := rfl
  have h2 : Matrix.of (fun i j => embT D τ ((star γ' * B * γ) i j)) = (star γ' * B * γ).map (embT D τ) := rfl
  rw [h1, h2, Matrix.map_mul, Matrix.map_mul]

theorem Hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : γ * star γ = 1) (hγ' : γ' * star γ' = 1) (z w : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D cc δ) (tPull D (tor0 D cc δ) γ γ' z) (tPull D (tor0 D cc δ) γ γ' w) =
      Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D cc δ) z w := by
  unfold Formalism.MainNotions.TaylorLogMetric.Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ))
    (by rw [← Matrix.star_eq_conjTranspose]; exact map_mul_star D _ γ hγ)
    (by rw [← Matrix.star_eq_conjTranspose]; exact map_mul_star D _ γ' hγ') (Matrix.of (z τ)) (Matrix.of (w τ))
  simp only [starRingEnd_apply, tPull]
  simp only [Matrix.of_apply] at this
  exact this

theorem U_pull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : γ * star γ = 1) (hγ' : γ' * star γ' = 1) (t : VC D N N')
    (G : VC D N N' → ℂ) :
    U D (tor0 D cc δ) t (pull D (tor0 D cc δ) γ γ' G) =
      U D (tor0 D cc δ) (tPull D (tor0 D cc δ) γ γ' t) G ∘ tPullL cc δ γ γ' := by
  funext z
  rw [Function.comp_apply, tPullL_apply]
  show G (tPull D (tor0 D cc δ) γ γ' (z + t)) * _ = G (tPull D (tor0 D cc δ) γ γ' z + tPull D (tor0 D cc δ) γ γ' t) * _
  rw [tPull_add, Hf_tPull cc δ γ γ' hγ hγ', Hf_tPull cc δ γ γ' hγ hγ']

end Formalism.L2.KerInert.PullbackComparison

noncomputable section

namespace Formalism.L2.KerInert.PullbackComparison

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lamC_sum_mul {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*} (s : Finset ι) (x y : ι → ℂ)
    (hx : ∀ i, x i ∈ Qbar) (hy : ∀ i, y i ∈ Qbar) :
    lamC lam (∑ i ∈ s, x i * y i) = ∑ i ∈ s, lamC lam (x i) * lamC lam (y i) := by
  have e : (∑ i ∈ s, x i * y i) = algebraMap Qbar ℂ (∑ i ∈ s, (⟨x i, hx i⟩ : Qbar) * ⟨y i, hy i⟩) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [e, lamC_alg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← lamC_alg lam ⟨x i, hx i⟩, ← lamC_alg lam ⟨y i, hy i⟩]
  rfl

theorem cz_apply {N N' : ℕ} (A : VC D N N' →L[ℂ] VC D N N') (z : VC D N N') (s : D.what₂.Tau × Fin N' × Fin N) :
    cz D (A z) s = ∑ k, cz D (A (coordV D k)) s * cz D z k := by
  conv_lhs => rw [← sum_coordV D z]
  simp only [map_sum, map_smul, cz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def PQ {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun B := P * B * Q
  map_add' B C := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem PQ_apply {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E)
    (B : Matrix (Fin N') (Fin N) D.host.E) : PQ P Q B = P * B * Q := rfl

def PQK {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E where
  toFun B := P * B * Q
  map_add' B C := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem PQK_apply {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E)
    (B : Matrix (Fin N') (Fin N) D.host.E) : PQK P Q B = P * B * Q := rfl

theorem homL_map {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E)
    (L1 L2 : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L1' L2' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L1, A.mulVec x ∈ L1') → ∀ x ∈ L2, (P * A * Q).mulVec x ∈ L2') :
    ∀ B ∈ homL D L1 L1', P * B * Q ∈ homL D L2 L2' := by
  intro B hB
  have hle : Submodule.map ((PQ P Q).restrictScalars (𝓞 D.host.E)) (homL D L1 L1') ≤ homL D L2 L2' := by
    unfold homL
    rw [Submodule.map_span_le]
    intro A hA
    exact Submodule.subset_span (h A hA)
  exact hle (Submodule.mem_map_of_mem hB)

theorem YY_map {N N' : ℕ} (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E)
    (L1 L2 : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L1' L2' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L1, A.mulVec x ∈ L1') → ∀ x ∈ L2, (P * A * Q).mulVec x ∈ L2') :
    ∀ B ∈ YYl D L1 L1', P * B * Q ∈ YYl D L2 L2' := by
  intro B hB
  have hle : Submodule.map ((PQ P Q).restrictScalars (𝓞 D.host.E)) (YYl D L1 L1') ≤ YYl D L2 L2' := by
    unfold YYl
    rw [Submodule.map_span_le]
    rintro _ ⟨a, ha, A, hA, rfl⟩
    apply Submodule.subset_span
    refine ⟨a, ha, P * A * Q, homL_map P Q L1 L2 L1' L2' h A hA, ?_⟩
    show P * (a • A) * Q = a • (P * A * Q)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hle (Submodule.mem_map_of_mem hB)

theorem mem_smulLat {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (x : Fin N → D.host.E) : x ∈ SDLat.smulLat γ M ↔ ∃ y ∈ M, γ.mulVec y = x := by
  unfold SDLat.smulLat
  simp [Submodule.mem_map, Matrix.toLin'_apply]

theorem gens_pull {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h4 : star γ' * γ' = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ x ∈ SDLat.smulLat γ M, A.mulVec x ∈ SDLat.smulLat γ' M') :
    ∀ y ∈ M, (star γ' * A * γ).mulVec y ∈ M' := by
  intro y hy
  obtain ⟨m', hm', he⟩ := (mem_smulLat γ' M' _).1 (hA (γ.mulVec y) ((mem_smulLat γ M _).2 ⟨y, hy, rfl⟩))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← he, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  exact hm'

theorem gens_push {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h2 : star γ * γ = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ y ∈ M, A.mulVec y ∈ M') :
    ∀ x ∈ SDLat.smulLat γ M, (γ' * A * star γ).mulVec x ∈ SDLat.smulLat γ' M' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_smulLat γ M x).1 hx
  have e : (star γ).mulVec (γ.mulVec y) = y := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  exact (mem_smulLat γ' M' _).2 ⟨A.mulVec y, hA y hy, rfl⟩

theorem locBasis_pull {N N' r : ℕ} (p : ℕ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h1 : γ * star γ = 1) (h2 : star γ * γ = 1)
    (h3 : γ' * star γ' = 1) (h4 : star γ' * γ' = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : LocBasis D p (YYl D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) b) :
    LocBasis D p (YYl D M M') (fun i => star γ' * b i * γ) := by
  have hΦ := YY_map (star γ') γ (SDLat.smulLat γ M) M (SDLat.smulLat γ' M') M' (gens_pull γ γ' h4 M M')
  have hΨ := YY_map γ' (star γ) M (SDLat.smulLat γ M) M' (SDLat.smulLat γ' M') (gens_push γ γ' h2 M M')
  have hinv : ∀ B : Matrix (Fin N') (Fin N) D.host.E, γ' * (star γ' * B * γ) * star γ = B := by
    intro B
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hinv' : ∀ B : Matrix (Fin N') (Fin N) D.host.E, star γ' * (γ' * B * star γ) * γ = B := by
    intro B
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨hli, hsp, hgen⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective (PQK (star γ') γ) := by
      intro B B' h
      have := congrArg (fun X => γ' * X * star γ) h
      simp only [PQK_apply, hinv] at this
      exact this
    have := hli.map' (PQK (star γ') γ) (LinearMap.ker_eq_bot.2 hinj)
    simpa only [Function.comp_def, PQK_apply] using this
  · intro i
    obtain ⟨s, hs, hm⟩ := hsp i
    refine ⟨s, hs, ?_⟩
    have := hΦ _ hm
    rwa [Matrix.mul_smul, Matrix.smul_mul] at this
  · intro y hy
    obtain ⟨s, hs, c, hc⟩ := hgen _ (hΨ y hy)
    refine ⟨s, hs, c, ?_⟩
    have := congrArg (PQ (star γ') γ) hc
    rw [map_smul, map_sum, PQ_apply, hinv'] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, PQ_apply]

theorem ortho_pull {N N' r : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h1 : γ * star γ = 1) (h3 : γ' * star γ' = 1)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : Orthonormal D b) :
    Orthonormal D (fun i => star γ' * b i * γ) := by
  intro i j
  rw [← hb i j]
  unfold hYY
  congr 1
  simp only [conj_eq_star]
  have := sum_mul_star_conj γ γ' (by rw [← Matrix.star_eq_conjTranspose]; exact h1)
    (by rw [← Matrix.star_eq_conjTranspose]; exact h3) (b i) (b j)
  rw [Matrix.star_eq_conjTranspose]
  exact this

theorem atLog_subst {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (c : (D.what₂.Tau × Fin N' × Fin N) → (D.what₂.Tau × Fin N' × Fin N) → ℂ_[p])
    (hc : ∀ s i, ∑ k, c s k * lamC lam (embT D k.1 (b i k.2.1 k.2.2)) =
      lamC lam (embT D s.1 (b' i s.2.1 s.2.2)))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b (MvPowerSeries.subst (fun s => ((∑ k, c s k • MvPolynomial.X k :
      MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) F) =
      atLog D lam Λ C wq b' F := by
  have hB : MvPowerSeries.HasSubst (fun s => ((∑ k, c s k • MvPolynomial.X k :
      MvPolynomial (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_X, smul_zero,
        Finset.sum_const_zero])
  have hL : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 := by
    intro i
    apply PowerSeries.constantCoeff_subst_eq_zero
    · simp
    · simp [flog]
  have hφ : ∀ bb : Fin r → Matrix (Fin N') (Fin N) D.host.E, MvPowerSeries.HasSubst
      (fun k : D.what₂.Tau × Fin N' × Fin N => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
        (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (bb i k.2.1 k.2.2))) *
        PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)) := by
    intro bb
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro k
    simp only [map_sum, map_mul, hL, mul_zero, Finset.sum_const_zero]
  dsimp only [atLog]
  rw [MvPowerSeries.subst_comp_subst_apply hB (hφ b)]
  congr 1
  funext s
  rw [MvPowerSeries.subst_coe, map_sum]
  simp only [map_smul, MvPolynomial.aeval_X, ← hc s]
  simp only [Finset.smul_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  simp only [map_mul]
  ring

end Formalism.L2.KerInert.PullbackComparison

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pullback_fact : PullFact := by
  intro D cc δ p _ lam N N' γ γ' M M' t G hAlg hInt
  unfold IntS at hInt ⊢
  intro C wq r b hC hwq hb hon
  have h1 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  have h2 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  have h3 : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ'.2
  have h4 : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ'.2
  have hc : ∀ (s : D.what₂.Tau × Fin N' × Fin N) (i : Fin r),
      ∑ k, lamC lam (cz D (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (coordV D k)) s) * lamC lam (embT D k.1 (b i k.2.1 k.2.2)) =
      lamC lam (embT D s.1 ((star (γ' : Matrix (Fin N') (Fin N') D.host.E) * b i *
        (γ : Matrix (Fin N) (Fin N) D.host.E)) s.2.1 s.2.2)) := by
    intro s i
    rw [← lamC_sum_mul lam Finset.univ _ _ (fun k => tPull_entry_mem cc δ _ _ s k) (fun k => emb_mem D _ _)]
    congr 1
    have := cz_apply (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
      (embV D (tor0 D cc δ) (b i)) s
    rw [tPullL_apply, tPull_embV] at this
    exact this.symm
  rw [U_pull cc δ _ _ h1 h3 t G,
    pSer_comp D _ hAlg.1 hAlg.2 (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E)) (fun s k => tPull_entry_mem cc δ _ _ s k) lam,
    atLog_subst lam _ C wq b (fun i => star (γ' : Matrix (Fin N') (Fin N') D.host.E) * b i *
      (γ : Matrix (Fin N) (Fin N) D.host.E)) _ hc]
  exact hInt C wq r _ hC hwq (locBasis_pull p _ _ h1 h2 h3 h4 M M' b hb) (ortho_pull _ _ h1 h3 b hon)

end Formalism.L2.KerInert
