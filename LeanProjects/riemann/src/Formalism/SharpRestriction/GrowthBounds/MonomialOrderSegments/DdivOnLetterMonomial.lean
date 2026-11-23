import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

section Gen

variable {σ : Type} [Fintype σ]

def bin (M α : σ →₀ ℕ) : K := ∏ x, ((α x).choose (M x) : K)

private theorem finsupp_prod_choose_eq_bin_of_le (M α : σ →₀ ℕ) (h : M ≤ α) :
    (α.prod fun x k => (k.choose (M x) : K)) = bin M α := by
  unfold bin Finsupp.prod
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : α x = 0 := by simpa using hx
  have hle : M x ≤ α x := by
    exact Finsupp.le_def.1 h x
  have h1 : M x = 0 := by omega
  simp [h0, h1]

theorem ddiv_monomial' (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) = monomial (α - M) (c * bin M α) := by
  rw [ddiv_monomial]
  by_cases h : M ≤ α
  · rw [if_pos h, finsupp_prod_choose_eq_bin_of_le M α h]
  · rw [if_neg h]
    obtain ⟨x, hx⟩ : ∃ x, α x < M x := by
      by_contra hc
      push_neg at hc
      apply h
      exact Finsupp.le_def.2 hc
    have h0 : (bin M α : K) = 0 := by
      unfold bin
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Nat.choose_eq_zero_of_lt hx])
    rw [h0, mul_zero, map_zero]

theorem vge_bin (v : AddValuation K (WithTop ℚ)) (M α : σ →₀ ℕ) : vge v 0 (bin M α : K) := by
  have h : (bin M α : K) = ((∏ x, (α x).choose (M x) : ℕ) : K) := by
    rw [bin, Nat.cast_prod]
  rw [h]
  exact vge_natCast v _

theorem ddiv_ddiv_of_disjoint (M₁ M₂ : σ →₀ ℕ) (h : ∀ x, M₁ x = 0 ∨ M₂ x = 0)
    (F : MvPolynomial σ K) : ddiv M₁ (ddiv M₂ F) = ddiv (M₁ + M₂) F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · have hb : (bin M₂ α : K) * bin M₁ (α - M₂) = bin (M₁ + M₂) α := by
      unfold bin
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rcases h x with h1 | h2
      · simp [h1]
      · simp [h2]
    simp only [ddiv_monomial']
    rw [tsub_tsub, add_comm M₂ M₁, mul_assoc, hb]
  · simp only [ddiv_add, h₁, h₂]

theorem ddiv_zero' (F : MvPolynomial σ K) : ddiv 0 F = F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [ddiv_monomial']
    simp [bin]
  · rw [ddiv_add, h₁, h₂]

theorem expand_monomial' {τ : Type} (P : ℕ) (d : τ →₀ ℕ) (c : K) :
    expand P (monomial d c) = monomial (P • d) c := by
  rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_eq,
    Finsupp.prod_of_support_subset _ Finsupp.support_smul (fun n e => (X n : MvPolynomial τ K) ^ e)
      (fun i _ => pow_zero _)]

end Gen

section Letter

variable {L : Type} [DecidableEq L] {r : ℕ}

theorem onLetter_apply (i : L) (β : Fin r →₀ ℕ) (j : L) (a : Fin r) :
    onLetter i β (j, a) = if j = i then β a else 0 := by
  unfold onLetter
  by_cases h : j = i
  · subst h
    rw [if_pos rfl]
    exact Finsupp.mapDomain_apply (fun x y hxy => by simpa using hxy) β a
  · rw [if_neg h]
    have hne : (j, a) ∉ Set.range (fun b : Fin r => (i, b)) := by
      rintro ⟨b, hb⟩
      exact h (congrArg Prod.fst hb).symm
    first
      | exact Finsupp.mapDomain_of_notMem_range _ _ hne
      | exact Finsupp.mapDomain_notin_range _ _ hne

def letE (α : L × Fin r →₀ ℕ) (i : L) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α (i, a)

@[simp] theorem letE_apply (α : L × Fin r →₀ ℕ) (i : L) (a : Fin r) : letE α i a = α (i, a) := rfl

def offE (i : L) (α : L × Fin r →₀ ℕ) : L × Fin r →₀ ℕ := α.filter fun x => x.1 ≠ i

theorem offE_apply (i : L) (α : L × Fin r →₀ ℕ) (j : L) (a : Fin r) :
    offE i α (j, a) = if j = i then 0 else α (j, a) := by
  unfold offE
  rw [Finsupp.filter_apply]
  by_cases h : j = i <;> simp [h]

theorem absE_eq_sum (β : Fin r →₀ ℕ) : absE β = ∑ a, β a := by
  unfold absE
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

theorem absE_letE (α : L × Fin r →₀ ℕ) (i : L) : absE (letE α i) = ldeg α i := by
  rw [absE_eq_sum]
  unfold ldeg
  simp only [letE_apply]

end Letter

section Der

variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)

def divE {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => η a / P

@[simp] theorem divE_apply {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) (a : Fin r) : divE P η a = η a / P := rfl

theorem der' (hDER : DER K v p) (hD : DVRHyp v p) (r g : ℕ) (M : Fin r →₀ ℕ) (c : ℕ) (hc : 1 ≤ c) :
    ∃ (I : Type) (_ : Fintype I) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)),
      (∀ s, 0 ≤ v (cf s)) ∧ (∀ s, (absE (κ s) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % p ^ g) then
          monomial (ρ' s + p ^ g • (δ s + (divE (p ^ g) η - κ s))) (cf s * bin (κ s) (divE (p ^ g) η))
          else 0) := by
  have hP : 0 < p ^ g := pow_pos hD.prime.pos g
  have H : ∀ ρf : Fin r → Fin (p ^ g), ∃ (n : ℕ) (cf : Fin n → K) (ρ' δ κ : Fin n → (Fin r →₀ ℕ)),
      (∀ t, 0 ≤ v (cf t)) ∧ (∀ t, (absE (κ t) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ (β γ : Fin r →₀ ℕ), ((c : ℕ) : WithTop ℚ) ≤
        v ((ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • β) (1 : K)) -
          ∑ t, monomial (ρ' t) (cf t) *
            expand (p ^ g) (monomial (δ t) (1 : K) * ddiv (κ t) (monomial β (1 : K)))).coeff γ) :=
    fun ρf => hDER hD r g _ (fun a => by simp) M c hc
  choose n cf ρ' δ κ hcf hκ happ using H
  refine ⟨Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf), inferInstance, fun s a => (s.1 a : ℕ),
    fun s => cf s.1 s.2, fun s => ρ' s.1 s.2, fun s => δ s.1 s.2, fun s => κ s.1 s.2,
    fun s => hcf s.1 s.2, fun s => hκ s.1 s.2, fun η => ?_⟩
  obtain ⟨ρf, hρf⟩ : ∃ ρf : Fin r → Fin (p ^ g), ∀ a, (ρf a : ℕ) = η a % p ^ g :=
    ⟨fun a => ⟨η a % p ^ g, Nat.mod_lt _ hP⟩, fun a => rfl⟩
  have hη : η = (Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η := by
    ext a
    have hm := Nat.mod_add_div (η a) (p ^ g)
    simp [divE_apply, hρf]
    all_goals first | exact hm.symm | omega
  have hterm : ∀ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
      ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) =
      monomial (ρ' ρf t + p ^ g • (δ ρf t + (divE (p ^ g) η - κ ρf t)))
        (cf ρf t * bin (κ ρf t) (divE (p ^ g) η)) := by
    intro t
    rw [ddiv_monomial', monomial_mul, expand_monomial', monomial_mul, one_mul, one_mul]
  have hsum : (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
        ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single ρf]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [hterm t]
      exact if_pos (funext hρf)
    · intro b _ hb
      refine Finset.sum_eq_zero fun t _ => if_neg ?_
      intro h
      apply hb
      funext a
      apply Fin.ext
      have h2 : ((b a : ℕ)) = η a % p ^ g := congrFun h a
      rw [h2, hρf a]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hpoly : ddiv M (monomial η (1 : K)) - (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η) (1 : K)) -
        ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
          ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [hsum, ← hη]
  intro γ
  have key := happ ρf (divE (p ^ g) η) γ
  rw [← hpoly] at key
  exact (vge_natCast_bound v c _).2 key

end Der

section App

variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}

theorem bin_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    (bin (onLetter i M) α : K) = bin M (letE α i) := by
  unfold bin
  rw [Fintype.prod_prod_type, Finset.prod_eq_single i]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [onLetter_apply, if_pos rfl, letE_apply]
  · intro j _ hj
    refine Finset.prod_eq_one fun a _ => ?_
    rw [onLetter_apply, if_neg hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sub_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    α - onLetter i M = offE i α + onLetter i (letE α i - M) := by
  ext ⟨j, a⟩
  simp only [Finsupp.tsub_apply, Finsupp.add_apply, offE_apply, onLetter_apply, letE_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem cge_rename (v : AddValuation K (WithTop ℚ)) {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    {a : ℝ} {Q : MvPolynomial σ K} (hQ : cge v a Q) : cge v a (rename f Q) := by
  intro β
  by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain f hf]
    exact hQ u
  · rw [coeff_rename_eq_zero f Q β (fun u hu => absurd ⟨u, hu⟩ h)]
    exact vge_zero v a

def putL (i : L) (α : L × Fin r →₀ ℕ) : MvPolynomial (Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  (LinearMap.mulLeft K (monomial (offE i α) (1 : K))).comp (rename fun a : Fin r => (i, a)).toLinearMap

private theorem putL_eq_monomial_mul_rename (i : L) (α : L × Fin r →₀ ℕ) (Q : MvPolynomial (Fin r) K) :
    putL i α Q = monomial (offE i α) (1 : K) * rename (fun a : Fin r => (i, a)) Q := by
  simp only [putL, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]

theorem putL_monomial (i : L) (α : L × Fin r →₀ ℕ) (η : Fin r →₀ ℕ) (c : K) :
    putL i α (monomial η c) = monomial (offE i α + onLetter i η) c := by
  rw [putL_eq_monomial_mul_rename, rename_monomial, monomial_mul, one_mul, onLetter]

theorem cge_putL (v : AddValuation K (WithTop ℚ)) (i : L) (α : L × Fin r →₀ ℕ) {a : ℝ}
    {Q : MvPolynomial (Fin r) K} (hQ : cge v a Q) : cge v a (putL i α Q) := by
  rw [putL_eq_monomial_mul_rename]
  have h := cge_mul v (cge_monomial v (offE i α) (vge_one v))
    (cge_rename v (fun a : Fin r => (i, a)) (fun x y hxy => by simpa using hxy) hQ)
  rwa [zero_add] at h

theorem ddiv_onLetter_monomial (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    ddiv (onLetter i M) (monomial α (1 : K)) = putL i α (ddiv M (monomial (letE α i) 1)) := by
  rw [ddiv_monomial', ddiv_monomial', putL_monomial, sub_onLetter, bin_onLetter]

variable {I : Type} [Fintype I]

def appMon (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) : MvPolynomial (L × Fin r) K :=
  ∑ s, if cls s = (fun a => α (i, a) % P) then
    monomial (offE i α + onLetter i (ρ' s + P • (δ s + (divE P (letE α i) - κ s))))
      (cf s * bin (κ s) (divE P (letE α i))) else 0

theorem appMon_eq (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) :
    appMon i P cls cf ρ' δ κ α = putL i α (∑ s, if cls s = (fun a => letE α i a % P) then
      monomial (ρ' s + P • (δ s + (divE P (letE α i) - κ s))) (cf s * bin (κ s) (divE P (letE α i)))
      else 0) := by
  rw [map_sum, appMon]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h, if_pos (show cls s = fun a => letE α i a % P from h), putL_monomial]
  · rw [if_neg h, if_neg (show ¬ cls s = fun a => letE α i a % P from h), map_zero]

theorem cge_appMon (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) (α : L × Fin r →₀ ℕ) :
    cge v 0 (appMon i P cls cf ρ' δ κ α) := by
  unfold appMon
  apply cge_sum v
  intro s _
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h]
    refine cge_monomial v _ ?_
    have h2 := vge_mul v ((vge_zero_iff v (cf s)).2 (hcf s))
      (vge_bin v (κ s) (divE P (letE α i)))
    rwa [add_zero] at h2
  · rw [if_neg h]
    exact cge_zero v 0

end App

section AppL

variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]

theorem ddiv_as_sum {σ : Type} (M : σ →₀ ℕ) (G : MvPolynomial σ K) :
    ddiv M G = ∑ α ∈ G.support, G.coeff α • ddiv M (monomial α (1 : K)) := by
  conv_lhs => rw [G.as_sum]
  rw [ddiv_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← ddiv_smul]
  simp only [smul_monomial, smul_eq_mul, mul_one]

def appL (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) :
    MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  lsup (appMon i P cls cf ρ' δ κ)

theorem cge_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) {a : ℝ} {G : MvPolynomial (L × Fin r) K}
    (hG : cge v a G) : cge v a (appL i P cls cf ρ' δ κ G) := by
  rw [appL, lsup_apply]
  apply cge_sum v
  intro α _
  have h := cge_smul v (hG α) (cge_appMon v i P cls cf ρ' δ κ hcf α)
  rwa [add_zero] at h

theorem cge_ddiv_sub_appL (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (M : Fin r →₀ ℕ)
    (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) (c : ℝ)
    (hder : ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % P) then
          monomial (ρ' s + P • (δ s + (divE P η - κ s))) (cf s * bin (κ s) (divE P η)) else 0))
    {a : ℝ} {G : MvPolynomial (L × Fin r) K} (hG : cge v a G) :
    cge v (a + c) (ddiv (onLetter i M) G - appL i P cls cf ρ' δ κ G) := by
  rw [ddiv_as_sum, appL, lsup_apply, ← Finset.sum_sub_distrib]
  apply cge_sum v
  intro α _
  rw [← smul_sub]
  refine cge_smul v (hG α) ?_
  rw [ddiv_onLetter_monomial, appMon_eq, ← map_sub]
  exact cge_putL v i α (hder (letE α i))

end AppL

namespace TwistData

variable (D : TwistData K) (p : ℕ)

theorem liftE_mb (α : D.EA) (b : D.Lb) (a : Fin D.r) : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by
  rfl

theorem liftE_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by
  rfl

def emb (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1

theorem emb_inl (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  rfl

theorem emb_inr (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inr t, a) = ρ t a + D.P p t * ζ (D.mw t, a) := by
  rfl

theorem emb_liftE (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (h : D.InClass p ρ α) :
    D.emb p ρ (D.liftE p α) = α := by
  ext ⟨x, a⟩
  rcases x with b | t
  · rw [emb_inl, liftE_mb]
  · rw [emb_inr, liftE_mw, ← h t a, Nat.mod_add_div]

theorem digitPart_dg (ρ : D.Tau → Fin D.r → ℕ) (f : D.EA → K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (dg f G) = dg (fun ζ => f (D.emb p ρ ζ)) (D.digitPart p ρ G) := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.dg_monomial, digitPart_monomial, digitPart_monomial]
    by_cases h : D.InClass p ρ α
    · rw [if_pos h, if_pos h, Formalism.MainNotions.PlaneGram.dg_monomial, D.emb_liftE p ρ α h]
    · rw [if_neg h, if_neg h, map_zero]
  · rw [map_add, digitPart_add, digitPart_add, map_add, h₁, h₂]

theorem cge_digitPart (v : AddValuation K (WithTop ℚ)) (ρ : D.Tau → Fin D.r → ℕ) {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (hG : cge v a G) : cge v a (D.digitPart p ρ G) := by
  unfold digitPart
  apply Formalism.MainNotions.PlaneGram.cge_sum v
  intro α _
  by_cases h : D.InClass p ρ α
  · rw [if_pos h]
    exact Formalism.MainNotions.PlaneGram.cge_monomial v _ (hG α)
  · rw [if_neg h]
    exact Formalism.MainNotions.PlaneGram.cge_zero v a

variable (t : D.Tau)

theorem inClass_new (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (ρ1 x : Fin D.r →₀ ℕ) :
    D.InClass p ρ'' (offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x)) ↔
      (∀ a, ρ1 a % D.P p t = ρ'' t a) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  have hval : ∀ t' a, ((Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x) : D.EA)) (Sum.inr t', a) =
      if t' = t then ρ1 a + D.P p t * x a else α (Sum.inr t', a) := by
    intro t' a
    rw [Finsupp.add_apply, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply]
    by_cases h : t' = t
    · subst h
      simp
    · have hne : (Sum.inr t' : D.OL) ≠ Sum.inr t := fun e => h (Sum.inr_injective e)
      simp [h, hne]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [hval, if_pos rfl, Nat.add_mul_mod_self_left] at h1
      exact h1
    · have h1 := h t' a
      rw [hval, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [hval]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, Nat.add_mul_mod_self_left]
      exact h1 a
    · rw [if_neg h]
      exact h2 t' h a

theorem inClass_update (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (cl : Fin D.r → ℕ) :
    D.InClass p (Function.update ρ'' t cl) α ↔
      (cl = fun a => α (Sum.inr t, a) % D.P p t) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by
  constructor
  · intro h
    refine ⟨funext fun a => ?_, fun t' ht' a => ?_⟩
    · have h1 := h t a
      rw [Function.update_apply, if_pos rfl] at h1
      exact h1.symm
    · have h1 := h t' a
      rw [Function.update_apply, if_neg ht'] at h1
      exact h1
  · rintro ⟨h1, h2⟩ t' a
    rw [Function.update_apply]
    by_cases h : t' = t
    · subst h
      rw [if_pos rfl, h1]
    · rw [if_neg h]
      exact h2 t' h a

private theorem liftE_apply_eq_sum_elim (α : D.EA) (x : D.ML × Fin D.r) :
    D.liftE p α x = Sum.elim (fun b => α (Sum.inl b, x.2))
      (Sum.elim (fun _ => 0) (Sum.elim (fun s => α (Sum.inr s, x.2) / D.P p s) (fun _ => 0))) x.1 := by
  rfl

theorem liftE_new (hP : 0 < D.P p t) (α : D.EA) (ρ1 δ1 κ1 : Fin D.r →₀ ℕ) :
    D.liftE p (offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ1 + D.P p t • (δ1 + (divE (D.P p t) (letE α (Sum.inr t)) - κ1)))) =
      onLetter (D.mw t) (divE (D.P p t) ρ1 + δ1) + (D.liftE p α - onLetter (D.mw t) κ1) := by
  ext ⟨y, a⟩
  rcases y with b | t' | t' | t'
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
  · by_cases h : t' = t
    · subst h
      simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]
      first
        | (rw [← mul_add, Nat.add_mul_div_left _ _ hP]; omega)
        | (rw [Nat.add_mul_div_left _ _ hP]; omega)
        | omega
    · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw, h]
  · simp [liftE_apply_eq_sum_elim, Formalism.MainNotions.PlaneGram.offE_apply, onLetter_apply, mw]

theorem letE_liftE_mw (α : D.EA) :
    letE (D.liftE p α) (D.mw t) = divE (D.P p t) (letE α (Sum.inr t)) := by
  ext a
  simp only [Formalism.MainNotions.PlaneGram.letE_apply, Formalism.MainNotions.PlaneGram.divE_apply, liftE_mw]

theorem digitPart_zero (ρ : D.Tau → Fin D.r → ℕ) :
    D.digitPart p ρ (0 : MvPolynomial (D.OL × Fin D.r) K) = 0 := by
  rw [digitPart_eq, map_zero]

def opS (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  c1 • ((LinearMap.mulLeft K (monomial (onLetter (D.mw t) μ) (1 : K))).comp
    (ddivL (onLetter (D.mw t) κ1)))

theorem opS_apply (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) (Q : MvPolynomial (D.ML × Fin D.r) K) :
    D.opS t μ κ1 c1 Q = c1 • (monomial (onLetter (D.mw t) μ) (1 : K) * ddiv (onLetter (D.mw t) κ1) Q) := by
  simp only [opS, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Formalism.MainNotions.PlaneGram.ddiv_eq]

private theorem digitPart_approx_term_lemma_4 (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cl : Fin D.r → ℕ) (e : K) (ρ0 δ0 κ0 : Fin D.r →₀ ℕ) (α : D.EA) (c : K) :
    c • D.digitPart p ρ'' (if cl = (fun a => α (Sum.inr t, a) % D.P p t) then
      monomial (Formalism.MainNotions.PlaneGram.offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ0 + D.P p t • (δ0 + (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)) - κ0))))
        (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.divE (D.P p t) (Formalism.MainNotions.PlaneGram.letE α (Sum.inr t)))) else 0) =
      if (fun a => ρ0 a % D.P p t) = ρ'' t then
        D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (D.digitPart p (Function.update ρ'' t cl) (monomial α c))
      else 0 := by
  have hsh : ∀ L : D.EM, D.opS t (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) κ0 e (monomial L c) =
      monomial (onLetter (D.mw t) (Formalism.MainNotions.PlaneGram.divE (D.P p t) ρ0 + δ0) + (L - onLetter (D.mw t) κ0))
        (c * (e * Formalism.MainNotions.PlaneGram.bin κ0 (Formalism.MainNotions.PlaneGram.letE L (D.mw t)))) := by
    intro L
    rw [opS_apply, Formalism.MainNotions.PlaneGram.ddiv_monomial', Formalism.MainNotions.PlaneGram.bin_onLetter, monomial_mul, smul_monomial, smul_eq_mul,
      one_mul, mul_left_comm]
  by_cases h2 : (fun a => ρ0 a % D.P p t) = ρ'' t
  · rw [if_pos h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial, digitPart_monomial]
      by_cases hQ : ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a
      · rw [if_pos ((D.inClass_new p t ρ'' α ρ0 _).2 ⟨fun a => congrFun h2 a, hQ⟩),
          if_pos ((D.inClass_update p t ρ'' α cl).2 ⟨h1, hQ⟩), smul_monomial, smul_eq_mul, hsh,
          D.liftE_new p t hP, letE_liftE_mw]
      · rw [if_neg (fun h => hQ ((D.inClass_new p t ρ'' α ρ0 _).1 h).2),
          if_neg (fun h => hQ ((D.inClass_update p t ρ'' α cl).1 h).2), smul_zero, map_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero, digitPart_monomial,
        if_neg (fun h => h1 ((D.inClass_update p t ρ'' α cl).1 h).1), map_zero]
  · rw [if_neg h2]
    by_cases h1 : cl = (fun a => α (Sum.inr t, a) % D.P p t)
    · rw [if_pos h1, digitPart_monomial,
        if_neg (fun h => h2 (funext ((D.inClass_new p t ρ'' α ρ0 _).1 h).1)), smul_zero]
    · rw [if_neg h1, digitPart_zero, smul_zero]

theorem digitPart_appL {I : Type} [Fintype I] (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cls : I → Fin D.r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin D.r →₀ ℕ))
    (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ'' (appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G) =
      ∑ s, if (fun a => ρ' s a % D.P p t) = ρ'' t then
        D.opS t (divE (D.P p t) (ρ' s) + δ s) (κ s) (cf s)
          (D.digitPart p (Function.update ρ'' t (cls s)) G) else 0 := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.appL, Formalism.MainNotions.PlaneGram.lsup_monomial, digitPart_smul, Formalism.MainNotions.PlaneGram.appMon, digitPart_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact digitPart_approx_term_lemma_4 D p t hP ρ'' (cls s) (cf s) (ρ' s) (δ s) (κ s) α c
  · rw [map_add, digitPart_add, h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos h, if_pos h, if_pos h, digitPart_add, map_add]
    · rw [if_neg h, if_neg h, if_neg h, add_zero]

end TwistData

end Formalism.MainNotions.PlaneGram
