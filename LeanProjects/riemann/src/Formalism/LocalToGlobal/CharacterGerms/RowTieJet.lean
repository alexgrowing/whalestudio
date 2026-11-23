import Formalism.LocalToGlobal.CharacterGerms.MemVarsProdAll

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section Disjoint

variable {K : Type} [Field K] {σ : Type}

def rtjSerIn (A : Set σ) (F : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F ≠ 0 → (↑μ.support : Set σ) ⊆ A

theorem rtj_jet_subset (P : MvPolynomial σ K) (F : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetAt0 P F = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : K) * MvPowerSeries.coeff m F := by
  unfold jetAt0
  exact Finset.sum_subset hS fun m _ hm => by
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    rw [hm, zero_mul, zero_mul]

theorem rtj_split_unique {A : Set σ} {a b c d : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A)
    (hb : (↑b.support : Set σ) ⊆ Aᶜ) (hc : (↑c.support : Set σ) ⊆ A)
    (hd : (↑d.support : Set σ) ⊆ Aᶜ) (h : c + d = a + b) : c = a ∧ d = b := by
  have key : ∀ i, c i = a i ∧ d i = b i := by
    intro i
    have hi : c i + d i = a i + b i := by
      have := congrArg (fun f : σ →₀ ℕ => f i) h
      simpa only [Finsupp.add_apply] using this
    by_cases hA : i ∈ A
    · have hb0 : b i = 0 := by
        by_contra hne
        exact hb (Finsupp.mem_support_iff.mpr hne) hA
      have hd0 : d i = 0 := by
        by_contra hne
        exact hd (Finsupp.mem_support_iff.mpr hne) hA
      omega
    · have ha0 : a i = 0 := by
        by_contra hne
        exact hA (ha (Finsupp.mem_support_iff.mpr hne))
      have hc0 : c i = 0 := by
        by_contra hne
        exact hA (hc (Finsupp.mem_support_iff.mpr hne))
      omega
  exact ⟨Finsupp.ext fun i => (key i).1, Finsupp.ext fun i => (key i).2⟩

theorem rtj_antidiag_split {A : Set σ} (f g : (σ →₀ ℕ) → K)
    (hf : ∀ c, f c ≠ 0 → (↑c.support : Set σ) ⊆ A)
    (hg : ∀ d, g d ≠ 0 → (↑d.support : Set σ) ⊆ Aᶜ)
    {a b : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A) (hb : (↑b.support : Set σ) ⊆ Aᶜ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b), f x.1 * g x.2 = f a * g b := by
  rw [Finset.sum_eq_single_of_mem (a, b) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)]
  intro x hx hne
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_contra h0
  have hfc : f x.1 ≠ 0 := left_ne_zero_of_mul h0
  have hgd : g x.2 ≠ 0 := right_ne_zero_of_mul h0
  obtain ⟨h1, h2⟩ := rtj_split_unique ha hb (hf x.1 hfc) (hg x.2 hgd) hx
  exact hne (Prod.ext h1 h2)

theorem rtj_supp_of_supported {A : Set σ} {P : MvPolynomial σ K} (hP : P ∈ MvPolynomial.supported K A)
    (m : σ →₀ ℕ) (hm : MvPolynomial.coeff m P ≠ 0) : (↑m.support : Set σ) ⊆ A := by
  intro i hi
  rw [MvPolynomial.mem_supported] at hP
  exact hP ((MvPolynomial.mem_vars i).mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, hi⟩)

theorem rtj_mfact_add {a b : σ →₀ ℕ} (h : Disjoint a.support b.support) :
    mfact (a + b) = mfact a * mfact b := by
  unfold mfact
  exact Finsupp.prod_add_index_of_disjoint h (fun (_ : σ) (k : ℕ) => k.factorial)

theorem rtj_jet_mul (A : Set σ) (P Q : MvPolynomial σ K) (F G : MvPowerSeries σ K)
    (hP : P ∈ MvPolynomial.supported K A) (hQ : Q ∈ MvPolynomial.supported K Aᶜ)
    (hF : rtjSerIn A F) (hG : rtjSerIn Aᶜ G) :
    jetAt0 (P * Q) (F * G) = jetAt0 P F * jetAt0 Q G := by
  have hPs : ∀ a ∈ P.support, (↑a.support : Set σ) ⊆ A := fun a ha =>
    rtj_supp_of_supported hP a (MvPolynomial.mem_support_iff.mp ha)
  have hQs : ∀ b ∈ Q.support, (↑b.support : Set σ) ⊆ Aᶜ := fun b hb =>
    rtj_supp_of_supported hQ b (MvPolynomial.mem_support_iff.mp hb)
  have hterm : ∀ x ∈ P.support ×ˢ Q.support,
      MvPolynomial.coeff (x.1 + x.2) (P * Q) * (mfact (x.1 + x.2) : K) *
          MvPowerSeries.coeff (x.1 + x.2) (F * G) =
        (MvPolynomial.coeff x.1 P * (mfact x.1 : K) * MvPowerSeries.coeff x.1 F) *
          (MvPolynomial.coeff x.2 Q * (mfact x.2 : K) * MvPowerSeries.coeff x.2 G) := by
    intro x hx
    rw [Finset.mem_product] at hx
    have ha := hPs x.1 hx.1
    have hb := hQs x.2 hx.2
    have hdis : Disjoint x.1.support x.2.support := by
      rw [Finset.disjoint_left]
      intro i hia hib
      exact hb hib (ha hia)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul,
      rtj_antidiag_split (A := A) (fun c => MvPolynomial.coeff c P) (fun d => MvPolynomial.coeff d Q)
        (fun c hc => rtj_supp_of_supported hP c hc) (fun d hd => rtj_supp_of_supported hQ d hd) ha hb,
      rtj_antidiag_split (A := A) (fun c => MvPowerSeries.coeff c F) (fun d => MvPowerSeries.coeff d G)
        hF hG ha hb,
      rtj_mfact_add hdis]
    push_cast
    ring
  have hsupp : (P * Q).support ⊆ (P.support ×ˢ Q.support).image (fun x => x.1 + x.2) := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hm
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_product.mpr
      ⟨MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne),
        MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩, hx⟩
  have hinj : Set.InjOn (fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => x.1 + x.2) ↑(P.support ×ˢ Q.support) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_product.mp hx
    have hy' := Finset.mem_product.mp hy
    obtain ⟨h1, h2⟩ := rtj_split_unique (hPs _ hx'.1) (hQs _ hx'.2) (hPs _ hy'.1) (hQs _ hy'.2) hxy.symm
    exact Prod.ext h1.symm h2.symm
  rw [rtj_jet_subset (P * Q) (F * G) _ hsupp, Finset.sum_image hinj, Finset.sum_congr rfl hterm,
    rtj_jet_subset P F P.support subset_rfl, rtj_jet_subset Q G Q.support subset_rfl,
    Finset.sum_mul_sum, Finset.sum_product]

theorem rtj_serIn_mono {A B : Set σ} (h : A ⊆ B) {F : MvPowerSeries σ K} (hF : rtjSerIn A F) :
    rtjSerIn B F := by
  unfold rtjSerIn at hF ⊢
  intro μ hμ
  exact (hF μ hμ).trans h

theorem rtj_serIn_one (A : Set σ) : rtjSerIn A (1 : MvPowerSeries σ K) := by
  unfold rtjSerIn
  intro μ hμ
  rw [MvPowerSeries.coeff_one] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp
  · exact absurd rfl hμ

theorem rtj_serIn_mul {A : Set σ} {F G : MvPowerSeries σ K} (hF : rtjSerIn A F) (hG : rtjSerIn A G) :
    rtjSerIn A (F * G) := by
  unfold rtjSerIn at hF hG ⊢
  intro μ hμ
  rw [MvPowerSeries.coeff_mul] at hμ
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  have h1 := hF p.1 (left_ne_zero_of_mul hne)
  have h2 := hG p.2 (right_ne_zero_of_mul hne)
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
  · exact h1 h
  · exact h2 h

theorem rtj_serIn_prod {ι : Type} (A : Set σ) (s : Finset ι) (F : ι → MvPowerSeries σ K)
    (hF : ∀ i ∈ s, rtjSerIn A (F i)) : rtjSerIn A (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact rtj_serIn_one A
  | insert i t hi ih =>
    rw [Finset.prod_insert hi]
    exact rtj_serIn_mul (hF i (Finset.mem_insert_self i t))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem rtj_jet_one : jetAt0 (1 : MvPolynomial σ K) (1 : MvPowerSeries σ K) = 1 := by
  have hs : (1 : MvPolynomial σ K).support ⊆ {0} := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  rw [rtj_jet_subset 1 1 {0} hs]
  simp [mfact]

theorem rtj_jet_prod {ι : Type} (A : ι → Set σ) (s : Finset ι)
    (hA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (P : ι → MvPolynomial σ K) (F : ι → MvPowerSeries σ K)
    (hP : ∀ i ∈ s, P i ∈ MvPolynomial.supported K (A i)) (hF : ∀ i ∈ s, rtjSerIn (A i) (F i)) :
    jetAt0 (∏ i ∈ s, P i) (∏ i ∈ s, F i) = ∏ i ∈ s, jetAt0 (P i) (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Finset.prod_empty]
    exact rtj_jet_one
  | insert i t hi ih =>
    have hA' : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → Disjoint (A a) (A b) := fun a ha b hb hab =>
      hA a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hsub : ∀ j ∈ t, A j ⊆ (A i)ᶜ := by
      intro j hj x hx hxi
      have hij : i ≠ j := by
        rintro rfl
        exact hi hj
      exact Set.disjoint_left.mp
        (hA i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj) hij) hxi hx
    have hPt : (∏ j ∈ t, P j) ∈ MvPolynomial.supported K (A i)ᶜ :=
      prod_mem fun j hj => MvPolynomial.supported_mono (hsub j hj) (hP j (Finset.mem_insert_of_mem hj))
    have hFt : rtjSerIn (A i)ᶜ (∏ j ∈ t, F j) :=
      rtj_serIn_prod (A i)ᶜ t F fun j hj => rtj_serIn_mono (hsub j hj) (hF j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
      rtj_jet_mul (A i) (P i) _ (F i) _ (hP i (Finset.mem_insert_self i t)) hPt
        (hF i (Finset.mem_insert_self i t)) hFt,
      ih hA' (fun j hj => hP j (Finset.mem_insert_of_mem hj))
        (fun j hj => hF j (Finset.mem_insert_of_mem hj))]

end Disjoint

section Rename

variable {K : Type} [Field K] {σ τ : Type}

theorem rtj_mfact_embDomain (e : σ ↪ τ) (m : σ →₀ ℕ) : mfact (Finsupp.embDomain e m) = mfact m := by
  unfold mfact
  exact Finsupp.prod_embDomain (g := fun (_ : τ) (k : ℕ) => k.factorial)

private theorem coeff_embDomain_rename_character_germs (e : σ ↪ τ) (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain e d) (MvPowerSeries.rename e F) = MvPowerSeries.coeff d F := by
  rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem d]
  · simp [Finsupp.embDomain_eq_mapDomain]
  · intro y hy hne
    exfalso
    apply hne
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Finsupp.embDomain_eq_mapDomain] at hy
    exact Finsupp.mapDomain_injective e.injective hy

private theorem coeff_rename_eq_zero_of_ne_embDomain (e : σ ↪ τ) (F : MvPowerSeries σ K) (x : τ →₀ ℕ)
    (hx : ∀ d, Finsupp.embDomain e d ≠ x) : MvPowerSeries.coeff x (MvPowerSeries.rename e F) = 0 := by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hy
  exact absurd (by rw [Finsupp.embDomain_eq_mapDomain]; exact hy) (hx y)

theorem rtj_jet_rename (e : σ ↪ τ) (P : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    jetAt0 (MvPolynomial.rename e P) (MvPowerSeries.rename e F) = jetAt0 P F := by
  have hkey : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff (Finsupp.embDomain e d) (MvPowerSeries.rename e F) =
      MvPowerSeries.coeff d F := by
    intro d
    rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem d]
    · simp [Finsupp.embDomain_eq_mapDomain]
    · intro y hy hne
      exfalso
      apply hne
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Finsupp.embDomain_eq_mapDomain] at hy
      exact Finsupp.mapDomain_injective e.injective hy
  have hsupp : (MvPolynomial.rename e P).support ⊆ P.support.image (Finsupp.embDomain e) := by
    intro m hm
    obtain ⟨u, hu, hne⟩ := MvPolynomial.coeff_rename_ne_zero (⇑e) P m (MvPolynomial.mem_support_iff.mp hm)
    exact Finset.mem_image.mpr ⟨u, MvPolynomial.mem_support_iff.mpr hne, by
      rw [Finsupp.embDomain_eq_mapDomain]
      exact hu⟩
  rw [rtj_jet_subset _ _ _ hsupp, Finset.sum_image (by
    intro x _ y _ h
    exact Finsupp.embDomain_injective e h)]
  unfold jetAt0
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_embDomain, rtj_mfact_embDomain, hkey]

theorem rtj_serIn_rename (e : σ ↪ τ) (F : MvPowerSeries σ K) :
    rtjSerIn (Set.range e) (MvPowerSeries.rename e F) := by
  unfold rtjSerIn
  intro μ hμ
  rw [MvPowerSeries.coeff_rename] at hμ
  obtain ⟨y, hy, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hy
  subst hy
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hi)
  exact ⟨j, rfl⟩

theorem rtj_rename_supported (e : σ ↪ τ) (P : MvPolynomial σ K) :
    MvPolynomial.rename e P ∈ MvPolynomial.supported K (Set.range e) := by
  rw [MvPolynomial.mem_supported]
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename (⇑e) P hi)
  exact ⟨j, rfl⟩

theorem rtj_degree_embDomain (e : σ ↪ τ) (μ : σ →₀ ℕ) : (Finsupp.embDomain e μ).degree = μ.degree := by
  simp only [Finsupp.degree]
  exact Finsupp.sum_embDomain (g := fun (_ : τ) (k : ℕ) => k)

theorem rtj_rename_mvExp (e : σ ↪ τ) (L : MvPowerSeries σ K) :
    MvPowerSeries.rename e (mvExp L) = mvExp (MvPowerSeries.rename e L) := by
  ext x
  by_cases hx : ∃ d, Finsupp.embDomain e d = x
  · obtain ⟨d, rfl⟩ := hx
    rw [coeff_embDomain_rename_character_germs]
    change (∑ k ∈ Finset.range (Finsupp.degree d + 1), MvPowerSeries.coeff d (L ^ k) / (k.factorial : K)) =
      ∑ k ∈ Finset.range (Finsupp.degree (Finsupp.embDomain e d) + 1),
        MvPowerSeries.coeff (Finsupp.embDomain e d) ((MvPowerSeries.rename e L) ^ k) / (k.factorial : K)
    rw [rtj_degree_embDomain]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, coeff_embDomain_rename_character_germs]
  · push_neg at hx
    rw [coeff_rename_eq_zero_of_ne_embDomain e _ x hx]
    change (0 : K) = ∑ k ∈ Finset.range (Finsupp.degree x + 1),
        MvPowerSeries.coeff x ((MvPowerSeries.rename e L) ^ k) / (k.factorial : K)
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← map_pow, coeff_rename_eq_zero_of_ne_embDomain e _ x hx, zero_div]

theorem rtj_mvExp_zero : mvExp (0 : MvPowerSeries σ K) = 1 := by
  ext m
  change (∑ k ∈ Finset.range (Finsupp.degree m + 1),
    MvPowerSeries.coeff m ((0 : MvPowerSeries σ K) ^ k) / (k.factorial : K)) = MvPowerSeries.coeff m 1
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _))]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]

end Rename

section Rows

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

def rtjR (ρ : Fin N) : WV I ↪ Fin N × WV I := ⟨fun w => (ρ, w), Prod.mk_right_injective ρ⟩

def rtjE {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl) (i : Fin K) :
    Fin (what₂ i) × WV I ↪ Fin N × WV I :=
  ⟨fun x => (pl ⟨i, x.1⟩, x.2), fun x y h => by
    have h' : (pl ⟨i, x.1⟩, x.2) = (pl ⟨i, y.1⟩, y.2) := h
    have h1 : pl ⟨i, x.1⟩ = pl ⟨i, y.1⟩ := (Prod.ext_iff.1 h').1
    have h2 : x.2 = y.2 := (Prod.ext_iff.1 h').2
    have h3 := hpl h1
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h3
    exact Prod.ext h3 h2⟩

def rtjH (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (k : Knd d) : MvPowerSeries (WV I) C :=
  match k with
  | some (g, a, a') => hL g a a'
  | none => 0

theorem rtj_valOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {M : ℕ}
    (P : MvPolynomial (Fin M × WV I) C) (kind : Fin M → Knd d) (gr : Fin M → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (rtjH hL (kind ρ))))) := by
  unfold ValOf
  refine congrArg (jetAt0 P) (Finset.prod_congr rfl fun ρ _ => ?_)
  rcases kind ρ with _ | ⟨g, a, a'⟩ <;> rfl

theorem rtj_rowCopy_eq {M : ℕ} (ρ : Fin M) (F : MvPowerSeries (WV I) C) :
    rowCopy ρ F = MvPowerSeries.rename (rtjR ρ) F := by
  unfold rowCopy
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem rtj_rename_congr {α β : Type} {f g : α → β} [Filter.TendstoCofinite f] [Filter.TendstoCofinite g]
    (h : f = g) (p : MvPowerSeries α C) : MvPowerSeries.rename f p = MvPowerSeries.rename g p := by
  subst h
  rfl

theorem rtj_rename_rowCopy {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (i : Fin K) (ρ : Fin (what₂ i)) (F : MvPowerSeries (WV I) C) :
    MvPowerSeries.rename (rtjE hpl i) (rowCopy ρ F) = rowCopy (pl ⟨i, ρ⟩) F := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, MvPowerSeries.rename_rename]
  apply rtj_rename_congr
  funext w
  rfl

theorem rtj_grAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (s : Σ i : Fin K, Fin (what₂ i)) :
    grAll pl gr (pl s) = gr s.1 s.2 := by
  unfold grAll
  have h : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dif_pos h]
  have hs : h.choose = s := hpl h.choose_spec
  rw [hs]

theorem jetProd : JetProdSt := by
  intro C _ d I _ hL N K what₂ pl hpl P kind gr
  have hkind : ∀ s : (Σ i : Fin K, Fin (what₂ i)), kindAll pl kind (pl s) = kind s.1 s.2 := by
    intro s
    unfold kindAll
    have h : ∃ s', pl s' = pl s := ⟨s, rfl⟩
    rw [dif_pos h]
    have hs : h.choose = s := hpl h.choose_spec
    rw [hs]
  have hout : ∀ ρ : Fin N, ρ ∉ Finset.univ.image pl →
      rowCopy ρ (grAll pl gr ρ) * mvExp (rowCopy ρ (rtjH hL (kindAll pl kind ρ))) = 1 := by
    intro ρ hρ
    have h : ¬ ∃ s, pl s = ρ := by
      rintro ⟨s, rfl⟩
      exact hρ (Finset.mem_image_of_mem pl (Finset.mem_univ s))
    have h1 : grAll pl gr ρ = 1 := by
      unfold grAll
      rw [dif_neg h]
    have h2 : kindAll pl kind ρ = none := by
      unfold kindAll
      rw [dif_neg h]
    rw [h1, h2, rtj_rowCopy_eq, rtj_rowCopy_eq]
    simp only [rtjH, map_one, map_zero, rtj_mvExp_zero, mul_one]
  have hreindex : ∀ f : Fin N → MvPowerSeries (Fin N × WV I) C, (∀ ρ ∉ Finset.univ.image pl, f ρ = 1) →
      ∏ ρ, f ρ = ∏ i, ∏ r : Fin (what₂ i), f (pl ⟨i, r⟩) := by
    intro f hf
    rw [← Finset.prod_subset (Finset.subset_univ _) (fun ρ _ hρ => hf ρ hρ),
      Finset.prod_image (by intro x _ y _ h; exact hpl h)]
    exact Fintype.prod_sigma (fun s => f (pl s))
  have hblk : ∀ i, MvPowerSeries.rename (rtjE (I := I) hpl i)
        (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))) =
      ∏ r, (rowCopy (pl ⟨i, r⟩) (grAll pl gr (pl ⟨i, r⟩)) *
        mvExp (rowCopy (pl ⟨i, r⟩) (rtjH hL (kindAll pl kind (pl ⟨i, r⟩))))) := by
    intro i
    rw [map_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [map_mul, rtj_rename_mvExp, rtj_rename_rowCopy, rtj_rename_rowCopy, rtj_grAll_pl hpl gr ⟨i, r⟩,
      hkind ⟨i, r⟩]
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin K)), ∀ j ∈ (Finset.univ : Finset (Fin K)), i ≠ j →
      Disjoint (Set.range (rtjE (I := I) hpl i)) (Set.range (rtjE (I := I) hpl j)) := by
    intro i _ j _ hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    apply hij
    have h1 : pl ⟨j, y.1⟩ = pl ⟨i, x.1⟩ := congrArg Prod.fst hy
    exact (congrArg Sigma.fst (hpl h1)).symm
  simp only [rtj_valOf]
  calc jetAt0 (prodAll pl P)
        (∏ ρ, (rowCopy ρ (grAll pl gr ρ) * mvExp (rowCopy ρ (rtjH hL (kindAll pl kind ρ)))))
      = jetAt0 (∏ i, MvPolynomial.rename (rtjE (I := I) hpl i) (P i))
          (∏ i, MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r)))))) := by
        refine congrArg₂ jetAt0 rfl ?_
        rw [hreindex _ hout]
        exact Finset.prod_congr rfl fun i _ => (hblk i).symm
    _ = ∏ i, jetAt0 (MvPolynomial.rename (rtjE (I := I) hpl i) (P i)) (MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r)))))) :=
        rtj_jet_prod (fun i => Set.range (rtjE (I := I) hpl i)) Finset.univ hdis
          (fun i => MvPolynomial.rename (rtjE (I := I) hpl i) (P i))
          (fun i => MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))))
          (fun i _ => rtj_rename_supported _ _) (fun i _ => rtj_serIn_rename _ _)
    _ = ∏ i, jetAt0 (P i) (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))) :=
        Finset.prod_congr rfl fun i _ => rtj_jet_rename _ _ _

end Rows

end Formalism.L2.FormalSeriesBounds
