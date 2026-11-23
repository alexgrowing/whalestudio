import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ContAcr

open TopologicalSpace

section Abs

variable {R B X : Type} [CommRing R] [CommRing B] [TopologicalSpace X]

def Simple (j : B →+* R) (ev : X → R →+* B) (E : Clopens X → R) (x : R) : Prop :=
  ∀ z, ∃ V : Clopens X, z ∈ V ∧ E V * x = E V * j (ev z x)

def simpleRing (j : B →+* R) (ev : X → R →+* B) (E : Clopens X → R)
    (hmul : ∀ V W, E (V ⊓ W) = E V * E W) : Subring R where
  carrier := {x | Simple j ev E x}
  mul_mem' := by
    intro x y hx hy z
    obtain ⟨V, hV, h⟩ := hx z
    obtain ⟨W, hW, h'⟩ := hy z
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    rw [hmul, map_mul, map_mul]
    linear_combination (E W * y) * h + (E V * j (ev z x)) * h'
  one_mem' := fun z => ⟨⊤, trivial, by rw [map_one, map_one]⟩
  add_mem' := by
    intro x y hx hy z
    obtain ⟨V, hV, h⟩ := hx z
    obtain ⟨W, hW, h'⟩ := hy z
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    rw [hmul, map_add, map_add]
    linear_combination E W * h + E V * h'
  zero_mem' := fun z => ⟨⊤, trivial, by rw [map_zero, map_zero]⟩
  neg_mem' := by
    intro x hx z
    obtain ⟨V, hV, h⟩ := hx z
    refine ⟨V, hV, ?_⟩
    rw [map_neg, map_neg]
    linear_combination -h

variable {j : B →+* R} {ev : X → R →+* B} {E : Clopens X → R}

theorem lc_of_simple (hj : ∀ z b, ev z (j b) = b) (h1 : ∀ z (V : Clopens X), z ∈ V → ev z (E V) = 1) {x : R}
    (hx : Simple j ev E x) : IsLocallyConstant fun z => ev z x := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun z => ?_
  obtain ⟨V, hz, h⟩ := hx z
  refine ⟨V, V.isOpen, hz, fun z' hz' => ?_⟩
  have := congrArg (ev z') h
  rwa [map_mul, map_mul, h1 z' V hz', hj, one_mul, one_mul] at this

theorem zero_of_simple [CompactSpace X] (hmul : ∀ V W, E (V ⊓ W) = E V * E W) (htop : E ⊤ = 1) (hbot : E ⊥ = 0)
    (hcompl : ∀ V, E V + E Vᶜ = 1) {x : R} (hx : Simple j ev E x) (h0 : ∀ z, ev z x = 0) : x = 0 := by
  have key : ∃ V : Clopens X, (Set.univ : Set X) ⊆ (V : Set X) ∧ E V * x = 0 := by
    refine isCompact_univ.induction_on (p := fun s => ∃ V : Clopens X, s ⊆ (V : Set X) ∧ E V * x = 0)
      ⟨⊥, Set.empty_subset _, by rw [hbot, zero_mul]⟩ ?_ ?_ ?_
    · rintro s t hst ⟨V, hV, h⟩
      exact ⟨V, hst.trans hV, h⟩
    · rintro s t ⟨V, hV, h⟩ ⟨W, hW, h'⟩
      refine ⟨V ⊔ W, Set.union_subset_union hV hW, ?_⟩
      have e : E (V ⊔ W) = E V + E W - E V * E W := by
        have h1 := hcompl (V ⊔ W)
        have h2 : (V ⊔ W)ᶜ = Vᶜ ⊓ Wᶜ := compl_sup
        rw [h2, hmul] at h1
        have h3 := hcompl V
        have h4 := hcompl W
        linear_combination h1 - (1 - E W) * h3 - E Vᶜ * h4
      rw [e]
      linear_combination (1 - E W) * h + h'
    · intro z _
      obtain ⟨V, hz, h⟩ := hx z
      refine ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hz), V, subset_rfl, ?_⟩
      rw [h, h0, map_zero, mul_zero]
  obtain ⟨V, hV, h⟩ := key
  have hT : V = ⊤ := SetLike.coe_injective (Set.eq_univ_of_univ_subset hV)
  rw [hT, htop, one_mul] at h
  exact h

theorem exists_of_lc [CompactSpace X] (hcompl : ∀ V, E V + E Vᶜ = 1) (hj : ∀ z b, ev z (j b) = b)
    (h1 : ∀ z (V : Clopens X), z ∈ V → ev z (E V) = 1) (I : Ideal R) (f : X → B) (hf : IsLocallyConstant f)
    (hI : ∀ z, j (f z) ∈ I) : ∃ x ∈ I, ∀ z, ev z x = f z := by
  classical
  have h0 : ∀ z (V : Clopens X), z ∉ V → ev z (E V) = 0 := fun z V hz => by
    have h := congrArg (ev z) (hcompl V)
    rw [map_add, h1 z Vᶜ (by rw [← SetLike.mem_coe, Clopens.coe_compl]; exact hz), map_one] at h
    simpa using h
  let F : B → Clopens X := fun b => ⟨f ⁻¹' {b}, hf.isClopen_fiber b⟩
  have hF : ∀ z b, z ∈ F b ↔ f z = b := fun z b => Iff.rfl
  refine ⟨∑ b ∈ hf.range_finite.toFinset, E (F b) * j b, ?_, fun z => ?_⟩
  · refine Ideal.sum_mem _ fun b hb => ?_
    obtain ⟨z, rfl⟩ := hf.range_finite.mem_toFinset.1 hb
    exact Ideal.mul_mem_left _ _ (hI z)
  · rw [map_sum, Finset.sum_eq_single (f z)]
    · rw [map_mul, h1 z _ ((hF z _).2 rfl), hj, one_mul]
    · intro b _ hb
      rw [map_mul, h0 z _ (fun h => hb ((hF z b).1 h).symm), zero_mul]
    · intro h
      exact absurd (hf.range_finite.mem_toFinset.2 ⟨z, rfl⟩) h

end Abs

theorem pow_eq_of_pow_mem {R : Type} [CommRing R] {l n : ℕ} (hl : l.Prime) (hn : (l : R) ^ n = 0) {a b : R}
    (h : (a - b) ^ l ∈ Ideal.span {(l : R)}) : a ^ l ^ n = b ^ l ^ n := by
  cases n with
  | zero =>
    have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hn.symm)
    exact Subsingleton.elim _ _
  | succ m =>
    have h1 : (l : R) ∣ a ^ l - b ^ l := by
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (a - b) b
      rw [sub_add_cancel] at hr
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h
      exact ⟨c + (a - b) * b * r, by rw [hr, hc]; ring⟩
    have h2 := dvd_sub_pow_of_dvd_sub h1 m
    rw [hn, zero_dvd_iff, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
    exact sub_eq_zero.1 h2

section Gen

variable {l : ℕ} [Fact l.Prime]

theorem witt_mem (D : PAlg l) (S : Subring D.W) (h2 : ∀ g, WittVector.teichmuller l g ∈ S) (k : ℕ) (w : D.W) :
    ∃ t ∈ S, ∃ r, w = t + (l : D.W) ^ k * r := by
  induction k with
  | zero => exact ⟨0, S.zero_mem, w, by simp⟩
  | succ k ih =>
    obtain ⟨t, ht, r, rfl⟩ := ih
    have h0 : r - WittVector.teichmuller l (r.coeff 0) ∈ Ideal.span {(l : D.W)} := by
      rw [D.mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h0
    refine ⟨t + (l : D.W) ^ k * WittVector.teichmuller l (r.coeff 0),
      S.add_mem ht (S.mul_mem (S.pow_mem (natCast_mem S l) k) (h2 _)), c, ?_⟩
    linear_combination ((l : D.W) ^ k) * hc

theorem acr_top (D : PAlg l) (n : ℕ) (S : Subring (D.Acr n)) (h1 : ∀ a, D.cris n a ∈ S)
    (h2 : ∀ g, D.toAcr n (WittVector.teichmuller l g) ∈ S) (x : D.Acr n) : x ∈ S := by
  have hW : ∀ w : D.W, D.toAcr n w ∈ S := fun w => by
    obtain ⟨t, ht, r, rfl⟩ := witt_mem D (S.comap (D.toAcr n)) h2 n w
    rw [map_add, map_mul, map_pow, map_natCast, D.pow_l_acr, zero_mul, add_zero]
    exact ht
  obtain ⟨z, rfl⟩ := (RL.tens D n).1 x
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact S.zero_mem
  | tmul a w =>
    rw [Algebra.TensorProduct.lift_tmul]
    exact S.mul_mem (h1 a) (hW w)
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb

variable {A D : PAlg l} {Γ : Type} [TopologicalSpace Γ]

def EE (ind : Clopens Γ → D.A) (n : ℕ) (V : Clopens Γ) : D.Acr n := D.toAcr n (WittVector.teichmuller l (ind V))

theorem EE_compl (e : Γ → (D ⟶ A)) (ind : Clopens Γ → D.A)
    (hinj : ∀ a b : D.A, (∀ z, Hom.f (e z) a = Hom.f (e z) b) → a = b)
    (h1 : ∀ z V, z ∈ V → Hom.f (e z) (ind V) = 1) (h0 : ∀ z V, z ∉ V → Hom.f (e z) (ind V) = 0) (n : ℕ)
    (V : Clopens Γ) : EE ind n V + EE ind n Vᶜ = 1 := by
  have key : WittVector.teichmuller l (ind V) + WittVector.teichmuller l (ind Vᶜ) = (1 : D.W) := by
    ext i
    refine hinj _ _ fun z => ?_
    rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_add, map_one, WittVector.map_teichmuller,
      WittVector.map_teichmuller]
    congr 1
    by_cases hz : z ∈ V
    · have hz' : z ∉ Vᶜ := fun h => by
        rw [← SetLike.mem_coe, Clopens.coe_compl] at h
        exact h hz
      rw [h1 z V hz, h0 z _ hz', map_one, WittVector.teichmuller_zero, add_zero]
    · have hz' : z ∈ Vᶜ := by
        rw [← SetLike.mem_coe, Clopens.coe_compl]
        exact hz
      rw [h0 z V hz, h1 z _ hz', map_one, WittVector.teichmuller_zero, zero_add]
  rw [EE, EE, ← map_add, key, map_one]

theorem simple_all (j : A ⟶ D) (e : Γ → (D ⟶ A)) (ind : Clopens Γ → D.A)
    (hmul : ∀ V W, ind (V ⊓ W) = ind V * ind W)
    (hloc : ∀ (h : D.A) z, ∃ V : Clopens Γ, z ∈ V ∧ ind V * (h - Hom.f j (Hom.f (e z) h)) ∈ Ideal.span {D.pi})
    (n : ℕ) (x : D.Acr n) : Simple (mapAcr j n) (fun z => mapAcr (e z) n) (EE ind n) x := by
  have hEmul : ∀ V W, EE ind n (V ⊓ W) = EE ind n V * EE ind n W := fun V W => by
    rw [EE, EE, EE, hmul, map_mul, map_mul]
  have hp := (Fact.out : l.Prime)
  refine acr_top D n (simpleRing _ _ _ hEmul) (fun a z => ⟨⊤, trivial, ?_⟩) (fun g z => ?_) x
  · rw [mapAcr_cris, mapAcr_cris]
  · obtain ⟨π, hπ, -, hπ0, -⟩ := (GlobalTheory.CompanionTheory.AcrMod.acr_modp D n).1
    have hpow := (GlobalTheory.CompanionTheory.AcrMod.acr_modp D n).2.2.2.2.2.1
    have hperf : Function.Surjective fun y : D.A => y ^ l ^ n := (PerfectRing.pow D.A l n).bijective_frobenius.2
    obtain ⟨h, rfl⟩ := hperf g
    obtain ⟨V, hV, hm⟩ := hloc h z
    set c : D.A := Hom.f j (Hom.f (e z) h) with hc
    have hdiff : D.toAcr n (WittVector.teichmuller l (ind V * h)) - D.toAcr n (WittVector.teichmuller l (ind V * c))
        ∈ D.PFil n := by
      rw [← Ideal.Quotient.eq, ← hπ, ← hπ]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hm
      rw [← sub_eq_zero, ← map_sub, ← mul_sub, ← hy, map_mul, hπ0, mul_zero]
    have hfin := pow_eq_of_pow_mem hp (D.pow_l_acr n) (hpow _ hdiff).2
    have hidem : EE ind n V ^ l ^ n = EE ind n V := by
      have hi : IsIdempotentElem (EE ind n V) := by
        have := hEmul V V
        rw [inf_idem] at this
        exact this.symm
      exact hi.pow_eq (pow_ne_zero _ hp.ne_zero)
    refine ⟨V, hV, ?_⟩
    have hval : mapAcr j n (mapAcr (e z) n (D.toAcr n (WittVector.teichmuller l (h ^ l ^ n))))
        = D.toAcr n (WittVector.teichmuller l c) ^ l ^ n := by
      rw [mapAcr_toAcr, mapAcr_toAcr, mapW, mapW, WittVector.map_teichmuller, WittVector.map_teichmuller, map_pow,
        map_pow, map_pow, map_pow]
    change _ * _ = _ * mapAcr j n (mapAcr (e z) n _)
    rw [hval]
    simp only [map_mul, mul_pow] at hfin
    rw [map_pow, map_pow]
    change (EE ind n V) ^ l ^ n * _ = (EE ind n V) ^ l ^ n * _ at hfin
    rwa [hidem] at hfin

end Gen

section Main

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) {Γ : Type} [TopologicalSpace Γ]

def ind (V : Clopens Γ) : A.contR Γ :=
  ⟨Set.indicator (V : Set Γ) 1, fun k => by
    have h : IsLocallyConstant (Set.indicator (V : Set Γ) (1 : Γ → A.A)) := by
      rw [← LocallyConstant.coe_charFn A.A V.isClopen]
      exact LocallyConstant.isLocallyConstant _
    exact h.comp (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}))⟩

theorem ind_mem (V : Clopens Γ) {z : Γ} (h : z ∈ V) : (ind A V).1 z = 1 :=
  Set.indicator_of_mem (s := (V : Set Γ)) h _

theorem ind_not_mem (V : Clopens Γ) {z : Γ} (h : z ∉ V) : (ind A V).1 z = 0 :=
  Set.indicator_of_notMem (s := (V : Set Γ)) h _

theorem ind_mul (V W : Clopens Γ) : ind A (V ⊓ W) = ind A V * ind A W := by
  refine Subtype.ext (funext fun z => ?_)
  change (ind A (V ⊓ W)).1 z = (ind A V).1 z * (ind A W).1 z
  by_cases hV : z ∈ V
  · by_cases hW : z ∈ W
    · rw [ind_mem A _ (show z ∈ V ⊓ W from ⟨hV, hW⟩), ind_mem A V hV, ind_mem A W hW, one_mul]
    · rw [ind_not_mem A _ (show z ∉ V ⊓ W from fun h => hW h.2), ind_not_mem A W hW, mul_zero]
  · rw [ind_not_mem A _ (show z ∉ V ⊓ W from fun h => hV h.1), ind_not_mem A V hV, zero_mul]

theorem ind_top : ind A (⊤ : Clopens Γ) = 1 :=
  Subtype.ext (funext fun z => ind_mem A ⊤ (show z ∈ (⊤ : Clopens Γ) from trivial))

theorem ind_bot : ind A (⊥ : Clopens Γ) = 0 :=
  Subtype.ext (funext fun z => ind_not_mem A ⊥ (show z ∉ (⊥ : Clopens Γ) from fun h => h))

theorem ind_loc (h : A.contR Γ) (z : Γ) :
    ∃ V : Clopens Γ, z ∈ V ∧ ind A V * (h - A.contC Γ (h.1 z)) ∈ Ideal.span {A.contC Γ A.pi} := by
  have hl := h.2 1
  let V : Clopens Γ := ⟨_, hl.isClopen_fiber (Ideal.Quotient.mk _ (h.1 z))⟩
  refine ⟨V, rfl, ?_⟩
  have key := ((RL.cont_ex A Γ).2.2.2 1 (ind A V * (h - A.contC Γ (h.1 z)))).2
  rw [show A.contC Γ A.pi ^ 1 = A.contC Γ A.pi from pow_one _] at key
  refine key fun γ => ?_
  change (ind A V).1 γ * (h.1 γ - h.1 z) ∈ _
  by_cases hγ : γ ∈ V
  · rw [ind_mem A V hγ, one_mul]
    exact Ideal.Quotient.eq.1 hγ
  · rw [ind_not_mem A V hγ, zero_mul]
    exact zero_mem _

theorem toCont_evCont (z : Γ) : A.toCont Γ ≫ A.evCont z = 𝟙 A := Hom.ext (RingHom.ext fun _ => rfl)

end Main

theorem acr_cont : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∀ x : (A.cont ℤ_[l]).Acr n, IsLocallyConstant fun z => mapAcr (A.evCont z) n x) ∧ (∀ x : (A.cont ℤ_[l]).Acr n, (∀ z, mapAcr (A.evCont z) n x = 0) → x = 0) ∧ ∀ (𝔞 : Ideal ((base l).Acr n)) (f : ℤ_[l] → A.Acr n), IsLocallyConstant f → (∀ z, f z ∈ 𝔞.map (mapAcr A.fromBase n)) → ∃ x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), ∀ z, mapAcr (A.evCont z) n x = f z := by
  intro l _ A n
  have hinj : ∀ a b : (A.cont ℤ_[l]).A, (∀ z, Hom.f (A.evCont z) a = Hom.f (A.evCont z) b) → a = b :=
    fun a b h => Subtype.ext (funext h)
  have h1 : ∀ z (V : Clopens ℤ_[l]), z ∈ V → Hom.f (A.evCont z) (ind A V) = 1 := fun z V h => ind_mem A V h
  have h0 : ∀ z (V : Clopens ℤ_[l]), z ∉ V → Hom.f (A.evCont z) (ind A V) = 0 := fun z V h => ind_not_mem A V h
  have hS := simple_all (A.toCont ℤ_[l]) (fun z => A.evCont z) (ind A) (ind_mul A) (ind_loc A) n
  have hj : ∀ z (b : A.Acr n), mapAcr (A.evCont z) n (mapAcr (A.toCont ℤ_[l]) n b) = b := fun z b => by
    rw [← mapAcr_comp, toCont_evCont, mapAcr_id]
  have hE1 : ∀ z (V : Clopens ℤ_[l]), z ∈ V → mapAcr (A.evCont z) n (EE (ind A) n V) = 1 := fun z V h => by
    rw [EE, mapAcr_toAcr, mapW, WittVector.map_teichmuller, h1 z V h, map_one, map_one]
  have hEmul : ∀ V W : Clopens ℤ_[l], EE (D := A.cont ℤ_[l]) (ind A) n (V ⊓ W) = EE (ind A) n V * EE (ind A) n W :=
    fun V W => by rw [EE, EE, EE, ind_mul, map_mul, map_mul]
  have hEtop : EE (D := A.cont ℤ_[l]) (ind A) n ⊤ = 1 := by rw [EE, ind_top, map_one, map_one]
  have hEbot : EE (D := A.cont ℤ_[l]) (ind A) n ⊥ = 0 := by rw [EE, ind_bot, WittVector.teichmuller_zero, map_zero]
  have hEc := EE_compl (fun z => A.evCont z) (ind A) hinj h1 h0 n
  refine ⟨fun x => lc_of_simple hj hE1 (hS x), fun x hx => zero_of_simple hEmul hEtop hEbot hEc (hS x) hx,
    fun 𝔞 f hf hI => exists_of_lc hEc hj hE1 _ f hf fun z => ?_⟩
  have hcomp : (mapAcr (A.toCont ℤ_[l]) n).comp (mapAcr A.fromBase n) = mapAcr (A.cont ℤ_[l]).fromBase n := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, ← mapAcr_comp, fromBase_comp]
  rw [← hcomp, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ (hI z)

end GlobalTheory.CompanionTheory.ContAcr
