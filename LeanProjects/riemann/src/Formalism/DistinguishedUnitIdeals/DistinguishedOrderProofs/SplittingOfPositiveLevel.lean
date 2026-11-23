import Mathlib
import Formalism.DistinguishedUnitIdeals.StatementE

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace S1

section base
variable {O : Type} [CommRing O] (B : Base O)

theorem lc_eq : B.lc = ((B.ℓ : ℕ) : PowerSeries O) := by
  simp [Base.lc]

theorem phi_lc (k : ℕ) : B.φ (B.lc ^ k) = B.lc ^ k := by
  rw [lc_eq]; simp

theorem gam_lc (k : ℕ) : B.γ (B.lc ^ k) = B.lc ^ k := by
  rw [lc_eq]; simp

theorem phiIter_lc (s k : ℕ) : (⇑B.φ)^[s] (B.lc ^ k) = B.lc ^ k :=
  Function.iterate_fixed (phi_lc B k) s

end base

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

theorem mem_sm {a : PowerSeries O} {S : Submodule (PowerSeries O) V} {v : V} :
    v ∈ sm a S ↔ ∃ u ∈ S, a • u = v := by
  simp [sm, Submodule.mem_map]

theorem sm_le (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : sm a S ≤ S := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  exact S.smul_mem a hu

theorem sm_pow_le_X {M : ℕ} (hM : 1 ≤ M) (S : Submodule (PowerSeries O) V) :
    sm (X ^ M) S ≤ sm X S := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  refine mem_sm.2 ⟨X ^ (M - 1) • u, S.smul_mem _ hu, ?_⟩
  rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hM]

variable (L : Lat B n V)

theorem phiIt_succ (i : ZMod n) (k : ℕ) (v : V) :
    L.phiIt i (k + 1) v = L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v) := rfl

theorem phiIt_add (i : ZMod n) (k : ℕ) (u v : V) :
    L.phiIt i k (u + v) = L.phiIt i k u + L.phiIt i k v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiIt_succ, ih, map_add]; rfl

theorem phiIt_map_zero (i : ZMod n) (k : ℕ) : L.phiIt i k (0 : V) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiIt_succ, ih, map_zero]

def phiHom (i : ZMod n) (k : ℕ) : V →+ V where
  toFun := L.phiIt i k
  map_zero' := phiIt_map_zero L i k
  map_add' := phiIt_add L i k

theorem phiIt_sub (i : ZMod n) (k : ℕ) (u v : V) :
    L.phiIt i k (u - v) = L.phiIt i k u - L.phiIt i k v := map_sub (phiHom L i k) u v

theorem phiIt_neg (i : ZMod n) (k : ℕ) (u : V) :
    L.phiIt i k (-u) = -L.phiIt i k u := map_neg (phiHom L i k) u

theorem phiIt_smul (i : ZMod n) (k : ℕ) (a : PowerSeries O) (v : V) :
    L.phiIt i k (a • v) = ((⇑B.φ)^[k] a) • L.phiIt i k v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiIt_succ, ih, L.φ_semi, Function.iterate_succ_apply']; rfl

theorem phiIt_lc (i : ZMod n) (k s : ℕ) (v : V) :
    L.phiIt i k (B.lc ^ s • v) = B.lc ^ s • L.phiIt i k v := by
  rw [phiIt_smul, phiIter_lc]

theorem phi_lc_smul (i : ZMod n) (s : ℕ) (v : V) :
    L.φ i (B.lc ^ s • v) = B.lc ^ s • L.φ i v := by
  rw [L.φ_semi, phi_lc]

theorem gam_lc_smul (i : ZMod n) (s : ℕ) (v : V) :
    L.γ i (B.lc ^ s • v) = B.lc ^ s • L.γ i v := by
  rw [L.γ_semi, gam_lc]

theorem phiIt_comp (i i' : ZMod n) (a b : ℕ) (h : i' = i + (a : ZMod n)) (v : V) :
    L.phiIt i' b (L.phiIt i a v) = L.phiIt i (a + b) v := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have e : i' + ((b + 1 : ℕ) : ZMod n) = i + ((a + b + 1 : ℕ) : ZMod n) := by
      subst h; push_cast; ring
    rw [phiIt_succ, ih, ← add_assoc, phiIt_succ, e]

theorem gam_phiIt (i i' : ZMod n) (k : ℕ) (h : i' = i + (k : ZMod n)) (v : V) :
    L.γ i' (L.phiIt i k v) = L.phiIt i k (L.γ i v) := by
  induction k generalizing i' with
  | zero => subst h; simp [Lat.phiIt]
  | succ k ih =>
    subst h
    have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    rw [phiIt_succ, phiIt_succ, ← ih (i + (k : ZMod n)) rfl, ← e, L.comm]

theorem phiIt_pull (c i' : ZMod n) (a b : ℕ) (h : i' = c + (a : ZMod n)) {v : V}
    (hv : v ∈ L.pull c a) : L.phiIt i' b v ∈ L.pull c (a + b) := by
  unfold Lat.pull at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [phiIt_comp L c i' a b h]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  | zero => rw [phiIt_map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [phiIt_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [phiIt_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_pull (c : ZMod n) (k : ℕ) {u : V} (hu : u ∈ L.N c) : L.phiIt c k u ∈ L.pull c k :=
  Submodule.subset_span ⟨u, hu, rfl⟩

theorem gam_N (h1 : ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i)) (i : ZMod n) {v : V}
    (hv : v ∈ L.N i) : L.γ i v ∈ L.N i := by
  have := (L.N i).add_mem (sm_le _ _ (h1 i v hv)) hv
  simpa using this

theorem gam_pull (h1 : ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i)) (c : ZMod n) (k : ℕ) {v : V}
    (hv : v ∈ L.pull c k) : L.γ (c + (k : ZMod n)) v ∈ L.pull c k := by
  unfold Lat.pull at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rw [gam_phiIt L c _ k rfl]
    exact mem_pull L c k (gam_N L h1 c hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [L.γ_semi]; exact Submodule.smul_mem _ _ hx

theorem gam_sm_pull (h1 : ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i)) (c : ZMod n) (k : ℕ)
    {f : PowerSeries O} (hf : B.γ f ∈ Ideal.span {f}) {v : V} (hv : v ∈ sm f (L.pull c k)) :
    L.γ (c + (k : ZMod n)) v ∈ sm f (L.pull c k) := by
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hf
  refine mem_sm.2 ⟨a • L.γ (c + (k : ZMod n)) u, Submodule.smul_mem _ _ (gam_pull L h1 c k hu), ?_⟩
  rw [L.γ_semi, ← ha, smul_smul, mul_comm]

theorem phiIt_XM (c : ZMod n) (j M : ℕ) {f : PowerSeries O}
    (hf : ((⇑B.φ)^[j] X) ^ M ∈ Ideal.span {f}) {v : V} (hv : v ∈ sm (X ^ M) (L.N c)) :
    L.phiIt c j v ∈ sm f (L.pull c j) := by
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hf
  refine mem_sm.2 ⟨a • L.phiIt c j u, Submodule.smul_mem _ _ (mem_pull L c j hu), ?_⟩
  rw [phiIt_smul, iterate_map_pow, ← ha, smul_smul, mul_comm]

theorem phiIt_stable {M : ℕ}
    (h2 : ∀ i, ∀ v ∈ sm (X ^ M) (L.N (i - 1)), L.φ i v ∈ sm (X ^ M) (L.N i))
    (i i' : ZMod n) (k : ℕ) (h : i' = i + (k : ZMod n)) {v : V} (hv : v ∈ sm (X ^ M) (L.N i)) :
    L.phiIt i k v ∈ sm (X ^ M) (L.N i') := by
  induction k generalizing i' with
  | zero => subst h; simpa [Lat.phiIt] using hv
  | succ k ih =>
    subst h
    rw [phiIt_succ]
    apply h2
    apply ih
    push_cast; ring

theorem gamR_mem {Cu : Cuts n} {j M g sig : ℕ} (hB : B.Good j M g) (hL : L.Good Cu j M g sig)
    {c : ZMod n} (hc : c ∈ Cu.cuts) {z τ : V} (hz : z ∈ sm X (L.N c))
    (hτ : L.IsTr c j M g sig z τ) :
    B.lc ^ sig • L.phiIt c j z - (L.γ (c + (j : ZMod n)) τ - τ)
      ∈ sm (X ^ M) (L.N (c + (j : ZMod n))) := by
  obtain ⟨h1, -, -, h4, -, -, h7, -⟩ := hL
  obtain ⟨-, hB2, hB3⟩ := hB
  obtain ⟨hτP, K, v, hv, e1, e2⟩ := hτ
  apply h4 c hc
  apply h7 c hc K
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mem_pull L c j (sm_le _ _ hz)))
      (Submodule.sub_mem _ (gam_pull L h1 c j hτP) hτP)
  · have key : B.lc ^ K • (B.lc ^ sig • L.phiIt c j z - (L.γ (c + (j : ZMod n)) τ - τ))
        = -(B.lc ^ sig • L.phiIt c j ((L.γ c v - v) - B.lc ^ K • z))
          - (L.γ (c + (j : ZMod n)) (B.lc ^ K • τ - B.lc ^ sig • L.phiIt c j v)
              - (B.lc ^ K • τ - B.lc ^ sig • L.phiIt c j v)) := by
      rw [phiIt_sub, phiIt_sub, phiIt_lc, map_sub, gam_lc_smul, gam_lc_smul,
        gam_phiIt L c _ j rfl]
      simp only [smul_sub, smul_smul, mul_comm (B.lc ^ K) (B.lc ^ sig)]
      abel
    rw [key]
    exact Submodule.sub_mem _
      (Submodule.neg_mem _ (Submodule.smul_mem _ _ (phiIt_XM L c j M hB3 e1)))
      (Submodule.sub_mem _ (gam_sm_pull L h1 c j hB2 e2) e2)

end lat

section hom
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V V' : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] [AddCommGroup V'] [Module (PowerSeries O) V']
  {L : Lat B n V} {L' : Lat B n V'} (h : LatHom L L')

theorem hom_phiIt (i : ZMod n) (k : ℕ) (v : V) : h.f (L.phiIt i k v) = L'.phiIt i k (h.f v) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiIt_succ, h.φ_comm, ih]; rfl

theorem hom_pull (c : ZMod n) (k : ℕ) {v : V} (hv : v ∈ L.pull c k) : h.f v ∈ L'.pull c k := by
  have : L.pull c k ≤ (L'.pull c k).comap h.f := by
    apply Submodule.span_le.2
    rintro _ ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hom_phiIt]
    exact mem_pull L' c k (h.map_N _ _ hu)
  exact this hv

end hom

section cuts
variable {n : ℕ} [NeZero n] (Cu : Cuts n)

theorem ex_back (i : ZMod n) : ∃ k : ℕ, i - (k : ZMod n) ∈ Cu.cuts := by
  obtain ⟨c, hc⟩ := Cu.nonempty
  refine ⟨(i - c).val, ?_⟩
  rw [ZMod.natCast_zmod_val]
  simpa using hc

def back (i : ZMod n) : ℕ := Nat.find (ex_back Cu i)

theorem back_spec (i : ZMod n) : i - (back Cu i : ZMod n) ∈ Cu.cuts := Nat.find_spec (ex_back Cu i)

theorem back_min (i : ZMod n) {k : ℕ} (hk : k < back Cu i) : i - (k : ZMod n) ∉ Cu.cuts :=
  Nat.find_min (ex_back Cu i) hk

theorem back_eq (i : ZMod n) (k : ℕ) (h : i - (k : ZMod n) ∈ Cu.cuts)
    (hm : ∀ m < k, i - (m : ZMod n) ∉ Cu.cuts) : back Cu i = k :=
  (Nat.find_eq_iff (ex_back Cu i)).2 ⟨h, hm⟩

theorem back_cut {c : ZMod n} (hc : c ∈ Cu.cuts) : back Cu c = 0 :=
  back_eq Cu c 0 (by simpa using hc) (by simp)

theorem back_succ {i : ZMod n} (hi : i ∉ Cu.cuts) : back Cu i = back Cu (i - 1) + 1 := by
  apply back_eq
  · have := back_spec Cu (i - 1)
    have e : i - ((back Cu (i - 1) + 1 : ℕ) : ZMod n) = i - 1 - (back Cu (i - 1) : ZMod n) := by
      push_cast; ring
    rwa [e]
  · intro m hm
    rcases m with _ | m
    · simpa using hi
    · have := back_min Cu (i - 1) (k := m) (by omega)
      have e : i - ((m + 1 : ℕ) : ZMod n) = i - 1 - (m : ZMod n) := by push_cast; ring
      rwa [e]

theorem back_prev {c : ZMod n} (hc : c ∈ Cu.cuts) : back Cu (c - 1) + 1 = Cu.ell c := by
  have h1 := Cu.ell_pos c hc
  obtain ⟨b, hb⟩ : ∃ b, Cu.ell c = b + 1 := ⟨Cu.ell c - 1, by omega⟩
  have : back Cu (c - 1) = b := by
    apply back_eq
    · have := Cu.prev_mem c hc
      rw [hb] at this
      have e : c - ((b + 1 : ℕ) : ZMod n) = c - 1 - (b : ZMod n) := by push_cast; ring
      rwa [e] at this
    · intro m hm
      have := Cu.no_inner c hc (m + 1) (by omega) (by omega)
      have e : c - ((m + 1 : ℕ) : ZMod n) = c - 1 - (m : ZMod n) := by push_cast; ring
      rwa [e] at this
  omega

variable {O : Type} [CommRing O] {B : Base O} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V) (j : ℕ) (R : ZMod n → V)

def Efun (i : ZMod n) : V :=
  L.phiIt (i - j - back Cu (i - j) + j) (back Cu (i - j)) (R (i - j - back Cu (i - j)))

theorem Efun_cut {c : ZMod n} (hc : c ∈ Cu.cuts) : Efun Cu L j R (c + j) = R c := by
  unfold Efun
  have e : c + (j : ZMod n) - j = c := by ring
  rw [e, back_cut Cu hc]
  simp [Lat.phiIt]

theorem Efun_step {i : ZMod n} (hi : i - (j : ZMod n) ∉ Cu.cuts) :
    Efun Cu L j R i = L.φ i (Efun Cu L j R (i - 1)) := by
  unfold Efun
  have e : i - 1 - (j : ZMod n) = i - j - 1 := by ring
  rw [e, back_succ Cu hi]
  generalize back Cu (i - j - 1) = b
  have a : i - (j : ZMod n) - ((b + 1 : ℕ) : ZMod n) = i - j - 1 - b := by push_cast; ring
  rw [a, phiIt_succ]
  have a' : i - (j : ZMod n) - 1 - b + j + ((b + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  rw [a']

theorem Efun_prev {c : ZMod n} (hc : c ∈ Cu.cuts) :
    L.φ (c + j) (Efun Cu L j R (c + j - 1))
      = L.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c) (R (c - (Cu.ell c : ZMod n))) := by
  unfold Efun
  have e : c + (j : ZMod n) - 1 - j = c - 1 := by ring
  rw [e, ← back_prev Cu hc]
  generalize back Cu (c - 1) = b
  have a : c - ((b + 1 : ℕ) : ZMod n) = c - 1 - b := by push_cast; ring
  rw [a, phiIt_succ]
  have a' : c - 1 - (b : ZMod n) + j + ((b + 1 : ℕ) : ZMod n) = c + j := by push_cast; ring
  rw [a']

theorem Efun_idx (i : ZMod n) :
    i = i - j - back Cu (i - j) + j + (back Cu (i - j) : ZMod n) := by ring

theorem Efun_gam (i : ZMod n) :
    L.γ i (Efun Cu L j R i) = Efun Cu L j (fun c => L.γ (c + j) (R c)) i :=
  gam_phiIt L _ i _ (Efun_idx Cu j i) _

theorem Efun_sub (R' : ZMod n → V) (i : ZMod n) :
    Efun Cu L j (fun c => R c - R' c) i = Efun Cu L j R i - Efun Cu L j R' i :=
  phiIt_sub L _ _ _ _

theorem Efun_hom {V' : Type} [AddCommGroup V'] [Module (PowerSeries O) V'] {L' : Lat B n V'}
    (h : LatHom L L') (i : ZMod n) :
    h.f (Efun Cu L j R i) = Efun Cu L' j (fun c => h.f (R c)) i :=
  hom_phiIt h _ _ _

theorem Efun_ind (P : ZMod n → V → Prop) (h0 : ∀ c ∈ Cu.cuts, P (c + j) (R c))
    (hs : ∀ i v, P (i - 1) v → P i (L.φ i v)) (i : ZMod n) : P i (Efun Cu L j R i) := by
  have gen : ∀ (k : ℕ) (a a' : ZMod n) (v : V), a' = a + (k : ZMod n) → P a v →
      P a' (L.phiIt a k v) := by
    intro k
    induction k with
    | zero => intro a a' v h hv; subst h; simpa [Lat.phiIt] using hv
    | succ k ih =>
      intro a a' v h hv
      subst h
      rw [phiIt_succ]
      apply hs
      apply ih a _ v _ hv
      push_cast; ring
  exact gen _ _ _ _ (Efun_idx Cu j i) (h0 _ (back_spec Cu _))

theorem sum_single (r : ZMod n → V) (i : ZMod n) :
    (∑ c ∈ Cu.cuts, (Pi.single (c + (j : ZMod n)) (r c) : ZMod n → V)) i
      = if i - (j : ZMod n) ∈ Cu.cuts then r (i - j) else 0 := by
  rw [Finset.sum_apply]
  have : ∀ c, (Pi.single (c + (j : ZMod n)) (r c) : ZMod n → V) i
      = if i - (j : ZMod n) = c then r c else 0 := by
    intro c
    rw [Pi.single_apply]
    by_cases h : i = c + j
    · rw [if_pos h, if_pos (by rw [h]; ring)]
    · rw [if_neg h, if_neg (fun h' => h (by rw [← h']; ring))]
  simp only [this]
  exact Finset.sum_ite_eq _ _ _

end cuts

section more
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

theorem le_dv (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : S ≤ dv a S :=
  fun _ hv => S.smul_mem a hv

theorem dφ_sum {ι : Type} (s : Finset ι) (f : ι → ZMod n → V) :
    L.dφ (∑ c ∈ s, f c) = ∑ c ∈ s, L.dφ (f c) := by
  funext i
  simp only [Lat.dφ, Finset.sum_apply, map_sum, Finset.sum_sub_distrib]

theorem dγ_sum {ι : Type} (s : Finset ι) (f : ι → ZMod n → V) :
    L.dγ (∑ c ∈ s, f c) = ∑ c ∈ s, L.dγ (f c) := by
  funext i
  simp only [Lat.dγ, Finset.sum_apply, map_sum, Finset.sum_sub_distrib]

theorem phiIt_fixed {e : V} (he : ∀ i, L.φ i e = e) (i : ZMod n) (k : ℕ) : L.phiIt i k e = e := by
  induction k with
  | zero => rfl
  | succ k ih => rw [phiIt_succ, ih, he]

end more

theorem splitting_of_positive_level :
    ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (Cu : Cuts n)
    (abelian₂ : ZMod n → PowerSeries O) (j M g sig rr : ℕ)
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀) (Y : Ext L₂ L₀)
    (y₀ z₀ : ZMod n → V₂), 1 ≤ M →
    B.Good j M g → L₂.Good Cu j M g sig → (∀ c ∈ Cu.cuts, j ≤ Cu.ell c) →
    (∀ i, L₀.φ i e₀ = e₀) → (∀ i, L₀.γ i e₀ = e₀) →
    Y.Rep e₀ y₀ z₀ → Y.Good e₀ Cu abelian₂ j M g rr →
    ∃ (w : ZMod n → V₂) (yc zc : ZMod n → ZMod n → V₂),
      (∀ c ∈ Cu.cuts, L₂.Wc Cu abelian₂ c (w c) ∧ L₂.IsRho c j M g sig (w c) (yc c) (zc c)) ∧
      L₂.IsCobound (B.lc ^ (rr + 2 * sig) • y₀ - ∑ c ∈ Cu.cuts, yc c)
        (B.lc ^ (rr + 2 * sig) • z₀ - ∑ c ∈ Cu.cuts, zc c) := by
  intro O _ B n _ Cu abelian₂ j M g sig rr V₂ V₀ _ _ _ _ L₂ L₀ e₀ Y y₀ z₀ hM hB hL hj hφ0 hγ0 hRep hY
  obtain ⟨E₀, hE₀π, hE₀y, hE₀z⟩ := hRep
  obtain ⟨Ya, Yb, Yc, -, -, Yf, Yg⟩ := hY
  obtain ⟨-, h2, h3, -, h5, -, -, -⟩ := id hL
  have πι : ∀ u, Y.π.f (Y.ι.f u) = 0 := fun u => (Y.exact _).2 ⟨u, rfl⟩

  have choice : ∀ c, ∃ (x : Y.VY) (z τ : V₂), Y.ι.f z = Y.LY.γ c x - x ∧ (c ∈ Cu.cuts →
      x ∈ Y.LY.N c ∧ Y.π.f x = B.lc ^ rr • e₀ ∧ z ∈ sm X (L₂.N c) ∧
        L₂.IsTr c j M g sig z τ) := by
    intro c
    by_cases hc : c ∈ Cu.cuts
    · obtain ⟨x, hx, hxπ⟩ := Ya c hc
      have h0 : Y.π.f (Y.LY.γ c x - x) = 0 := by
        rw [map_sub, Y.π.γ_comm, hxπ, gam_lc_smul, hγ0, sub_self]
      obtain ⟨z, hz⟩ := (Y.exact _).1 h0
      have hzN : z ∈ sm X (L₂.N c) := by
        have := Yc c 1 z (by rw [hz, pow_one]; exact Yb c x hx)
        rwa [pow_one] at this
      obtain ⟨τ, hτ⟩ := h5 c hc z hzN
      exact ⟨x, z, τ, hz, fun _ => ⟨hx, hxπ, hzN, hτ⟩⟩
    · exact ⟨0, 0, 0, by simp, fun h => absurd h hc⟩
  choose x z τ hzx hdat using choice
  obtain ⟨R, hR⟩ : ∃ R : ZMod n → Y.VY,
      ∀ c, R c = B.lc ^ sig • Y.LY.phiIt c j (x c) - Y.ι.f (τ c) := ⟨_, fun _ => rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ZMod n → V₂,
      ∀ c, ξ c = B.lc ^ sig • L₂.phiIt c j (z c) - (L₂.γ (c + j) (τ c) - τ c) := ⟨_, fun _ => rfl⟩
  have hιξ : ∀ c, Y.ι.f (ξ c) = Y.LY.γ (c + j) (R c) - R c := by
    intro c
    rw [hR, hξ]
    simp only [map_sub, map_smul, hom_phiIt, hzx, Y.ι.γ_comm, phiIt_sub, gam_lc_smul]
    rw [gam_phiIt Y.LY c _ j rfl]
    simp only [smul_sub]
    abel
  have hξM : ∀ c ∈ Cu.cuts, ξ c ∈ sm (X ^ M) (L₂.N (c + j)) := by
    intro c hc
    rw [hξ]
    exact gamR_mem L₂ hB hL hc (hdat c hc).2.2.1 (hdat c hc).2.2.2
  have hRπ : ∀ c ∈ Cu.cuts, Y.π.f (R c) = B.lc ^ (rr + sig) • e₀ := by
    intro c hc
    rw [hR, map_sub, map_smul, hom_phiIt, (hdat c hc).2.1, πι, sub_zero, phiIt_lc,
      phiIt_fixed L₀ hφ0, smul_smul, ← pow_add, add_comm]

  have hEπ : ∀ i, Y.π.f (Efun Cu Y.LY j R i) = B.lc ^ (rr + sig) • e₀ :=
    Efun_ind Cu Y.LY j R (fun _ v => Y.π.f v = B.lc ^ (rr + sig) • e₀) hRπ
      (fun i v hv => by rw [Y.π.φ_comm, hv, phi_lc_smul, hφ0])
  have hZM : ∀ i, Efun Cu L₂ j ξ i ∈ sm (X ^ M) (L₂.N i) :=
    Efun_ind Cu L₂ j ξ (fun i v => v ∈ sm (X ^ M) (L₂.N i)) hξM (fun i v hv => h2 i v hv)
  have hιZ : ∀ i, Y.ι.f (Efun Cu L₂ j ξ i)
      = Y.LY.γ i (Efun Cu Y.LY j R i) - Efun Cu Y.LY j R i := by
    intro i
    rw [Efun_hom, Efun_gam, ← Efun_sub]
    simp only [hιξ]
  have hm : ∀ i, ∃ m, Y.ι.f m = B.lc ^ (rr + sig) • E₀ i - Efun Cu Y.LY j R i := fun i =>
    (Y.exact _).1 (by rw [map_sub, map_smul, hE₀π, hEπ, sub_self])
  choose m hm using hm

  have hw : ∀ c, ∃ w, c ∈ Cu.cuts → Y.ι.f w
      = Y.LY.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j) (R (c - (Cu.ell c : ZMod n)))
        - B.lc ^ sig • x c := by
    intro c
    by_cases hc : c ∈ Cu.cuts
    · have h0 : Y.π.f (Y.LY.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j)
          (R (c - (Cu.ell c : ZMod n))) - B.lc ^ sig • x c) = 0 := by
        rw [map_sub, hom_phiIt, hRπ _ (Cu.prev_mem c hc), phiIt_lc, phiIt_fixed L₀ hφ0, map_smul,
          (hdat c hc).2.1, smul_smul, ← pow_add, add_comm sig rr, sub_self]
      obtain ⟨w, hw⟩ := (Y.exact _).1 h0
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose w hw using hw
  have idx : ∀ c ∈ Cu.cuts,
      c = c - (Cu.ell c : ZMod n) + j + ((Cu.ell c - j : ℕ) : ZMod n) := by
    intro c hc
    rw [Nat.cast_sub (hj c hc)]; ring
  have hγw : ∀ c ∈ Cu.cuts, L₂.γ c (w c) - w c
      = L₂.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j) (ξ (c - (Cu.ell c : ZMod n)))
        - B.lc ^ sig • z c := by
    intro c hc
    apply Y.ι_inj
    simp only [map_sub, map_smul, Y.ι.γ_comm, hw c hc, hom_phiIt, hιξ, phiIt_sub, hzx,
      gam_lc_smul]
    rw [gam_phiIt Y.LY _ c _ (idx c hc)]
    simp only [smul_sub]
    abel
  have hφξ : ∀ c ∈ Cu.cuts,
      L₂.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j) (ξ (c - (Cu.ell c : ZMod n)))
        ∈ sm (X ^ M) (L₂.N c) := fun c hc =>
    phiIt_stable L₂ h2 _ c _ (idx c hc) (hξM _ (Cu.prev_mem c hc))
  obtain ⟨r, hr⟩ : ∃ r : ZMod n → V₂,
      ∀ c, r c = B.lc ^ sig • L₂.phiIt c j (w c) - (-(B.lc ^ sig • τ c)) := ⟨_, fun _ => rfl⟩
  have hYid : ∀ i, Y.ι.f ((∑ c ∈ Cu.cuts, (Pi.single (c + (j : ZMod n)) (r c) : ZMod n → V₂)) i)
      = B.lc ^ sig • Y.LY.dφ (Efun Cu Y.LY j R) i := by
    intro i
    rw [sum_single]
    by_cases hi : i - (j : ZMod n) ∈ Cu.cuts
    · rw [if_pos hi]
      obtain ⟨c, rfl⟩ : ∃ c, i = c + (j : ZMod n) := ⟨i - j, by ring⟩
      have e : c + (j : ZMod n) - j = c := by ring
      rw [e] at hi ⊢
      have comp : Y.LY.phiIt c j (Y.LY.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j)
          (R (c - (Cu.ell c : ZMod n))))
          = Y.LY.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c) (R (c - (Cu.ell c : ZMod n))) := by
        rw [phiIt_comp Y.LY _ c _ _ (idx c hi), Nat.sub_add_cancel (hj c hi)]
      unfold Lat.dφ
      rw [Efun_prev Cu Y.LY j R hi, Efun_cut Cu Y.LY j R hi, hr, hR c]
      simp only [map_sub, map_neg, map_smul, hom_phiIt, hw c hi, phiIt_sub, phiIt_lc, comp]
      simp only [smul_sub]
      abel
    · rw [if_neg hi, map_zero]
      unfold Lat.dφ
      rw [← Efun_step Cu Y.LY j R hi, sub_self, smul_zero]
  have hcoc : ∀ i, L₂.dγ (∑ c ∈ Cu.cuts, (Pi.single (c + (j : ZMod n)) (r c) : ZMod n → V₂)) i
      = B.lc ^ sig • L₂.dφ (Efun Cu L₂ j ξ) i := by
    intro i
    apply Y.ι_inj
    unfold Lat.dγ Lat.dφ
    rw [map_sub, Y.ι.γ_comm, hYid, gam_lc_smul, LinearMap.map_smul, map_sub, Y.ι.φ_comm, hιZ, hιZ]
    unfold Lat.dφ
    rw [map_sub, map_sub, Y.LY.comm]
    simp only [smul_sub]
    abel
  have htM : ∀ i, B.lc ^ sig • L₂.dφ (Efun Cu L₂ j ξ) i ∈ sm (X ^ M) (L₂.N i) := fun i =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (h2 i _ (hZM (i - 1))) (hZM i))
  have hzc : ∀ c, ∃ zc : ZMod n → V₂, c ∈ Cu.cuts → (∀ i, zc i ∈ sm (X ^ M) (L₂.N i)) ∧
      L₂.dφ zc = L₂.dγ (Pi.single (c + (j : ZMod n)) (r c)) := by
    intro c
    by_cases hc : c ∈ Cu.cuts
    · obtain ⟨zc, hzc, -⟩ := h3 (L₂.dγ (Pi.single (c + (j : ZMod n)) (r c))) (by
        intro i
        by_cases hi : i = c + (j : ZMod n)
        · have := htM i
          rw [← hcoc] at this
          unfold Lat.dγ at this ⊢
          rw [sum_single] at this
          subst hi
          have e : c + (j : ZMod n) - j = c := by ring
          rw [e, if_pos hc] at this
          rwa [Pi.single_eq_same]
        · unfold Lat.dγ
          rw [Pi.single_eq_of_ne hi, map_zero, sub_zero]
          exact Submodule.zero_mem _)
      exact ⟨zc, fun _ => hzc⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose zc hzc using hzc
  have hsum : ∑ c ∈ Cu.cuts, zc c = B.lc ^ sig • Efun Cu L₂ j ξ := by
    apply (h3 _ htM).unique
    · refine ⟨fun i => ?_, ?_⟩
      · rw [Finset.sum_apply]
        exact Submodule.sum_mem _ (fun c hc => (hzc c hc).1 i)
      · rw [dφ_sum, Finset.sum_congr rfl (fun c hc => (hzc c hc).2), ← dγ_sum]
        funext i
        exact hcoc i
    · refine ⟨fun i => Submodule.smul_mem _ _ (hZM i), ?_⟩
      funext i
      simp only [Lat.dφ, Pi.smul_apply, phi_lc_smul, smul_sub]
  have hpow : B.lc ^ (rr + 2 * sig) = B.lc ^ sig * B.lc ^ (rr + sig) := by
    rw [← pow_add]; congr 1; ring
  refine ⟨w, fun c => Pi.single (c + (j : ZMod n)) (r c), zc, ?_, B.lc ^ sig • m, ?_, ?_⟩
  · intro c hc
    obtain ⟨hx, -, hz, hτP, K, v, hv, e1, e2⟩ := hdat c hc
    have hc' := Cu.prev_mem c hc
    refine ⟨⟨?_, ?_⟩, -(B.lc ^ sig • τ c), ⟨?_, K, -(B.lc ^ sig • v), ?_, ?_, ?_⟩, ?_,
      ((hzc c hc).2).symm, (hzc c hc).1⟩
    · unfold Lat.Ic
      rw [hγw c hc]
      exact Submodule.sub_mem _ (sm_pow_le_X hM _ (hφξ c hc)) (Submodule.smul_mem _ _ hz)
    · apply Yg c hc
      rw [hw c hc]
      refine Submodule.sub_mem _ (le_dv _ _ ?_) (Submodule.smul_mem _ _ (Yf c hc hx))
      rw [hR, phiIt_sub, phiIt_lc, phiIt_comp Y.LY _ _ j _ rfl, Nat.add_sub_cancel' (hj c hc)]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (mem_pull Y.LY _ _ (hdat _ hc').1)) ?_
      have := phiIt_pull Y.LY (c - (Cu.ell c : ZMod n)) _ j (Cu.ell c - j) rfl
        (hom_pull Y.ι _ j (hdat _ hc').2.2.2.1)
      rwa [Nat.add_sub_cancel' (hj c hc)] at this
    · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hτP)
    · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hv)
    · rw [hγw c hc]
      have e : L₂.γ c (-(B.lc ^ sig • v)) - -(B.lc ^ sig • v) - B.lc ^ K •
          (L₂.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j) (ξ (c - (Cu.ell c : ZMod n)))
            - B.lc ^ sig • z c)
          = -(B.lc ^ sig • ((L₂.γ c v - v) - B.lc ^ K • z c)) - B.lc ^ K •
            L₂.phiIt (c - (Cu.ell c : ZMod n) + j) (Cu.ell c - j)
              (ξ (c - (Cu.ell c : ZMod n))) := by
        rw [map_neg, gam_lc_smul]
        simp only [smul_sub, smul_smul, mul_comm (B.lc ^ K) (B.lc ^ sig)]
        abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ e1))
        (Submodule.smul_mem _ _ (hφξ c hc))
    · have e : B.lc ^ K • -(B.lc ^ sig • τ c) - B.lc ^ sig • L₂.phiIt c j (-(B.lc ^ sig • v))
          = -(B.lc ^ sig • (B.lc ^ K • τ c - B.lc ^ sig • L₂.phiIt c j v)) := by
        rw [phiIt_neg, phiIt_lc]
        simp only [smul_sub, smul_neg, smul_smul, mul_comm (B.lc ^ K) (B.lc ^ sig)]
        abel
      rw [e]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ e2)
    · simp only [hr]
  · funext i
    apply Y.ι_inj
    rw [Pi.sub_apply, map_sub, hYid, Pi.smul_apply, map_smul, hE₀y]
    simp only [Lat.dφ, Pi.smul_apply, map_sub, map_smul, Y.ι.φ_comm, hm, phi_lc_smul, hpow,
      smul_sub, smul_smul]
    abel
  · funext i
    apply Y.ι_inj
    rw [hsum, Pi.sub_apply, map_sub, Pi.smul_apply, Pi.smul_apply, map_smul, map_smul, hE₀z, hιZ]
    simp only [Lat.dγ, Pi.smul_apply, map_sub, map_smul, Y.ι.γ_comm, hm, gam_lc_smul, hpow,
      smul_sub, smul_smul]
    abel

end S1

theorem splitting_of_extension : Step1 := S1.splitting_of_positive_level

end Formalism.ExponentWindows.E
