import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def consZero (n : ℕ) : (Fin n → R') →ₗ[R'] (Fin (n + 1) → R') where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

omit [Algebra R R'] in
@[simp] lemma consZero_zero (n : ℕ) (w : Fin n → R') : consZero n w 0 = 0 := rfl

omit [Algebra R R'] in
@[simp] lemma consZero_succ (n : ℕ) (w : Fin n → R') (j : Fin n) : consZero n w j.succ = w j := rfl

theorem scalar_descent [IsDomain R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hπ : algebraMap R R' ϖ ≠ 0)
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) :
    ∀ (a : ℕ) (x : R'), (∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ x - x) →
      ∃ c : R, (algebraMap R R' ϖ) ^ a ∣ x - algebraMap R R' c := by
  intro a
  induction a with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ a ih =>
    intro x hx
    obtain ⟨c0, hc0⟩ := hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)
    obtain ⟨t, ht⟩ := hc0
    have hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t := by rw [← ht]; ring
    have ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t := by
      intro σ hσ
      have h := hx σ hσ
      have e : σ x - x = algebraMap R R' ϖ * (σ t - t) := by
        rw [hx']; simp only [map_add, map_mul, AlgEquiv.commutes]; ring
      rw [e, pow_succ'] at h
      exact (mul_dvd_mul_iff_left hπ).mp h
    obtain ⟨c1, hc1⟩ := ih t ht'
    refine ⟨c0 + ϖ * c1, ?_⟩
    have e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1) := by
      rw [hx']; simp only [map_add, map_mul]; ring
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hc1

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

theorem main_induction [IsDomain R'] [IsDiscreteValuationRing R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hirr : Irreducible (algebraMap R R' ϖ))
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) (r : ℕ) :
    ∀ (n : ℕ) (N : Submodule R' (Fin n → R')), (∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N) →
      (∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) →
      (∀ v ∈ N, v ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}) ∧
      (∀ u : Fin n → R', (∀ σ ∈ D, (fun i => σ (u i)) - u ∈ N) →
        ∃ a : Fin n → R', (∀ i, a i ∈ Set.range (algebraMap R R')) ∧ u - a ∈ N) := by
  have hπ : algebraMap R R' ϖ ≠ 0 := hirr.ne_zero
  have hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y := by
    rintro σ y ⟨c, rfl⟩; exact AlgEquiv.commutes σ c
  intro n
  induction n with
  | zero =>
    intro N _ _
    refine ⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · have : u - 0 = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    intro N hlat hstab
    set π := algebraMap R R' ϖ with hπdef
    let L := consZero (R' := R') n
    have hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'),
        (fun i => σ (L w i)) = L (fun i => σ (w i)) := by
      intro σ w; funext i
      refine Fin.cases ?_ ?_ i <;> simp [L]
    let K := N.comap L
    have hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K := fun w => by
      show L (π ^ r • w) ∈ N
      rw [L.map_smul]; exact hlat _
    have hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K := by
      intro σ hσ w hw
      show L _ ∈ N
      rw [← hLact]; exact hstab σ hσ _ hw
    obtain ⟨hPK, hQK⟩ := ih K hKlat hKstab
    let I : Ideal R' := N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)
    have hrI : π ^ r ∈ I := ⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hrI
      exact pow_ne_zero r hπ hrI
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr
    have hmemI : ∀ v ∈ N, π ^ a ∣ v 0 := by
      intro v hv
      have : v 0 ∈ I := ⟨v, hv, rfl⟩
      rw [ha, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by
      have : π ^ a ∈ I := by rw [ha]; exact Ideal.subset_span rfl
      obtain ⟨v, hv, hv0⟩ := this
      exact ⟨v, hv, hv0⟩
    have hpa : π ^ a ∈ Set.range (algebraMap R R') := ⟨ϖ ^ a, by simp [hπdef]⟩

    have hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K := by
      intro σ hσ
      have e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hvs0, hfix σ _ hpa]
        · intro j; simp [L, Fin.tail]
      show L _ ∈ N
      rw [e]; exact N.sub_mem (hstab σ hσ _ hvsN) hvsN
    obtain ⟨a0, ha0, ha0K⟩ := hQK (Fin.tail vs) hvsK
    obtain ⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0) := ⟨_, rfl⟩
    have hvoN : vo ∈ N := hvo ▸ N.sub_mem hvsN ha0K
    have hvo0 : vo 0 = π ^ a := by rw [hvo]; simp [L, hvs0]
    have hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R') := by
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [hvo0]; exact hpa
      · intro j
        have : vo j.succ = a0 j := by rw [hvo]; simp [L, Fin.tail]
        rw [this]; exact ha0 j
    have hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') →
        x + y ∈ Set.range (algebraMap R R') := by
      rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, map_add _ _ _⟩
    have hrat0 : (0 : R') ∈ Set.range (algebraMap R R') := ⟨0, map_zero _⟩
    have hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) →
        ∀ i, L w i ∈ Set.range (algebraMap R R') := by
      intro w hw i
      refine Fin.cases ?_ ?_ i
      · simpa [L] using hrat0
      · intro j; simpa [L] using hw j
    refine ⟨?_, ?_⟩
    ·
      intro v hv
      obtain ⟨t, ht⟩ := hmemI v hv
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo) := ⟨_, rfl⟩
      have hLw : L w = v - t • vo := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, ht, hvo0]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwK : w ∈ K := by
        show L w ∈ N
        rw [hLw]; exact N.sub_mem hv (N.smul_mem t hvoN)
      have hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤
          (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L := by
        rw [Submodule.span_le]
        rintro w' ⟨hw'K, hw'r⟩
        exact Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩
      have h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        hspan (hPK w hwK)
      have h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)
      have : v = L w + t • vo := by rw [hLw]; abel
      rw [this]; exact Submodule.add_mem _ h1 h2
    ·
      intro u hu
      have h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0 := by
        intro σ hσ; simpa using hmemI _ (hu σ hσ)
      obtain ⟨c, hc⟩ := scalar_descent D ϖ hπ hres a (u 0) h0
      obtain ⟨t, ht⟩ := hc
      obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0 := ⟨_, rfl⟩
      have herat : ∀ i, e i ∈ Set.range (algebraMap R R') := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [he]; exact ⟨c, rfl⟩
        · intro j; rw [he]; simpa using hrat0
      obtain ⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail u' := ⟨_, rfl⟩
      have hLw : L w = u' := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hu', he, hvo0]; rw [ht, hπdef]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K := by
        intro σ hσ
        have key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo := by
          rw [L.map_sub, ← hLact, hLw, hu']
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
            hfix σ _ (herat i), hfix σ _ (hvorat i)]
          ring
        show L _ ∈ N
        rw [key]; exact N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)
      obtain ⟨a', ha', ha'K⟩ := hQK w hwinv
      refine ⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩
      have : u - (e + L a') = t • vo + L (w - a') := by
        rw [L.map_sub, hLw, hu']; abel
      rw [this]; exact N.add_mem (N.smul_mem t hvoN) ha'K

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

theorem stable_lattice_descent_unramified (R R' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (D : Set (R' ≃ₐ[R] R'))
    (hres : ∀ x : R', (∀ σ ∈ D, σ x - x ∈ maximalIdeal R') →
      ∃ r : R, x - algebraMap R R' r ∈ maximalIdeal R')
    (n r : ℕ) (N : Submodule R' (Fin n → R'))
    (hlat : (maximalIdeal R') ^ r • (⊤ : Submodule R' (Fin n → R')) ≤ N)
    (hstab : ∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) :
    N = Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c := by
    intro x hx
    obtain ⟨c, hc⟩ := hres x fun σ hσ => by
      rw [hmax, Ideal.mem_span_singleton]; exact hx σ hσ
    rw [hmax, Ideal.mem_span_singleton] at hc
    exact ⟨c, hc⟩
  have hmem : algebraMap R R' ϖ ∈ maximalIdeal R' := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N := fun w =>
    hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)
  obtain ⟨hP, -⟩ :=
    StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab
  exact le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)

end GlobalTheory
