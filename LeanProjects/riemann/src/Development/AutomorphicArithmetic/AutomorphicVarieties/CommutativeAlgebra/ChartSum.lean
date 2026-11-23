import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O E σ τ : Type} [CommRing O] [CommRing E] [Algebra O E]

private theorem cs_ext [Finite σ] [Finite τ] (f g : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E)
    (h0 : ∀ s, constantCoeff (f (X s)) = 0) (h : ∀ s, f (X s) = g (X s)) : f = g := by
  apply AlgHom.ext
  intro p
  ext d
  have hJ : ∀ n : ℕ, f p - g p ∈ GlobalTheory.germIdeal τ E ^ n := fun n =>
    GlobalTheory.algHom_sub_mem_pow f g (J := GlobalTheory.germIdeal τ E) (fun s => RingHom.mem_ker.mpr (h0 s))
      (fun s => RingHom.mem_ker.mpr (by rw [← h s]; exact h0 s))
      (fun s => by rw [h s, sub_self]; exact Submodule.zero_mem _) p
  have hd := (GlobalTheory.mem_germIdeal_pow_iff.mp (hJ (Finsupp.degree d + 1))) d (Nat.lt_succ_self _)
  rwa [map_sub, sub_eq_zero] at hd

private theorem mul_mem_wtPart' {ι A G : Type} [CommRing A] [AddCommGroup G] (w' : ι → G)
    {p q : MvPowerSeries ι A} {i j : G} (hp : p ∈ wtPart A w' i) (hq : q ∈ wtPart A w' j) :
    p * q ∈ wtPart A w' (i + j) := by
  classical
  have hp' : ∀ n, Finsupp.weight w' n ≠ i → coeff n p = 0 := hp
  have hq' : ∀ n, Finsupp.weight w' n ≠ j → coeff n q = 0 := hq
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨b, c⟩ hbc
  have hbc' : b + c = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
  dsimp only
  by_cases hb : Finsupp.weight w' b = i
  · have hc : Finsupp.weight w' c ≠ j := by
      intro hc
      apply hn
      rw [← hbc', map_add, hb, hc]
    rw [hq' c hc, mul_zero]
  · rw [hp' b hb, zero_mul]

private theorem one_mem_wtPart_zero {ι A G : Type} [CommRing A] [AddCommGroup G] (w' : ι → G) :
    (1 : MvPowerSeries ι A) ∈ wtPart A w' 0 := by
  classical
  intro n hn
  rw [coeff_one, if_neg]
  rintro rfl
  exact hn (map_zero _)

private theorem pow_mem_wtPart {ι A G : Type} [CommRing A] [AddCommGroup G] (w' : ι → G)
    {p : MvPowerSeries ι A} {i : G} (hp : p ∈ wtPart A w' i) (k : ℕ) :
    p ^ k ∈ wtPart A w' (k • i) := by
  induction k with
  | zero => simpa using one_mem_wtPart_zero (A := A) w'
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_wtPart' w' ih hp

private theorem finsupp_prod_pow_mem_wtPart_weight {ι κ A G : Type} [CommRing A] [AddCommGroup G] (w : κ → G) (w' : ι → G)
    (a : κ → MvPowerSeries ι A) (hw : ∀ s, a s ∈ wtPart A w' (w s)) (d : κ →₀ ℕ) :
    (d.prod fun s e => a s ^ e) ∈ wtPart A w' (Finsupp.weight w d) := by
  classical
  rw [Finsupp.weight_apply]
  unfold Finsupp.prod Finsupp.sum
  induction d.support using Finset.induction_on with
  | empty => simpa using one_mem_wtPart_zero (A := A) w'
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    exact mul_mem_wtPart' w' (pow_mem_wtPart w' (hw s) (d s)) ih

private theorem cs_ex [Finite σ] {G : Type} [AddCommGroup G] (w : σ → G) (w' : τ → G)
    (a : σ → MvPowerSeries τ E) (h0 : ∀ s, constantCoeff (a s) = 0) (hw : ∀ s, a s ∈ wtPart E w' (w s)) :
    ∃ F : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E, (∀ s, F (X s) = a s) ∧
      ∀ j, ∀ f ∈ wtPart O w j, F f ∈ wtPart E w' j := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h0
  refine ⟨substAlgHom (R := O) ha, fun s => ?_, fun j f hf => ?_⟩
  · rw [coe_substAlgHom, subst_X ha]
  · rw [coe_substAlgHom]
    have hf' : ∀ n, Finsupp.weight w n ≠ j → coeff n f = 0 := hf
    intro n hn
    rw [coeff_subst ha]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : Finsupp.weight w d = j
    · have hp' : ∀ m, Finsupp.weight w' m ≠ Finsupp.weight w d →
          coeff m (d.prod fun s e => a s ^ e) = 0 := finsupp_prod_pow_mem_wtPart_weight w w' a hw d
      rw [hp' n (hd ▸ hn), smul_zero]
    · rw [hf' d hd, zero_smul]

private theorem cs_rename_mem [Finite σ] {G : Type} [AddCommGroup G] (w' : τ → G) (u : σ → τ) {j : G}
    {f : MvPowerSeries σ E} (hf : f ∈ wtPart E (fun s => w' (u s)) j) : rename u f ∈ wtPart E w' j := by
  have hf' : ∀ n, Finsupp.weight (fun s => w' (u s)) n ≠ j → coeff n f = 0 := hf
  intro n hn
  rw [coeff_rename]
  apply Finset.sum_eq_zero
  intro y hy
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hy
  apply hf' y
  intro hyj
  apply hn
  rw [← hy, ← hyj]
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]

private theorem cs_coeff_same {T : Type} {τ : T → Type} [∀ v, Finite (τ v)] (v : T) (i : τ v)
    (f : MvPowerSeries (τ v) E) :
    coeff (Finsupp.single (⟨v, i⟩ : Σ v, τ v) 1) (rename (Sigma.mk v) f) = coeff (Finsupp.single i 1) f := by
  have hc := coeff_embDomain_rename (R := E) ⟨Sigma.mk v, sigma_mk_injective⟩ f (Finsupp.single i 1)
  simpa [Finsupp.embDomain_single] using hc

private theorem cs_coeff_ne {T : Type} {τ : T → Type} [∀ v, Finite (τ v)] {v v' : T} (h : v' ≠ v) (i : τ v')
    (f : MvPowerSeries (τ v) E) :
    coeff (Finsupp.single (⟨v', i⟩ : Σ v, τ v) 1) (rename (Sigma.mk v) f) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨y, hy⟩
  have h1 := congrArg (fun g => g ⟨v', i⟩) hy
  simp only [Finsupp.single_eq_same] at h1
  rw [Finsupp.mapDomain_notin_range] at h1
  · exact zero_ne_one h1
  · rintro ⟨j, hj⟩
    exact h (congrArg Sigma.fst hj).symm

private theorem exists_single_of_degree_eq_one {σ : Type} (d : σ →₀ ℕ) (hd : Finsupp.degree d = 1) :
    ∃ t, d = Finsupp.single t 1 := by
  classical
  have hne : d ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨t, ?_⟩
  have hsum : d t + ∑ i ∈ d.support.erase t, d i = 1 := by
    rw [Finset.add_sum_erase _ _ ht, ← hd]
    rfl
  have hpos : 0 < d t := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ht)
  have hrest : ∑ i ∈ d.support.erase t, d i = 0 := by omega
  have ht1 : d t = 1 := by omega
  ext i
  by_cases hi : i = t
  · subst hi
    simp [ht1]
  · have hdi : d i = 0 := by
      by_contra hc
      exact hc (Finset.sum_eq_zero_iff.mp hrest i (Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hc⟩))
    simp [Finsupp.single_apply, Ne.symm hi, hdi]

private theorem cs_lin [Fintype σ] (g : MvPowerSeries σ O) (h0 : constantCoeff g = 0) :
    ((2 : ℕ) : ℕ∞) ≤ (g - ∑ s, coeff (Finsupp.single s 1) g • X s).order := by
  classical
  refine MvPowerSeries.nat_le_order (fun d hd => ?_)
  simp only [map_sub, map_sum, coeff_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases (Nat.lt_succ_iff.mp hd).lt_or_eq with hlt | h1
  · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst hd0
    simp [h0, eq_comm]
  · obtain ⟨t, rfl⟩ := exists_single_of_degree_eq_one d h1
    simp [Finsupp.single_eq_single_iff]

private theorem cs_sat [IsDomain O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
    (x : A →ₐ[O] O) (x' : A' →ₐ[O] O) (i : A →ₐ[O] A') (h : ∀ a, x' (i a) = x a) {a : A} (ha : a ∈ satSq x) :
    i a ∈ satSq x' := by
  obtain ⟨c, hc, hca⟩ := ha
  refine ⟨c, hc, ?_⟩
  have hle : Ideal.map i (RingHom.ker x) ≤ RingHom.ker x' := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    simp only [Ideal.mem_comap, RingHom.mem_ker] at hb ⊢
    rw [h]
    exact hb
  have hm := Ideal.mem_map_of_mem i hca
  rw [Ideal.map_pow, map_smul] at hm
  exact Ideal.pow_right_mono hle 2 hm

end

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Alg.chart_sum :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] (T : Type) [Fintype T] (B : T → Type) [∀ v, CommRing (B v)] [∀ v, Algebra O (B v)] (WB : ∀ v, WPres O X (B v)) (hB : ∀ v, (WB v).HasOrigin)
      (τ : T → Type) [∀ v, Fintype (τ v)] (wt : ∀ v, τ v → X) (φ : ∀ v, B v →ₐ[O] MvPowerSeries (τ v) (FractionRing O)), (∀ v, IsChart (WB v).part ((WB v).origin (hB v)) (wt v) (φ v)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (W : WPres O X R) (e : (Σ v, (WB v).σ) ≃ W.σ), (∀ v s, W.wt (e ⟨v, s⟩) = (WB v).wt s) →
      RingHom.ker W.π = ⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename fun s => e ⟨v, s⟩) →
      ∃ (h : W.HasOrigin) (ψ : R →ₐ[O] MvPowerSeries (Σ v, τ v) (FractionRing O)), IsChart W.part (W.origin h) (fun p => wt p.1 p.2) ψ ∧
        ∀ v s, ψ (W.z (e ⟨v, s⟩)) = MvPowerSeries.rename (Sigma.mk v) (φ v ((WB v).z s)) := by
  intro O X _ _ _ T _ B _ _ WB hB τ _ wt φ hφ R _ _ W e he hker
  classical
  haveI : Fintype W.σ := W.fin
  haveI : ∀ v, Fintype (WB v).σ := fun v => (WB v).fin
  have hO : W.HasOrigin := by
    intro f hf
    have hf' : f ∈ RingHom.ker W.π := RingHom.mem_ker.mpr hf
    rw [hker] at hf'
    have hle : (⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename fun s => e ⟨v, s⟩)) ≤
        RingHom.ker (constantCoeff (σ := W.σ) (R := O)) := by
      refine iSup_le fun v => ?_
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simpa using hB v g hg
    exact RingHom.mem_ker.mp (hle hf')
  let a : W.σ → MvPowerSeries (Σ v, τ v) (FractionRing O) := fun t =>
    MvPowerSeries.rename (Sigma.mk (e.symm t).1) (φ (e.symm t).1 ((WB (e.symm t).1).z (e.symm t).2))
  have hae' : ∀ p : Σ v, (WB v).σ, a (e p) = MvPowerSeries.rename (Sigma.mk p.1) (φ p.1 ((WB p.1).z p.2)) := by
    intro p
    show (fun q : Σ v, (WB v).σ => MvPowerSeries.rename (Sigma.mk q.1) (φ q.1 ((WB q.1).z q.2))) (e.symm (e p)) = _
    rw [e.symm_apply_apply]
  have hae : ∀ v s, a (e ⟨v, s⟩) = MvPowerSeries.rename (Sigma.mk v) (φ v ((WB v).z s)) :=
    fun v s => hae' ⟨v, s⟩
  have ha0 : ∀ t, constantCoeff (a t) = 0 := by
    intro t
    obtain ⟨⟨v, s⟩, rfl⟩ := e.surjective t
    rw [hae, constantCoeff_rename, (hφ v).const, WPres.z, WPres.origin_π, constantCoeff_X, map_zero]
  have haw : ∀ t, a t ∈ wtPart (FractionRing O) (fun p => wt p.1 p.2) (W.wt t) := by
    intro t
    obtain ⟨⟨v, s⟩, rfl⟩ := e.surjective t
    rw [hae, he]
    have h1 : φ v ((WB v).z s) ∈ wtPart (FractionRing O) (wt v) ((WB v).wt s) :=
      (hφ v).graded _ _ (WPres.z_mem _ s)
    exact cs_rename_mem (E := FractionRing O) (fun p : (Σ v, τ v) => wt p.1 p.2) (Sigma.mk v) h1
  obtain ⟨Φ, hΦX, hΦw⟩ := cs_ex (O := O) (E := FractionRing O) (σ := W.σ) (τ := Σ v, τ v) (G := X) W.wt (fun p => wt p.1 p.2) a ha0 haw
  have hΦg : ∀ t, Φ (MvPowerSeries.X t) ∈ GlobalTheory.germIdeal (Σ v, τ v) (FractionRing O) := fun t =>
    RingHom.mem_ker.mpr (by rw [hΦX]; exact ha0 t)
  have hcomp : ∀ v, Φ.comp (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩) =
      ((MvPowerSeries.rename (R := FractionRing O) (Sigma.mk v)).restrictScalars O).comp ((φ v).comp (WB v).π) := by
    intro v
    apply cs_ext
    · intro s
      rw [AlgHom.comp_apply, rename_X, hΦX]
      exact ha0 _
    · intro s
      rw [AlgHom.comp_apply, rename_X, hΦX, hae]
      rfl
  have hca : ∀ v p, Φ (MvPowerSeries.rename (fun s => e ⟨v, s⟩) p) =
      MvPowerSeries.rename (Sigma.mk v) (φ v ((WB v).π p)) := fun v p => AlgHom.congr_fun (hcomp v) p
  have hkerΦ : ∀ g ∈ RingHom.ker W.π, Φ g = 0 := by
    intro g hg
    rw [hker] at hg
    have hle : (⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩)) ≤
        RingHom.ker Φ := by
      refine iSup_le fun v => ?_
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [RingHom.mem_ker] at hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hca, hp, map_zero, map_zero]
    exact RingHom.mem_ker.mp (hle hg)
  let ψ : R →ₐ[O] MvPowerSeries (Σ v, τ v) (FractionRing O) :=
    (Ideal.Quotient.liftₐ (RingHom.ker W.π) Φ hkerΦ).comp
      ↑(Ideal.quotientKerAlgEquivOfSurjective W.surj).symm
  have hψ : ∀ g, ψ (W.π g) = Φ g := by
    intro g
    have hq : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Φ hkerΦ
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π g)) = Φ g
    rw [hq]
    rfl
  refine ⟨hO, ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j f hf
    obtain ⟨g, hg, rfl⟩ := hf
    show ψ (W.π g) ∈ _
    rw [hψ]
    exact hΦw j g hg
  · intro f
    obtain ⟨g, rfl⟩ := W.surj f
    rw [hψ, WPres.origin_π]
    have hm := GlobalTheory.algHom_sub_constantCoeff_mem Φ hΦg g
    rw [GlobalTheory.germIdeal, RingHom.mem_ker, map_sub, sub_eq_zero] at hm
    rw [hm, MvPowerSeries.algebraMap_apply, constantCoeff_C]
  · rintro ⟨v, k⟩
    obtain ⟨fv, hfv1, hfv2⟩ := (hφ v).onto k
    obtain ⟨g, rfl⟩ := (WB v).surj fv
    have hval : ψ (W.π (MvPowerSeries.rename (fun s => e ⟨v, s⟩) g)) =
        MvPowerSeries.rename (Sigma.mk v) (φ v ((WB v).π g)) := by
      rw [hψ, hca]
    refine ⟨W.π (MvPowerSeries.rename (fun s => e ⟨v, s⟩) g), ?_, ?_⟩
    · rw [hval, cs_coeff_same]
      exact hfv1
    · rintro ⟨v', k'⟩ hne
      rw [hval]
      by_cases hv : v' = v
      · subst hv
        rw [cs_coeff_same]
        exact hfv2 k' (fun h => hne (by rw [h]))
      · exact cs_coeff_ne hv k' _
  · intro f hf0 hf1
    obtain ⟨g, rfl⟩ := W.surj f
    rw [WPres.origin_π] at hf0
    simp only [hψ] at hf1
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : MvPowerSeries W.σ O,
        ℓ = ∑ t, coeff (Finsupp.single t 1) g • MvPowerSeries.X t := ⟨_, rfl⟩
    have hord := cs_lin g hf0
    rw [← hℓ] at hord
    have hq : W.π (g - ℓ) ∈ satSq (W.origin hO) := by
      refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact GlobalTheory.algHom_mem_pow_of_le_order W.π (K := RingHom.ker (W.origin hO))
        (fun t => by rw [RingHom.mem_ker, WPres.origin_π, constantCoeff_X]) hord
    have hΦl : ∀ i, coeff (Finsupp.single i 1) (Φ ℓ) = 0 := by
      intro i
      have hm := GlobalTheory.algHom_mem_pow_of_le_order Φ hΦg hord
      have h2 := GlobalTheory.mem_germIdeal_pow_iff.mp hm (Finsupp.single i 1) (by simp)
      have h3 := hf1 i
      rw [show g = ℓ + (g - ℓ) by ring, map_add, map_add, h2, add_zero] at h3
      exact h3
    let ℓv : ∀ v, MvPowerSeries (WB v).σ O := fun v =>
      ∑ s, coeff (Finsupp.single (e ⟨v, s⟩) 1) g • MvPowerSeries.X s
    have hℓsum : ℓ = ∑ v, MvPowerSeries.rename (fun s => e ⟨v, s⟩) (ℓv v) := by
      rw [hℓ]
      simp only [ℓv, map_sum, map_smul, rename_X]
      rw [← Fintype.sum_sigma (fun p : Σ v, (WB v).σ =>
        coeff (Finsupp.single (e p) 1) g • MvPowerSeries.X (e p))]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    have hmapv : ∀ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩) ≤
        RingHom.ker W.π := by
      intro v
      rw [hker]
      exact le_iSup (fun v => (RingHom.ker (WB v).π).map (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩)) v
    have hiv_ker : ∀ v, ∀ p ∈ RingHom.ker (WB v).π,
        (W.π.comp (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩)) p = 0 := by
      intro v p hp
      rw [AlgHom.comp_apply, ← RingHom.mem_ker]
      exact hmapv v (Ideal.mem_map_of_mem _ hp)
    have hv : ∀ v, W.π (MvPowerSeries.rename (fun s => e ⟨v, s⟩) (ℓv v)) ∈ satSq (W.origin hO) := by
      intro v
      let iv : B v →ₐ[O] R :=
        (Ideal.Quotient.liftₐ (RingHom.ker (WB v).π)
          (W.π.comp (MvPowerSeries.rename (R := O) fun s => e ⟨v, s⟩)) (hiv_ker v)).comp
          ↑(Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm
      have hivπ : ∀ p, iv ((WB v).π p) = W.π (MvPowerSeries.rename (fun s => e ⟨v, s⟩) p) := by
        intro p
        have hq' : (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm ((WB v).π p) =
            Ideal.Quotient.mk _ p := by
          rw [AlgEquiv.symm_apply_eq]
          rfl
        show Ideal.Quotient.liftₐ _ _ (hiv_ker v)
          ((Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm ((WB v).π p)) = _
        rw [hq']
        rfl
      have hiv : ∀ b, W.origin hO (iv b) = (WB v).origin (hB v) b := by
        intro b
        obtain ⟨p, rfl⟩ := (WB v).surj b
        rw [hivπ, WPres.origin_π, WPres.origin_π, constantCoeff_rename]
      have hc0 : (WB v).origin (hB v) ((WB v).π (ℓv v)) = 0 := by
        rw [WPres.origin_π]
        simp [ℓv]
      have hc1 : ∀ k, coeff (Finsupp.single k 1) (φ v ((WB v).π (ℓv v))) = 0 := by
        intro k
        have h1 := hΦl ⟨v, k⟩
        rw [hℓsum, map_sum, map_sum, Finset.sum_eq_single v] at h1
        · rw [hca, cs_coeff_same] at h1
          exact h1
        · intro v' _ hv'
          rw [hca]
          exact cs_coeff_ne (fun h => hv' h.symm) k _
        · intro h
          exact absurd (Finset.mem_univ v) h
      have hsat := (hφ v).inj _ hc0 hc1
      have hfin := cs_sat ((WB v).origin (hB v)) (W.origin hO) iv hiv hsat
      rwa [hivπ] at hfin
    have hl : W.π ℓ ∈ satSq (W.origin hO) := by
      rw [hℓsum, map_sum]
      exact Submodule.sum_mem _ (fun v _ => hv v)
    rw [show g = ℓ + (g - ℓ) by ring, map_add]
    exact Submodule.add_mem _ hl hq
  · intro v s
    rw [WPres.z, hψ, hΦX, hae]
