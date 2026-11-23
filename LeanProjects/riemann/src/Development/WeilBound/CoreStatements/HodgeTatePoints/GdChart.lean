import Development.WeilBound.CoreStatements.HodgeTatePoints.GdDual
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

section SlopeTestRemainingChoices

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {C O : Type} [Field C] [CommRing O]
  [Algebra O C] {E : Type} [Field E] [NumberField E]

theorem map_mem_span (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {S : Set K} {S' : Set C}
    (hS : ∀ x ∈ S, ψ x ∈ S') {x : K} (hx : x ∈ Submodule.span A S) : ψ x ∈ Submodule.span O S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hS x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem generatesDiff_map (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {σ : E →+* K} {d : A}
    (hd : GeneratesDiff σ d) : GeneratesDiff (ψ.comp σ) (φ d) := by
  unfold GeneratesDiff at hd ⊢
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, ← h]
    refine map_mem_span φ ψ h ?_ (hd.le (Submodule.mem_span_singleton_self _))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_span φ ψ h ?_ (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    rintro _ rfl
    exact h d

theorem emb_mem [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)

variable {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω' : Type} [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem qgen_mem (σ : E →+* K) (l : Fin N) :
    eigProj D.ρΩ σ (D.h (Pi.single l 1)) ∈ D.omHT σ :=
  ⟨_, Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩), rfl⟩

theorem omHT_fg [IsNoetherianRing A] (σ : E →+* K) : (D.omHT σ).FG := by
  refine Submodule.FG.map _ (Submodule.FG.of_le D.om_lat.fg (sup_le ?_ ?_))
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem tate_single {κ : O} (P : HTPoint C O c κ N V Ω') (l : Fin N) (a : 𝓞 E) :
    P.tate (Pi.single l a) = P.ρ a (P.t l) := by
  rw [HTPoint.tate, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

variable [CharZero K] [CharZero C] {κ : O} {P : HTPoint C O c κ N V Ω'} {φ : A →+* O}
  {ι : D.om →ₛₗ[φ] Ω'}

theorem gen_at_point (hAK : Function.Injective (algebraMap A K))
    (hOC : Function.Injective (algebraMap O C)) (hφ : Function.Injective φ) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) {π : O} (hπ : κ * π ∣ (p : O) ^ R) (J : D.omHT σ → Ω')
    (hJ : ∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → φ d • J z = ι y) (l : Fin N) :
    ∃ y ∈ P.omHT (ψ.comp σ), J ⟨_, qgen_mem D σ l⟩ =
      eigProj P.ρΩ (ψ.comp σ) (P.ht (P.t l)) + π • y := by
  obtain ⟨hd0, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  let y0 : D.om := ⟨D.h (Pi.single l 1), D.h_mem _⟩
  let y : D.om := ∑ k, u k • ⟨D.ρΩ (RingOfIntegers.basis E k) y0, D.om_stable _ _ y0.2⟩
  have h1 := hJ ⟨_, qgen_mem D σ l⟩ y (by
    simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (u k), hu, ← algebraMap_smul K d, smul_smul])
  have h2 : ι y = φ d • eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
      LinearMap.map_smulₛₗ, hred.lin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul C (φ (u k)), ← h, hu, ← algebraMap_smul C (φ d), smul_smul, map_mul, h]
    rfl
  have hd1 : algebraMap O C (φ d) ≠ 0 := by
    rw [← h]
    exact (map_ne_zero ψ).2 hd0
  have h3 : J ⟨_, qgen_mem D σ l⟩ = eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    rw [h2, ← algebraMap_smul C (φ d), ← algebraMap_smul C (φ d)] at h1
    exact smul_right_injective Ω' hd1 h1
  obtain ⟨y1, hy1, e1⟩ := hred.ht_eq (Pi.single l 1)
  obtain ⟨x1, hx1, e2⟩ := P.κ_mem y1 hy1
  obtain ⟨r, hr⟩ := hπ
  refine ⟨r • eigProj P.ρΩ (ψ.comp σ) (P.ht x1), Submodule.smul_mem _ _ (proj_ht_mem P _ hx1), ?_⟩
  rw [h3, e1, tate_single, map_one, Module.End.one_apply, map_add, e2, ← Nat.cast_smul_eq_nsmul O,
    Nat.cast_pow, hr, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_smul, smul_smul]
  congr 2
  ring

theorem gram_at_point (hAK : Function.Injective (algebraMap A K)) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) (l j : Fin N) :
    ∃ z : O, P.e (φ d • eigProj P.ρ (ψ.comp σ) (P.t l)) (P.t j) =
      ψ (D.gram σ d l j) + algebraMap O C ((p : O) ^ R * z) := by
  obtain ⟨-, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  choose z hz using hred.e_eq
  refine ⟨∑ k, φ (u k) * z (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1), ?_⟩
  rw [← algebraMap_smul C (φ d)]
  simp only [eigProj, HTChart.gram, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
    map_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := hz (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1)
  rw [tate_single, tate_single, map_one, Module.End.one_apply] at h1
  have h2 := congrArg ψ (hu k)
  rw [h, map_mul, h] at h2
  simp only [h1, smul_eq_mul, map_mul, map_add, map_natCast, h, h2, RingHom.comp_apply]
  ring

end SlopeTestRemainingChoices

theorem chart_comp_zero_of
    (hdiv : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y)
    (hdesc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L)
    (hbc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ')) :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ σ d d' m i hκ hd hd' _ hP hP' htest hi w
  have hAK := IsFractionRing.injective A K
  have hq : D.q σ (i w) ∈ D.omHT σ :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (qgen_mem D σ l)
  refine hdiv A K Ω (D.omHT σ) _ ((p : A) ^ m) (p : A) (omHT_fg D σ) hP hq ?_
    (fun 𝔮 h𝔮 h => h𝔮.mem_of_pow_mem m h) fun 𝔮 h𝔮 hht hp𝔮 => ?_
  · refine pow_ne_zero _ fun h0 => hp.out.ne_zero ?_
    have := congrArg (algebraMap A K) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    htest 𝔮 h𝔮 hht hp𝔮
  letI : Algebra A O := φ.toAlgebra
  have hOC := hv.hom_inj
  let ψ : K →+* C := IsFractionRing.lift (g := (algebraMap O C).comp φ) (hOC.comp hφ)
  have hψ : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a) := fun a => IsFractionRing.lift_algebraMap _ a
  have hκ' : φ κ * (p : O) ^ m ∣ (p : O) ^ R := by
    simpa using map_dvd φ hκ
  have hcomp : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h, hψ]
    rfl
  obtain ⟨j, hjinj, hjr, hj, -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ (ψ.comp σ) d
    (hcomp σ) hd (dvd_of_mul_right_dvd hκ') hP
  obtain ⟨j', hjinj', hjr', hj', -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) ((ψ.comp σ).comp c.toRingHom) d'
    (hcomp _) hd' (dvd_of_mul_right_dvd hκ') hP'
  choose y hy ey using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem σ) hd hκ' (fun z => j (1 ⊗ₜ z)) hj
  choose y' hy' ey' using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem _) hd' hκ'
    (fun z => j' (1 ⊗ₜ z)) hj'
  let eq' : (O ⊗[A] D.omHT (σ.comp c.toRingHom)) ≃ₗ[O] P.omHT ((ψ.comp σ).comp c.toRingHom) :=
    (LinearEquiv.ofInjective j' hjinj').trans (LinearEquiv.ofEq _ _ hjr')
  let wO : O ⊗[A] D.omHT (σ.comp c.toRingHom) →ₗ[O] O :=
    LinearMap.liftBaseChange O (Algebra.linearMap A O ∘ₗ w)
  let f : P.omHT ((ψ.comp σ).comp c.toRingHom) →ₗ[O] O := wO ∘ₗ eq'.symm.toLinearMap
  have hf : ∀ z, f (eq' (1 ⊗ₜ z)) = φ (w z) := fun z => by
    simp only [f, wO, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  obtain ⟨w', hw', ew'⟩ := exists_alt_bis hv hc P (ψ.comp σ) f
  have htT : ∀ l, P.t l ∈ P.T := fun l => by
    have h1 : P.t l = P.ρ 1 (P.t l) := by simp
    rw [h1, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(l, k), rfl⟩
  obtain ⟨y1, hy1, e1⟩ := pt_comp_zero C v O hv E c hc (φ κ) N V Ω' P (ψ.comp σ) (φ d) ((p : O) ^ m)
    (fun l => φ (i w l)) w' (generatesDiff_map φ ψ hψ hd) hw' (fun l => by
      choose z hz using gram_at_point D hAK ψ hψ hred (emb_mem σ) hd
      obtain ⟨z1, hz1⟩ := hi w l ⟨_, qgen_mem D _ l⟩ rfl
      obtain ⟨r, hr⟩ := dvd_of_mul_left_dvd hκ'
      have h1 : eq' (1 ⊗ₜ ⟨_, qgen_mem D _ l⟩) = ⟨_, proj_ht_mem P _ (htT l)⟩ +
          ((p : O) ^ m) • ⟨y' l, hy' l⟩ := Subtype.ext (ey' l)
      have h2 := hf ⟨_, qgen_mem D _ l⟩
      rw [h1, map_add, map_smul] at h2
      have h3 := congrArg ψ hz1
      rw [hψ, map_add, map_mul, map_pow, map_natCast, ← h2, map_sum] at h3
      refine ⟨f ⟨y' l, hy' l⟩ + φ z1 + ∑ k, φ (i w k) * (r * z k l), ?_⟩
      simp only [hz, ew' _ (htT l), mul_add, Finset.sum_add_distrib, map_mul, hψ, hr] at h3 ⊢
      rw [h3]
      simp only [map_add, map_mul, map_sum, smul_eq_mul, Finset.mul_sum, add_assoc]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
  have h2 : j (1 ⊗ₜ ⟨_, hq⟩) = ((p : O) ^ m) • (y1 + ∑ l, φ (i w l) • y l) := by
    have : (⟨_, hq⟩ : D.omHT σ) = ∑ l, i w l • ⟨_, qgen_mem D σ l⟩ := Subtype.ext (by
      simp [HTChart.q])
    rw [this, TensorProduct.tmul_sum, map_sum, smul_add, ← e1, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul O (i w l), map_smul, ey, smul_add, smul_comm]
    rfl
  have h3 : y1 + ∑ l, φ (i w l) • y l ∈ LinearMap.range j := by
    rw [hjr]
    exact Submodule.add_mem _ hy1 (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hy l))
  obtain ⟨t, ht⟩ := h3
  rw [← ht, ← map_smul] at h2
  have h4 := hjinj h2
  obtain ⟨s, hs, u, hu⟩ := hdesc A K C v O hv 𝔮 (D.omHT σ)
    (LinearMap.range (((p : A) ^ m) • LinearMap.id)) ⟨_, hq⟩ h𝔮 hht hφ hcen (by
      rw [h4]
      clear h4 h2 ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | tmul a b =>
        have : ((p : O) ^ m) • (a ⊗ₜ[A] b) = a • ((1 : O) ⊗ₜ[A] (((p : A) ^ m) • b)) := by
          rw [TensorProduct.tmul_smul, ← algebraMap_smul O ((p : A) ^ m), map_pow, map_natCast,
            smul_comm, TensorProduct.smul_tmul' a, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨b, rfl⟩, rfl⟩))
  exact ⟨s, hs, u, u.2, (congrArg Subtype.val hu).symm⟩

end PositivityTheory.HtPt.Gd
