import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityLatticeDescendsIntegralExtStatement

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.MapDescent

theorem exists_factor {A' B M' N' N : Type} [CommRing A'] [CommRing B] {g : A' →+* B} [AddCommGroup M'] [Module A' M']
    [AddCommGroup N'] [Module A' N'] [AddCommGroup N] [Module B N] (F : M' →ₛₗ[g] N) (ι : N' →ₛₗ[g] N)
    (hι : Function.Injective ι) (hF : ∀ x, ∃ y, ι y = F x) : ∃ f : M' →ₗ[A'] N', ∀ x, ι (f x) = F x := by
  choose f hf using hF
  exact ⟨{ toFun := f
           map_add' := fun x y => hι (by rw [map_add, hf, hf, hf, map_add])
           map_smul' := fun a x => hι (by rw [RingHom.id_apply, map_smulₛₗ, hf, hf, map_smulₛₗ]) }, hf⟩

theorem exists_baseMap {A A' B M M' : Type} [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    (g : A' →+* B) (hg : ∀ a, g (algebraMap A A' a) = algebraMap A B a) [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A' M'] (e : A' ⊗[A] M ≃ₗ[A'] M') : ∃ l : M' →ₛₗ[g] B ⊗[A] M, ∀ y, l (e (1 ⊗ₜ y)) = 1 ⊗ₜ y := by
  let gA : A' →ₐ[A] B := { g with commutes' := hg }
  let l₀ : A' ⊗[A] M →ₛₗ[g] B ⊗[A] M :=
    { toFun := LinearMap.rTensor M gA.toLinearMap
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
        | tmul b y =>
          rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']
          congr 1
          exact map_mul g a b }
  refine ⟨l₀.comp e.symm.toLinearMap, fun y => ?_⟩
  change l₀ (e.symm (e _)) = _
  rw [LinearEquiv.symm_apply_apply]
  change (g 1) ⊗ₜ y = _
  rw [map_one]

theorem exists_descend {A A' B M M' N' N : Type} [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    {g : A' →+* B} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M'] [AddCommGroup N'] [Module A' N']
    [AddCommGroup N] [Module B N] (e : A' ⊗[A] M ≃ₗ[A'] M') (F : M' →ₛₗ[g] N) (ι : N' →ₛₗ[g] N)
    (hι : Function.Injective ι) (Y : Set M) (hY : Submodule.span A Y = ⊤) (hF : ∀ y ∈ Y, ∃ z, ι z = F (e (1 ⊗ₜ y))) :
    ∃ f : M' →ₗ[A'] N', ∀ x, ι (f x) = F x := by
  refine exists_factor F ι hι fun x => ?_
  obtain ⟨t, rfl⟩ := e.surjective x
  have h1 : ∀ y : M, ∃ z, ι z = F (e (1 ⊗ₜ y)) := fun y => by
    have hy : y ∈ Submodule.span A Y := hY ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hF y hy
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨z, hz⟩ := h
      obtain ⟨z', hz'⟩ := h'
      exact ⟨z + z', by rw [map_add, hz, hz', TensorProduct.tmul_add, map_add, map_add]⟩
    | smul a y _ h =>
      obtain ⟨z, hz⟩ := h
      refine ⟨algebraMap A A' a • z, ?_⟩
      rw [map_smulₛₗ, hz, ← map_smulₛₗ, ← map_smul, TensorProduct.tmul_smul, algebraMap_smul]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add s t hs ht =>
    obtain ⟨z, hz⟩ := hs
    obtain ⟨z', hz'⟩ := ht
    exact ⟨z + z', by rw [map_add, hz, hz', map_add, map_add]⟩
  | tmul a y =>
    obtain ⟨z, hz⟩ := h1 y
    exact ⟨a • z, by rw [map_smulₛₗ, hz, ← map_smulₛₗ, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩

theorem exists_support {A B M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    (t : B ⊗[A] M) : ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] (g : A' →+* B) (M' : Type) [AddCommGroup M']
      [Module A' M'] (l : M' →ₛₗ[g] B ⊗[A] M), (∀ y, ∃ z, l z = 1 ⊗ₜ y) → T ⊆ Set.range g → ∃ z, l z = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨∅, Set.finite_empty, fun _ _ _ _ _ _ l _ _ => ⟨0, map_zero l⟩⟩
  | add s t hs ht =>
    obtain ⟨T, hT, h⟩ := hs
    obtain ⟨T', hT', h'⟩ := ht
    refine ⟨T ∪ T', hT.union hT', fun A' _ g M' _ _ l hl k => ?_⟩
    obtain ⟨z, hz⟩ := h A' g M' l hl (Set.subset_union_left.trans k)
    obtain ⟨z', hz'⟩ := h' A' g M' l hl (Set.subset_union_right.trans k)
    exact ⟨z + z', by rw [map_add, hz, hz']⟩
  | tmul b y =>
    refine ⟨{b}, Set.finite_singleton b, fun A' _ g M' _ _ l hl k => ?_⟩
    obtain ⟨a, rfl⟩ := k rfl
    obtain ⟨z, hz⟩ := hl y
    exact ⟨a • z, by rw [map_smulₛₗ, hz, TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩

theorem exists_generators {B : Type} [CommRing B] [IsDomain B] {h : ℕ} {ϖ : B} (P : Submodule B (Fin h → B))
    [Module.Finite B P] [Module.Projective B P] (h0 : ϖ ≠ 0) (hb : baseOf ϖ h ≤ P) :
    ∃ (n : ℕ) (u : Fin n → P) (T : Set B), T.Finite ∧ ∀ (A' : Type) [CommRing A'] (g : A' →+* B) (π' : A'), g π' = ϖ →
      (∀ x : A', g π' ∣ g x → π' ∣ x) → T ⊆ Set.range g → ∀ x : Fin h → A', piMap g (Fin h) x ∈ P →
        ∃ c : Fin n → A', piMap g (Fin h) x = ∑ i, g (c i) • (u i).1 := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' B P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  let v : Fin h → P := fun k => ⟨ϖ • Pi.single k 1, hb (Submodule.smul_mem_pointwise_smul _ _ _ trivial)⟩
  refine ⟨n, fun i => p (Pi.single i 1), ⋃ k, Set.range (s (v k)), Set.finite_iUnion fun k => Set.finite_range _,
    fun A' _ g π' e hd hT x hx => ?_⟩
  have ht : ∀ k i, ∃ a, g a = s (v k) i := fun k i => hT (Set.mem_iUnion.2 ⟨k, i, rfl⟩)
  choose a ha using ht
  have h1 : ϖ • (⟨_, hx⟩ : P) = ∑ k, g (x k) • v k := by
    apply Subtype.ext
    funext i
    simp [v, Pi.single_apply, mul_comm]
  have h2 : ∀ i, ϖ * s ⟨_, hx⟩ i = g (∑ k, x k * a k i) := fun i => by
    have := congrFun (congrArg s h1) i
    rw [map_smul] at this
    simpa [ha] using this
  have h3 : ∀ i, ∃ c, g c = s ⟨_, hx⟩ i := fun i => by
    obtain ⟨c, hc⟩ := hd (∑ k, x k * a k i) ⟨_, by rw [← h2, e]⟩
    refine ⟨c, mul_left_cancel₀ h0 ?_⟩
    rw [h2, hc, map_mul, e]
  choose c hc using h3
  refine ⟨c, ?_⟩
  have h4 : (⟨_, hx⟩ : P) = ∑ i, g (c i) • p (Pi.single i 1) := by
    have : p (s ⟨_, hx⟩) = ⟨_, hx⟩ := LinearMap.congr_fun hs _
    rw [← this, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    congr 2
    funext k
    simp [Pi.single_apply, eq_comm]
  simpa using congrArg Subtype.val h4

theorem maps_descend : ∀ (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] (h : ℕ) (ϖ : B) (P : Submodule B (Fin h → B)) [Module.Finite B P] [Module.Projective B P] (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [Module.Finite A Lie] [Module.Finite A Om] [Module.Projective A Om] (j : B ⊗[A] Lie →ₗ[B] Qt P (baseOf ϖ h)) (ρ : B ⊗[A] Om →ₗ[B] Qt P (baseOf ϖ h) ⧸ LinearMap.range j) (S : Set (Om × P)), ϖ ≠ 0 → baseOf ϖ h ≤ P → Function.Surjective ρ → S.Finite → (∀ s ∈ S, ρ (1 ⊗ₜ s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk s.2)) → ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [Algebra A A'] (g : A' →+* B), Function.Injective g → g.IsIntegral → (∀ a, g (algebraMap A A' a) = algebraMap A B a) → T ⊆ Set.range g → ∀ (π' : A') (P' : Submodule A' (Fin h → A')), g π' = ϖ → (∀ x, x ∈ P' ↔ piMap g (Fin h) x ∈ P) → ∀ (Lie' Om' : Type) [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] (eL : A' ⊗[A] Lie ≃ₗ[A'] Lie') (eO : A' ⊗[A] Om ≃ₗ[A'] Om'), ∃ (j' : Lie' →ₗ[A'] Qt P' (baseOf π' h)) (ρ' : Om' →ₗ[A'] Qt P' (baseOf π' h) ⧸ LinearMap.range j') (l : Lie' →ₛₗ[g] B ⊗[A] Lie) (m : Om' →ₛₗ[g] B ⊗[A] Om), (∀ y, l (eL (1 ⊗ₜ y)) = 1 ⊗ₜ y) ∧ (∀ w, m (eO (1 ⊗ₜ w)) = 1 ⊗ₜ w) ∧ Function.Surjective ρ' ∧ (∀ (y : Lie') (x : P') (x' : P), x'.1 = piMap g (Fin h) x.1 → j' y = Submodule.Quotient.mk x → j (l y) = Submodule.Quotient.mk x') ∧ (∀ (w : Om') (x : P') (x' : P), x'.1 = piMap g (Fin h) x.1 → ρ' w = Submodule.Quotient.mk (Submodule.Quotient.mk x) → ρ (m w) = Submodule.Quotient.mk (Submodule.Quotient.mk x')) ∧ ∀ s ∈ S, ∃ x : P', piMap g (Fin h) x.1 = s.2.1 ∧ ρ' (eO (1 ⊗ₜ s.1)) = Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
  intro A B _ _ _ _ h ϖ P _ _ Lie Om _ _ _ _ _ _ _ j ρ S h0 hb hρ hS hSρ
  obtain ⟨n, u, T₀, hT₀, hu⟩ := exists_generators P h0 hb
  obtain ⟨Y, hYf, hY⟩ := Submodule.fg_def.1 (Module.Finite.fg_top (R := A) (M := Lie))
  obtain ⟨Z, hZf, hZ⟩ := Submodule.fg_def.1 (Module.Finite.fg_top (R := A) (M := Om))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property
    ((LinearMap.range j).mkQ ∘ₗ ((baseOf ϖ h).comap P.subtype).mkQ) ρ
    ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _))
  replace hσ : ∀ t, ρ t = Submodule.Quotient.mk (Submodule.Quotient.mk (σ t)) := fun t => (LinearMap.congr_fun hσ t).symm
  choose xj hxj using fun y : Lie => Submodule.Quotient.mk_surjective _ (j (1 ⊗ₜ y))
  choose t ht using fun x : P => hρ (Submodule.Quotient.mk (Submodule.Quotient.mk x))
  have hw : ∀ (w : B ⊗[A] Om) (x : P), ∃ y, ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) →
      j y = Submodule.Quotient.mk (σ w) - Submodule.Quotient.mk x := fun w x => by
    by_cases k : ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x)
    · rw [hσ, Submodule.Quotient.eq] at k
      exact k.imp fun _ k _ => k
    · exact ⟨0, fun k' => absurd k' k⟩
  choose r hr using hw
  choose TL hTL hL using fun t : B ⊗[A] Lie => exists_support t
  choose TO hTO hO using fun t : B ⊗[A] Om => exists_support t
  refine ⟨T₀ ∪ (⋃ i, Set.range (u i).1 ∪ TO (t (u i)) ∪ TL (r (t (u i)) (u i))) ∪ (⋃ y ∈ Y, Set.range (xj y).1) ∪
    (⋃ z ∈ Z, Set.range (σ (1 ⊗ₜ z)).1) ∪ ⋃ s ∈ S, Set.range s.2.1 ∪ TL (r (1 ⊗ₜ s.1) s.2),
    (((hT₀.union (Set.finite_iUnion fun i => ((Set.finite_range _).union (hTO _)).union (hTL _))).union
      (hYf.biUnion fun _ _ => Set.finite_range _)).union (hZf.biUnion fun _ _ => Set.finite_range _)).union
      (hS.biUnion fun _ _ => (Set.finite_range _).union (hTL _)), ?_⟩
  intro A' _ _ _ _ g hg hgi hga hT π' P' hπ hP' Lie' Om' _ _ _ _ eL eO
  simp only [Set.union_subset_iff, Set.iUnion_subset_iff] at hT
  obtain ⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩ := hT
  have hπ0 : π' ≠ 0 := by
    rintro rfl
    exact h0 (hπ ▸ map_zero g)
  obtain ⟨kd, kb⟩ := GlobalTheory.T.divisibility_lattice_descends_integral_ext A' B g hg hgi
  let ι₀ : P' →ₛₗ[g] P := ((piMap g (Fin h)).comp P'.subtype).codRestrict P fun x => (hP' _).1 x.2
  have hι₀v : ∀ x, (ι₀ x).1 = piMap g (Fin h) x.1 := fun _ => rfl
  have hι₀ : Function.Injective ι₀ := fun x y e => Subtype.ext (funext fun i => hg (congrFun (congrArg Subtype.val e) i))
  have hb' : ∀ x : P', x ∈ (baseOf π' h).comap P'.subtype ↔ ι₀ x ∈ (baseOf ϖ h).comap P.subtype := fun x => by
    have := kb h π' hπ0 x.1
    rw [hπ] at this
    exact this.symm
  let ι : Qt P' (baseOf π' h) →ₛₗ[g] Qt P (baseOf ϖ h) := Submodule.mapQ _ _ ι₀ fun x hx => (hb' x).1 hx
  have hιv : ∀ x, ι (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ι₀ x) := fun _ => rfl
  have hι : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun q hq => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hιv, Submodule.Quotient.mk_eq_zero] at hq
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hb' x).2 hq)
  have hlift : ∀ x : P, Set.range x.1 ⊆ Set.range g → ∃ x', ι₀ x' = x := fun x hx => by
    choose c hc using fun i => hx ⟨i, rfl⟩
    have e : piMap g (Fin h) c = x.1 := funext hc
    exact ⟨⟨c, (hP' c).2 (e ▸ x.2)⟩, Subtype.ext e⟩
  obtain ⟨l, hl⟩ := exists_baseMap g hga eL
  obtain ⟨m, hm⟩ := exists_baseMap g hga eO
  obtain ⟨j', hj'⟩ := exists_descend eL (j.comp l) ι hι Y hY fun y hy => by
    obtain ⟨x, hx⟩ := hlift _ (k2 y hy)
    exact ⟨Submodule.Quotient.mk x, by rw [hιv, hx, hxj, LinearMap.comp_apply, hl]⟩
  obtain ⟨σ', hσ'⟩ := exists_descend eO (σ.comp m) ι₀ hι₀ Z hZ fun z hz => by
    rw [LinearMap.comp_apply, hm]
    exact hlift _ (k3 z hz)
  simp only [LinearMap.comp_apply] at hj' hσ'
  let ρ' : Om' →ₗ[A'] Qt P' (baseOf π' h) ⧸ LinearMap.range j' :=
    (LinearMap.range j').mkQ ∘ₗ ((baseOf π' h).comap P'.subtype).mkQ ∘ₗ σ'
  have hρ' : ∀ w, ρ' w = Submodule.Quotient.mk (Submodule.Quotient.mk (σ' w)) := fun _ => rfl
  have key : ∀ (w : Om') (x : P'), ρ (m w) = Submodule.Quotient.mk (Submodule.Quotient.mk (ι₀ x)) →
      TL (r (m w) (ι₀ x)) ⊆ Set.range g → ρ' w = Submodule.Quotient.mk (Submodule.Quotient.mk x) := fun w x e k => by
    obtain ⟨y, hy⟩ := hL _ A' g Lie' l (fun y => ⟨_, hl y⟩) k
    rw [hρ', Submodule.Quotient.eq]
    refine ⟨y, hι ?_⟩
    rw [hj', hy, hr _ _ e, map_sub, hιv, hιv, hσ']
  refine ⟨j', ρ', l, m, hl, hm, fun q => ?_, fun y x x' e k => ?_, fun w x x' e k => ?_, fun s hs => ?_⟩
  · obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose u' hu' using fun i => hlift _ (k1 i).1.1
    choose w hw using fun i => hO _ A' g Om' m (fun y => ⟨_, hm y⟩) (k1 i).1.2
    have h1 : ∀ i, ρ' (w i) = Submodule.Quotient.mk (Submodule.Quotient.mk (u' i)) := fun i =>
      key _ _ (by rw [hw, hu', ht]) (by rw [hw, hu']; exact (k1 i).2)
    obtain ⟨c, hc⟩ := hu A' g π' hπ (fun x => kd π' x hπ0) k0 x.1 ((hP' _).1 x.2)
    have hx : x = ∑ i, c i • u' i := hι₀ (Subtype.ext (by
      rw [hι₀v, hc, map_sum]
      simp only [map_smulₛₗ, hu']
      simp))
    refine ⟨∑ i, c i • w i, ?_⟩
    rw [hx, map_sum]
    change _ = (LinearMap.range j').mkQ (((baseOf π' h).comap P'.subtype).mkQ _)
    simp only [map_sum, map_smul, h1]
    rfl
  · obtain rfl : x' = ι₀ x := Subtype.ext e
    rw [← hj', k, hιv]
  · obtain rfl : x' = ι₀ x := Subtype.ext e
    rw [hρ', Submodule.Quotient.eq] at k
    obtain ⟨y, hy⟩ := k
    rw [hσ, Submodule.Quotient.eq]
    exact ⟨l y, by rw [← hj', hy, map_sub, hιv, hιv, hσ']⟩
  · obtain ⟨x, hx⟩ := hlift _ (k4 s hs).1
    exact ⟨x, congrArg Subtype.val hx, key _ _ (by rw [hm, hx, hSρ s hs]) (by rw [hm, hx]; exact (k4 s hs).2)⟩

end GlobalTheory.MapDescent
