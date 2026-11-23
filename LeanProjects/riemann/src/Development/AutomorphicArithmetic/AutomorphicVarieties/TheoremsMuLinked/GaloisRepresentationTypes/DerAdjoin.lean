import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TpSingle
open UpperTheory.V UpperTheory.V.Th

namespace UpperTheory.V.Th.EtaleDerivations

open IsLocalRing Polynomial

variable {O B X : Type} [CommRing O] [CommRing B] [Algebra O B] [AddCommGroup X] [Module O X]

private theorem der_alg {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) (c : O) : δ (algebraMap O B c) = 0 := by
  have h1 : δ 1 = 0 := by
    have := h 1 1
    simpa using this
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_adjoin {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) {S : Set B} (hS : ∀ s ∈ S, δ s = 0)
    {a : B} (ha : a ∈ Algebra.adjoin O S) : δ a = 0 := by
  induction ha using Algebra.adjoin_induction with
  | mem s hs => exact hS s hs
  | algebraMap c => exact der_alg h c
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | mul a b _ _ ha hb => rw [h, ha, hb, smul_zero, smul_zero, add_zero]

private theorem der_fg [IsNoetherianRing B] {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) :
    (LinearMap.range δ).FG := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (RingHom.ker x : Ideal B)
  have key : ∀ p ∈ Submodule.span B (s : Set B), δ p ∈ Submodule.span O (δ '' (s : Set B)) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a ha0 ha =>
      rw [hs] at ha0
      have : x a = 0 := ha0
      rw [smul_eq_mul, h, this, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ ha
  have : LinearMap.range δ = Submodule.span O (δ '' (s : Set B)) := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      have hb : b - algebraMap O B (x b) ∈ Submodule.span B (s : Set B) := by
        rw [hs]; show x _ = 0; simp
      have := key _ hb
      rwa [map_sub, der_alg h, sub_zero] at this
    · rw [Submodule.span_le]
      rintro _ ⟨b, _, rfl⟩
      exact ⟨b, rfl⟩
  rw [this]
  exact Submodule.fg_span (s.finite_toSet.image _)

private theorem der_zero [IsNoetherianRing B] [IsLocalRing O] [IsLocalRing B] [IsLocalHom (algebraMap O B)]
    {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) {S : Set B} (hS : ∀ s ∈ S, δ s = 0)
    (hgen : ∀ b : B, ∃ a ∈ Algebra.adjoin O S, b - a ∈ maximalIdeal B ^ 2) (b : B) : δ b = 0 := by
  have hx : ∀ a ∈ maximalIdeal B, x a ∈ maximalIdeal O := by
    intro a ha hu
    have h1 : a - algebraMap O B (x a) ∈ maximalIdeal B := by
      intro hu'
      have := hu'.map x
      simp at this
    have h2 : algebraMap O B (x a) ∈ maximalIdeal B := by simpa using Ideal.sub_mem _ ha h1
    exact h2 (hu.map _)
  have hle : LinearMap.range δ ≤ maximalIdeal O • LinearMap.range δ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, hb⟩ := hgen b
    have e : δ b = δ (b - a) := by rw [map_sub, der_adjoin h hS ha, sub_zero]
    rw [e]
    rw [pow_two] at hb
    refine Submodule.mul_induction_on hb (fun m hm k hk => ?_) (fun m k hm hk => ?_)
    · rw [h]
      exact add_mem (Submodule.smul_mem_smul (hx m hm) ⟨k, rfl⟩) (Submodule.smul_mem_smul (hx k hk) ⟨m, rfl⟩)
    · rw [map_add]; exact add_mem hm hk
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (der_fg h) hle
    (maximalIdeal_le_jacobson _)
  have hb : δ b ∈ LinearMap.range δ := ⟨b, rfl⟩
  rw [this] at hb
  simpa using hb

private theorem kill_red [IsDomain O] (x : B →ₐ[O] O) (I : Ideal B) (A : Subalgebra O B)
    (hred : ∀ t ∈ A, ∀ k : ℕ, t ^ k ∈ I → t ∈ I) {a : B} (ha : a ∈ A) (hx : x a = 0)
    (q : O[X]) (hq : q ≠ 0) (hI : aeval a q ∈ I) : ∃ s : B, x s ≠ 0 ∧ s * a ∈ I := by
  obtain ⟨g, hg, hd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  refine ⟨aeval a g, ?_, ?_⟩
  · rw [← aeval_algHom_apply, hx]
    intro h0
    apply hd
    rw [dvd_iff_isRoot]
    simpa [coe_aeval_eq_eval] using h0
  · set k := rootMultiplicity 0 q
    have hgA : aeval a g ∈ A := (Algebra.adjoin_le (Set.singleton_subset_iff.2 ha)) (aeval_mem_adjoin_singleton O a)
    apply hred _ (A.mul_mem hgA ha) (k + 1)
    have e : (aeval a g * a) ^ (k + 1) = (aeval a g ^ k * a) * aeval a q := by
      conv_rhs => rw [hg]
      simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero]
      ring
    rw [e]
    exact I.mul_mem_left _ hI

private theorem det_trick [IsDomain O] [IsNoetherianRing B] (x : B →ₐ[O] O) (I : Ideal B)
    (h : ∀ a, x a = 0 → ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x * RingHom.ker x ⊔ I) :
    ∃ t : B, x t ≠ 0 ∧ ∀ a, x a = 0 → t * a ∈ I := by
  classical
  set P : Ideal B := RingHom.ker x with hP
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian P
  have h' : ∀ a : B, ∃ c : O, c ≠ 0 ∧ (a ∈ P → c • a ∈ P * P ⊔ I) := by
    intro a
    by_cases ha : x a = 0
    · obtain ⟨c, h1, h2⟩ := h a ha
      exact ⟨c, h1, fun _ => h2⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h ha⟩
  choose f hf0 hf using h'
  set c : O := ∏ a ∈ s, f a
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hf0 a
  have hcP : ∀ a ∈ P, algebraMap O B c * a ∈ P * P ⊔ I := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      have haP : a ∈ P := hs ▸ Submodule.subset_span ha
      obtain ⟨d, hd⟩ : f a ∣ c := Finset.dvd_prod_of_mem f ha
      rw [hd, mul_comm (f a), map_mul, mul_assoc, ← Algebra.smul_def (f a)]
      exact Ideal.mul_mem_left _ _ (hf a haP)
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
  let N : Submodule B (B ⧸ I) := Submodule.map (Submodule.mkQ I) P
  let φ : Module.End B N := algebraMap B _ (algebraMap O B c)
  have hφ : LinearMap.range φ ≤ P • ⊤ := by
    rintro _ ⟨⟨_, a, ha, rfl⟩, rfl⟩
    obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hcP a ha)
    rw [Submodule.mem_smul_top_iff]
    have : ((φ ⟨_, a, ha, rfl⟩ : N) : B ⧸ I) = Submodule.mkQ I y := by
      show algebraMap O B c • Submodule.mkQ I a = _
      rw [← map_smul, smul_eq_mul, ← e, map_add]
      have : Submodule.mkQ I z = 0 := (Submodule.Quotient.mk_eq_zero I).2 hz
      rw [this, add_zero]
    rw [this]
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun m k hm hk => ?_)
    · rw [← smul_eq_mul, map_smul]
      exact Submodule.smul_mem_smul hm ⟨k, hk, rfl⟩
    · rw [map_add]; exact add_mem hm hk
  obtain ⟨p, hp, -, hco, hev⟩ := LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul B φ P hφ
  refine ⟨p.eval (algebraMap O B c), ?_, fun a ha => ?_⟩
  · have e : p.map (x : B →+* O) = Polynomial.X ^ p.natDegree := by
      ext k
      rw [coeff_map, coeff_X_pow]
      rcases lt_trichotomy k p.natDegree with hk | hk | hk
      · rw [if_neg hk.ne]
        exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hk) (hco k)
      · rw [if_pos hk, hk, hp.coeff_natDegree, map_one]
      · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]
    have e2 : x (p.eval (algebraMap O B c)) = c ^ p.natDegree := by
      have := (eval₂_at_apply (x : B →+* O) (algebraMap O B c) (p := p)).symm
      rw [eval₂_eq_eval_map, e] at this
      simpa using this
    rw [e2]
    exact pow_ne_zero _ hc
  · have := congrArg (fun ψ : Module.End B N => ((ψ ⟨_, a, ha, rfl⟩ : N) : B ⧸ I)) hev
    simp only [φ, aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    have h2 : p.eval (algebraMap O B c) • Submodule.mkQ I a = 0 := this
    rw [← map_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero I).1 h2

private theorem core [IsDomain O] [IsLocalRing O] [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap O B)]
    (x : B →ₐ[O] O) (I : Ideal B) (S0 S : Set B)
    (hint : ∀ a : B, ∃ q : O[X], q ≠ 0 ∧ aeval a q ∈ I)
    (hred : ∀ t ∈ Algebra.adjoin O S0, ∀ k : ℕ, t ^ k ∈ I → t ∈ I)
    (hgen : ∀ b : B, ∃ a ∈ Algebra.adjoin O S, b - a ∈ maximalIdeal B ^ 2)
    (hder : ∀ (Y : Type) [AddCommGroup Y] [Module O Y] (δ : B →ₗ[O] Y), IsDer x δ →
      (∀ (c : O) (y : Y), c ≠ 0 → c • y = 0 → y = 0) → (∀ s ∈ S0, δ s = 0) → ∀ s ∈ S, δ s = 0) :
    ∃ t : B, x t ≠ 0 ∧ ∀ a, x a = 0 → t * a ∈ I := by
  apply det_trick x I
  let K : Ideal B := RingHom.ker x * RingHom.ker x ⊔ I
  let N : Submodule O B :=
    { carrier := {a | ∃ c : O, c ≠ 0 ∧ c • a ∈ K}
      add_mem' := by
        rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
        refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact Submodule.smul_of_tower_mem _ _ ha
        · rw [mul_smul]; exact Submodule.smul_of_tower_mem _ _ hb
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro r a ⟨c, hc, ha⟩
        exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_of_tower_mem _ _ ha⟩ }
  have hKN : ∀ a ∈ K, a ∈ N := fun a ha => ⟨1, one_ne_zero, by simpa using ha⟩
  let δ : B →ₗ[O] B ⧸ N := N.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O B) ∘ₗ x.toLinearMap)
  have hδ : ∀ b, δ b = N.mkQ (b - algebraMap O B (x b)) := fun b => rfl
  have hδ0 : ∀ b, x b = 0 → (δ b = 0 ↔ b ∈ N) := by
    intro b hb
    rw [hδ, hb, map_zero, sub_zero]
    exact Submodule.Quotient.mk_eq_zero N
  have hk : ∀ b, x (b - algebraMap O B (x b)) = 0 := fun b => by simp
  have hD : IsDer x δ := by
    intro a b
    rw [hδ, hδ, hδ, ← map_smul, ← map_smul, ← map_add]
    apply (Submodule.Quotient.eq N).2
    apply hKN
    have e : a * b - algebraMap O B (x (a * b)) - (x a • (b - algebraMap O B (x b)) + x b • (a - algebraMap O B (x a))) =
        (a - algebraMap O B (x a)) * (b - algebraMap O B (x b)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (hk a) (hk b))
  have htf : ∀ (c : O) (y : B ⧸ N), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc hy
    obtain ⟨a, rfl⟩ := N.mkQ_surjective y
    rw [← map_smul] at hy
    obtain ⟨d, hd, h⟩ := (Submodule.Quotient.mk_eq_zero N).1 hy
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have h0 : ∀ s ∈ S0, δ s = 0 := by
    intro s hs
    have hsA : s - algebraMap O B (x s) ∈ Algebra.adjoin O S0 :=
      sub_mem (Algebra.subset_adjoin hs) (Subalgebra.algebraMap_mem _ _)
    obtain ⟨q, hq, hqI⟩ := hint (s - algebraMap O B (x s))
    obtain ⟨t, ht, hta⟩ := kill_red x I _ hred hsA (hk s) q hq hqI
    have h1 : δ (t * (s - algebraMap O B (x s))) = 0 :=
      (hδ0 _ (by rw [map_mul, hk, mul_zero])).2 (hKN _ (Ideal.mem_sup_right hta))
    rw [hD, hk, zero_smul, add_zero, map_sub, der_alg hD, sub_zero] at h1
    exact htf _ _ ht h1
  intro a ha
  exact (hδ0 a ha).1 (der_zero hD (hder _ δ hD htf h0) hgen a)

private theorem integ {Λ M : Type} [CommRing Λ] [Algebra O Λ] [Nontrivial O] [AddCommGroup M] [Module B M] [Module Λ M]
    [Module.Finite Λ M] (lam : Λ →ₐ[O] B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (ξ : Λ →ₐ[O] O) (a : B) :
    ∃ q : O[X], q ≠ 0 ∧ ∀ m : M, aeval a q • m ∈ (RingHom.ker ξ • ⊤ : Submodule Λ M) := by
  let φ : Module.End Λ M :=
    { toFun := fun m => a • m
      map_add' := fun m k => smul_add _ _ _
      map_smul' := fun r m => by simp only [RingHom.id_apply, hl]; rw [smul_comm] }
  obtain ⟨p, hp, hev⟩ := LinearMap.exists_monic_and_aeval_eq_zero Λ φ
  have hpow : ∀ (k : ℕ) (m : M), (φ ^ k) m = a ^ k • m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro m; rw [pow_succ, pow_succ, Module.End.mul_apply, ih, mul_smul]; rfl
  have key : ∀ (p : Λ[X]) (m : M), aeval φ p m - aeval a (p.map (ξ : Λ →+* O)) • m ∈
      (RingHom.ker ξ • ⊤ : Submodule Λ M) := by
    intro p m
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add, map_add, add_smul, LinearMap.add_apply, add_sub_add_comm]
      exact add_mem hp hq
    | monomial k c =>
      have e : aeval φ (monomial k c) m - aeval a ((monomial k c).map (ξ : Λ →+* O)) • m =
          (c - algebraMap O Λ (ξ c)) • (a ^ k • m) := by
        rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, hpow, sub_smul,
          hl (algebraMap O Λ (ξ c)), AlgHom.commutes, mul_smul]
        rfl
      rw [e]
      exact Submodule.smul_mem_smul (by show ξ _ = 0; simp) trivial
  refine ⟨p.map (ξ : Λ →+* O), (hp.map _).ne_zero, fun m => ?_⟩
  have := key p m
  rw [hev, LinearMap.zero_apply, zero_sub] at this
  exact neg_mem_iff.1 this

end UpperTheory.V.Th.EtaleDerivations

open UpperTheory.V.Th.EtaleDerivations UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.etOf :
    EtOf := by
  intro l _ L G0 n O _ _ _ _ _ r B _ _ _ u J D b y x hn hmap hgen hctrl
  let I : Ideal B :=
    { carrier := {a | ∀ m : b.M, a • m ∈ wtSub b x}
      add_mem' := fun ha hb m => by rw [add_smul]; exact add_mem (ha m) (hb m)
      zero_mem' := fun m => by rw [zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha m => by rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ }
  obtain ⟨c, hc, hψ⟩ := trPsi l L G0 n O y hn
  haveI := b.fin
  refine core x I {a : B | ∃ i g, a = u.D.lam i (MonoidAlgebra.single g 1)} (pairVals u)
    (fun a => integ b.lam b.smul_lam (x.comp b.lam) a) hctrl (hgen 2) ?_
  intro Y _ _ δ hδ htf h0 s hs
  rcases hs with hs | ⟨v, i, g, rfl⟩
  · exact h0 s hs
  · exact htf c _ hc (hψ G0 (Glob.Hom.refl G0) r B u x hmap Y δ hδ (fun g => h0 _ ⟨1, g, rfl⟩) v i g)
