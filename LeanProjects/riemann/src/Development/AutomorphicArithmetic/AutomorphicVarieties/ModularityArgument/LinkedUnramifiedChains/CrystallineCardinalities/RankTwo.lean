import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
import Mathlib.Algebra.Module.PID

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem tors_card {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)] (c : O)
    [Finite (O ⧸ Ideal.span {c})] :
    Nat.card {x : O ⧸ I // c • x = 0} ≤ Nat.card (O ⧸ Ideal.span {c}) := by
  let φ : (O ⧸ I) →ₗ[O] (O ⧸ I) := c • LinearMap.id
  have hφ : ∀ x, φ x = c • x := fun x => rfl
  have hker : Nat.card {x : O ⧸ I // c • x = 0} = Nat.card (LinearMap.ker φ) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [LinearMap.mem_ker, hφ]))
  have hA1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
  have hA2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
  have hq : Nat.card ((O ⧸ I) ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
    Nat.card_congr (φ.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
  have heq : Nat.card (LinearMap.ker φ) = Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
    rw [hq] at hA1
    have h : Nat.card (LinearMap.range φ) * Nat.card (LinearMap.ker φ) =
        Nat.card (LinearMap.range φ) * Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
      rw [mul_comm, ← hA1, hA2]
    exact Nat.eq_of_mul_eq_mul_left hpos h
  rw [hker, heq]
  let g : O →ₗ[O] (O ⧸ I) ⧸ LinearMap.range φ := (LinearMap.range φ).mkQ ∘ₗ (Submodule.mkQ I)
  have hg : Submodule.span O {c} ≤ LinearMap.ker g := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [g, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    rw [hφ, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  refine Nat.card_le_card_of_surjective ((Submodule.span O {c}).liftQ g hg) ?_
  intro z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨o, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨Submodule.Quotient.mk o, rfl⟩

private theorem hom_alt {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    (hfin : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}))
    (Q : Type) [AddCommGroup Q] [Module O Q] [Module.Finite O Q] :
    (∃ f g : Q →ₗ[O] O, ∃ x y : Q, f x = 1 ∧ g x = 0 ∧ f y = 0 ∧ g y = 1) ∨
    ∃ C : ℕ, ∀ I : Ideal O, Finite (O ⧸ I) → Nat.card (Q →ₗ[O] O ⧸ I) ≤ Nat.card (O ⧸ I) * C := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨E⟩⟩ := Module.equiv_free_prod_directSum O Q
  by_cases hn : 2 ≤ n
  · left
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    refine ⟨(Finsupp.lapply i0) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      (Finsupp.lapply i1) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      E.symm (Finsupp.single i0 1, 0), E.symm (Finsupp.single i1 1, 0), ?_, ?_, ?_, ?_⟩ <;>
    simp [i0, i1, Finsupp.single_apply]
  · right
    have hq : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
    haveI : ∀ i, Finite (O ⧸ Ideal.span {p i ^ e i}) := fun i => hfin _ (hq i)
    refine ⟨∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}), fun I hI => ?_⟩
    have htor : ∀ (φ : Q →ₗ[O] O ⧸ I) (i : ι), (p i ^ e i) • φ (E.symm (0,
        DirectSum.lof O ι (fun i => O ⧸ O ∙ p i ^ e i) i (Submodule.Quotient.mk 1))) = 0 := by
      intro φ i
      rw [← map_smul, ← map_smul, Prod.smul_mk, smul_zero, ← map_smul, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        map_zero, Prod.mk_zero_zero, map_zero, map_zero]
    let F : (Q →ₗ[O] O ⧸ I) → (Fin n → O ⧸ I) × ((i : ι) → {x : O ⧸ I // (p i ^ e i) • x = 0}) :=
      fun φ => (fun j => φ (E.symm (Finsupp.single j 1, 0)), fun i => ⟨_, htor φ i⟩)
    have hF : Function.Injective F := by
      intro φ ψ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have key : φ ∘ₗ E.symm.toLinearMap = ψ ∘ₗ E.symm.toLinearMap := by
        apply LinearMap.prod_ext
        · apply Finsupp.lhom_ext
          intro j b
          have hj := congrFun h1 j
          rw [← Finsupp.smul_single_one, map_smul, map_smul]
          exact congrArg (b • ·) hj
        · apply DirectSum.linearMap_ext
          intro i
          apply Submodule.linearMap_qext
          apply LinearMap.ext_ring
          exact congrArg Subtype.val (congrFun h2 i)
      ext x
      simpa using LinearMap.congr_fun key (E x)
    have hcard := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_pi, Nat.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hcard
    have hP : ∏ i, Nat.card {x : O ⧸ I // (p i ^ e i) • x = 0} ≤
        ∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}) :=
      Finset.prod_le_prod' (fun i _ => tors_card I (p i ^ e i))
    have hpos : 0 < Nat.card (O ⧸ I) := Nat.card_pos
    have hpow : Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) :=
      calc Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) ^ 1 := Nat.pow_le_pow_right hpos (by omega)
        _ = Nat.card (O ⧸ I) := pow_one _
    exact hcard.trans (Nat.mul_le_mul hpow hP)

private def rel {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R) : Submodule O R :=
  Submodule.span O ({x | ∃ a b, x = a * b - (ξ a • b + ξ b • a)} ∪ T)

private theorem rel_le {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R)
    {X : Type} [AddCommGroup X] [Module O X] (δ : R →ₗ[O] X) :
    rel ξ T ≤ LinearMap.ker δ ↔ (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0 := by
  unfold rel
  rw [Submodule.span_le, Set.union_subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b => ?_, fun a ha => LinearMap.mem_ker.mp (h2 ha)⟩
    have h := h1 ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, sub_eq_zero] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun a ha => LinearMap.mem_ker.mpr (h2 a ha)⟩
    rintro x ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, sub_eq_zero]
    exact h1 a b

private theorem rel_fin {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O)
    (T : Set R) : Module.Finite O (R ⧸ rel ξ T) := by
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (RingHom.ker ξ) : (RingHom.ker ξ).FG)
  have hS' : Ideal.span (S : Set R) = RingHom.ker ξ := hS
  have hrel : ∀ a b, a * b - (ξ a • b + ξ b • a) ∈ rel ξ T := fun a b =>
    Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)
  have hmm : ∀ a b, ξ a = 0 → ξ b = 0 → a * b ∈ rel ξ T := by
    intro a b ha hb
    have h := hrel a b
    rwa [ha, hb, zero_smul, zero_smul, add_zero, sub_zero] at h
  have hker : ∀ x, x ∈ Ideal.span (S : Set R) → x ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x hxS hx =>
      have hxk : ξ x = 0 := by
        have h := hxS
        rw [hS, RingHom.mem_ker] at h
        exact h
      have h1 : r • x = ξ r • x + (r - ξ r • 1) * x := by
        rw [smul_eq_mul, sub_mul, smul_mul_assoc, one_mul]
        abel
      rw [h1]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (hmm _ _ ?_ hxk))
      simp
  have h1 : (1 : R) ∈ rel ξ T := by
    have h := hrel 1 1
    rw [map_one, one_smul, mul_one] at h
    have h2 : (1 : R) - (1 + 1) = -1 := by ring
    rw [h2] at h
    exact neg_mem_iff.mp h
  have htop : ∀ r : R, r ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro r
    have hmem : r - ξ r • 1 ∈ Ideal.span (S : Set R) := by
      rw [hS', RingHom.mem_ker]
      simp
    rw [← sub_add_cancel r (ξ r • 1)]
    exact Submodule.add_mem _ (hker _ hmem) (Submodule.mem_sup_right (Submodule.smul_mem _ _ h1))
  haveI : Module.Finite O (Submodule.span O (S : Set R)) := Module.Finite.span_of_finite O S.finite_toSet
  refine Module.Finite.of_surjective ((rel ξ T).mkQ ∘ₗ (Submodule.span O (S : Set R)).subtype) ?_
  intro q
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.mp (htop r)
  refine ⟨⟨n, hn⟩, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
  rw [← hnm]
  exact (Submodule.Quotient.eq _).mpr (by simpa using hm)

end UpperTheory.V.Z.J

private theorem finite_linearMap_of_finite_module_finite {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N]
    [Module O N] [Module.Finite O M] [Finite N] : Finite (M →ₗ[O] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[O] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem UpperTheory.V.Z.J.rankTwo :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O) (T : Set R) (C : ℕ), (l : O) ≠ 0 → (∀ k, 0 < k → ∀ X : Set (R →ₗ[O] Ok l O k), X = {δ | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0} → X.Finite → Nat.card (Ok l O k) ^ 2 ≤ C * X.ncard) → ∃ δ δ' : R →ₗ[O] O, (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ (∀ a ∈ T, δ a = 0) ∧ (∀ a b, δ' (a * b) = ξ a • δ' b + ξ b • δ' a) ∧ (∀ a ∈ T, δ' a = 0) ∧ LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ R _ _ _ ξ T C hl hX
  obtain ⟨hOk, hfin, -, h2k, -, -, -⟩ := okFin l O hl
  haveI : Module.Finite O (R ⧸ rel ξ T) := rel_fin ξ T
  have hder : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (φ : (R ⧸ rel ξ T) →ₗ[O] Y),
      (∀ a b, (φ ∘ₗ (rel ξ T).mkQ) (a * b) =
        ξ a • (φ ∘ₗ (rel ξ T).mkQ) b + ξ b • (φ ∘ₗ (rel ξ T).mkQ) a) ∧
      ∀ a ∈ T, (φ ∘ₗ (rel ξ T).mkQ) a = 0 := by
    intro Y _ _ φ
    refine (rel_le ξ T (φ ∘ₗ (rel ξ T).mkQ)).mp ?_
    intro x hx
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  rcases hom_alt hfin (R ⧸ rel ξ T) with ⟨f, g, x, y, hfx, hgx, hfy, hgy⟩ | ⟨C', hC'⟩
  · obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨f ∘ₗ (rel ξ T).mkQ, g ∘ₗ (rel ξ T).mkQ, (hder f).1, (hder f).2, (hder g).1, (hder g).2, ?_⟩
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun δ => δ x0) hst
    have h2 := congrArg (fun δ => δ y0) hst
    simp [hfx, hgx, hfy, hgy] at h1 h2
    exact ⟨h1, h2⟩
  · exfalso
    obtain ⟨D, hD⟩ : ∃ D, D = C * C' := ⟨_, rfl⟩
    obtain ⟨k, hkD⟩ : ∃ k, k = D + 1 := ⟨_, rfl⟩
    have hk : 0 < k := by omega
    haveI := hOk k
    haveI : Finite ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := finite_linearMap_of_finite_module_finite
    let Φ : ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) → (R →ₗ[O] Ok l O k) := fun φ => φ ∘ₗ (rel ξ T).mkQ
    have hΦinj : Function.Injective Φ := fun φ ψ h => Submodule.linearMap_qext _ h
    have hrange : Set.range Φ = {δ : R →ₗ[O] Ok l O k | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧
        ∀ a ∈ T, δ a = 0} := by
      ext δ
      constructor
      · rintro ⟨φ, rfl⟩
        exact hder φ
      · intro hδ
        exact ⟨(rel ξ T).liftQ δ ((rel_le ξ T δ).mpr hδ), Submodule.liftQ_mkQ _ _ _⟩
    have hcard := hX k hk (Set.range Φ) hrange (Set.finite_range Φ)
    rw [Set.ncard_range_of_injective hΦinj] at hcard
    have hbound := hC' (Ideal.span {(l : O) ^ k}) (hOk k)
    have hpos : 0 < Nat.card (Ok l O k) := Nat.card_pos
    have h2 := h2k k
    have hle : Nat.card (Ok l O k) ≤ D := by
      have h3 : Nat.card (Ok l O k) * Nat.card (Ok l O k) ≤ Nat.card (Ok l O k) * D := by
        calc Nat.card (Ok l O k) * Nat.card (Ok l O k) = Nat.card (Ok l O k) ^ 2 := (sq _).symm
          _ ≤ C * Nat.card ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := hcard
          _ ≤ C * (Nat.card (Ok l O k) * C') := Nat.mul_le_mul_left _ hbound
          _ = Nat.card (Ok l O k) * D := by rw [hD]; ring
      exact Nat.le_of_mul_le_mul_left h3 hpos
    have h4 : k < 2 ^ k := Nat.lt_two_pow_self
    omega
