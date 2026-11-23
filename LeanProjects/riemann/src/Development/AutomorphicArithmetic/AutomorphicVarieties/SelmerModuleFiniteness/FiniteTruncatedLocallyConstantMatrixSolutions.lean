import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SolCnt
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section aux
open PowerSeries

private theorem fc_img {G H : Type} [AddCommGroup G] [AddCommGroup H] (ψ : G →+ H) (S : AddSubgroup G) :
    Nat.card S = Nat.card (S.map ψ) * Nat.card (S ⊓ ψ.ker : AddSubgroup G) := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (ψ.domRestrict S).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (ψ.domRestrict S)).toEquiv,
    AddMonoidHom.domRestrict_range, AddMonoidHom.ker_domRestrict] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun _ => rfl, fun _ => rfl⟩

private theorem fc_idx {G H : Type} [AddCommGroup G] [AddCommGroup H] (ψ : G →+ H) (S B : AddSubgroup G)
    [Finite S] (h : B ≤ S) (N : ℕ) (hN : Nat.card S ≤ Nat.card B * N) :
    Nat.card (S.map ψ) ≤ Nat.card (B.map ψ) * N := by
  have : Finite (S ⊓ ψ.ker : AddSubgroup G) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective (inf_le_left : S ⊓ ψ.ker ≤ S))
  have h1 : Nat.card (B ⊓ ψ.ker : AddSubgroup G) ≤ Nat.card (S ⊓ ψ.ker : AddSubgroup G) :=
    AddSubgroup.card_le_of_le (inf_le_inf_right _ h)
  rw [fc_img ψ S, fc_img ψ B] at hN
  refine Nat.le_of_mul_le_mul_right (hN.trans ?_) (Nat.card_pos (α := (S ⊓ ψ.ker : AddSubgroup G)))
  rw [mul_right_comm]
  exact Nat.mul_le_mul_left _ h1

private theorem fc_eqv {A C Y : Type} [CommRing A] [AddCommGroup C] [Module A C] [AddCommGroup Y] [Module A Y]
    (r : C →ₗ[A] Y) (T S : Submodule A C) (h : LinearMap.ker r = T) :
    Nonempty (S.map T.mkQ ≃ S.map r) := by
  subst h
  have hi : Function.Injective ((LinearMap.ker r).liftQ r le_rfl) := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have := Submodule.equivMapOfInjective _ hi (S.map (LinearMap.ker r).mkQ)
  rw [← Submodule.map_comp, Submodule.liftQ_mkQ] at this
  exact ⟨this.toEquiv⟩

private theorem fc_mem {A C : Type} [CommRing A] [AddCommGroup C] [Module A C] (a : A) (x : C) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule A C) ↔ ∃ c, a • c = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

variable {K : Type} [Field K]

private theorem fc_mk (m : ℕ) (a b : K⟦X⟧) :
    Ideal.Quotient.mk (Ideal.span {(X : K⟦X⟧) ^ m}) a = Ideal.Quotient.mk _ b ↔
      ∀ k < m, coeff k a = coeff k b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, X_pow_dvd_iff]
  simp [sub_eq_zero]

private theorem fc_lc {Γ : Type} [TopologicalSpace Γ] (m : ℕ) (f : Γ → K⟦X⟧) :
    (IsLocallyConstant fun g => Ideal.Quotient.mk (Ideal.span {(X : K⟦X⟧) ^ m}) (f g)) ↔
      ∀ k < m, IsLocallyConstant fun g => coeff k (f g) := by
  simp only [IsLocallyConstant.iff_eventually_eq, fc_mk]
  constructor
  · intro h k hk x
    exact (h x).mono fun y hy => hy k hk
  · intro h x
    have := (Finset.range m).eventually_all.2 fun k hk => h k (Finset.mem_range.1 hk) x
    exact this.mono fun y hy k hk => hy k (Finset.mem_range.2 hk)

private theorem fc_ac {Γ : Type} [TopologicalSpace Γ] (f : Γ → K⟦X⟧) :
    AdicCont (Ideal.span {(X : K⟦X⟧)}) f ↔ ∀ k, IsLocallyConstant fun g => coeff k (f g) := by
  have e : ∀ (N : ℕ) (I : Ideal K⟦X⟧), I = Ideal.span {(X : K⟦X⟧) ^ N} →
      ((IsLocallyConstant fun g => Ideal.Quotient.mk I (f g)) ↔
        ∀ k < N, IsLocallyConstant fun g => coeff k (f g)) := by
    rintro N _ rfl
    exact fc_lc N f
  exact ⟨fun h k => (e _ _ (Ideal.span_singleton_pow _ _)).1 (h (k + 1)) k (Nat.lt_succ_self k),
    fun h N => (e _ _ (Ideal.span_singleton_pow _ _)).2 fun k _ => h k⟩

variable {n : ℕ} {Γ Y : Type} [TopologicalSpace Γ] (φ : Γ → Y)

variable (K n) in
private def fcC : Submodule K⟦X⟧ (Y → Matrix (Fin n) (Fin n) K⟦X⟧) where
  carrier := {f | ∀ i j k, IsLocallyConstant fun g => coeff k (f (φ g) i j)}
  add_mem' ha hb i j k := by
    simp only [Pi.add_apply, Matrix.add_apply, map_add]
    exact (ha i j k).add (hb i j k)
  zero_mem' i j k := by
    simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
    exact IsLocallyConstant.const _
  smul_mem' c f hf i j k := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := (Finset.HasAntidiagonal.antidiagonal k).eventually_all.2 fun p _ => (hf i j p.2).eventually_eq x
    refine this.mono fun y hy => ?_
    simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, coeff_mul]
    exact Finset.sum_congr rfl fun p hp => by rw [hy p hp]

private theorem fc_memC (m : ℕ) (x : fcC K n φ) :
    x ∈ (Ideal.span {(X : K⟦X⟧) ^ m} • ⊤ : Submodule K⟦X⟧ (fcC K n φ)) ↔
      ∀ y i j, ∀ k < m, coeff k (x.1 y i j) = 0 := by
  rw [fc_mem]
  constructor
  · rintro ⟨c, rfl⟩ y i j
    exact X_pow_dvd_iff.1 ⟨c.1 y i j, rfl⟩
  · intro h
    refine ⟨⟨fun y i j => mk fun k => coeff (k + m) (x.1 y i j), fun i j k => ?_⟩, ?_⟩
    · simpa using x.2 i j (k + m)
    · ext y i j k
      change coeff k (X ^ m * mk fun k => coeff (k + m) (x.1 y i j)) = _
      rw [coeff_X_pow_mul']
      split_ifs with hk
      · simp [Nat.sub_add_cancel hk]
      · exact (h y i j k (not_le.1 hk)).symm

private theorem fc_complete : IsAdicComplete (Ideal.span {(X : K⟦X⟧)}) (fcC K n φ) where
  haus' x hx := by
    ext y i j k
    have := hx (k + 1)
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, sub_zero, fc_memC] at this
    simpa using this y i j k (Nat.lt_succ_self k)
  prec' f hf := by
    refine ⟨⟨fun y i j => mk fun k => coeff k ((f (k + 1)).1 y i j), fun i j k => ?_⟩, fun m => ?_⟩
    · simpa using (f (k + 1)).2 i j k
    · rw [SModEq.sub_mem, Ideal.span_singleton_pow, fc_memC]
      intro y i j k hk
      have := hf (show k + 1 ≤ m from hk)
      rw [SModEq.sub_mem, Ideal.span_singleton_pow, fc_memC] at this
      have := this y i j k (Nat.lt_succ_self k)
      change coeff k ((f (k + 1)).1 y i j - (f m).1 y i j) = 0 at this
      change coeff k ((f m).1 y i j - mk fun k => coeff k ((f (k + 1)).1 y i j)) = 0
      rw [map_sub, sub_eq_zero] at this ⊢
      rw [coeff_mk, this]

private theorem fc_memJ {J : Type} (a : K⟦X⟧) (x : J → K⟦X⟧) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule K⟦X⟧ (J → K⟦X⟧)) ↔ ∀ j, x j ∈ Ideal.span {a} := by
  rw [fc_mem]
  constructor
  · rintro ⟨c, rfl⟩ j
    exact Ideal.mem_span_singleton.2 ⟨c j, rfl⟩
  · intro h
    choose c hc using fun j => Ideal.mem_span_singleton.1 (h j)
    exact ⟨c, funext fun j => (hc j).symm⟩

private theorem fc_haus {J : Type} : IsHausdorff (Ideal.span {(X : K⟦X⟧)}) (J → K⟦X⟧) where
  haus' x hx := by
    ext j k
    have := hx (k + 1)
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, sub_zero, fc_memJ] at this
    simpa using X_pow_dvd_iff.1 (Ideal.mem_span_singleton.1 (this j)) k (Nat.lt_succ_self k)

variable (K n Y) in
private noncomputable def fcR (m : ℕ) : (Y → Matrix (Fin n) (Fin n) K⟦X⟧) →ₗ[K⟦X⟧]
    (Y → Matrix (Fin n) (Fin n) (K⟦X⟧ ⧸ Ideal.span {(X : K⟦X⟧) ^ m})) where
  toFun f y := (f y).map (Ideal.Quotient.mk _)
  map_add' f g := by ext y i j; simp
  map_smul' c f := by ext y i j; rfl

private theorem fc_ker (m : ℕ) : LinearMap.ker ((fcR K n Y m).comp (fcC K n φ).subtype) =
    (Ideal.span {(X : K⟦X⟧) ^ m} • ⊤ : Submodule K⟦X⟧ (fcC K n φ)) := by
  ext x
  rw [fc_memC, LinearMap.mem_ker]
  simp only [funext_iff, ← Matrix.ext_iff]
  refine forall₃_congr fun y i j => ?_
  have := fc_mk m (x.1 y i j) 0
  simp only [map_zero] at this
  exact this

private theorem fc_sol {J : Type} (Φ : (Y → Matrix (Fin n) (Fin n) K⟦X⟧) →ₗ[K⟦X⟧] (J → K⟦X⟧)) (m : ℕ)
    (fb : Y → Matrix (Fin n) (Fin n) (K⟦X⟧ ⧸ Ideal.span {(X : K⟦X⟧) ^ m})) :
    fb ∈ ((Ideal.span {(X : K⟦X⟧) ^ m} • ⊤ : Submodule K⟦X⟧ (J → K⟦X⟧)).comap
      (Φ.comp (fcC K n φ).subtype)).map ((fcR K n Y m).comp (fcC K n φ).subtype) ↔
    (∀ i j, IsLocallyConstant fun g => fb (φ g) i j) ∧ ∃ f : Y → Matrix (Fin n) (Fin n) K⟦X⟧,
      (∀ y, (f y).map (Ideal.Quotient.mk (Ideal.span {(X : K⟦X⟧) ^ m})) = fb y) ∧
      ∀ j, Φ f j ∈ Ideal.span {(X : K⟦X⟧) ^ m} := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i j => (fc_lc m fun g => f.1 (φ g) i j).2 fun k _ => f.2 i j k, f.1, fun y => rfl,
      (fc_memJ _ _).1 hf⟩
  · rintro ⟨h1, f, h2, h3⟩
    obtain rfl : fcR K n Y m f = fb := funext h2
    let f' : Y → Matrix (Fin n) (Fin n) K⟦X⟧ := fun y i j => mk fun k => if k < m then coeff k (f y i j) else 0
    have e : ∀ y i j, ∀ k < m, coeff k (f' y i j) = coeff k (f y i j) := fun y i j k hk => by
      simp [f', hk]
    refine ⟨⟨f', fun i j k => ?_⟩, ?_, ?_⟩
    · by_cases hk : k < m
      · simp only [e _ _ _ k hk]
        exact (fc_lc m fun g => f (φ g) i j).1 (h1 i j) k hk
      · simp only [f', coeff_mk, if_neg hk]
        exact IsLocallyConstant.const _
    · have : ∀ y i j, ∃ c, f' y i j - f y i j = X ^ m * c := fun y i j =>
        X_pow_dvd_iff.2 fun k hk => by rw [map_sub, e y i j k hk, sub_self]
      choose c hc using this
      have e2 : f' = f + (X : K⟦X⟧) ^ m • (fun y => Matrix.of (c y)) := by
        funext y i j
        exact sub_eq_iff_eq_add'.1 (hc y i j)
      change Φ f' ∈ (Ideal.span {(X : K⟦X⟧) ^ m} • ⊤ : Submodule K⟦X⟧ (J → K⟦X⟧))
      rw [e2, map_add, map_smul]
      exact add_mem ((fc_memJ _ _).2 h3) ((fc_mem _ _).2 ⟨_, rfl⟩)
    · ext y i j
      exact (fc_mk m _ _).2 (e y i j)

end aux

theorem UpperTheory.finite_truncated_locallyConstant_matrix_solutions :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ) (Γ X J : Type) [TopologicalSpace Γ] (φ : Γ → X) (Φ : (X → Matrix (Fin n) (Fin n) (PowerSeries K)) →ₗ[PowerSeries K] (J → PowerSeries K)) (B : Submodule (PowerSeries K) (X → Matrix (Fin n) (Fin n) (PowerSeries K))) (Sol : ∀ m : ℕ, Set (X → Matrix (Fin n) (Fin n) (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}))), (∀ m fb, fb ∈ Sol m ↔ (∀ i j, IsLocallyConstant fun g => fb (φ g) i j) ∧ ∃ f : X → Matrix (Fin n) (Fin n) (PowerSeries K), (∀ y, (f y).map (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) = fb y) ∧ ∀ j, Φ f j ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) → (Sol 1).Finite → (∀ f ∈ B, (∀ i j, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) fun g => f (φ g) i j) ∧ Φ f = 0) → (∀ f : X → Matrix (Fin n) (Fin n) (PowerSeries K), (∀ i j, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) fun g => f (φ g) i j) → Φ f = 0 → ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • f ∈ B) → ∃ e : ℕ, ∀ m : ℕ, (Sol m).Finite ∧ ((fun fb => fb ∘ φ) '' Sol m).ncard ≤ ((fun (f : X → Matrix (Fin n) (Fin n) (PowerSeries K)) (g : Γ) => (f (φ g)).map (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}))) '' (B : Set _)).ncard * Nat.card K ^ e := by
  intro K _ _ n Γ Y J _ φ Φ B Sol hS h1 hB hBs
  have eK : IsLocalRing.ResidueField (PowerSeries K) ≃+* K := PowerSeries.residueFieldOfPowerSeries
  have : Finite (IsLocalRing.ResidueField (PowerSeries K)) := Finite.of_equiv _ eK.toEquiv.symm
  have hS' : ∀ m, Sol m = ((Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} • ⊤ :
      Submodule (PowerSeries K) (J → PowerSeries K)).comap (Φ.comp (fcC K n φ).subtype)).map
        ((fcR K n Y m).comp (fcC K n φ).subtype) := fun m => by
    ext fb
    rw [hS, SetLike.mem_coe, fc_sol]
  have hBC : B ≤ fcC K n φ := fun f hf i j => (fc_ac _).1 ((hB f hf).1 i j)
  have hker : B.comap (fcC K n φ).subtype ≤ LinearMap.ker (Φ.comp (fcC K n φ).subtype) :=
    fun f hf => (hB f.1 hf).2
  obtain ⟨-, e, he⟩ := UpperTheory.V.Pa.solCnt (PowerSeries K) (fcC K n φ) (J → PowerSeries K) PowerSeries.X
    (Φ.comp (fcC K n φ).subtype) (B.comap (fcC K n φ).subtype) PowerSeries.X_irreducible
    (fun y hy => by
      refine Subtype.ext (funext fun a => funext fun i => funext fun j => ?_)
      exact (mul_eq_zero.1 (congrFun (congrFun (congrFun (congrArg Subtype.val hy) a) i) j)).resolve_left
        PowerSeries.X_ne_zero)
    (fun y hy => funext fun j => (mul_eq_zero.1 (congrFun hy j)).resolve_left PowerSeries.X_ne_zero)
    inferInstance (fc_complete φ) fc_haus
    (by
      rw [hS'] at h1
      obtain ⟨q⟩ := fc_eqv _ _ ((Ideal.span {(PowerSeries.X : PowerSeries K) ^ 1} • ⊤ :
        Submodule (PowerSeries K) (J → PowerSeries K)).comap (Φ.comp (fcC K n φ).subtype)) (fc_ker φ 1)
      have := h1.to_subtype
      have := Finite.of_equiv _ q.symm
      rwa [pow_one] at this)
    hker (fun z hz => hBs z.1 (fun i j => (fc_ac _).2 (z.2 i j)) hz)
  refine ⟨e, fun m => ?_⟩
  obtain ⟨hf, hc⟩ := he m
  obtain ⟨q⟩ := fc_eqv _ _ ((Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} • ⊤ :
    Submodule (PowerSeries K) (J → PowerSeries K)).comap (Φ.comp (fcC K n φ).subtype)) (fc_ker φ m)
  obtain ⟨q'⟩ := fc_eqv _ _ (B.comap (fcC K n φ).subtype) (fc_ker φ m)
  rw [Nat.card_congr q, Nat.card_congr q', Nat.card_congr eK.toEquiv] at hc
  have hf' := Finite.of_equiv _ q
  rw [hS']
  refine ⟨Set.toFinite _, ?_⟩
  have key := fc_idx (LinearMap.funLeft (PowerSeries K) _ φ).toAddMonoidHom (Submodule.toAddSubgroup _)
    (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup_mono (Submodule.map_mono (hker.trans fun f hf => by
      rw [Submodule.mem_comap, LinearMap.mem_ker.1 hf]; exact zero_mem _))) _ hc
  rw [Submodule.map_comp _ _ (B.comap _), Submodule.map_comap_subtype, inf_eq_right.2 hBC] at key
  refine le_of_le_of_eq key ?_
  congr 1
  rw [← Nat.card_coe_set_eq]
  congr 2
  funext x
  apply propext
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
