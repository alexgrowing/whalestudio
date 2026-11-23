import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_eigenvector_tame_inertia {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ p) (hφ : IsOpenEmbedding φ) (c : ↥((Iq p).comap φ) →* (Om p)ˣ) (m : ℕ) (hm : ¬ p ∣ m)
    (hc : ∀ τ, c τ ^ m = 1) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hUc : ∀ τ : ↥((Iq p).comap φ), (τ : G) ∈ U → c τ = 1) :
    ∃ x : Om p, x ≠ 0 ∧ ∀ τ : ↥((Iq p).comap φ), φ τ x = c τ * x := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  haveI : NeZero m := ⟨hm0⟩
  have hfix : ∀ τ σ : ↥((Iq p).comap φ), φ τ (c σ : Om p) = c σ := fun τ σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 τ.2 _
      (IntermediateField.subset_adjoin _ _ ⟨m, Nat.pos_of_ne_zero hm0, hm, by
        rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩)
  have hle : c.range ≤ rootsOfUnity m (Om p) := by
    rintro _ ⟨τ, rfl⟩
    exact hc τ
  haveI : Finite c.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  haveI : Fintype c.range := Fintype.ofFinite _
  let J : Subgroup (GQ p) := (c.ker.map ((Iq p).comap φ).subtype).map φ
  have hJ : IsClosed (J : Set (GQ p)) := by
    have h1 : IsOpen (c.ker : Set ↥((Iq p).comap φ)) :=
      Subgroup.isOpen_mono (H₁ := U.subgroupOf _) (fun τ hτ => hUc τ hτ) (hU.preimage continuous_subtype_val)
    have h2 := c.ker.isClosed_of_isOpen h1
    have h3 : IsClosed (((Iq p).comap φ : Subgroup G) : Set G) := (iqBasic p).2.1.preimage hφ.continuous
    have h4 := h3.isClosedMap_subtype_val _ h2
    have h5 : IsClosedEmbedding φ := ⟨hφ.isEmbedding, by
      rw [← MonoidHom.coe_range]
      exact φ.range.isClosed_of_isOpen (by rw [MonoidHom.coe_range]; exact hφ.isOpen_range)⟩
    exact h5.isClosedMap _ h4
  have hJ' : (IntermediateField.fixedField J).fixingSubgroup = J :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨J, hJ⟩
  have key : ∀ τ σ : ↥((Iq p).comap φ), c τ = c σ ↔
      ∀ z : ↥(IntermediateField.fixedField J), φ τ (z : Om p) = φ σ (z : Om p) := by
    intro τ σ
    have h1 : c τ = c σ ↔ φ (σ⁻¹ * τ : ↥((Iq p).comap φ)) ∈ J := by
      constructor
      · intro h
        exact ⟨_, ⟨σ⁻¹ * τ, by simp [h], rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
        have h2 : a = σ⁻¹ * τ := Subtype.ext (hφ.injective h)
        rw [h2] at ha
        have h3 : c (σ⁻¹ * τ) = 1 := ha
        rw [map_mul, map_inv, inv_mul_eq_one] at h3
        exact h3.symm
    rw [h1, ← hJ', IntermediateField.mem_fixingSubgroup_iff]
    have h4 : ∀ z : Om p, φ (σ⁻¹ * τ : ↥((Iq p).comap φ)) z = z ↔ φ τ z = φ σ z := by
      intro z
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, AlgEquiv.mul_apply]
      exact (φ σ).symm_apply_eq
    rw [hJ']
    exact ⟨fun h z => (h4 _).1 (h z z.2), fun h z hz => (h4 _).2 (h ⟨z, hz⟩)⟩
  choose s hs using fun q : c.range => q.2
  let F : c.range → (↥(IntermediateField.fixedField J) →* Om p) := fun q =>
    ((φ (s q) : Om p →+* Om p).comp (IntermediateField.fixedField J).subtype).toMonoidHom
  have hF : Function.Injective F := by
    intro q q' h
    refine Subtype.ext ?_
    rw [← hs, ← hs, key]
    exact fun z => DFunLike.congr_fun h z
  have hli := (linearIndependent_monoidHom ↥(IntermediateField.fixedField J) (Om p)).comp F hF
  rw [Fintype.linearIndependent_iff] at hli
  have hne : ¬ (∑ q : c.range, (((q : (Om p)ˣ)⁻¹ : (Om p)ˣ) : Om p) • (F q : _ → Om p)) = 0 := fun h =>
    Units.ne_zero _ (hli _ h 1)
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  refine ⟨_, hz, fun τ => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (c.rangeRestrict τ)) _ _ fun q => ?_
  have e1 : φ τ (((q : (Om p)ˣ)⁻¹ : (Om p)ˣ) : Om p) = (((q : (Om p)ˣ)⁻¹ : (Om p)ˣ) : Om p) := by
    rw [← hs, ← map_inv, hfix]
  have e2 : φ τ (F q z) = F (c.rangeRestrict τ * q) z := by
    have := (key (τ * s q) (s (c.rangeRestrict τ * q))).1 (by rw [map_mul, hs, hs]; rfl) z
    rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply] at this
    exact this
  rw [e1, e2, Equiv.coe_mulLeft, ← mul_assoc, ← Units.val_mul]
  congr 2
  simp [mul_comm]

private theorem tame_character_conjugation {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ p) (hφ : IsOpenEmbedding φ) (c : ↥((Iq p).comap φ) →* (Om p)ˣ) (m : ℕ) (hm : ¬ p ∣ m)
    (hc : ∀ τ, c τ ^ m = 1) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hUc : ∀ τ : ↥((Iq p).comap φ), (τ : G) ∈ U → c τ = 1) (g : G) (τ τ' : ↥((Iq p).comap φ))
    (h : (τ' : G) = g * τ * g⁻¹) : (c τ' : Om p) = φ g (c τ) := by
  obtain ⟨x, hx0, hx⟩ := exists_eigenvector_tame_inertia φ hφ c m hm hc U hU hUc
  have hc' : ∀ τ, (c τ : Om p) ^ m = 1 := fun τ => by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have e1 : φ τ ((φ g)⁻¹ x) = (φ g)⁻¹ (c τ') * (φ g)⁻¹ x := by
    rw [← map_mul, ← hx, h, map_mul, map_mul, map_inv, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  have hn : ∀ (σ : GQ p) (y : Om p), ‖σ y‖ = ‖y‖ := KStar.IdealValuations.norm_aut_and_roots.1
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hy : ‖(φ g)⁻¹ x / x‖ = 1 := by rw [norm_div, hn, div_self (norm_ne_zero_iff.2 hx0)]
  have h1 := ((iqBasic p).2.2.1 _).1 τ.2 _ hy.le
  have hτ : ‖(c τ : Om p)‖ = 1 := by
    have := congrArg norm (hc' τ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this
  have e2 : φ τ ((φ g)⁻¹ x / x) - (φ g)⁻¹ x / x =
      ((φ g)⁻¹ (c τ') - c τ) * ((φ g)⁻¹ x / x) / c τ := by
    rw [map_div₀, e1, hx]
    have := (c τ).ne_zero
    field_simp
  rw [e2, norm_div, norm_mul, hy, hτ, mul_one, div_one] at h1
  have h2 := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hc', map_one]) (hc' τ) h1
  rw [← h2, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem cyclotomic_congruence_fixed_root {p l : ℕ} [Fact p.Prime] [Fact l.Prime] (σ : GQ p) (x : Om p) (k : ℕ)
    (hx : x ^ l ^ k = 1) (hx1 : x ≠ 1) (h : σ x = x) : (l : ℤ_[l]) ∣ (cyc p l σ : ℤ_[l]) - 1 := by
  have hl : l.Prime := Fact.out
  obtain ⟨y, hy, hy1, h⟩ : ∃ y : Om p, y ^ l ^ 1 = 1 ∧ y ≠ 1 ∧ σ y = y := by
    induction k with
    | zero => exact absurd (by simpa using hx) hx1
    | succ k ih =>
      by_cases h0 : x ^ l ^ k = 1
      · exact ih h0
      · exact ⟨x ^ l ^ k, by rw [← pow_mul, ← pow_add, hx], h0, by rw [map_pow, h]⟩
  have hs := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (GQ p) (Om p) σ) y hy
  have hs' : σ y = y ^ (PadicInt.toZModPow 1 (cyc p l σ : ℤ_[l])).val := hs
  have ho : orderOf y = l ^ 1 := by
    rw [pow_one] at hy ⊢
    exact orderOf_eq_prime hy hy1
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h4 : (PadicInt.toZModPow 1 (cyc p l σ : ℤ_[l])).val ≡ 1 [MOD l ^ 1] := by
    have := (isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos _, hy⟩).pow_eq_pow_iff_modEq.mp
      (hs'.symm.trans (h.trans (pow_one y).symm))
    rwa [ho] at this
  have h5 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h5
  rw [← pow_one (l : ℤ_[l]), ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    h5, map_one, sub_self]

private theorem matrix_pow_l_congruence_succ {A : Type} [CommRing A] (I : Ideal A) {l : ℕ} (hl : (l : A) ∈ I) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (c : A) (k : ℕ)
    (h : ∀ i j, (M - Matrix.scalar (Fin n) c) i j ∈ I ^ (k + 1)) :
    ∀ i j, (M ^ l - Matrix.scalar (Fin n) (c ^ l)) i j ∈ I ^ (k + 2) := by
  intro i j
  have hcomm : Commute M (Matrix.scalar (Fin n) c) := (Matrix.scalar_commute c (fun _ => Commute.all _ _) M).symm
  rw [map_pow, ← hcomm.geom_sum₂_mul, Matrix.mul_apply, pow_succ' I (k + 1)]
  refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul ?_ (h a j)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix (Matrix.scalar (Fin n) c) := by
    rw [← sub_eq_zero, ← map_sub]
    ext a b
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_le_self (Nat.succ_ne_zero k) (h a b))
  have h2 : (Ideal.Quotient.mk I).mapMatrix
      (∑ i ∈ Finset.range l, M ^ i * Matrix.scalar (Fin n) c ^ (l - 1 - i)) = 0 := by
    simp only [map_sum, map_mul, map_pow, h1]
    rw [geom_sum₂_self, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul (A ⧸ I), ← map_natCast (Ideal.Quotient.mk I),
      Ideal.Quotient.eq_zero_iff_mem.2 hl, zero_smul]
  exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h2 i) a)

private theorem matrix_pow_l_iterate_congruence {A : Type} [CommRing A] (I : Ideal A) {l : ℕ} (hl : (l : A) ∈ I) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (c : A) (h : ∀ i j, (M - Matrix.scalar (Fin n) c) i j ∈ I) (k : ℕ) :
    ∀ i j, (M ^ l ^ k - Matrix.scalar (Fin n) (c ^ l ^ k)) i j ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ l, pow_mul, pow_mul]
    exact matrix_pow_l_congruence_succ I hl _ _ k ih

private theorem unipotent_residue_pow_mod_maximal {A : Type} [CommRing A] [IsLocalRing A] {l : ℕ} [Fact l.Prime]
    [CharP (IsLocalRing.ResidueField A) l] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (c : A)
    (h : (M.map (IsLocalRing.residue A)).charpoly = (Polynomial.X - Polynomial.C (IsLocalRing.residue A c)) ^ n) :
    ∀ i j, (M ^ l ^ n - Matrix.scalar (Fin n) (c ^ l ^ n)) i j ∈ IsLocalRing.maximalIdeal A := by
  intro i j
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h1 := (M.map (IsLocalRing.residue A)).aeval_self_charpoly
  rw [h, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h1
  have h2 : (M.map (IsLocalRing.residue A) - algebraMap _ _ (IsLocalRing.residue A c)) ^ l ^ n = 0 :=
    pow_eq_zero_of_le (Nat.lt_pow_self hl.one_lt).le h1
  rw [sub_pow_char_pow_of_commute l n (Algebra.commute_algebraMap_right _ _)] at h2
  have h3 : (IsLocalRing.residue A).mapMatrix (M ^ l ^ n - Matrix.scalar (Fin n) (c ^ l ^ n)) = 0 := by
    rw [← h2, map_sub, map_pow, map_pow, map_pow, RingHom.mapMatrix_apply]
    congr 2
    ext a b
    by_cases hab : a = b <;> simp [Matrix.algebraMap_eq_diagonal, hab]
  exact (IsLocalRing.residue_eq_zero_iff _).1 (congrFun (congrFun h3 i) j)

private theorem exists_nontrivial_character_pgroup {H : Type} [Group H] [Finite H] [Nontrivial H] {l : ℕ} [Fact l.Prime] (hH : IsPGroup l H)
    (F : Type) [Field F] [IsAlgClosed F] [CharZero F] : ∃ (ψ : H →* Fˣ) (a : H), ψ a ≠ 1 := by
  haveI := hH.isNilpotent
  have h1 := IsSolvable.commutator_lt_top_of_nontrivial H
  obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt h1
  have h2 : Abelianization.of a ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
  haveI : NeZero (Monoid.exponent (Abelianization H)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization H) F h2
  exact ⟨ψ.comp Abelianization.of, a, hψ⟩

private theorem eq_zero_of_twisted_commutation {A : Type} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] {n : ℕ}
    (M Y : Matrix (Fin n) (Fin n) A) (c x : A) (hc : IsUnit c) (hx : IsUnit (x - 1))
    (h : ∀ i j, (M - Matrix.scalar (Fin n) c) i j ∈ IsLocalRing.maximalIdeal A) (hY : x • (M * Y) = Y * M) : Y = 0 := by
  have e : ((x - 1) * c) • Y = Y * (M - Matrix.scalar (Fin n) c) - x • ((M - Matrix.scalar (Fin n) c) * Y) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub, hY, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
      ← Matrix.smul_eq_mul_diagonal]
    module
  have key : ∀ N : ℕ, ∀ i j, Y i j ∈ IsLocalRing.maximalIdeal A ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro i j
      rw [← Ideal.unit_mul_mem_iff_mem _ (hx.mul hc)]
      have e' := congrFun (congrFun e i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply] at e' h
      rw [e']
      refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ ?_)
      · rw [pow_succ]
        exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih _ _) (h _ _)
      · rw [pow_succ']
        exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (h _ _) (ih _ _)
  ext i j
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) inferInstance _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key N i j

theorem UpperTheory.V.Loc.v0b :
    ∀ {p l : ℕ} [Fact p.Prime] [Fact l.Prime], p ≠ l → ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ p) (hφ : IsOpenEmbedding φ) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Finite (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) l] [Algebra ℤ_[l] A] (κ : G →* (IsLocalRing.ResidueField A)ˣ), (∀ g, φ g ∈ Iq p → κ g = 1) → (∃ g, IsLocalRing.residue A (cycA p l A (φ g) : A) ≠ 1) → ∀ {n : ℕ} (r : G →* GL (Fin n) A), (∀ (N : ℕ) i j, IsLocallyConstant fun g => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ N) ((r g : Matrix (Fin n) (Fin n) A) i j)) → (∀ g, ((r g : Matrix (Fin n) (Fin n) A).map (IsLocalRing.residue A)).charpoly = (Polynomial.X - Polynomial.C (κ g : IsLocalRing.ResidueField A)) ^ n) → (∀ g, φ g ∈ Iq p → r g = 1) ∧ ∀ (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (X : Matrix (Fin n) (Fin n) K), (∀ g, algebraMap A K (cycA p l A (φ g) : A) • ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A K) * X) = X * (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A K)) → X = 0 := by
  intro p l _ _ hpl G _ _ _ φ hφ A _ _ _ _ _ _ _ κ hκ ⟨g, hg⟩ n r hr hch
  have hl : l.Prime := Fact.out
  have hp : p.Prime := Fact.out
  have hlm : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hgk : ∀ k : ℕ, IsLocalRing.residue A (cycA p l A (φ (g ^ l ^ k)) : A) ≠ 1 := by
    intro k h
    rw [map_pow, map_pow, Units.val_pow_eq_pow_val, map_pow, ← sub_eq_zero, ← one_pow (l ^ k),
      ← sub_pow_char_pow] at h
    exact hg (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 h))
  have hpow : ∀ (a : G) (c : A), IsLocalRing.residue A c = κ a → ∀ N i j,
      ((r (a ^ l ^ (n + N)) : Matrix (Fin n) (Fin n) A) - Matrix.scalar (Fin n) (c ^ l ^ (n + N))) i j ∈
        IsLocalRing.maximalIdeal A ^ (N + 1) := by
    intro a c hc N
    rw [map_pow, Units.val_pow_eq_pow_val, pow_add l, pow_mul, pow_mul]
    exact matrix_pow_l_iterate_congruence _ hlm _ _ (unipotent_residue_pow_mod_maximal _ c (by rw [hch, hc])) N
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (κ g : IsLocalRing.ResidueField A)
  refine ⟨fun τ hτ => ?_, fun K _ _ _ X hX => ?_⟩
  · have main : ∀ N : ℕ, Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ N)) (r τ) = 1 := by
      intro N
      haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := inferInstanceAs (Finite (IsLocalRing.ResidueField A))
      haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A ^ N) :=
        Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
      let ρ : G →* GL (Fin n) (A ⧸ IsLocalRing.maximalIdeal A ^ N) :=
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ N))).comp r
      have hρ : ∀ (a : G) (c : A), IsLocalRing.residue A c = κ a →
          (ρ (a ^ l ^ (n + N))).val =
            Matrix.scalar (Fin n) (Ideal.Quotient.mk _ (c ^ l ^ (n + N))) := by
        intro a c hc
        ext i j
        have h1 := Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (Nat.le_succ N) (hpow a c hc N i j))
        refine h1.trans ?_
        by_cases hab : i = j <;> simp [hab]
      have hU : IsOpen (ρ.ker : Set G) := by
        have : (ρ.ker : Set G) = ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ N)
            ((r g : Matrix (Fin n) (Fin n) A) i j)) ⁻¹' {(1 : Matrix (Fin n) (Fin n) _) i j} := by
          ext a
          simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
          rw [Units.ext_iff, ← Matrix.ext_iff]
          rfl
        rw [this]
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hr N i j _
      let ρ' := ρ.comp ((Iq p).comap φ).subtype
      have h1 : ∀ a : ↥((Iq p).comap φ), ρ'.rangeRestrict a ^ l ^ (n + N) = 1 := by
        intro a
        refine Subtype.ext (Units.ext ?_)
        have := hρ a 1 (by rw [hκ a a.2, map_one, Units.val_one])
        rw [one_pow, map_one, map_one, map_pow] at this
        exact this
      have hP : IsPGroup l ρ'.range := by
        rintro ⟨_, a, rfl⟩
        exact ⟨_, h1 a⟩
      by_contra hne
      haveI : Nontrivial ρ'.range := ⟨⟨ρ'.rangeRestrict ⟨τ, hτ⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
      obtain ⟨ψ, ⟨_, a, rfl⟩, ha⟩ := exists_nontrivial_character_pgroup hP (Om p)
      have hcm : ∀ b, (ψ.comp ρ'.rangeRestrict) b ^ l ^ (n + N) = 1 := fun b => by
        rw [MonoidHom.comp_apply, ← map_pow, h1, map_one]
      let a' : ↥((Iq p).comap φ) := ⟨g ^ l ^ (n + N) * a * (g ^ l ^ (n + N))⁻¹,
        ((iqBasic p).1.comap φ).conj_mem _ a.2 _⟩
      have h2 := tame_character_conjugation φ hφ (ψ.comp ρ'.rangeRestrict) (l ^ (n + N))
        (fun h => hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow h))) hcm ρ.ker hU
        (fun b hb => by
          rw [MonoidHom.comp_apply, show ρ'.rangeRestrict b = 1 from Subtype.ext hb, map_one])
        (g ^ l ^ (n + N)) a a' rfl
      have h3 : ρ'.rangeRestrict a' = ρ'.rangeRestrict a := by
        refine Subtype.ext ?_
        change ρ (g ^ l ^ (n + N) * a * (g ^ l ^ (n + N))⁻¹) = ρ a
        rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, hρ g c hc]
        exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
      rw [MonoidHom.comp_apply, h3, ← MonoidHom.comp_apply] at h2
      obtain ⟨y, hy⟩ := cyclotomic_congruence_fixed_root (l := l) _ _ (n + N) (by rw [← Units.val_pow_eq_pow_val]; exact congrArg Units.val (hcm a))
        (fun h => ha (Units.ext h)) h2.symm
      apply hgk (n + N)
      change IsLocalRing.residue A (algebraMap ℤ_[l] A (cyc p l (φ (g ^ l ^ (n + N))) : ℤ_[l])) = 1
      rw [sub_eq_iff_eq_add.1 hy]
      simp
    ext i j
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal A) inferInstance _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    have := Matrix.ext_iff.2 (congrArg Units.val (main N)) i j
    refine this.trans ?_
    by_cases hab : i = j <;> simp [hab]
  · obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
      (fun x : Fin n × Fin n => X x.1 x.2)
    choose y hy using hb
    have hY : (Matrix.of fun i j => y (i, j)).map (algebraMap A K) = algebraMap A K b • X := by
      ext i j
      simp [hy, Algebra.smul_def]
    have h0 := eq_zero_of_twisted_commutation (r (g ^ l ^ (n + 0)) : Matrix (Fin n) (Fin n) A) (Matrix.of fun i j => y (i, j))
      (c ^ l ^ (n + 0)) (cycA p l A (φ (g ^ l ^ (n + 0))) : A)
      (IsUnit.pow _ ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rw [hc]; exact Units.ne_zero _)))
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by
        rw [map_sub, map_one, sub_ne_zero]; exact hgk _))
      (by simpa using hpow g c hc 0) (by
        apply Matrix.map_injective (IsFractionRing.injective A K)
        beta_reduce
        rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul, hY, Matrix.mul_smul, Matrix.smul_mul, smul_comm, hX])
    rw [h0, Matrix.map_zero _ (map_zero _)] at hY
    exact (smul_eq_zero.1 hY.symm).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
