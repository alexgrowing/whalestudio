import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbsRam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dx_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j : Ω →+* ℂ) :
    ∃ c : G ℚ Ω, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let s : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut (R := ℂ)) fun x => by simp
  exact ⟨s.restrictNormal Ω, fun x => s.restrictNormal_commutes Ω x⟩

private theorem dx_field {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [IsTotallyReal F]
    (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ H) (m : ℕ) (hm : Odd m)
    (hp : ∀ g ∈ F.fixingSubgroup, g ^ m ∈ H) :
    ∃ L : IntermediateField ℚ Ω, L.fixingSubgroup = H ∧ NumberField L ∧ IsTotallyReal L ∧ IsAbelianGalois ℚ L := by
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let N : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω) := ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  obtain ⟨L, hfix⟩ : ∃ L : IntermediateField ℚ Ω, L.fixingSubgroup = H :=
    ⟨_, InfiniteGalois.fixingSubgroup_fixedField N⟩
  subst hfix
  have : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 hH
  have hG : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois _).1 (Subgroup.Normal.of_commutator_le _ hc)
  have : NumberField L := NumberField.of_module_finite ℚ _
  have hker : ∀ g ∈ L.fixingSubgroup, UpperTheory.V.CF.resTo ℚ L Ω g = 1 := fun g hg => by
    refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
    rw [UpperTheory.V.CF.resTo_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ x.2
  have hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := UpperTheory.V.CF.resTo_surjective ℚ L Ω a
        obtain ⟨b, rfl⟩ := UpperTheory.V.CF.resTo_surjective ℚ L Ω b
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact hker _ (hc (Subgroup.commutator_mem_commutator trivial trivial))⟩ }
  refine ⟨L, rfl, this, ⟨fun w => ?_⟩, hab⟩
  letI : Algebra L ℂ := w.embedding.toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let j : Ω →ₐ[L] ℂ := IsAlgClosed.lift
  obtain ⟨c, hcj⟩ := dx_conj (j : Ω →+* ℂ)
  have h2 : c ^ 2 = 1 := AlgEquiv.ext fun x => (j : Ω →+* ℂ).injective (by
    rw [pow_two, AlgEquiv.mul_apply, hcj, hcj]; simp)
  have hF : c ∈ F.fixingSubgroup := (F.mem_fixingSubgroup_iff c).2 fun x hx => (j : Ω →+* ℂ).injective (by
    rw [hcj]
    have h := IsTotallyReal.complexEmbedding_isReal (K := F) ((j : Ω →+* ℂ).comp (algebraMap F Ω))
    exact RingHom.congr_fun h ⟨x, hx⟩)
  have hL : c ∈ L.fixingSubgroup := by
    obtain ⟨k, rfl⟩ := hm
    have := hp c hF
    rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at this
  rw [InfinitePlace.isReal_iff]
  refine RingHom.ext fun x => ?_
  have h3 := hcj x
  rw [(L.mem_fixingSubgroup_iff c).1 hL x x.2] at h3
  have h4 : (j : Ω →+* ℂ) x = w.embedding x := j.commutes x
  rw [h4] at h3
  exact h3.symm

private theorem dx_mu {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) (n : ℕ) : ∀ ζ : Ω, ζ ^ w ^ (n + 1) = 1 → (g ^ w ^ n) ζ = ζ := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    intro ζ hζ
    set h := g ^ w ^ n with hh
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hw)] at hζ
      exact zero_ne_one hζ
    have h1 : h (ζ ^ w) = ζ ^ w := ih _ (by rw [← pow_mul, ← pow_succ']; exact hζ)
    have h2 : (h ζ / ζ) ^ w = 1 := by rw [div_pow, ← map_pow, h1, div_self (pow_ne_zero _ h0)]
    have h3 : h (h ζ / ζ) = h ζ / ζ := ih _ (by rw [pow_succ', pow_mul, h2, one_pow])
    have h4 : ∀ k : ℕ, (h ^ k) ζ = (h ζ / ζ) ^ k * ζ := fun k => by
      induction k with
      | zero => simp
      | succ k ih2 =>
        rw [pow_succ', AlgEquiv.mul_apply, ih2, map_mul, map_pow, h3, pow_succ, mul_assoc, div_mul_cancel₀ _ h0]
    rw [pow_succ, pow_mul, ← hh, h4, h2, one_mul]

private theorem dx_ker {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l w : ℕ} (hl : l.Prime) (hw : w.Prime) (hne : w ≠ l)
    (θ : G ℚ Ω →* Multiplicative (ZMod l)) (ho : IsOpen (θ.ker : Set (G ℚ Ω)))
    (hu : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) (g : G ℚ Ω) (hg : ∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) : g ∈ θ.ker := by
  obtain ⟨n, hn⟩ := UpperTheory.V.CF.kwAbsRam Ω θ.ker ho (Abelianization.commutator_subset_ker θ) w hw.pos
    fun A hA => hu A fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hA
  have h1 := hn (g ^ w ^ n) fun ζ hζ => dx_mu hw.ne_zero g hg n ζ (by rw [pow_succ, pow_mul, hζ, one_pow])
  rw [MonoidHom.mem_ker, map_pow] at h1
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have h2 : θ g ^ l = 1 := by
    have := pow_card_eq_one (x := θ g)
    rwa [Fintype.card_multiplicative, ZMod.card] at this
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [Nat.Coprime.gcd_eq_one (((Nat.coprime_primes hw hl).2 hne).pow_left n), pow_one] at h3
  exact h3

private theorem dx_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (H : Subgroup (G ℚ Ω))
    (h : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) → g ∈ H) : IsOpen (H : Set (G ℚ Ω)) := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hf : Set.Finite {ζ : Ω | ζ ^ w = 1} := by
    refine (nthRootsFinset w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRootsFinset (Nat.pos_of_ne_zero hw) _).2 hζ
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => h g fun ζ hζ => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.V.Ws.diesEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, TameL l T.F → T.Ok → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∃ T' : Tower D, T.Le T' ∧ TameL l T'.F ∧ ∀ w ∈ W, Dies l w T'.F := by
  intro Ω _ _ _ l hl c D hD T ht hO W hW
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hne : ∀ w ∈ W, w ≠ l := by
    rintro w hw rfl
    have hT : w ∈ D.T := Finset.mem_insert_self _ _
    have h1 := (hW w hw).2 _ (hD.pl_over w hl.out) (hD.sg_frob w hT).1
    have h2 : D.rbar (D.sg w) = 1 := h1.1.2
    have h3 : D.om (D.sg w) = 1 := h1.2
    have h4 : Raw.bar D.al (D.sg w) = 1 := by
      have := congrFun (congrFun h2 2) 2
      simpa [Raw.rbar, Raw.r0, mapRep, diagRep, Raw.ps] using this
    have h5 := hD.om_bar (D.sg w)
    apply hD.condD w hT 0
    simp only [Raw.bar, Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, h3, inv_one, mul_one, Units.val_mul, map_mul,
      Units.val_one, map_one] at h4 h5
    rw [← h5, one_mul] at h4
    simpa using h4
  let U : ℕ → Subgroup (G ℚ Ω) := fun w => ⨅ θ : {θ : G ℚ Ω →* Multiplicative (ZMod l) // IsOpen (θ.ker : Set (G ℚ Ω)) ∧
    ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker}, θ.1.ker
  let V : Subgroup (G ℚ Ω) := ⨅ w : W, U w
  have hV : ∀ g, g ∈ V ↔ ∀ w ∈ W, ∀ θ : G ℚ Ω →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (G ℚ Ω)) →
      (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) → g ∈ θ.ker := fun g => by
    simp only [V, U, Subgroup.mem_iInf, Subtype.forall, and_imp]
  have hVo : IsOpen (V : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun w => dx_open (hW w w.2).1.ne_zero _ fun g hg =>
      Subgroup.mem_iInf.2 fun θ => dx_ker hl.out (hW w w.2).1 (hne w w.2) θ.1 θ.2.1 θ.2.2 g hg
  have hVl : ∀ g, g ^ l ∈ V := fun g => (hV _).2 fun w _ θ _ _ => by
    have := pow_card_eq_one (x := θ g)
    rwa [Fintype.card_multiplicative, ZMod.card, ← map_pow] at this
  have hFc : commutator (G ℚ Ω) ≤ T.F.fixingSubgroup := by
    have hab := T.abF
    have hn : Normal ℚ T.F := hab.toIsGalois.to_normal
    rw [← @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.F hn, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab.is_comm.comm _ _
  obtain ⟨L, hL, _, _, _⟩ := dx_field T.F (T.F.fixingSubgroup ⊓ V)
    ((IntermediateField.fixingSubgroup_isOpen _).inter hVo)
    (le_inf hFc fun g hg => (hV g).2 fun w _ θ _ _ => Abelianization.commutator_subset_ker θ hg) l
    (hl.out.odd_of_ne_two hD.l_odd) fun g hg => ⟨pow_mem hg _, hVl g⟩
  have hg0 : resQ T.F T.g0 ^ l ∈ L.fixingSubgroup := by
    rw [hL]
    exact ⟨pow_mem ((T.F.mem_fixingSubgroup_iff _).2 fun x hx => T.g0.commutes ⟨x, hx⟩) _, hVl _⟩
  let g1 : G L Ω := AlgEquiv.ofRingEquiv (f := (resQ T.F T.g0 ^ l).toRingEquiv)
    fun x => (L.mem_fixingSubgroup_iff _).1 hg0 x.1 x.2
  obtain ⟨T', h1, h2, h3, h4⟩ := mkTower D hD T.pr T.K L T.degK (hO.split l hD.l_mem) g1
  refine ⟨T', ⟨h1, h2, ?_, ⟨1, fun g hg => ?_⟩, ⟨1, ?_⟩⟩, fun A hA g hg => ?_, fun w hw θ ho hu g hg => ?_⟩
  · rw [h3, ← InfiniteGalois.fixedField_fixingSubgroup L]
    exact (IntermediateField.le_iff_le _ _).2 (hL ▸ inf_le_left)
  · rw [h3, hL, pow_one]
    exact ⟨pow_mem hg _, hVl g⟩
  · rw [h4, pow_one]
    rfl
  · obtain ⟨m, hm, hgm⟩ := ht A hA g hg
    refine ⟨m, hm, ?_⟩
    rw [h3, hL]
    refine ⟨hgm, pow_mem ((hV g).2 fun w hw θ _ hu => hu A (fun p hp hpA => ?_) hg) _⟩
    rw [Finset.mem_singleton.1 hp] at hpA
    obtain ⟨a, b, hab⟩ : IsCoprime (w : ℤ) (l : ℤ) :=
      Nat.Coprime.cast ((Nat.coprime_primes (hW w hw).1 hl.out).2 (hne w hw))
    have e : (a : Ω) * w + b * l = 1 := by exact_mod_cast hab
    have hi : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
    have := A.valuation.map_add_lt (x := (a : Ω) * w) (y := (b : Ω) * l) (g := 1)
      (by rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hi a) zero_le' hpA)
      (by rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hi b) zero_le' hA)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rw [h3, hL] at hg
    exact (hV g).1 hg.2 w hw θ ho hu
