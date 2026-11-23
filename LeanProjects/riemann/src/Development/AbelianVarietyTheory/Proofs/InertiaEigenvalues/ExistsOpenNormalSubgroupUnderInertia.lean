import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.TwistDet

namespace GlobalTheory.ResSel.SmallSub

theorem exists_fix_roots {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    (hn : n ≠ 0) : ∃ K : Subgroup (G F Ω), IsOpen (K : Set (G F Ω)) ∧ (∀ a b : G F Ω, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
      ∀ g ∈ K, ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero n := ⟨hn⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hp : ∀ ζ : Ω, ζ ^ n = 1 → ∃ k : ℕ, ξ ^ k = ζ := fun ζ h => by
    obtain ⟨k, -, hk⟩ := hξ.eq_pow_of_pow_eq_one h
    exact ⟨k, hk⟩
  have hc : ∀ a b : G F Ω, a (b ξ) = b (a ξ) := fun a b => by
    obtain ⟨j, hj⟩ := hp (a ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    obtain ⟨k, hk⟩ := hp (b ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    conv_lhs => rw [← hk, map_pow, ← hj]
    conv_rhs => rw [← hj, map_pow, ← hk]
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨MulAction.stabilizer (G F Ω) ξ, stabilizer_isOpen_of_isIntegral ξ, fun a b => ?_, fun g hg ζ h => ?_⟩
  · show a (b (a⁻¹ (b⁻¹ ξ))) = ξ
    rw [hc a⁻¹ b⁻¹, mul_inv_apply, mul_inv_apply]
  · obtain ⟨k, rfl⟩ := hp ζ h
    have : g ξ = ξ := hg
    rw [map_pow, this]

theorem normal_of_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} (h : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ K) : K.Normal :=
  ⟨fun k hk g => by simpa using K.mul_mem (h g k) hk⟩

theorem comm_mem_ker {Γ A : Type} [Group Γ] [CommGroup A] (φ : Γ →* A) (a b : Γ) : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
  simp [MonoidHom.mem_ker]

theorem isOpen_ideal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) {I : Ideal O} (hI : I ≠ ⊥) : IsOpen (I : Set O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have := (isAdic_iff.1 h).1 n
  rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at this

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  apply h1
  have := congrArg (phiK X i 1) h
  simpa using this

theorem l_mem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem exists_eps : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧ (∀ a b : GE N, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
    ∀ g ∈ K, IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  refine ⟨((Units.map (IsLocalRing.residue (X.O0 i)).toMonoidHom).comp (eps0 X i)).ker, ?_, comm_mem_ker _,
    fun g hg => congrArg Units.val hg⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g : GE N => ‖((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1‖ :=
    ((Units.continuous_val.comp (continuous_cycZ D.host.E N.Om (X.l i))).sub continuous_const).norm
  refine Filter.mem_of_superset ((isOpen_lt hc (continuous_const (y := (1 : ℝ)))).mem_nhds (by simp)) fun g hg => ?_
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hg
  apply Units.ext
  change IsLocalRing.residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
  rw [sub_eq_iff_eq_add.1 hc, map_add, map_add, map_one, map_one, map_mul, map_natCast, map_mul,
    (IsLocalRing.residue_eq_zero_iff _).2 (l_mem X i), zero_mul, zero_add]

theorem not_mem_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (v : PlE D.host)
    (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem pD_not_mem {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at hv' with h
  · exact ⟨not_mem_two D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv',
      fun k => not_mem_two D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 v hv'⟩
  · exact ⟨not_mem_two D.host.pde_prime hl (Ne.symm h) v hv',
      fun k => not_mem_two D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 v hv'⟩

theorem exists_kerT (s : X.Sig i) {I : Ideal (X.O0 i)} (hI : I ≠ ⊥) : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧
    K.Normal ∧ (∀ w, X.rhoS i s w = 1 → ∀ g, g * w * g⁻¹ * w⁻¹ ∈ K) ∧ ∀ g ∈ K, ∀ a b, (Tmat i s g - 1) a b ∈ I := by
  let φ : GE N →* GL (Fin D.R.r) (X.O0 i ⧸ I) := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (Tgl i s)
  have hφ : ∀ g, g ∈ φ.ker ↔ ∀ a b, (Tmat i s g - 1) a b ∈ I := by
    intro g
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff, ← Tgl_coe]
    refine forall₂_congr fun a b => ?_
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have : ((1 : GL (Fin D.R.r) (X.O0 i ⧸ I)) : Matrix _ _ (X.O0 i ⧸ I)) a b =
        Ideal.Quotient.mk I ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this]
    rfl
  refine ⟨φ.ker, ?_, inferInstance, fun w hw g => ?_, fun g hg => (hφ g).1 hg⟩
  · have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
      simp only [← map_inv]
      exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have hc : Continuous (Tmat i s) := h1.smul (X.rhoS_cont i s)
    have e : (φ.ker : Set (GE N)) = ⋂ a, ⋂ b, (fun g => (Tmat i s g - 1) a b) ⁻¹' (I : Set (X.O0 i)) := by
      ext g
      simp only [SetLike.mem_coe, hφ, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_ideal (X.twistBaseCoefficientRing_isAdic i) hI).preimage ((hc.sub continuous_const).matrix_elem a b)
  · have h1 : Tgl i s w = scalGL D.R.r (chiS i s w)⁻¹ := by
      change scalGL _ _ * X.rhoS i s w = _
      rw [hw, mul_one]
    have h2 : Tgl i s (g * w * g⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, ← scalGL_comm]
      group
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h2, map_one]

theorem exists_small : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)),
    IsOpen (H : Set (GE N)) → H.Normal →
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) →
    ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧
      (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b,
        (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  intro D N X bkP i T hT z hz M H hH hN hI
  obtain ⟨K₁, o₁, c₁, f₁⟩ := exists_fix_roots (F := D.host.E) (Ω := N.Om) (n := 2 * X.l i ^ M)
    (mul_ne_zero two_ne_zero (pow_ne_zero _ (X.lPrime i).out.ne_zero))
  obtain ⟨K₂, o₂, c₂, f₂⟩ := exists_eps X i
  have hne : Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) ≠ ⊥ :=
    mul_ne_zero (fun h => pow_ne_zero _ (l_ne_zero X i) (Ideal.span_singleton_eq_bot.1 h)) (IsDiscreteValuationRing.not_a_field _)
  choose K o n c f using fun s => exists_kerT X i s hne
  have := normal_of_comm c₁
  have := normal_of_comm c₂
  let H₀ : Subgroup (GE N) := H ⊓ (K₁ ⊓ (K₂ ⊓ ⨅ s : T, K s))
  have hK : (⨅ s : T, K s).Normal := Subgroup.normal_iInf_normal fun s => n s
  have hn₀ : H₀.Normal := inferInstance
  have ho₀ : IsOpen (H₀ : Set (GE N)) := by
    refine hH.inter (o₁.inter (o₂.inter ?_))
    change IsOpen ((⨅ s : T, K s : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun s => o s
  have hw : ∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ w ∈ Ine (F := D.host.E) A,
      ∀ g, g * w * g⁻¹ * w⁻¹ ∈ H₀ := fun v hv A hA w hw g =>
    ⟨H.mul_mem (hN.conj_mem _ (hI v hv A hA hw) g) (H.inv_mem (hI v hv A hA hw)), c₁ _ _, c₂ _ _,
      Subgroup.mem_iInf.2 fun s => c s w ((hT s s.2).1.1 v (pD_not_mem X i hv).1 (pD_not_mem X i hv).2 A hA w hw) g⟩
  have hL : IsOpen ((H₀ ⊓ H₀.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := ho₀.inter (isOpen_comap_cConj X ho₀)
  have hf : ∀ s ∈ T, ∀ g ∈ H₀ ⊓ H₀.comap (cConj X), ∀ a b,
      (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
    fun s hs g hg => f s g (Subgroup.mem_iInf.1 hg.1.2.2.2 ⟨s, hs⟩)
  refine ⟨H₀ ⊓ H₀.comap (cConj X), hL, inferInstance, fun g hg => hg.1.1,
    fun s hs => ⟨hL, inferInstance, fun g g' hg => ?_, fun g => ?_, fun g hg => ⟨?_, f₂ g hg.1.2.2.1⟩⟩,
    fun g hg => f₁ g hg.1.2.1, hf⟩
  · obtain rfl : g' = cConj X g := AlgEquiv.ext hg
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, cConj_cConj]
    exact and_comm
  · obtain ⟨v, hv, A, hA, hzA, -⟩ := hz
    refine ⟨hw v hv A hA z hzA g, ?_⟩
    obtain ⟨v', hv'⟩ := exists_isConjPl v
    have hv'' : v' ∈ X.pD i := by
      rw [← Finset.mem_coe, X.pD_eq] at hv ⊢
      exact mem_placesOver_conj hv' hv
    have := hw v' hv'' _ (isPlaceOver_moveVal_cc X hv' hA) _ (cConj_mem_ine X hzA) (cConj X g)
    change cConj X _ ∈ H₀
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv]
  · ext a b
    have h0 : (Tmat i s g - 1) a b ∈ IsLocalRing.maximalIdeal (X.O0 i) := Ideal.mul_le_right (hf s hs g hg a b)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h0
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.ResSel.SmallSub

end
