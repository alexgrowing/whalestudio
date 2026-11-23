import Formalism.AdmissibleDesigns.BlockTwistedCyclotomic

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset IsLocalRing Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.GaloisCohomology

namespace Formalism.MainNotions.N.K.CoefT

open Formalism.MainNotions.N.K.ShaT

section MapX

variable {R S G M M' : Type} [CommRing R] [CommRing S] [Algebra S R] [Group G]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] [AddCommGroup M'] [Module S M']
  (ρ : Representation R G M) (ρ' : Representation S G M') (φ : M →ₗ[S] M')
  (hφ : ∀ g m, φ (ρ g m) = ρ' g (φ m))

def cocycleMap : coZ1s ρ →ₗ[S] coZ1s ρ' where
  toFun c := ⟨fun g => φ ((c : G → M) g), fun g h => by
    show φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρ' g (φ ((c : G → M) h))
    rw [c.2 g h, map_add, hφ]⟩
  map_add' a b := Subtype.ext <| funext fun g => map_add φ ((a : G → M) g) ((b : G → M) g)
  map_smul' r a := Subtype.ext <| funext fun g => map_smul φ r ((a : G → M) g)

def h1MapAlt : H1z ρ →ₗ[S] H1z ρ' :=
  (Submodule.mapQ (((coB1 ρ).comap (coZ1s ρ).subtype).restrictScalars S) ((coB1 ρ').comap (coZ1s ρ').subtype)
    (cocycleMap ρ ρ' φ hφ) (by
      rintro x ⟨v, hv⟩
      refine ⟨φ v, funext fun g => ?_⟩
      have h : ρ g v - v = (x : G → M) g := congrFun hv g
      show ρ' g (φ v) - φ v = φ ((x : G → M) g)
      rw [← h, map_sub, hφ])).comp
    (Submodule.Quotient.restrictScalarsEquiv S ((coB1 ρ).comap (coZ1s ρ).subtype)).symm.toLinearMap

theorem h1Map_mk_alt (c : coZ1s ρ) :
    h1MapAlt ρ ρ' φ hφ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (cocycleMap ρ ρ' φ hφ c) := rfl

theorem res_h1MapX (Dg : Subgroup G) (x : H1z ρ) :
    resH1 ρ' Dg (h1MapAlt ρ ρ' φ hφ x) =
      h1MapAlt (resRep ρ Dg) (resRep ρ' Dg) φ (fun g m => hφ g m) (resH1 ρ Dg x) := by
  induction x using Submodule.Quotient.induction_on with
  | H c => rfl

theorem h1Map_mem_unramified {Dg : Subgroup G} {x : H1z ρ} (hx : x ∈ unrH1 ρ Dg) : h1MapAlt ρ ρ' φ hφ x ∈ unrH1 ρ' Dg := by
  unfold unrH1 at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  rw [res_h1MapX, hx, map_zero]

theorem h1Map_mem_locally_constant [TopologicalSpace G] {x : H1z ρ} (hx : x ∈ lcH1 ρ) : h1MapAlt ρ ρ' φ hφ x ∈ lcH1 ρ' := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨cocycleMap ρ ρ' φ hφ c, IsLocallyConstant.comp hc φ, rfl⟩

theorem h1Map_mem_local_condition (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) {x : H1z ρ}
    (hx : resH1 ρ (D w) x ∈ Fsha ρ D Iq qs w) : resH1 ρ' (D w) (h1MapAlt ρ ρ' φ hφ x) ∈ Fsha ρ' D Iq qs w := by
  rw [res_h1MapX]
  unfold Fsha at hx ⊢
  split_ifs at hx ⊢ with hw
  · exact h1Map_mem_unramified _ _ _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem h1Map_mem_selmer [TopologicalSpace G] {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) {x : H1z ρ}
    (hx : x ∈ selRep2 ρ J JS D (Fsha ρ D Iq qs) P) :
    h1MapAlt ρ ρ' φ hφ x ∈ selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P := by
  simp only [selRep2, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨⟨⟨h1Map_mem_locally_constant _ _ _ _ h1, fun v => h1Map_mem_unramified _ _ _ _ (h2 v)⟩, fun v => h1Map_mem_unramified _ _ _ _ (h3 v)⟩,
    fun w hw => h1Map_mem_local_condition _ _ _ _ D Iq qs w (h4 w hw)⟩

end MapX

section LenX

variable {R S G M M' : Type} [CommRing R] [CommRing S] [Algebra S R] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] [AddCommGroup M'] [Module S M']

theorem len_sel_le_of_equiv (ρ : Representation R G M) (ρ' : Representation S G M') {ι : Type} [Fintype ι]
    (Φ : M ≃ₗ[S] (ι → M')) (hΦ : ∀ g m j, Φ (ρ g m) j = ρ' g (Φ m j)) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) :
    Module.length S ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) ≤
      (Fintype.card ι : ℕ∞) * Module.length S ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
  let π : ι → (M →ₗ[S] M') := fun j => (LinearMap.proj j).comp Φ.toLinearMap
  have hπ : ∀ j g m, π j (ρ g m) = ρ' g (π j m) := fun j g m => hΦ g m j
  let Fm : ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) →ₗ[S] (ι → ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)) :=
    { toFun := fun x j => ⟨h1MapAlt ρ ρ' (π j) (hπ j) x, h1Map_mem_selmer ρ ρ' (π j) (hπ j) J JS D Iq qs P x.2⟩
      map_add' := fun x y => funext fun j => Subtype.ext (map_add (h1MapAlt ρ ρ' (π j) (hπ j)) (x : H1z ρ) (y : H1z ρ))
      map_smul' := fun a x => funext fun j => Subtype.ext (map_smul (h1MapAlt ρ ρ' (π j) (hπ j)) a (x : H1z ρ)) }
  have hinj : Function.Injective Fm := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ h0
    rw [LinearMap.mem_ker] at h0
    have h0' : ∀ j, h1MapAlt ρ ρ' (π j) (hπ j) x = 0 := fun j => congrArg Subtype.val (congrFun h0 j)
    apply Subtype.ext
    show x = 0
    clear h0 hx
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      have hj : ∀ j, ∃ v : M', ∀ g, ρ' g v - v = π j ((c : G → M) g) := by
        intro j
        have := h0' j
        rw [h1Map_mk_alt, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨v, hv⟩ := this
        exact ⟨v, fun g => congrFun hv g⟩
      choose v hv using hj
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨Φ.symm v, funext fun g => ?_⟩
      show ρ g (Φ.symm v) - Φ.symm v = (c : G → M) g
      apply Φ.injective
      funext j
      rw [map_sub, Pi.sub_apply, hΦ, LinearEquiv.apply_symm_apply]
      exact hv j g
  calc Module.length S ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P)
      ≤ Module.length S (ι → ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)) := Module.length_le_of_injective Fm hinj
    _ = (Fintype.card ι : ℕ∞) * Module.length S ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end LenX

section Ring

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem smul_eq_zero_of_mem_max (hl : ((l : ℕ) : O) = 0) {a : ℤ_[l]} (ha : a ∈ maximalIdeal ℤ_[l]) (x : O) :
    a • x = 0 := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at ha
  obtain ⟨t, rfl⟩ := ha
  rw [Algebra.smul_def, map_mul, map_natCast, hl, mul_zero, zero_mul]

theorem alg_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  by_contra hni
  have hl : ((l : ℕ) : O) = 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨a, hfa, ha⟩ := hni
    have h := congrArg (algebraMap ℤ_[l] O) (PadicInt.unitCoeff_spec ha)
    rw [hfa, map_mul, map_pow, map_natCast] at h
    have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff ha : ℤ_[l])) := (Units.isUnit _).map _
    by_contra hl0
    exact pow_ne_zero _ hl0 ((hu.mul_right_eq_zero).mp h.symm)
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  have hsurj : Function.Surjective (fun v : Fin k → ZMod l => ∑ i, ((v i).cast : ℤ_[l]) • s i) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hx
    refine ⟨fun i => PadicInt.toZMod (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    have h := smul_eq_zero_of_mem_max l O hl (PadicInt.toZMod_spec (c i)) (s i)
    rw [sub_smul, sub_eq_zero] at h
    exact h.symm
  have : Finite O := Finite.of_surjective _ hsurj
  exact IsDiscreteValuationRing.not_a_field O
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp (Finite.isField_of_domain O))

theorem faithful : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).mpr (alg_inj l O)

theorem torsionFree : Module.IsTorsionFree ℤ_[l] O := Module.isTorsionFree_iff_algebraMap_injective.mpr (alg_inj l O)

theorem l_mem_max [IsLocalHom (algebraMap ℤ_[l] O)] : ((l : ℕ) : O) ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] O)]
  intro hu
  have := (isUnit_map_iff (algebraMap ℤ_[l] O) _).mp hu
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _) this

theorem dvd_pow_l [IsLocalHom (algebraMap ℤ_[l] O)] {t : O} (ht : t ≠ 0) : ∃ m : ℕ, t ∣ ((l : ℕ) : O) ^ m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht hϖ
  have hl := l_mem_max l O
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hl
  exact ⟨m, hm.dvd.trans (pow_dvd_pow_of_dvd hl m)⟩

theorem len_quot_l [Module.Free ℤ_[l] O] :
    Module.length ℤ_[l] (O ⧸ Ideal.span {((l : ℕ) : O)}) = Module.finrank ℤ_[l] O := by
  let b := Module.finBasis ℤ_[l] O
  have hmap : (Submodule.restrictScalars ℤ_[l] (Ideal.span {((l : ℕ) : O)})).map b.equivFun.toLinearMap =
      Submodule.pi Set.univ (fun _ => maximalIdeal ℤ_[l]) := by
    ext v
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_pi,
      Set.mem_univ, true_implies, PadicInt.maximalIdeal_eq_span_p]
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩ j
      refine ⟨b.equivFun y j, ?_⟩
      have : y * ((l : ℕ) : O) = (l : ℤ_[l]) • y := by rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [LinearEquiv.coe_coe, this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    · intro hv
      choose w hw using hv
      refine ⟨b.equivFun.symm w * ((l : ℕ) : O), ⟨_, rfl⟩, ?_⟩
      have : b.equivFun.symm w * ((l : ℕ) : O) = (l : ℤ_[l]) • b.equivFun.symm w := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [LinearEquiv.coe_coe, this, map_smul, LinearEquiv.apply_symm_apply]
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hw j]
  rw [((Submodule.Quotient.restrictScalarsEquiv ℤ_[l] (Ideal.span {((l : ℕ) : O)})).symm.trans
    ((Submodule.Quotient.equiv _ _ b.equivFun hmap).trans
      (Submodule.quotientPi (fun _ => maximalIdeal ℤ_[l])))).length_eq, Module.length_pi_of_fintype]
  have h1 : Module.length ℤ_[l] (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = 1 := by
    have := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal ℤ_[l] 1
    rwa [pow_one, Nat.cast_one] at this
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Ring

section Iso

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

def iotaK : ℚ_[l] →+* FractionRing O :=
  IsFractionRing.lift (A := ℤ_[l]) (K := ℚ_[l])
    (g := (algebraMap O (FractionRing O)).comp (algebraMap ℤ_[l] O))
    ((IsFractionRing.injective O (FractionRing O)).comp (alg_inj l O))

theorem iotaK_alg (a : ℤ_[l]) :
    iotaK l O (algebraMap ℤ_[l] ℚ_[l] a) = algebraMap O (FractionRing O) (algebraMap ℤ_[l] O a) :=
  IsFractionRing.lift_algebraMap _ _

theorem smulK (a : ℤ_[l]) (z : FractionRing O) :
    a • z = algebraMap O (FractionRing O) (algebraMap ℤ_[l] O a) * z := by
  rw [← algebraMap_smul O a z, Algebra.smul_def]

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

def psiQ (j : ι) : ℚ_[l] →ₗ[ℤ_[l]] KO O where
  toFun x := Submodule.Quotient.mk (iotaK l O x * algebraMap O (FractionRing O) (b j))
  map_add' x y := by rw [map_add, add_mul, Submodule.Quotient.mk_add]
  map_smul' a x := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, smulK, Algebra.smul_def a x, map_mul, iotaK_alg,
      mul_assoc]

def PsiJ (j : ι) : QZ l →ₗ[ℤ_[l]] KO O :=
  (ZlSub l).liftQ (psiQ l O b j) (by
    rintro x ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Algebra.linearMap_apply]
    show Submodule.Quotient.mk _ = _
    rw [iotaK_alg, ← map_mul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩)

theorem PsiJ_mk (j : ι) (x : ℚ_[l]) :
    PsiJ l O b j (QZ.mk l x) = Submodule.Quotient.mk (iotaK l O x * algebraMap O (FractionRing O) (b j)) := rfl

def Psi : (ι → QZ l) →ₗ[ℤ_[l]] KO O := ∑ j, (PsiJ l O b j).comp (LinearMap.proj j)

theorem Psi_apply (v : ι → QZ l) : Psi l O b v = ∑ j, PsiJ l O b j (v j) := by
  simp [Psi]

theorem Psi_inj : Function.Injective (Psi l O b) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  choose x hx using fun j => Submodule.Quotient.mk_surjective (ZlSub l) (v j)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[l]) x
  have hs' : ∀ j, ∃ cj : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] cj = (s : ℤ_[l]) • x j := fun j => hs j
  choose c hc using hs'
  have h1 : (∑ j, iotaK l O (x j) * algebraMap O (FractionRing O) (b j)) ∈ (1 : Submodule O (FractionRing O)) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum, ← hv, Psi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hx j]
    rfl
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  have h2 : algebraMap O (FractionRing O) ((s : ℤ_[l]) • o) =
      algebraMap O (FractionRing O) (∑ j, c j • b j) := by
    rw [Algebra.smul_def, map_mul, ho, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, ← mul_assoc]
    congr 1
    rw [← iotaK_alg, ← map_mul, ← Algebra.smul_def, ← hc j, iotaK_alg]
  have h3 := IsFractionRing.injective O (FractionRing O) h2
  rw [← Module.Basis.equivFun_symm_apply] at h3
  have hs0 : algebraMap ℤ_[l] ℚ_[l] (s : ℤ_[l]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr (nonZeroDivisors.coe_ne_zero s)
  funext j
  have h4 : (s : ℤ_[l]) * b.equivFun o j = c j := by
    have := congrArg (fun y => b.equivFun y j) h3
    simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] using this
  show v j = 0
  rw [← hx j]
  show Submodule.Quotient.mk (p := ZlSub l) (x j) = (0 : ℚ_[l] ⧸ ZlSub l)
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨b.equivFun o j, ?_⟩
  rw [Algebra.linearMap_apply]
  exact mul_left_cancel₀ hs0 (by rw [← map_mul, h4, hc j, Algebra.smul_def])

theorem Psi_surj [IsLocalHom (algebraMap ℤ_[l] O)] : Function.Surjective (Psi l O b) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨a, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨m, w, hw⟩ := dvd_pow_l l O (nonZeroDivisors.ne_zero ht)
  refine ⟨fun j => QZ.mk l (algebraMap ℤ_[l] ℚ_[l] (b.equivFun (a * w) j) / ((l : ℕ) : ℚ_[l]) ^ m), ?_⟩
  rw [Psi_apply]
  simp only [PsiJ_mk, ← Submodule.mkQ_apply]
  rw [← map_sum]
  congr 1
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] O)]
    exact (map_ne_zero_iff _ (alg_inj l O)).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    exact pow_ne_zero m hl0 hw
  have hwK : algebraMap O (FractionRing O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hw0
  have hlK : ((l : ℕ) : FractionRing O) ^ m =
      algebraMap O (FractionRing O) t * algebraMap O (FractionRing O) w := by
    rw [← map_mul, ← hw, map_pow, map_natCast]
  have hsum : ∑ j, algebraMap O (FractionRing O) (algebraMap ℤ_[l] O (b.equivFun (a * w) j)) *
      algebraMap O (FractionRing O) (b j) = algebraMap O (FractionRing O) (a * w) := by
    conv_rhs => rw [← b.sum_equivFun (a * w), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul (algebraMap O (FractionRing O))]
  calc ∑ j, iotaK l O (algebraMap ℤ_[l] ℚ_[l] (b.equivFun (a * w) j) / ((l : ℕ) : ℚ_[l]) ^ m) *
        algebraMap O (FractionRing O) (b j)
      = (∑ j, algebraMap O (FractionRing O) (algebraMap ℤ_[l] O (b.equivFun (a * w) j)) *
          algebraMap O (FractionRing O) (b j)) / ((l : ℕ) : FractionRing O) ^ m := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_div₀, map_pow, map_natCast, iotaK_alg, div_mul_eq_mul_div]
    _ = algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) t := by
        rw [hsum, hlK, map_mul (algebraMap O (FractionRing O)), mul_div_mul_right _ _ hwK]

end Iso

theorem coefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : CoefChange l O := by
  intro G _ _ ψ V VS J JS D Iq qs P ψO ρO ρZ
  have : FaithfulSMul ℤ_[l] O := faithful l O
  have : Module.IsTorsionFree ℤ_[l] O := torsionFree l O
  have : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  let b := Module.finBasis ℤ_[l] O
  let Φ : KO O ≃ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] O) → QZ l) :=
    (LinearEquiv.ofBijective (Psi l O b) ⟨Psi_inj l O b, Psi_surj l O b⟩).symm
  have hΦ : ∀ g m j, Φ (ρO g m) j = ρZ g (Φ m j) := by
    intro g m j
    simp only [ρO, ρZ, ψO, scalRep_apply, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, algebraMap_smul, map_smul, Pi.smul_apply]
  have h1 := len_sel_le_of_equiv ρO ρZ Φ hΦ J JS D Iq qs P
  have h2 := IsLocalRing.length_restrictScalars ℤ_[l] (B := O) (M := ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P))
  have h3 := IsLocalRing.length_restrictScalars ℤ_[l] (B := O) (M := O ⧸ Ideal.span {((l : ℕ) : O)})
  rw [len_quot_l l O] at h3
  have hn0 : Module.finrank ℤ_[l] O ≠ 0 := Module.finrank_pos.ne'
  have hf0 : Module.length (ResidueField ℤ_[l]) (ResidueField O) ≠ 0 := Module.length_pos.ne'
  have hft : Module.length (ResidueField ℤ_[l]) (ResidueField O) ≠ ⊤ := by
    intro hf
    rw [hf] at h3
    rcases eq_or_ne (Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)})) 0 with he | he
    · rw [he, zero_mul, Nat.cast_eq_zero] at h3
      exact hn0 h3
    · rw [ENat.mul_top he] at h3
      exact ENat.natCast_ne_top _ h3
  rw [← ENat.mul_le_mul_right_iff hf0 hft, ← h2]
  calc _ ≤ _ := h1
    _ = _ := by rw [Fintype.card_fin, h3]; ring

end Formalism.MainNotions.N.K.CoefT

end
