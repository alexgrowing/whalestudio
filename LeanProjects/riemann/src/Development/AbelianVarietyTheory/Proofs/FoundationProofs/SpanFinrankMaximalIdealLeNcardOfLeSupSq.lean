import Mathlib
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open TensorProduct IsLocalRing

namespace GlobalTheory

universe u

theorem spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {s : Set S} (hs : s.Finite) (h₁ : Ideal.span s ≤ maximalIdeal S)
    (h₂ : maximalIdeal S ≤ Ideal.span s ⊔ maximalIdeal S ^ 2) :
    (maximalIdeal S).spanFinrank ≤ s.ncard := by
  have h : maximalIdeal S ≤ Ideal.span s :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson ⊥) (by rwa [smul_eq_mul, ← pow_two])
  rw [le_antisymm h h₁]
  exact Submodule.spanFinrank_span_le_ncard_of_finite hs

theorem spanFinrank_maximalIdeal_le_of_ker_le_sq {P S : Type*} [CommRing P] [IsLocalRing P]
    [IsNoetherianRing P] [CommRing S] [IsLocalRing S] (f : P →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ maximalIdeal P ^ 2) :
    (maximalIdeal P).spanFinrank ≤ (maximalIdeal S).spanFinrank := by
  have : IsNoetherianRing S := isNoetherianRing_of_surjective P S f hf
  have := IsLocalHom.of_surjective f hf
  have hfg := (maximalIdeal S).fg_of_isNoetherianRing
  have hfin := Submodule.FG.finite_generators hfg
  let g := Function.surjInv hf
  have hg (y : S) : f (g y) = y := Function.surjInv_eq hf y
  have hmap : (Ideal.span (g '' (maximalIdeal S).generators)).map f = maximalIdeal S := by
    rw [Ideal.map_span, ← Set.image_comp]
    have : f ∘ g = id := funext hg
    rw [this, Set.image_id]
    exact (maximalIdeal S).span_generators
  have hcomap : maximalIdeal P = Ideal.span (g '' (maximalIdeal S).generators) ⊔ RingHom.ker f := by
    rw [← maximalIdeal_comap f]
    conv_lhs => rw [← hmap, Ideal.comap_map_of_surjective f hf]
    rfl
  rw [← Submodule.FG.generators_ncard hfg]
  refine (spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (hfin.image g) ?_ ?_).trans
    (Set.ncard_image_le hfin)
  · exact le_sup_left.trans hcomap.ge
  · exact hcomap.le.trans (sup_le_sup_left hker _)

theorem ker_eq_bot_of_isRegularLocalRing_of_le_sq {P S : Type*} [CommRing P] [IsRegularLocalRing P]
    [CommRing S] [IsRegularLocalRing S] (f : P →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ maximalIdeal P ^ 2) : RingHom.ker f = ⊥ := by
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain P
  rw [eq_bot_iff]
  intro x hx
  by_contra h0
  have h₁ := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero h0) hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := P),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)] at h₁
  have h₂ := spanFinrank_maximalIdeal_le_of_ker_le_sq f hf hker
  have h₃ : (maximalIdeal S).spanFinrank + 1 ≤ (maximalIdeal P).spanFinrank := by
    exact_mod_cast h₁
  omega

theorem ker_inf_sq_le_of_isRegularLocalRing {S : Type*} [CommRing S] [IsRegularLocalRing S]
    (P : Type u) [CommRing P] [IsRegularLocalRing P] (f : P →+* S) (hf : Function.Surjective f) :
    RingHom.ker f ⊓ maximalIdeal P ^ 2 ≤ maximalIdeal P * RingHom.ker f := by
  induction hn : (maximalIdeal P).spanFinrank using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  by_cases hker : RingHom.ker f ≤ maximalIdeal P ^ 2
  · rw [ker_eq_bot_of_isRegularLocalRing_of_le_sq f hf hker]
    simp
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hker
  have hxm : x ∈ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top f) hx
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hxm hx2
  have hlt : (maximalIdeal (P ⧸ Ideal.span {x})).spanFinrank < n := by
    have h₁ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le
      P hxm hx2
    rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h₁
    omega
  have hle : Ideal.span {x} ≤ RingHom.ker f := (Ideal.span_singleton_le_iff_mem _).mpr hx
  let π := Ideal.Quotient.mk (Ideal.span {x})
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let f' : P ⧸ Ideal.span {x} →+* S := Ideal.Quotient.lift _ f hle
  have hf' : Function.Surjective f' := Ideal.Quotient.lift_surjective_of_surjective _ hle hf
  have hk : RingHom.ker f' = (RingHom.ker f).map π := Ideal.ker_quotient_lift f hle
  have hm : maximalIdeal (P ⧸ Ideal.span {x}) = (maximalIdeal P).map π :=
    (map_maximalIdeal_of_surjective π hπ).symm
  have h := ih _ hlt _ f' hf' rfl
  rw [hk, hm, ← Ideal.map_pow, ← Ideal.map_mul] at h
  rintro y ⟨hy₁, hy₂⟩
  have hy := h ⟨Ideal.mem_map_of_mem π hy₁, Ideal.mem_map_of_mem π hy₂⟩
  obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hy
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hzy.symm)
  have hz2 : z ∈ maximalIdeal P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mono_right (le_maximalIdeal (RingHom.ker_ne_top f)) hz
  have ham : a ∈ maximalIdeal P := by
    by_contra hu
    have hu : IsUnit a := by simpa using hu
    exact hx2 ((Ideal.unit_mul_mem_iff_mem _ hu).mp (ha ▸ sub_mem hy₂ hz2))
  rw [← sub_add_cancel y z, ← ha]
  exact add_mem (Ideal.mul_mem_mul ham hx) hz

theorem formallySmooth_of_isRegularLocalRing_of_surjective (R P S : Type*) [CommRing R]
    [CommRing P] [IsRegularLocalRing P] [CommRing S] [IsRegularLocalRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (hf : Function.Surjective (algebraMap P S))
    [Algebra.FormallySmooth R (ResidueField S)] : Algebra.FormallySmooth R S := by
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P hf
    (IsNoetherian.noetherian _), injective_iff_map_eq_zero]
  have hs : Function.Surjective (algebraMap P (ResidueField S)) := by
    rw [IsScalarTower.algebraMap_eq P S]
    exact residue_surjective.comp hf
  have hk : RingHom.ker (algebraMap P (ResidueField S)) = maximalIdeal P :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs)
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := R) hs).mpr
    inferInstance
  intro t ht
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P _ _ hs t
  rw [TensorProduct.mk_apply, KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul] at ht
  have hxm : x.1 ∈ RingHom.ker (algebraMap P (ResidueField S)) :=
    hk.ge (le_maximalIdeal (RingHom.ker_ne_top _) x.2)
  have h₁ : (RingHom.ker (algebraMap P (ResidueField S))).toCotangent ⟨x.1, hxm⟩ = 0 :=
    hinj (by rw [map_zero]; exact ht)
  have h₁ : x.1 ∈ maximalIdeal P ^ 2 := hk ▸ (Ideal.toCotangent_eq_zero _ _).mp h₁
  have h₂ := ker_inf_sq_le_of_isRegularLocalRing P _ hf ⟨x.2, h₁⟩
  have h₃ : x ∈ maximalIdeal P • (⊤ : Submodule P (RingHom.ker (algebraMap P S))) := by
    rw [Submodule.mem_smul_top_iff]
    exact h₂
  refine Submodule.smul_induction_on h₃ (fun a ha y _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · have : algebraMap P (ResidueField S) a = 0 := hk.ge ha
    rw [TensorProduct.mk_apply, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, this,
      TensorProduct.zero_tmul]
  · rw [map_add, ha, hb, add_zero]

theorem formallySmooth_of_isRegularLocalRing_of_residueField (k S : Type*) [Field k]
    [CommRing S] [IsRegularLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S]
    [Algebra.FormallySmooth k (ResidueField S)] : Algebra.FormallySmooth k S := by
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k (Algebra.EssFiniteType.subalgebra k S))
  let g : MvPolynomial (Fin n) k →ₐ[k] S := (Algebra.EssFiniteType.subalgebra k S).val.comp f₀
  let p : Ideal (MvPolynomial (Fin n) k) := (maximalIdeal S).comap g
  let P := Localization.AtPrime p
  have hu (x : MvPolynomial (Fin n) k) : x ∈ p.primeCompl ↔ IsUnit (g x) := by
    simp [p, Ideal.mem_primeCompl_iff]
  let fP : P →ₐ[k] S := IsLocalization.liftAlgHom (M := p.primeCompl) (f := g)
    fun x ↦ (hu _).mp x.2
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.EssFiniteType.submonoid k S) x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := p.primeCompl) _ x ⟨s, (hu _).mpr hs⟩, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    change _ * g s = g x
    have e (y) : g y = fP (algebraMap _ P y) := by simp [fP]
    have := congrArg fP (IsLocalization.mk'_spec P x (⟨s, (hu _).mpr hs⟩ : p.primeCompl))
    rwa [map_mul, ← e, ← e] at this
  algebraize [fP.toRingHom]
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) k) P := .of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth k P := .comp _ (MvPolynomial (Fin n) k) _
  have : Module.Free P Ω[P⁄k] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) P)
  exact formallySmooth_of_isRegularLocalRing_of_surjective k P S hf₁

theorem formallySmooth_of_isRegularLocalRing_of_perfectField (k S : Type*) [Field k]
    [PerfectField k] [CommRing S] [IsRegularLocalRing S] [Algebra k S]
    [Algebra.EssFiniteType k S] : Algebra.FormallySmooth k S :=
  have : Algebra.EssFiniteType k (ResidueField S) := .comp k S _
  formallySmooth_of_isRegularLocalRing_of_residueField k S

theorem free_and_finrank_kaehler_eq_finrank_cotangentSpace (k S : Type*) [Field k] [CommRing S]
    [IsLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] [Algebra.FormallySmooth k S]
    [Algebra.FormallyEtale k (ResidueField S)] :
    Module.Free S Ω[S⁄k] ∧
      Module.finrank S Ω[S⁄k] = Module.finrank (ResidueField S) (CotangentSpace S) := by
  have hfree : Module.Free S Ω[S⁄k] := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_⟩
  have hs : Function.Surjective (algebraMap S (ResidueField S)) := residue_surjective
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hs).mpr
    inferInstance
  have hsurj : Function.Surjective
      (KaehlerDifferential.kerCotangentToTensor k S (ResidueField S)) := fun y ↦
    (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k S _ hs y).mp
      (Subsingleton.elim _ _)
  let e : CotangentSpace S ≃ₗ[S] ResidueField S ⊗[S] Ω[S⁄k] :=
    (Ideal.Cotangent.equivOfEq _ _ ker_residue.symm).trans (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)
  rw [(e.extendScalarsOfSurjective hs).finrank_eq, Module.finrank_baseChange]

theorem finrank_cotangentSpace_le_finrank_cotangent {B : Type*} [CommRing B] [IsNoetherianRing B]
    (x : Ideal B) [x.IsMaximal] (S : Type*) [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalization.AtPrime S x] :
    Module.finrank (ResidueField S) (CotangentSpace S) ≤ Module.finrank (B ⧸ x) x.Cotangent := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing x.primeCompl S inferInstance
  let := Ideal.Quotient.field x
  have : Module.Finite B x.Cotangent := .of_surjective _ x.toCotangent_surjective
  have : Module.Finite (B ⧸ x) x.Cotangent := .of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ x) x.Cotangent
  choose y hy using fun i ↦ x.toCotangent_surjective (b i)
  have h : x ≤ Ideal.span (Set.range fun i ↦ (y i : B)) ⊔ x ^ 2 := by
    intro z hz
    choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (b.repr (x.toCotangent ⟨z, hz⟩) i)
    have h₁ : x.toCotangent ⟨z, hz⟩ = x.toCotangent (∑ i, c i • y i) := by
      rw [← b.sum_repr (x.toCotangent ⟨z, hz⟩), map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, hy, ← hc]
      rfl
    have h₂ := (Ideal.toCotangent_eq x).mp h₁
    rw [← add_sub_cancel ((∑ i, c i • y i : x) : B) z]
    refine Submodule.add_mem_sup ?_ h₂
    rw [Submodule.coe_sum]
    exact sum_mem fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hm : x.map (algebraMap B S) = maximalIdeal S := IsLocalization.AtPrime.map_eq_maximalIdeal x S
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  refine (spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq
    (s := Set.range fun i ↦ algebraMap B S (y i)) (Set.finite_range _) ?_ ?_).trans ?_
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hm.le (Ideal.mem_map_of_mem _ (y i).2)
  · have := Ideal.map_mono (f := algebraMap B S) h
    rwa [Ideal.map_sup, Ideal.map_pow, hm, Ideal.map_span, ← Set.range_comp] at this
  · rw [← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    simp

theorem isRegularLocalRing_of_finrank_cotangentSpace_le (S : Type*) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {d : ℕ} (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim S)
    (h₂ : Module.finrank (ResidueField S) (CotangentSpace S) ≤ d) :
    IsRegularLocalRing S ∧ ringKrullDim S = d ∧
      Module.finrank (ResidueField S) (CotangentSpace S) = d := by
  have h₃ := ringKrullDim_le_spanFinrank_maximalIdeal S
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h₃
  have h₄ : Module.finrank (ResidueField S) (CotangentSpace S) = d :=
    h₂.antisymm (by exact_mod_cast h₁.trans h₃)
  have h₅ : ringKrullDim S = d := le_antisymm (h₄ ▸ h₃) h₁
  exact ⟨(IsRegularLocalRing.iff_finrank_cotangentSpace S).mpr (by rw [h₄, h₅]), h₅, h₄⟩

theorem formallyEtale_residueField_of_isMaximal (R k : Type*) [CommRing R] [Field k]
    [PerfectField k] [Algebra R k] {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (x : Ideal B) [x.IsMaximal] (S : Type*) [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalization.AtPrime S x] [Algebra R S] [Algebra k S] [IsScalarTower R B S]
    [IsScalarTower R k S] : Algebra.FormallyEtale k (ResidueField S) := by
  have hs : Function.Surjective (IsScalarTower.toAlgHom R B (ResidueField S)) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal x S).surjective.comp Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType R (ResidueField S) := .of_surjective _ hs
  have : Algebra.FiniteType k (ResidueField S) := .of_restrictScalars_finiteType R _ _
  have : Module.Finite k (ResidueField S) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Algebra.FormallyEtale.of_isSeparable k _

theorem formallySmooth_of_finrank_cotangentSpace_le (k S : Type*) [Field k] [PerfectField k]
    [CommRing S] [IsLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] {d : ℕ}
    (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim S)
    (h₂ : Module.finrank (ResidueField S) (CotangentSpace S) ≤ d) :
    Algebra.FormallySmooth k S :=
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing k S
  have := (isRegularLocalRing_of_finrank_cotangentSpace_le S h₁ h₂).1
  formallySmooth_of_isRegularLocalRing_of_perfectField k S

theorem isSmoothAt_of_finrank_cotangent_le_of_perfectField (k : Type*) [Field k] [PerfectField k]
    {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]
    {d : ℕ} (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m))
    (h₂ : Module.finrank (A ⧸ m) m.Cotangent ≤ d) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = d ∧
      Module.finrank (A ⧸ m) m.Cotangent = d ∧ Algebra.IsSmoothAt k m ∧
      Module.Free (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] ∧
      Module.finrank (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] = d := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have h₃ := finrank_cotangentSpace_le_finrank_cotangent m (Localization.AtPrime m)
  obtain ⟨h₄, h₅, h₆⟩ := isRegularLocalRing_of_finrank_cotangentSpace_le _ h₁ (h₃.trans h₂)
  have h₇ := formallySmooth_of_isRegularLocalRing_of_perfectField k (Localization.AtPrime m)
  have := formallyEtale_residueField_of_isMaximal k k m (Localization.AtPrime m)
  obtain ⟨h₈, h₉⟩ := free_and_finrank_kaehler_eq_finrank_cotangentSpace k (Localization.AtPrime m)
  exact ⟨h₄, h₅, h₂.antisymm (h₆ ▸ h₃), h₇, h₈, h₉.trans h₆⟩

theorem height_le_height_comap_of_surjective {B C : Type*} [CommRing B] [CommRing C]
    (ψ : B →+* C) (hψ : Function.Surjective ψ) (y : Ideal C) [y.IsPrime] :
    y.height ≤ (y.comap ψ).height := by
  have e₁ := PrimeSpectrum.height_eq_orderHeight (⟨y, inferInstance⟩ : PrimeSpectrum C)
  have e₂ := PrimeSpectrum.height_eq_orderHeight (PrimeSpectrum.comap ψ ⟨y, inferInstance⟩)
  refine e₁.trans_le (le_of_le_of_eq ?_ e₂.symm)
  refine Order.height_le_height_apply_of_strictMono _ (Monotone.strictMono_of_injective ?_ ?_) _
  · exact fun _ _ h ↦ Ideal.comap_mono h
  · exact PrimeSpectrum.comap_injective_of_surjective ψ hψ

section DVR

variable (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {A : Type u} [CommRing A] [Algebra V A] [Algebra.FiniteType V A]

theorem le_height_of_trdeg_quotient_eq {B : Type*} [CommRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A)) (x : Ideal B) [x.IsMaximal]
    (p : Ideal A) [p.IsPrime] (hp : p.under V = ⊥) (hpx : p ≤ x.comap φ) {e : ℕ}
    (he : Algebra.trdeg V (A ⧸ p) = e) : (e : ℕ∞) ≤ x.height := by
  have : FaithfulSMul V (A ⧸ p) := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro v hv
    exact hp.le ((Ideal.Quotient.eq_zero_iff_mem (I := p)).mp hv)
  have hq : (x.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  have hq' : ((x.comap φ).map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpx
  have hle : (maximalIdeal V).map (algebraMap V (A ⧸ p)) ≤
      (x.comap φ).map (Ideal.Quotient.mk p) := by
    rw [IsScalarTower.algebraMap_eq V A (A ⧸ p), ← Ideal.map_map, ← hker]
    exact Ideal.map_mono (Ideal.ker_le_comap φ)
  obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le hle
  have := hr.1.1
  have := liesOver_maximalIdeal_of_mem_minimalPrimes V hr
  let := Ideal.Quotient.field (maximalIdeal V)
  have : Algebra.FiniteType (V ⧸ maximalIdeal V) ((A ⧸ p) ⧸ r) :=
    .of_restrictScalars_finiteType V _ _
  have htr := (trdeg_quotient_eq_of_mem_minimalPrimes V (V ⧸ maximalIdeal V)
    Ideal.Quotient.mk_surjective hr).trans he
  let χ : A →+* (A ⧸ p) ⧸ r := (Ideal.Quotient.mk r).comp (Ideal.Quotient.mk p)
  have hχ : Function.Surjective χ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hkχ : RingHom.ker φ ≤ RingHom.ker χ := by
    rw [hker, Ideal.map_le_iff_le_comap]
    intro v hv
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hr.1.2 (Ideal.mem_map_of_mem _ hv))
  have hχq : RingHom.ker χ ≤ x.comap φ := fun a ha ↦
    (Ideal.mem_quotient_iff_mem hpx).mp (hrq (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  let ψ : B →+* (A ⧸ p) ⧸ r := φ.liftOfSurjective hφ ⟨χ, hkχ⟩
  have hψφ (a : A) : ψ (φ a) = χ a := RingHom.liftOfSurjective_comp_apply _ hφ ⟨χ, hkχ⟩ a
  have hψ : Function.Surjective ψ := fun c ↦ by
    obtain ⟨a, rfl⟩ := hχ c
    exact ⟨φ a, hψφ a⟩
  have hψx : RingHom.ker ψ ≤ x := fun b hb ↦ by
    obtain ⟨a, rfl⟩ := hφ b
    exact hχq (show χ a = 0 from hψφ a ▸ hb)
  have hcm : (x.map ψ).comap ψ = x := by
    rw [Ideal.comap_map_of_surjective ψ hψ, sup_eq_left]
    exact hψx
  have : (x.map ψ).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective ψ hψ inferInstance).resolve_left fun h ↦ ?_
    rw [h, Ideal.comap_top] at hcm
    exact Ideal.IsMaximal.ne_top inferInstance hcm.symm
  have h := height_le_height_comap_of_surjective ψ hψ (x.map ψ)
  rwa [hcm, ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field e htr] at h

omit [IsDiscreteValuationRing V] [Algebra.FiniteType V A] in

theorem under_eq_bot_of_mem_minimalPrimes_of_flat [Module.Flat V A] {p : Ideal A}
    (hp : p ∈ minimalPrimes A) : p.under V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  by_contra h0
  have hreg : IsSMulRegular A v :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h0)
  refine Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) hv ?_
  refine mem_nonZeroDivisors_iff_left.mpr fun a ha ↦ hreg ?_
  simpa [Algebra.smul_def] using ha

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsDiscreteValuationRing V] in

theorem mem_minimalPrimes_genericFibre_of_flat [Module.Flat V A]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] {p : Ideal A}
    (hp : p ∈ minimalPrimes A) {e : ℕ} (he : Algebra.trdeg V (A ⧸ p) = e) :
    p.map (Algebra.TensorProduct.includeRight : A →ₐ[V] K ⊗[V] A) ∈ minimalPrimes (K ⊗[V] A) ∧
      ringKrullDim ((K ⊗[V] A) ⧸
        p.map (Algebra.TensorProduct.includeRight : A →ₐ[V] K ⊗[V] A)) = e := by
  have hbot := under_eq_bot_of_mem_minimalPrimes_of_flat V hp
  have := hp.1.1
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors V)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid A (nonZeroDivisors V) : Set A) p := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ h
    exact nonZeroDivisors.ne_zero hv (hbot.le h)
  constructor
  · have h := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid A (nonZeroDivisors V))
      (K ⊗[V] A) ⊥
    rw [Ideal.map_bot] at h
    refine h.ge ?_
    have h' := IsLocalization.under_map_of_isPrime_disjoint _ (K ⊗[V] A) ‹p.IsPrime› hdisj
    exact (congrArg (· ∈ minimalPrimes A) h').mpr hp
  · have : FaithfulSMul V (A ⧸ p) := by
      rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
      intro v hv
      exact hbot.le ((Ideal.Quotient.eq_zero_iff_mem (I := p)).mp hv)
    have hk := Algebra.TensorProduct.lTensor_ker (A := K) (Ideal.Quotient.mkₐ V p)
      Ideal.Quotient.mk_surjective
    rw [show RingHom.ker (Ideal.Quotient.mkₐ V p) = p from Ideal.mk_ker] at hk
    have hs : Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id V K) (Ideal.Quotient.mkₐ V p)) :=
      LinearMap.lTensor_surjective K (g := (Ideal.Quotient.mkₐ V p).toLinearMap)
        Ideal.Quotient.mk_surjective
    rw [← hk, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv]
    exact ringKrullDim_genericFibre_eq V K he

theorem le_height_of_flat [Module.Flat V A]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A)) (x : Ideal B) [x.IsMaximal] :
    (d : ℕ∞) ≤ x.height := by
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ x.comap φ)
  have := hp.1.1
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast V (A := A ⧸ p)
  obtain ⟨h₁, h₂⟩ := mem_minimalPrimes_genericFibre_of_flat V K hp he
  have h₃ := hd _ h₁
  rw [h₂] at h₃
  refine le_trans ?_ (le_height_of_trdeg_quotient_eq V φ hφ hker x p
    (under_eq_bot_of_mem_minimalPrimes_of_flat V hp) hpx he)
  exact_mod_cast h₃

end DVR

theorem ker_includeRight_of_surjective (R : Type*) [CommRing R] [IsLocalRing R] (k : Type*)
    [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k)) {A : Type*} [CommRing A]
    [Algebra R A] :
    RingHom.ker (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A).toRingHom =
      (maximalIdeal R).map (algebraMap R A) := by
  have hm : RingHom.ker (Algebra.ofId R k) = maximalIdeal R :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap R k) hk)
  have h := Algebra.TensorProduct.rTensor_ker (R := R) (C := A) (Algebra.ofId R k) hk
  rw [hm] at h
  let e := Algebra.TensorProduct.lid R A
  have h₁ : (maximalIdeal R).map (algebraMap R A) =
      ((maximalIdeal R).map (algebraMap R (R ⊗[R] A))).map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    ext r
    simp [e, Algebra.algebraMap_eq_smul_one]
  ext a
  rw [h₁, Ideal.mem_map_iff_of_surjective e.toRingEquiv.toRingHom e.surjective]
  constructor
  · intro ha
    exact ⟨1 ⊗ₜ a, h.le (by simpa [RingHom.mem_ker] using ha), by simp [e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := e.symm.surjective y
    simpa [e, RingHom.mem_ker] using h.ge hy

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem isSmoothAt_of_flat_of_isRegularLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [PerfectField (ResidueField R)] {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal R).map (algebraMap R A)) (x : Ideal B) [x.IsMaximal]
    (S : Type*) [CommRing S] [IsRegularLocalRing S] [Algebra B S] [IsLocalization.AtPrime S x] :
    Algebra.IsSmoothAt R (x.comap φ) ∧
      Module.Free (Localization.AtPrime (x.comap φ)) Ω[Localization.AtPrime (x.comap φ)⁄R] ∧
      (Module.finrank (Localization.AtPrime (x.comap φ)) Ω[Localization.AtPrime (x.comap φ)⁄R] :
        WithBot ℕ∞) = ringKrullDim S := by
  let q := x.comap φ
  let L := Localization.AtPrime q
  let T := ResidueField R ⊗[R] L
  have hmq : (maximalIdeal R).map (algebraMap R A) ≤ q := hker ▸ Ideal.ker_le_comap φ
  have : q.LiesOver (maximalIdeal R) := ⟨(maximalIdeal.isMaximal R).eq_of_le
    (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.mp hmq)⟩
  have := isLocalHom_algebraMap_localization_of_liesOver R q
  let g : L →+* T := algebraMap L T
  have hg : Function.Surjective g :=
    TensorProduct.mk_surjective R L _ residue_surjective
  have hgk : RingHom.ker g = (RingHom.ker φ).map (algebraMap A L) := by
    rw [hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact ker_includeRight_of_surjective R _ residue_surjective
  have hle : RingHom.ker φ ≤ RingHom.ker (g.comp (algebraMap A L)) :=
    fun a ha ↦ hgk.ge (Ideal.mem_map_of_mem _ ha)
  let : Algebra B T := (φ.liftOfSurjective hφ ⟨_, hle⟩).toAlgebra
  have hcomp : g.comp (algebraMap A L) = (algebraMap B T).comp φ :=
    (RingHom.liftOfSurjective_comp _ hφ ⟨_, hle⟩).symm
  have hloc := IsLocalization.of_surjective q.primeCompl L φ hφ g hg hcomp hgk.le
  have hM : q.primeCompl.map φ = x.primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      obtain ⟨a, rfl⟩ := hφ b
      exact ⟨a, hb, rfl⟩
  rw [hM] at hloc
  let e : S ≃+* T := (IsLocalization.algEquiv x.primeCompl S T).toRingEquiv
  have : IsRegularLocalRing T := .of_ringEquiv e
  have : Algebra.EssFiniteType A L := .of_isLocalization L q.primeCompl
  have : Algebra.EssFiniteType R L := .comp R A L
  have : Algebra.FormallySmooth (ResidueField R) T :=
    formallySmooth_of_isRegularLocalRing_of_perfectField _ _
  have hsm : Algebra.FormallySmooth R L :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (P := A) q.primeCompl
  have hfree : Module.Free L Ω[L⁄R] := Module.free_of_flat_of_isLocalRing
  refine ⟨hsm, hfree, ?_⟩
  let : Algebra R B := (φ.comp (algebraMap R A)).toAlgebra
  have : Algebra.FiniteType R B :=
    .of_surjective (⟨φ, fun _ ↦ rfl⟩ : A →ₐ[R] B) hφ
  have : IsScalarTower R B T := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R L T, IsScalarTower.algebraMap_apply R A L]
    exact congr($hcomp (algebraMap R A r))
  have := formallyEtale_residueField_of_isMaximal R (ResidueField R) x T
  have h := (free_and_finrank_kaehler_eq_finrank_cotangentSpace (ResidueField R) T).2
  rw [← (KaehlerDifferential.tensorKaehlerEquiv R (ResidueField R) L T).finrank_eq,
    Module.finrank_baseChange] at h
  rw [ringKrullDim_eq_of_ringEquiv e,
    ← (IsRegularLocalRing.iff_finrank_cotangentSpace T).mp inferInstance, ← h]

theorem exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] (q : Ideal A)
    [q.IsPrime] [Algebra.IsSmoothAt R q] {d : ℕ}
    (hd : Module.finrank (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R] = d) :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away f) := by
  obtain ⟨f, hf, hs⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q
  refine ⟨f, hf, ?_⟩
  have hle : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.mpr hf
  let L := Localization.AtPrime q
  let : Algebra (Localization.Away f) L :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower A (Localization.Away f) L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsScalarTower R (Localization.Away f) L := .to₁₃₄ R A _ _
  have := IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) L _ _ hle
  have : Algebra.FormallyEtale (Localization.Away f) L :=
    .of_isLocalization (q.primeCompl.map (algebraMap A (Localization.Away f)))
  have : Nontrivial (Localization.Away f) := (algebraMap (Localization.Away f) L).domain_nontrivial
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth, ← hd,
    ← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (Localization.Away f) L).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_rank]

section Main

variable (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Type u} [CommRing A] [Algebra V A] [Algebra.FiniteType V A] [Module.Flat V A]

theorem isSmoothAt_of_flat_of_finrank_cotangentSpace_le {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A)) (x : Ideal B) [x.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalization.AtPrime S x]
    (hx : Module.finrank (ResidueField S) (CotangentSpace S) ≤ d) :
    Algebra.IsSmoothAt V (x.comap φ) ∧
      (∃ f ∉ x.comap φ, Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing S ∧ ringKrullDim S = d ∧
      Module.finrank (ResidueField S) (CotangentSpace S) = d := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  have : IsNoetherianRing B := isNoetherianRing_of_surjective A B φ hφ
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing x.primeCompl S inferInstance
  have : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim S := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height x S]
    exact_mod_cast le_height_of_flat V K hd φ hφ hker x
  obtain ⟨h₂, h₃, h₄⟩ := isRegularLocalRing_of_finrank_cotangentSpace_le S h₁ hx
  obtain ⟨h₅, -, h₆⟩ := isSmoothAt_of_flat_of_isRegularLocalRing V φ hφ hker x S
  rw [h₃] at h₆
  exact ⟨h₅, exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt V _ (by exact_mod_cast h₆),
    h₂, h₃, h₄⟩

theorem isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A)) (x : Ideal B) [x.IsMaximal]
    (hx : Module.finrank (B ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V (x.comap φ) ∧
      (∃ f ∉ x.comap φ, Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank (B ⧸ x) x.Cotangent = d := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  have : IsNoetherianRing B := isNoetherianRing_of_surjective A B φ hφ
  have h := finrank_cotangentSpace_le_finrank_cotangent x (Localization.AtPrime x)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := isSmoothAt_of_flat_of_finrank_cotangentSpace_le V K hd φ hφ hker x
    (Localization.AtPrime x) (h.trans hx)
  exact ⟨h₁, h₂, h₃, h₄, hx.antisymm (h₅ ▸ h)⟩

theorem isSmoothAt_of_liesOver_of_flat_of_forall_finrank_cotangent_le {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A))
    (hx : ∀ x : Ideal B, x.IsMaximal → Module.finrank (B ⧸ x) x.Cotangent ≤ d)
    (q : Ideal A) [q.IsPrime] [q.LiesOver (maximalIdeal V)] :
    Algebra.IsSmoothAt V q ∧
      ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f) := by
  have hkq : RingHom.ker φ ≤ q := by
    rw [hker, Ideal.map_le_iff_le_comap]
    exact (q.over_def (maximalIdeal V)).le
  have hprime : (q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hkq
  obtain ⟨x, hxm, hqx⟩ := Ideal.exists_le_maximal _ hprime.ne_top
  obtain ⟨-, ⟨f, hf, hs⟩, -⟩ :=
    isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K hd φ hφ hker x (hx x hxm)
  have hfq : f ∉ q := fun h ↦ hf (Ideal.map_le_iff_le_comap.mp hqx h)
  refine ⟨?_, f, hfq, hs⟩
  have : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.IsStandardSmooth V (Localization.Away f) := hs.isStandardSmooth d
  exact (Algebra.basicOpen_subset_smoothLocus_iff (R := V) (f := f)).mpr inferInstance
    (show (⟨q, ‹_›⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen f from hfq)

theorem isSmoothAt_of_flat_of_finrank_cotangent_le {ϖ : V} (hϖ : Irreducible ϖ) {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), ringKrullDim ((K ⊗[V] A) ⧸ p) = d)
    (x : Ideal (A ⧸ Ideal.span {algebraMap V A ϖ})) [x.IsMaximal]
    (hx : Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V (x.comap (Ideal.Quotient.mk _)) ∧
      (∃ f ∉ x.comap (Ideal.Quotient.mk _),
        Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent = d :=
  isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K (fun p hp ↦ (hd p hp).ge) _
    Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans (map_maximalIdeal_eq_span_of_irreducible V hϖ).symm) x hx

theorem isSmoothAt_of_flat_of_finrank_cotangent_le_tensor (k : Type*) [Field k] [Algebra V k]
    (hk : Function.Surjective (algebraMap V k)) {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), ringKrullDim ((K ⊗[V] A) ⧸ p) = d)
    (x : Ideal (k ⊗[V] A)) [x.IsMaximal]
    (hx : Module.finrank ((k ⊗[V] A) ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V
        (x.comap (Algebra.TensorProduct.includeRight : A →ₐ[V] k ⊗[V] A).toRingHom) ∧
      (∃ f ∉ x.comap (Algebra.TensorProduct.includeRight : A →ₐ[V] k ⊗[V] A).toRingHom,
        Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank ((k ⊗[V] A) ⧸ x) x.Cotangent = d :=
  isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K (fun p hp ↦ (hd p hp).ge) _
    (TensorProduct.mk_surjective V A k hk) (ker_includeRight_of_surjective V k hk) x hx

end Main

section Scheme

open AlgebraicGeometry CategoryTheory Topology

theorem exists_affine_chart_over {O : Type u} [CommRing O] {X : Scheme.{u}} (f : X ⟶ Spec (.of O))
    (x : X) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra O A) (j : Spec (.of A) ⟶ X)
      (_ : IsOpenImmersion j) (q : PrimeSpectrum A), j q = x ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  obtain ⟨q, hq⟩ : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hxU
  exact ⟨Γ(X, U), inferInstance, φ.hom.toAlgebra, hU.fromSpec, inferInstance, q, hq,
    (Spec.map_preimage _).symm⟩

theorem exists_affine_chart_of_isPullback {O k : Type u} [CommRing O] [CommRing k] [Algebra O k]
    {X X₀ : Scheme.{u}} {f : X ⟶ Spec (.of O)} {i : X₀ ⟶ X} {p : X₀ ⟶ Spec (.of k)}
    (h : IsPullback i p f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    {A : Type u} [CommRing A] [Algebra O A] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A))) :
    ∃ (j₀ : Spec (.of (k ⊗[O] A)) ⟶ X₀) (_ : IsOpenImmersion j₀),
      IsPullback j₀ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[O] k ⊗[O] A).toRingHom)) i j := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O k A)
  rw [← hj] at H
  let j₀ := h.lift _ _ ((Category.assoc _ _ _).trans H.w.symm)
  have h₂ : j₀ ≫ p = _ := h.lift_snd _ _ _
  rw [← h₂] at H
  have H' := IsPullback.of_right H (h.lift_fst _ _ _) h.flip
  exact ⟨j₀, MorphismProperty.of_isPullback H'.flip ‹_›, H'⟩

theorem topologicalKrullDim_range_inter_closure_eq {Y : Scheme.{u}} {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding) ?_
  refine (Set.range_comp _ _).trans
    (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
  refine (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans ?_
  rw [Ideal.mk_ker]
  exact (PrimeSpectrum.closure_singleton q).symm.trans
    ((j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image _).trans
      (congrArg (fun s ↦ j ⁻¹' closure s) Set.image_singleton))

theorem ringKrullDim_localizationAway_eq (K : Type u) [Field K] {C : Type u} [CommRing C]
    [IsDomain C] [Algebra K C] [Algebra.FiniteType K C] {g : C} (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim C := by
  have hle : Submonoid.powers g ≤ nonZeroDivisors C := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  have : FaithfulSMul C (Localization.Away g) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic C (Localization.Away g) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers g)
  obtain ⟨e, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq K C
  rw [h₁]
  exact ringKrullDim_eq_of_trdeg_eq K _ ((trdeg_eq_of_isAlgebraic_top K C _).trans h₂)

theorem topologicalKrullDim_closure_eq_ringKrullDim_quotient {K : Type u} [Field K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p] {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by
  rw [← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y, hy, hj'⟩ := exists_affine_chart_over p z.1
  have : Algebra.FiniteType K C := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap K C))).mp (hj' ▸ inferInstance)
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y, hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y, hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show q' ∈ j' ⁻¹' Set.range j from ⟨q, hq'.symm⟩)
    (j.isOpenEmbedding.isOpen_range.preimage j'.continuous)
  have := q'.isPrime
  have hg' : Ideal.Quotient.mk q'.asIdeal g ≠ 0 := fun h ↦ hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [← ringKrullDim_localizationAway_eq K hg', ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have he := (j'.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q'.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding).comp
    (PrimeSpectrum.localization_comap_isEmbedding
      (Localization.Away (Ideal.Quotient.mk q'.asIdeal g))
      (Submonoid.powers (Ideal.Quotient.mk q'.asIdeal g)))
  refine (he.isInducing.codRestrict (s := Set.range j ∩ closure {j q})
    fun t ↦ ⟨hsub ?_, ?_⟩).topologicalKrullDim_le
  · intro h
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk q'.asIdeal g)))
  · rw [← specializes_iff_mem_closure, ← hq']
    refine ((PrimeSpectrum.le_iff_specializes _ _).mp fun a ha ↦ ?_).map j'.continuous
    change algebraMap _ _ (Ideal.Quotient.mk q'.asIdeal a) ∈ t.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    exact zero_mem _

theorem closure_mem_irreducibleComponents_of_mem_minimalPrimes {Y : Scheme.{u}} {B : Type u}
    [CommRing B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ minimalPrimes B) : closure {j q} ∈ irreducibleComponents Y := by
  refine ⟨isIrreducible_singleton.closure, fun W hW hle ↦ ?_⟩
  have hη := hW.isGenericPoint_genericPoint_closure
  have h₁ : hW.genericPoint ⤳ j q := hη.specializes (subset_closure (hle (subset_closure rfl)))
  obtain ⟨q', hq'⟩ := h₁.mem_open j.isOpenEmbedding.isOpen_range ⟨q, rfl⟩
  rw [← hq'] at h₁ hη
  have h₂ : q'.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes q' q).mpr
    (j.isOpenEmbedding.isInducing.specializes_iff.mp h₁)
  obtain rfl : q' = q := PrimeSpectrum.ext (h₂.antisymm (hq.2 ⟨q'.isPrime, bot_le⟩ h₂))
  exact subset_closure.trans hη.def.ge

variable (V K k : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  [Field k] [Algebra V k] (hk : Function.Surjective (algebraMap V k))
  {X X₀ X₁ : Scheme.{u}} {f : X ⟶ Spec (.of V)} [LocallyOfFiniteType f] [Flat f]
  {i₀ : X₀ ⟶ X} {p₀ : X₀ ⟶ Spec (.of k)} {i₁ : X₁ ⟶ X} {p₁ : X₁ ⟶ Spec (.of K)}
  (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap V k))))
  (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap V K))))

include hk h₀ h₁

theorem exists_smoothOfRelativeDimension_of_flat_of_finrank_cotangentSpace_le {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X₁, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z)
    (x : X₀) (hxc : IsClosed ({x} : Set X₀))
    (hx : Module.finrank (ResidueField (X₀.presheaf.stalk x))
      (CotangentSpace (X₀.presheaf.stalk x)) ≤ d) :
    (∃ U : X.Opens, i₀ x ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f)) ∧
      IsRegularLocalRing (X₀.presheaf.stalk x) ∧ ringKrullDim (X₀.presheaf.stalk x) = d ∧
      Module.finrank (ResidueField (X₀.presheaf.stalk x))
        (CotangentSpace (X₀.presheaf.stalk x)) = d := by
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f (i₀ x)
  have : Algebra.FiniteType V A := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap V A))).mp (hj ▸ inferInstance)
  have : Module.Flat V A := RingHom.flat_algebraMap_iff.mp <|
    (HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (algebraMap V A))).mp (hj ▸ inferInstance)
  have : LocallyOfFiniteType p₁ := MorphismProperty.of_isPullback h₁ ‹_›
  obtain ⟨j₀, _, H₀⟩ := exists_affine_chart_of_isPullback h₀ j hj
  obtain ⟨j₁, _, -⟩ := exists_affine_chart_of_isPullback h₁ j hj
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H₀ x q hq.symm
  have hmax : y.asIdeal.IsMaximal := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp ?_
    have := hxc.preimage j₀.continuous
    rwa [← Set.image_singleton, j₀.isOpenEmbedding.injective.preimage_image] at this
  have hd' (p) (hp : p ∈ minimalPrimes (K ⊗[V] A)) :
      (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p) :=
    (hd _ (closure_mem_irreducibleComponents_of_mem_minimalPrimes j₁ ⟨p, hp.1.1⟩ hp)).trans_eq
      (topologicalKrullDim_closure_eq_ringKrullDim_quotient p₁ j₁ ⟨p, hp.1.1⟩)
  let e : Localization.AtPrime y.asIdeal ≃+* X₀.presheaf.stalk (j₀ y) :=
    (asIso (j₀.stalkMap y) ≪≫ Spec.stalkIso (.of (k ⊗[V] A)) y).commRingCatIsoToRingEquiv.symm
  let : Algebra (k ⊗[V] A) (X₀.presheaf.stalk (j₀ y)) :=
    (e.toRingHom.comp (algebraMap _ _)).toAlgebra
  have : IsLocalization.AtPrime (X₀.presheaf.stalk (j₀ y)) y.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl
      ({ e with commutes' _ := rfl } : Localization.AtPrime y.asIdeal ≃ₐ[k ⊗[V] A] _)
  obtain ⟨-, ⟨g, hg, hs⟩, h⟩ := isSmoothAt_of_flat_of_finrank_cotangentSpace_le V K hd' _
    (TensorProduct.mk_surjective V A k hk) (ker_includeRight_of_surjective V k hk) y.asIdeal _ hx
  refine ⟨?_, h⟩
  let j' := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) ≫ j
  have hs' : SmoothOfRelativeDimension d (j' ≫ f) := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hs)
  refine ⟨j'.opensRange, ?_, ?_⟩
  · obtain ⟨t, ht⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ g, ← hy]
      exact hg
    refine ⟨t, ?_⟩
    rw [← hq, ← ht]
    rfl
  · rw [← j'.isoOpensRange_inv_comp, Category.assoc]
    have := smoothOfRelativeDimension_comp 0 d j'.isoOpensRange.inv (j' ≫ f)
    rwa [zero_add] at this

theorem exists_smoothOfRelativeDimension_of_flat_of_forall_finrank_cotangentSpace_le {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X₁, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z)
    (hx : ∀ x : X₀, IsClosed ({x} : Set X₀) → Module.finrank (ResidueField (X₀.presheaf.stalk x))
      (CotangentSpace (X₀.presheaf.stalk x)) ≤ d) :
    ∃ U : X.Opens, Set.range i₀ ⊆ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f) := by
  have : LocallyOfFiniteType p₀ := MorphismProperty.of_isPullback h₀ ‹_›
  have : JacobsonSpace X₀ := LocallyOfFiniteType.jacobsonSpace p₀
  choose U hU hs using fun x : closedPoints X₀ ↦
    (exists_smoothOfRelativeDimension_of_flat_of_finrank_cotangentSpace_le V K k hk h₀ h₁ hd x.1
      x.2 (hx x.1 x.2)).1
  refine ⟨⨆ x, U x, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := nonempty_inter_closedPoints (Z := closure {z})
      ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    exact ((specializes_iff_mem_closure.mpr hx₁).map i₀.continuous).mem_open (⨆ x, U x).isOpen
      (le_iSup U ⟨x, hx₂⟩ (hU ⟨x, hx₂⟩))
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
    refine IsZariskiLocalAtSource.of_openCover (Scheme.Opens.iSupOpenCover U) fun x ↦ ?_
    have : (Scheme.Opens.iSupOpenCover U).f x ≫ (⨆ x, U x).ι = (U x).ι := by
      simp [Scheme.Opens.iSupOpenCover]
    rw [← Category.assoc, this]
    exact hs x

end Scheme

example (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [PerfectField (ResidueField V)] (x : Ideal (Polynomial (ResidueField V))) [x.IsMaximal] :
    Algebra.IsSmoothAt V (x.comap (Polynomial.mapRingHom (residue V))) ∧
      Module.finrank (Polynomial (ResidueField V) ⧸ x) x.Cotangent = 1 := by
  have h := isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V (FractionRing V)
    (A := Polynomial V) (d := 1) ?_ (Polynomial.mapRingHom (residue V))
    (Polynomial.map_surjective _ residue_surjective)
    (by rw [Polynomial.ker_mapRingHom, ker_residue]; rfl) x ?_
  · exact ⟨h.1, h.2.2.2.2⟩
  · have : IsDomain (FractionRing V ⊗[V] Polynomial V) :=
      (polyEquivTensor V (FractionRing V)).symm.toMulEquiv.isDomain
    intro p hp
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
    rw [hp, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      ringKrullDim_genericFibre_eq V (FractionRing V) (d := 1)
        (by simp [Polynomial.trdeg_of_isDomain])]
  · let := Ideal.Quotient.field x
    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal x
    refine finrank_le_one (x.toCotangent ⟨a, ha.ge (Submodule.mem_span_singleton_self a)⟩)
      fun w ↦ ?_
    obtain ⟨⟨w, hw⟩, rfl⟩ := x.toCotangent_surjective w
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (ha.le hw)
    exact ⟨Ideal.Quotient.mk x c, (map_smul x.toCotangent c _).symm⟩

end GlobalTheory
