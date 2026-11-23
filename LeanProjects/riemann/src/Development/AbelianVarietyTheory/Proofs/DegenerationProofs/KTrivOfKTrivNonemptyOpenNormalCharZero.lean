import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.UU

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivSpread

theorem mono_of_finite {R : Type} [CommRing R] {X : Scheme.{0}} (h : X ⟶ Sp R) [IsFinite h] (e : Sp R ⟶ X)
    (H : ∀ p : PrimeSpectrum R, ∃ (V : Type) (_ : CommRing V) (φ : R →+* V),
      p ∈ Set.range (PrimeSpectrum.comap φ) ∧ ∀ (T : Scheme.{0}) (a : T ⟶ Sp V) (y : T ⟶ X),
        y ≫ h = a ≫ spMap φ → y = a ≫ spMap φ ≫ e) : Mono h := by
  have : IsAffine X := isAffine_of_isAffineHom h
  obtain ⟨B, ψ, i, hi, rfl⟩ : ∃ (B : CommRingCat.{0}) (ψ : CommRingCat.of R ⟶ B) (i : X ⟶ Spec B),
      IsIso i ∧ h = i ≫ Spec.map ψ :=
    ⟨_, Spec.preimage (X.isoSpec.inv ≫ h), X.isoSpec.hom, inferInstance, by simp⟩
  have hf : IsFinite (Spec.map ψ) := by
    rw [← IsIso.inv_hom_id_assoc i (Spec.map ψ)]
    infer_instance
  let : Algebra R B := ψ.hom.toAlgebra
  have : Module.Finite R B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 hf)
  have hs : Function.Surjective ψ.hom := by
    let N : Submodule R B := LinearMap.range (Algebra.linearMap R B)
    suffices hs : Subsingleton (B ⧸ N) from LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hs)
    rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨V, _, φ, ⟨m, rfl⟩, hV⟩ := H p
    let : Algebra R V := φ.toAlgebra
    have e₁ := hV _ (spMap (Algebra.TensorProduct.includeLeftRingHom : V →+* V ⊗[R] B))
      (spMap (Algebra.TensorProduct.includeRight.toRingHom : B →+* V ⊗[R] B) ≫ inv i) (by
        rw [Category.assoc, IsIso.inv_hom_id_assoc]
        exact (DenseFibreIso.isPullback_tensor R V B).w.symm)
    rw [IsIso.comp_inv_eq, Category.assoc, Category.assoc, ← Spec.map_preimage (e ≫ i), ← Spec.map_comp,
      ← Spec.map_comp] at e₁
    have e₂ := Spec.map_injective e₁
    have e₃ : ∀ b : B, (1 : V) ⊗ₜ[R] b = φ ((Spec.preimage (e ≫ i)).hom b) ⊗ₜ[R] (1 : B) := fun b =>
      congrArg (fun q => q.hom b) e₂
    have hsurj : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : V →+* V ⊗[R] B) := by
      intro z
      induction z with
      | zero => exact ⟨0, map_zero _⟩
      | add y z hy hz =>
        obtain ⟨y, rfl⟩ := hy
        obtain ⟨z, rfl⟩ := hz
        exact ⟨y + z, map_add _ _ _⟩
      | tmul c b =>
        refine ⟨c * φ ((Spec.preimage (e ≫ i)).hom b), ?_⟩
        rw [map_mul, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
          ← e₃, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have := (DenseFibreIso.surjective_iff V).1 hsurj
    obtain ⟨a, ha, ha'⟩ := DenseFibreIso.exists_smul_eq_zero (A := R) (N := B ⧸ N) V m
    exact ha (Module.mem_support_iff_of_finite.1 hp (Module.mem_annihilator.2 ha'))
  have := IsClosedImmersion.spec_of_surjective ψ hs
  infer_instance

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left}

theorem inK_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) {T' : Over S'} (x : T' ⟶ A')
    (hx : InK A' (L.pull φ) x) : InK A L (pushPt h.1.w x) := by
  have hL' := pull_isLB hL φ
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst T' A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T' A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T' A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull φ) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

variable (A L) in

def TrivAlong (f : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ f = T.hom → ∀ x : T ⟶ A, InK A L x → x = 1

theorem TrivAlong.comp (h : TrivAlong A L f) {S'' : Scheme.{0}} (g : S'' ⟶ S') : TrivAlong A L (g ≫ f) :=
  fun T a ha => h T (a ≫ g) ((Category.assoc _ _ _).trans ha)

theorem trivAlong_of_kTriv (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hK : KTriv A' (L.pull φ)) :
    TrivAlong A L f := by
  intro T a ha x hx
  have hL' := pull_isLB hL φ
  have hxw : x.left ≫ A.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : Over.mk a ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  let U : Over.mk ((Over.mk a).hom ≫ f) ⟶ T := Over.homMk (𝟙 _) ((Category.id_comp _).trans ha.symm)
  have e₁ : pushPt h.1.w x' = U ≫ x :=
    Over.OverMorphism.ext ((h.1.lift_fst _ _ _).trans (Category.id_comp _).symm)
  have e₂ : x' = 1 := (inK_of_push h hL hL' (PolBaseChange.lbIso_refl hL') x' (e₁ ▸ hx.comp U)).eq_one hK
  have e₃ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [← e₁, MonObj.comp_one]
    exact (congrArg (pushHom h _) e₂).trans (map_one (pushHom h _))
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
    ((congrArg (fun q => q.left) e₃).trans (Category.id_comp _)))

theorem TrivAlong.pull (h : IsGrpPullback A' A f φ) (hL : L.IsLB) {Z : Scheme.{0}} {g : Z ⟶ S'}
    (hK : TrivAlong A L (g ≫ f)) : TrivAlong A' (L.pull φ) g := by
  intro T' a ha x hx
  have e := (hK _ a (by rw [← Category.assoc, ha]; rfl) _ (inK_push h hL x hx)).trans (map_one (pushHom h T')).symm
  exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem exists_dvr (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O] (hf : ¬ IsField O) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : O →+* V),
      Function.Injective ρ ∧ IsLocalHom ρ := by
  obtain ⟨V, hV, hd⟩ := exists_discreteValuationSubring_dominating O (FractionRing O) (FractionRing O) hf
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).1 hd
  exact ⟨V, inferInstance, inferInstance, hV, (algebraMap O (FractionRing O)).codRestrict V h1, fun a b hab =>
    IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val hab), h2⟩

theorem kTriv_of_primes (hG : GlobalFnsSt) (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (N : LB B.left) (hN : N.IsLB) (ha : RelAmple B N)
    (h : ∀ p : PrimeSpectrum R, ∃ (V : Type) (_ : CommRing V) (ψ : R →+* V),
      p ∈ Set.range (PrimeSpectrum.comap ψ) ∧ TrivAlong B N (spMap ψ)) : KTriv B N := by
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B N hN).1 ha
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B N hN
  obtain ⟨H, k, hk, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB ⟨_, isLB_pw hN _, n, s, hs⟩ N (pw N 0) hN hO
  have hfin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG R B hB N (pw N 0) hN hO ha H k hk hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), InK B N x ↔ ∃ y : T ⟶ H, y ≫ k = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono k := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono k.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hN (𝟙_ _))
  have he' : ∀ T : Over (Spec (CommRingCat.of R)), (toUnit T ≫ e) ≫ k = 1 := fun T => by
    rw [Category.assoc, he, MonObj.comp_one]
  have hmono : Mono H.hom := by
    refine mono_of_finite H.hom e.left fun p => ?_
    obtain ⟨V, _, ψ, hψ, hV⟩ := h p
    refine ⟨V, inferInstance, ψ, hψ, fun T a y hy => ?_⟩
    let y' : Over.mk (a ≫ spMap ψ) ⟶ H := Over.homMk y hy
    have e₁ : y' = toUnit _ ≫ e := by
      rw [← cancel_mono k, he']
      exact hV _ a rfl _ ((hrep _ _).2 ⟨y', rfl⟩)
    exact (congrArg (fun q => q.left) e₁).trans (Category.assoc _ _ _)
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  have e₁ : y = toUnit T ≫ e :=
    Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w (toUnit T ≫ e)).symm))
  rw [e₁, he']

section Affine

variable [IsCommMonObj A] {R : Type} [CommRing R]

omit [IsCommMonObj A] in

theorem relAmple_chart (j : Sp R ⟶ S) [IsOpenImmersion j] (g : S' ⟶ Sp R) (hL : L.IsLB) (hA : RelAmple A L) :
    RelAmple ((Over.pullback (g ≫ j)).obj A) (L.pull (pullback.fst A.hom (g ≫ j))) := by
  have hL' := pull_isLB hL (pullback.fst A.hom (g ≫ j))
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
  exact relAmple_pull (A' := (Over.pullback (g ≫ j)).obj A) (IsPullback.of_hasPullback _ _) hL hL'
    ((isGen_iff w).1 hw) j.opensRange (isAffineOpen_opensRange j) (fun y => ⟨g y, rfl⟩) hA

theorem trivAlong_dvr (hG : GlobalFnsSt) (j : Sp R ⟶ S) [IsOpenImmersion j] (hA : IsAbelianScheme A) (M : RigLB A)
    (c : CubicalStr A M) (ha : RelAmple A M.L) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CharZero V] (g : Sp V ⟶ Sp R)
    (h : TrivAlong A M.L ((TF (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ g ≫ j)) :
    TrivAlong A M.L (g ≫ j) := by
  have hp := isGrpPullback_pullback A (g ≫ j)
  obtain ⟨hL, hr, ⟨c', -⟩, -⟩ := CubePf.cubePull S _ A _ (cubeMapOf hp) M c
  refine trivAlong_of_kTriv hp M.isLB (GlobalTheory.KTrivGeneric.kTriv_of_generic hG V _ (TLinPf.isAb_pullback _ A hA)
    ((cubeMapOf hp).rigLB M hL hr) c' (relAmple_chart j g M.isLB ha) fun x hx => ?_)
  exact h.pull hp M.isLB _ (𝟙 _) (Category.id_comp _) x hx

omit [IsCommMonObj A] in

theorem trivAlong_generic [IsDomain R] [IsIntegral S] (j : Sp R ⟶ S) [IsOpenImmersion j] (U : S.Opens)
    (hU : (U : Set S).Nonempty) (h : TrivAlong A L U.ι) (F : Type) [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ j) := by
  have hr : Set.range (spMap ψ ≫ j) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨_, hz, z, rfl⟩ := nonempty_preirreducible_inter U.isOpen j.isOpenEmbedding.isOpen_range hU
      ⟨_, (⊥ : PrimeSpectrum R), rfl⟩
    have hs : spMap ψ y ⤳ z := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
      have h0 : ψ r = 0 := by
        by_contra h0
        exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (Ne.isUnit h0))
      rw [hψ (h0.trans (map_zero ψ).symm)]
      exact zero_mem _
    exact (hs.map j.continuous).mem_open U.isOpen hz
  rw [← IsOpenImmersion.lift_fac U.ι _ hr]
  exact h.comp _

theorem exists_trivAlong (hG : GlobalFnsSt) [IsDomain R] [IsNoetherianRing R] [CharZero R] [IsIntegral S]
    (j : Sp R ⟶ S) [IsOpenImmersion j] (hA : IsAbelianScheme A) (M : RigLB A) (c : CubicalStr A M)
    (ha : RelAmple A M.L) (U : S.Opens) (hU : (U : Set S).Nonempty) (h : TrivAlong A M.L U.ι) (p : PrimeSpectrum R) :
    ∃ (V : Type) (_ : CommRing V) (ψ : R →+* V),
      p ∈ Set.range (PrimeSpectrum.comap ψ) ∧ TrivAlong A M.L (spMap ψ ≫ j) := by
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    exact @trivAlong_generic S A _ M.L R _ _ _ j _ U hU h O hf.toField (algebraMap R O) hO
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩,
      trivAlong_dvr hG j hA M c ha V _ ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · let F := AlgebraicClosure (FractionRing V)
      have H := trivAlong_generic j U hU h F
        ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
        ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
      have e : (TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
          ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
        (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
      rw [← e, Category.assoc] at H
      exact H

theorem trivAlong_chart (hG : GlobalFnsSt) (j : Sp R ⟶ S) [IsOpenImmersion j] (hA : IsAbelianScheme A)
    (hL : L.IsLB) (ha : RelAmple A L)
    (h : ∀ p : PrimeSpectrum R, ∃ (V : Type) (_ : CommRing V) (ψ : R →+* V),
      p ∈ Set.range (PrimeSpectrum.comap ψ) ∧ TrivAlong A L (spMap ψ ≫ j)) : TrivAlong A L j := by
  have ha' := relAmple_chart j (𝟙 _) hL ha
  rw [Category.id_comp j] at ha'
  have hp := isGrpPullback_pullback A j
  refine trivAlong_of_kTriv hp hL (kTriv_of_primes hG R _ (TLinPf.isAb_pullback j A hA) _ (pull_isLB hL _) ha'
    fun p => ?_)
  obtain ⟨V, _, ψ, hψ, hV⟩ := h p
  exact ⟨V, inferInstance, ψ, hψ, hV.pull hp hL⟩

end Affine

theorem kTriv_of_open_integral : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L := by
  intro hl S _ _ hn U hU G _ _ L c hG ha hK
  have hU' := trivAlong_of_kTriv (isGrpPullback_pullback G U.ι) L.isLB hK
  refine kTriv_iff_forall.2 fun T x hx => Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun τ => ?_)
  obtain ⟨R, j, _, hj, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := T.hom τ) (U := ⊤) trivial
  have : Nonempty (Spec R) := ⟨hj.choose⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)
  have : CharZero Γ(S, ⊤) := charZero_of_inj_zero fun n h => by_contra fun h' => hn n h' h
  have : Nonempty (j ''ᵁ ⊤) := ⟨⟨_, hj.choose, trivial, rfl⟩⟩
  have : CharZero Γ(S, j ''ᵁ ⊤) :=
    charZero_of_injective_ringHom (map_injective_of_isIntegral S (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)))
  have : CharZero R := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (j.appIso ⊤ ≪≫ Scheme.ΓSpecIso R).hom).1
  have h := trivAlong_chart (R := R) hl.globalFns j hG L.isLB ha
    (exists_trivAlong (R := R) hl.globalFns j hG L c ha U hU hU')
  let W := T.hom ⁻¹ᵁ j.opensRange
  let u : Over.mk (W.ι ≫ T.hom) ⟶ T := Over.homMk W.ι rfl
  have hr : Set.range (W.ι ≫ T.hom) ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  have e := h (Over.mk (W.ι ≫ T.hom)) (IsOpenImmersion.lift j _ hr) (IsOpenImmersion.lift_fac _ _ _) _ (hx.comp u)
  exact ⟨W, hj, congrArg (fun q => q.left) (e.trans (MonObj.comp_one u).symm)⟩

end GlobalTheory.KTrivSpread

theorem GlobalTheory.KTrivSpread.kTriv_of_open_normal : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L :=
  fun hl S _ _ _ => GlobalTheory.KTrivSpread.kTriv_of_open_integral hl S
