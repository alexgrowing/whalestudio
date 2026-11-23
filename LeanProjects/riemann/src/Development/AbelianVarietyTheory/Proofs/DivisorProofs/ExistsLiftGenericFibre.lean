import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep.Setup

def RootsIn {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) (F : Polynomial V) : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (ψ : V₁ →+* D) (d : D), F.eval₂ (ψ.comp ρ) d = 0 → d ∈ ψ.range

theorem rootsIn_of_splits {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) {F : Polynomial V} (hF : F.Monic)
    (h : (F.map ρ).Splits) : RootsIn ρ F := by
  intro D _ _ ψ d hd
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 h
  rw [← Polynomial.eval₂_map, hm, (hF.map ρ).leadingCoeff, map_one, _root_.one_mul, Polynomial.eval₂_multiset_prod,
    Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  obtain ⟨a, -, ha⟩ := hd
  exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩

theorem exists_ext (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V) (L : Type) [Field L]
    [Algebra (FractionRing V) L] [FiniteDimensional (FractionRing V) L] (F : Polynomial V) (hF : F.Monic) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (σ : L →+* FractionRing V₁),
      GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧
      (σ.comp (algebraMap (FractionRing V) L)).comp (algebraMap V _) = (algebraMap V₁ _).comp ρ ∧ RootsIn ρ F := by
  haveI := hV.2
  let K := FractionRing V
  let F₁ : Polynomial L := F.map ((algebraMap K L).comp (algebraMap V K))
  let L₂ := F₁.SplittingField
  haveI : FiniteDimensional K L₂ := Module.Finite.trans L L₂
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K L₂ 1 le_rfl
  obtain ⟨V₁, _, _, _, ρ, e, -, hρ, he, -, -⟩ := MumLevel.exists_ring V hV E ζ 1 le_rfl hζ
  let τ : L₂ →+* FractionRing V₁ := e.toRingHom.comp j.toRingHom
  have hσ : ((τ.comp (algebraMap L L₂)).comp (algebraMap K L)).comp (algebraMap V K) = (algebraMap V₁ _).comp ρ :=
    RingHom.ext fun r => (congrArg e ((congrArg j (IsScalarTower.algebraMap_apply K L L₂ _).symm).trans
      (j.commutes _))).trans (he r)
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  haveI := hρ.1.2.2.1
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, τ.comp (algebraMap L L₂),
    ⟨hρ.1, (ρ.charZero_iff hρ.2.1).1 inferInstance⟩, hρ.2.1, hρ.2.2, hσ, rootsIn_of_splits ρ hF ?_⟩
  refine Polynomial.Splits.of_splits_map_of_injective hinj ?_ fun a ha => ?_
  · have := (Polynomial.SplittingField.splits F₁).map τ
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hσ] at this
    rwa [Polynomial.map_map]
  · exact IsIntegrallyClosed.isIntegral_iff.1 ⟨F.map ρ, hF.map ρ, by
      rw [← Polynomial.eval_map]; exact (Polynomial.mem_roots'.1 ha).2⟩

theorem RootsIn.exists_sq {V V₁ : Type} [CommRing V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {F : Polynomial V}
    (h : RootsIn ρ F) {s : V} (hs : Polynomial.X ^ 2 - Polynomial.C s ∣ F) : ∃ r : V₁, r ^ 2 = ρ s := by
  let D := AlgebraicClosure (FractionRing V₁)
  let ψ : V₁ →+* D := (algebraMap (FractionRing V₁) D).comp (algebraMap V₁ _)
  have hψ : Function.Injective ψ := (algebraMap (FractionRing V₁) D).injective.comp (IsFractionRing.injective V₁ _)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (ρ s)) two_pos
  obtain ⟨G, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := h D ψ d (by simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, hd])
  exact ⟨r, hψ (by rw [map_pow, hd])⟩

open TensorProduct in

theorem exists_poly_sections (V B : Type) [CommRing V] [CommRing B] [Algebra V B] [Module.Finite V B] [Module.Flat V B] :
    ∃ F : Polynomial V, F.Monic ∧ ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (G : Polynomial V),
      RootsIn ρ (F * G) → ∀ (K : Type) [Field K] (x : V₁ →+* K) (p : B →+* K), p.comp (algebraMap V B) = x.comp ρ →
        ∃ s : B →+* V₁, s.comp (algebraMap V B) = ρ ∧ x.comp s = p := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := V) (M := B)
  choose f hf hf0 using fun b : B => Algebra.IsIntegral.isIntegral (R := V) b
  refine ⟨∏ b ∈ t, f b, Polynomial.monic_prod_of_monic _ _ fun b _ => hf b, fun V₁ _ _ ρ G hR K _ x p hp => ?_⟩
  letI := ρ.toAlgebra
  letI := x.toAlgebra
  letI := (x.comp ρ).toAlgebra
  haveI : IsScalarTower V V₁ K := IsScalarTower.of_algebraMap_eq' rfl
  let p' : B →ₐ[V] K := ⟨p, fun a => RingHom.congr_fun hp a⟩
  let Q : V₁ ⊗[V] B →ₐ[V₁] K := Algebra.TensorProduct.lift (Algebra.ofId V₁ K) p' fun _ _ => Commute.all _ _
  haveI : (RingHom.ker Q).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqp, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal V₁))
    (q := (RingHom.ker Q).under V₁) (RingHom.ker Q) bot_le
  let ψ : V₁ →+* (V₁ ⊗[V] B) ⧸ q := algebraMap _ _
  let β : B →+* (V₁ ⊗[V] B) ⧸ q := (Ideal.Quotient.mk q).comp Algebra.TensorProduct.includeRight.toRingHom
  have hβ : β.comp (algebraMap V B) = ψ.comp ρ := RingHom.ext fun a => by
    show Ideal.Quotient.mk q (Algebra.TensorProduct.includeRight (R := V) (A := V₁) (algebraMap V B a)) = Ideal.Quotient.mk q _
    rw [AlgHom.commutes]
    rfl
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.under V₁ := (Ideal.Quotient.eq_zero_iff_mem (I := q)).1 ha
    rwa [← hlo.over, Ideal.mem_bot] at this
  have hr : ∀ b, β b ∈ ψ.range := fun b => by
    have hb : b ∈ Submodule.span V (t : Set B) := ht ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine hR _ ψ _ ?_
      obtain ⟨g, hg⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hb)
      rw [hg, ← hβ, ← Polynomial.hom_eval₂, Polynomial.eval₂_mul, Polynomial.eval₂_mul, hf0, zero_mul, zero_mul, map_zero]
    | zero => exact map_zero β ▸ zero_mem _
    | add a b _ _ ha hb => exact map_add β a b ▸ add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact mul_mem ⟨ρ c, (RingHom.congr_fun hβ c).symm⟩ ha
  let e : V₁ ≃+* ψ.range := RingEquiv.ofBijective ψ.rangeRestrict
    ⟨fun a b h => hψ (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩
  let s : B →+* V₁ := e.symm.toRingHom.comp (β.codRestrict _ hr)
  have hs : ∀ b, ψ (s b) = β b := fun b => congrArg Subtype.val (e.apply_symm_apply ⟨β b, hr b⟩)
  refine ⟨s, RingHom.ext fun a => hψ ((hs _).trans (RingHom.congr_fun hβ a)), RingHom.ext fun b => ?_⟩
  have h1 : Q (algebraMap V₁ _ (s b) - Algebra.TensorProduct.includeRight b) = 0 :=
    hq (Ideal.Quotient.eq.1 (hs b))
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h1
  exact h1.trans (by simp [Q, p'])

theorem exists_poly_points (V : Type) [CommRing V] [IsLocalRing V] (T : Scheme.{0}) (q : T ⟶ Sp V) [IsFinite q] [Flat q] :
    ∃ F : Polynomial V, F.Monic ∧ ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (G : Polynomial V),
      RootsIn ρ (F * G) → Finite {s : Sp V₁ ⟶ T // s ≫ q = spMap ρ} ∧
        ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp V₁) (p : Sp K ⟶ T), p ≫ q = x ≫ spMap ρ →
          ∃ s : Sp V₁ ⟶ T, s ≫ q = spMap ρ ∧ x ≫ s = p := by
  haveI : IsAffine T := isAffine_of_isAffineHom q
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (T.isoSpec.inv ≫ q)
  letI := φ.hom.toAlgebra
  haveI : Module.Finite V Γ(T, ⊤) := (IsFinite.SpecMap_iff φ).1 (hφ ▸ inferInstance)
  haveI : Module.Flat V Γ(T, ⊤) := (Flat.SpecMap_iff (f := φ)).1 (hφ ▸ inferInstance)
  haveI : Module.Free V Γ(T, ⊤) := Module.free_of_flat_of_isLocalRing
  have key : ∀ (W : Type) [CommRing W] (s : Sp W ⟶ T) (χ : V →+* W), s ≫ q = spMap χ →
      (Spec.preimage (s ≫ T.isoSpec.hom)).hom.comp φ.hom = χ := fun W _ s χ h =>
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := φ ≫ Spec.preimage (s ≫ T.isoSpec.hom))
      (a₂ := CommRingCat.ofHom χ) (by rw [Spec.map_comp, Spec.map_preimage, hφ, Category.assoc, Iso.hom_inv_id_assoc, h]))
  obtain ⟨F, hF, H⟩ := exists_poly_sections V Γ(T, ⊤)
  refine ⟨F, hF, fun V₁ _ _ ρ G hR => ⟨?_, fun K _ x p hp => ?_⟩⟩
  · letI := ρ.toAlgebra
    refine Finite.of_injective (β := Γ(T, ⊤) →ₐ[V] V₁)
      (fun s => ⟨(Spec.preimage (s.1 ≫ T.isoSpec.hom)).hom, RingHom.congr_fun (key V₁ s.1 ρ s.2)⟩) fun s s' h => ?_
    have h1 : Spec.preimage (s.1 ≫ T.isoSpec.hom) = Spec.preimage (s'.1 ≫ T.isoSpec.hom) :=
      CommRingCat.hom_ext (congrArg AlgHom.toRingHom h)
    have h2 := congrArg Spec.map h1
    rw [Spec.map_preimage, Spec.map_preimage, cancel_mono] at h2
    exact Subtype.ext h2
  · obtain ⟨x, rfl⟩ := Spec.map_surjective x
    obtain ⟨s, hs, hx⟩ := H V₁ ρ G hR K x.hom _ (key K p _ (hp.trans (Spec.map_comp _ _).symm))
    refine ⟨spMap s ≫ T.isoSpec.inv, ?_, ?_⟩
    · rw [Category.assoc, ← hφ, ← hs]
      exact (Spec.map_comp _ _).symm
    · rw [← Category.assoc, Iso.comp_inv_eq, ← Spec.map_preimage (p ≫ _), ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext hx)

theorem exists_poly_torsion (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (P : PolAV (Sp V)) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ F : Polynomial V, F.Monic ∧ ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (G : Polynomial V),
      RootsIn ρ (F * G) → ∀ (A : Over (Sp V₁)) [GrpObj A] (φ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ρ) φ →
        ∃ (C : Type) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ A)), Finite C ∧
          ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ A), p ^ m = 1 → ∃ c, p = toUnit _ ≫ b c := by
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN _ P m hm
  let e : Sp V ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w (η[P.A])
  have hfst : pullback.fst (mulA P.A m).left e ≫ P.A.hom = pullback.snd _ _ := by
    rw [← Over.w (mulA P.A m), ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  obtain ⟨F, hF, H⟩ := exists_poly_points V _ (pullback.snd (mulA P.A m).left e)
  refine ⟨F, hF, fun V₁ _ _ ρ G hR A _ φ hφ => ?_⟩
  obtain ⟨hfin, hex⟩ := H V₁ ρ G hR
  have w : ∀ s : {s : Sp V₁ ⟶ pullback (mulA P.A m).left e // s ≫ pullback.snd _ _ = spMap ρ},
      (s.1 ≫ pullback.fst _ _) ≫ P.A.hom = 𝟙 _ ≫ spMap ρ := fun s => by
    rw [Category.assoc, hfst, s.2, Category.id_comp]
  refine ⟨_, fun s => Over.homMk (hφ.1.lift _ _ (w s)) (hφ.1.lift_snd _ _ _), hfin, fun K _ x p hp => ?_⟩
  let t : (Over.mk x ⟶ A) →* (Over.mk (x ≫ spMap ρ) ⟶ P.A) :=
    MonoidHom.mk' (toBase hφ.1.w) fun a b => Over.OverMorphism.ext (hφ.2 _ a b _ _ rfl rfl).symm
  have h1 : t p ≫ mulA P.A m = toUnit _ ≫ η[P.A] := by
    rw [mulA, MonObj.comp_pow, Category.comp_id, ← map_pow, hp, map_one, Hom.one_def]
  have h2 : (p.left ≫ φ) ≫ (mulA P.A m).left = (x ≫ spMap ρ) ≫ e := congrArg (·.left) h1
  obtain ⟨s, hs, hx⟩ := hex K x (pullback.lift _ _ h2) (pullback.lift_snd _ _ _)
  refine ⟨⟨s, hs⟩, Over.OverMorphism.ext (hφ.1.hom_ext ?_ ?_)⟩
  · show p.left ≫ φ = (x ≫ hφ.1.lift _ _ (w ⟨s, hs⟩)) ≫ φ
    rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, hx, pullback.lift_fst]
  · rw [Over.w, Over.w]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

open GlobalTheory.UPoinc.GSetup in

theorem exists_model (C : UCompact Xo c) (x₀ : Xo.XF c) (n : ℕ) (hn : n.Prime) (ho : Odd n) (j₀ : ℕ) :
    ∃ (j : ℕ) (o₁ Ω : Type) (_ : CommRing o₁) (_ : Field Ω) (_ : Algebra o₁ Ω) (_ : ArithBase o₁ Ω) (S : ThetaSys o₁ Ω)
      (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c) (M : RatModel o₁ Ω) (U : C.Z.Opens) (g : M.Z ⟶ U.toScheme),
      j₀ ≤ j ∧ S.Big ∧ ρ.n = n ∧ S.r * S.N = (n ^ j) ^ 2 ∧ UOver Xo c ρ.P (toRat S.R) u ∧
      (∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w = x₀) ∧
      M.pt ≫ g ≫ U.ι = spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i ∧ GlobalTheory.IsNormalScheme M.Z ∧ IsFinite g ∧
      Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    GSetup.exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x₀
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = x₀ := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = x₀
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, hS₀, hU₀⟩ := exists_fibre Xo c y
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_level A₀.g n hn.two_le 0
  have hpos : 1 ≤ (n ^ (2 * (j₀ + j₁)) * (n ^ k) ^ 2) ^ 2 := Nat.one_le_iff_ne_zero.2 (by have := hn.pos; positivity)
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ := exists_level_finite P.ResidueField A₀ _ hpos
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  have hS₁ : HypS A₁.A A₁.L :=
    SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A₀.isLB A₁.isLB hA₁.2.1 (LBIso.symm hA₁.2.2) hS₀
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded

  have hnF : C.b (n : C.o) ≠ 0 := by rw [map_natCast]; exact Nat.cast_ne_zero.2 hn.ne_zero
  have hno : (n : C.o) ≠ 0 := fun h => hnF (by rw [h, map_zero])
  have hle : Submonoid.powers (n : C.o) ≤ nonZeroDivisors C.o := powers_le_nonZeroDivisors_of_noZeroDivisors hno
  let o' := Localization.Away (n : C.o)
  haveI : IsDomain o' := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain o' := IsLocalization.isDedekindDomain C.o hle o'
  let b' : o' →+* c.F := IsLocalization.Away.lift (n : C.o) (IsUnit.mk0 _ hnF)
  have hb' : b'.comp (algebraMap C.o o') = C.b := IsLocalization.Away.lift_comp _ _
  letI : Algebra o' c.F := b'.toAlgebra
  haveI : IsScalarTower C.o o' c.F := IsScalarTower.of_algebraMap_eq' hb'.symm
  haveI : IsFractionRing o' c.F := IsFractionRing.isFractionRing_of_isLocalization _ o' c.F hle
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ := exists_base_root o' c.F Ω β ze _ hpos hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    have h₁ : (algebraMap ℤ C.o).FiniteType := RingHom.finiteType_algebraMap.2 C.ft
    have h₂ : (algebraMap C.o o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h₃ := hκ.finiteType.comp (h₂.comp h₁)
    rw [RingHom.ext_int (κ.comp _) (algebraMap ℤ o₁)] at h₃
    exact RingHom.finiteType_algebraMap.1 h₃
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (n : o₁) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := o') (n : C.o)).map κ
  rw [← hze₁] at lev
  have hβ : β.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp hφ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := A) (S := P.ResidueField)).2 inferInstance)) hf.finiteType.essFiniteType
  obtain ⟨R₀, hR₀, hfr, hR₀e⟩ := exists_fg_ratHull b' (fun y => exists_int_mul_mem y) κ β hcomp hβ φ hφ (f.comp ev) rfl
  let u₀ : Sp (ratHull R₀) ⟶ Xo.XF c := spMap ((f.comp ev).codRestrict (ratHull R₀) hR₀e) ≫ j
  have hu₀ : spMap (ratHull R₀).val.toRingHom ≫ u₀ = spMap f ≫ y := by
    simp only [u₀, y, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨S, ρ, u, hN, hr, hg, hUS, hpt⟩ :=
    exists_thetaSys_uOver Xo c R₀ hR₀ hfr u₀ A₁ (hu₀ ▸ hU₁) hS₁ n k _ hn ho hk (by omega) hun ze₁ lev
  have hbig : S.Big := big _ (by omega) o₁ Ω S (hg.trans hA₁.1) hN hr
  have hρn : ρ.n = n := by
    have h₁ : ρ.n ∣ (n ^ k) ^ 2 := by
      rw [← hN, ρ.N_eq]
      exact dvd_pow (dvd_pow_self _ (by have := ρ.two_le; omega)) two_ne_zero
    exact (Nat.prime_dvd_prime_iff_eq ρ.n_prime hn).1 (ρ.n_prime.dvd_of_dvd_pow (ρ.n_prime.dvd_of_dvd_pow h₁))
  have hp : spMap (ratHull S.R).val.toRingHom ≫ u = spMap f ≫ spMap ev ≫ j := hpt.trans hu₀
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.iF_open
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)

  let a : Sp o' ⟶ Sp C.o := spMap (algebraMap C.o o')
  haveI : IsOpenImmersion a := IsOpenImmersion.of_isLocalization (n : C.o)
  have hba : spMap b' ≫ a = spMap C.b := by rw [← hb']; exact (Spec.map_comp _ _).symm
  let inc : pullback C.z a ⟶ C.Z := pullback.fst _ _
  let gf : pullback C.z (spMap C.b) ⟶ pullback C.z a := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap b')
    (by rw [Category.assoc, hba, pullback.condition])
  have hgf : gf ≫ inc = pullback.fst _ _ := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (gf ≫ inc) := hgf ▸ inferInstance
  haveI : IsPreimmersion gf := IsPreimmersion.of_comp gf inc
  have hpz : (spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf) ≫ pullback.snd _ _ = spMap ((algebraMap o₁ Ω).comp κ) := by
    simp only [Category.assoc, gf, pullback.lift_snd]
    rw [← Category.assoc C.iF, C.iF_over, ← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨M, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization o' o₁ Ω κ hκ _ (pullback.snd C.z a) inferInstance
    inferInstance inferInstance _ hpz hst
  refine ⟨j₀ + j₁ + k, o₁, Ω, inferInstance, inferInstance, inferInstance, inferInstance, S, ρ, u, M, inc.opensRange,
    π ≫ inc.isoOpensRange.hom, by omega, hbig, hρn, by rw [hr, hN]; ring, hUS, fun w => by rw [hp]; exact hy _, ?_,
    GlobalTheory.IsNormalScheme.of_pred hMn, inferInstance, ?_⟩
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, hMp, ← Category.assoc _ u, hp]
    simp only [Category.assoc, hgf]
  · rintro _ ⟨x, rfl⟩
    exact ⟨gf x, by rw [← Scheme.Hom.comp_apply, hgf]⟩

theorem exists_lift_genericFibre (C : UCompact Xo c) {O W : Type} [CommRing O] [CommRing W] (ev : O →+* W) [IsLocalHom ev]
    (t : Sp O ⟶ C.Z) (ξ : Sp W ⟶ pullback C.z (spMap C.b)) (h : spMap ev ≫ t = ξ ≫ pullback.fst _ _) :
    ∃ ζ : Sp O ⟶ pullback C.z (spMap C.b), ζ ≫ pullback.fst _ _ = t := by
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ C.z)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (ξ ≫ pullback.snd _ _)
  have e : φ ≫ CommRingCat.ofHom ev = CommRingCat.ofHom C.b ≫ β := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (φ.hom a) := fun a => by
    refine (isUnit_map_iff ev _).1 ?_
    rw [show ev (φ.hom a) = β.hom (C.b a) from congrArg (fun χ => χ.hom a.1) e]
    exact (IsLocalization.map_units c.F a).map β.hom
  refine ⟨pullback.lift t (spMap (IsLocalization.lift (S := c.F) hu)) ?_, pullback.lift_fst _ _ _⟩
  rw [← hφ, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsLocalization.lift_comp (S := c.F) hu).symm)

theorem fromSpecStalk_bot {X : Scheme.{0}} [IsIntegral X] (z : X) (p : Sp (X.presheaf.stalk z)) (hp : p.asIdeal = ⊥) :
    X.fromSpecStalk z p = genericPoint X := by
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  have h : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (show p.asIdeal ≤ q.asIdeal from hp ▸ bot_le)
  exact ((hq ▸ h.map (X.fromSpecStalk z).continuous).antisymm (genericPoint_specializes _)).eq

theorem exists_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (o₁ Ω₁ : Type) (_ : CommRing o₁) (_ : Field Ω₁) (_ : Algebra o₁ Ω₁) (_ : ArithBase o₁ Ω₁) (S : ThetaSys o₁ Ω₁) (ρS : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c) (Mm : RatModel o₁ Ω₁) (π : Mm.Z ⟶ C.Z) (z₁ : Mm.Z) (ζ : Sp (Mm.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : Mm.Z.presheaf.stalk z₁ →+* V₁) (D₁ : DegPre V₁) (_ : IsPullDeg ρ₁ Cm.P.D.toPre D₁) (r : Fin Cm.m → V₁) (Cb : Type) (bs : Cb → (𝟙_ (Over (Sp V₁)) ⟶ D₁.P.A)), j₀ ≤ j ∧ S.Big ∧ ρS.n = n ∧ S.r * S.N = (n ^ j) ^ 2 ∧ UOver Xo c ρS.P (toRat S.R) u ∧ (∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w ∈ genericPoints (Xo.XF c)) ∧ Mm.pt ≫ π = spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i ∧ IsCov C π z₁ ζ ∧ GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ (∀ k, r k ^ 2 = ρ₁ (Cm.s k)) ∧ Finite Cb ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D₁.P.A), p ^ ((n ^ j) ^ 2) = 1 → ∃ c', p = toUnit _ ≫ bs c' := by
  intro E _ _ _ H Dw _ l Xo c C φ V _ _ _ Cm hV ξ hξ n hn ho j₀
  classical
  haveI := hV.1.1
  obtain ⟨x₀, hx₀, hsp⟩ := exists_mem_genericPoints_specializes (Cm.y (closedPoint (FractionRing V)))
  obtain ⟨j, o₁, Ω, _, _, _, _, S, ρS, u, M, U, g, hj, hbig, hρn, hrN, hU, hgen, hpt, hMn, hg, hrange⟩ :=
    exists_model C x₀ n hn ho j₀

  have hr : Set.range (ξ ≫ pullback.fst _ _ :) ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hrange ⟨ξ p, rfl⟩
  let f : Sp V ⟶ U.toScheme := IsOpenImmersion.lift U.ι _ hr
  have hf : f ≫ U.ι = ξ ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
  have h₁ : U.ι (g (M.pt (closedPoint Ω))) = C.i x₀ := by
    rw [← hgen (closedPoint Ω)]
    exact congrArg (fun χ : Sp Ω ⟶ C.Z => χ (closedPoint Ω)) hpt
  have hmem : (jK V ≫ f) (closedPoint (FractionRing V)) ∈ Set.range g := by
    have h₂ : U.ι ((jK V ≫ f) (closedPoint (FractionRing V))) = C.i (Cm.y (closedPoint (FractionRing V))) :=
      congrArg (fun χ : Sp (FractionRing V) ⟶ C.Z => χ (closedPoint (FractionRing V)))
        (show (jK V ≫ f) ≫ U.ι = Cm.y ≫ C.i by rw [Category.assoc, hf, ← Category.assoc, ← hξ, Category.assoc])
    have h₃ : g (M.pt (closedPoint Ω)) ⤳ (jK V ≫ f) (closedPoint (FractionRing V)) := by
      rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, h₁, h₂]
      exact hsp.map C.i.continuous
    exact h₃.mem_closed g.isClosedMap.isClosed_range ⟨_, rfl⟩
  have hsurj : Surjective (pullback.snd g (jK V ≫ f)) := ⟨fun p => by
    obtain rfl : p = closedPoint (FractionRing V) := Subsingleton.elim (α := PrimeSpectrum _) _ _
    show _ ∈ Set.range (pullback.snd g (jK V ≫ f))
    rw [Scheme.Pullback.range_snd]
    exact hmem⟩
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.FinLift.lift_point_finite_surjective (FractionRing V) _ _ (𝟙 _)
    (pullback.snd g (jK V ≫ f)) inferInstance hsurj

  obtain ⟨F, hF, HF⟩ := exists_poly_torsion V Cm.P.D.toPre.P ((n ^ j) ^ 2)
    (Nat.one_le_iff_ne_zero.2 (by have := hn.pos; positivity))
  let G : Polynomial V := ∏ k, (Polynomial.X ^ 2 - Polynomial.C (Cm.s k))
  have hG : G.Monic := Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_pow_sub_C _ two_ne_zero
  obtain ⟨V₁, _, _, _, ρ₁, σ, hV₁, hinj, hfin, hσ, hR⟩ := exists_ext V hV L (F * G) (hF.mul hG)
  choose r hr₂ using fun k => hR.exists_sq
    ((Finset.dvd_prod_of_mem (fun k => Polynomial.X ^ 2 - Polynomial.C (Cm.s k)) (Finset.mem_univ k)).mul_left F)
  obtain ⟨z₁, ev, hloc, hev, -⟩ := GlobalTheory.FiniteLift.exists_stalk_lift V₁ hV₁.1.2.2.1 M.Z _ g hg (spMap ρ₁ ≫ f)
    (spMap σ ≫ yL ≫ pullback.fst _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc yL, hyL, Category.comp_id]
      simp only [← Category.assoc, ← Spec.map_comp]
      exact congrArg (fun χ => spMap χ ≫ f) hσ)
  have hev' : spMap ev ≫ M.Z.fromSpecStalk z₁ ≫ g ≫ U.ι = (spMap ρ₁ ≫ ξ) ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← hf, ← Category.assoc _ f, ← hev]
    simp only [Category.assoc]
  obtain ⟨ζ, hζ⟩ := exists_lift_genericFibre C ev _ _ hev'
  haveI : IsPreimmersion (spMap C.b) := by
    letI : Algebra C.o c.F := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)

  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V _ hV.1 Cm.P.D
  have hgen' : specOf ρ₁ (genericPoint (Spec (CommRingCat.of V₁))) ∈ Wo := by
    have : specOf ρ₁ (genericPoint (Spec (CommRingCat.of V₁))) = genericPoint (Spec (CommRingCat.of V)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ₁ hinj)
    rw [this]; exact hWo
  obtain ⟨D₁, hD, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg GlobalTheory.polBaseChange_holds V V₁ ρ₁ Cm.P.D.toPre Wo hψ hgen'
  haveI := hD.e_hom
  obtain ⟨Cb, bs, hCb, hbs⟩ := HF V₁ ρ₁ G hR D₁.P.A _
    (((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ (spMap ρ₁))).congr (Category.id_comp _) rfl)
  refine ⟨j, o₁, Ω, inferInstance, inferInstance, inferInstance, inferInstance, S, ρS, u, M, g ≫ U.ι, z₁, ζ, V₁,
    inferInstance, inferInstance, inferInstance, ρ₁, ev, D₁, hD, r, Cb, bs, hj, hbig, hρn, hrN, hU,
    fun w => (hgen w).symm ▸ hx₀, hpt, ⟨hMn, ⟨U, g, hg, rfl, hrange⟩, hζ, fun p hp => ?_⟩, hV₁, hinj, hfin, hloc, ?_, hr₂, hCb,
    fun K _ _ => hbs K⟩
  · refine ⟨x₀, (pullback.fst C.z (spMap C.b)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply ζ, hζ, Scheme.Hom.comp_apply, fromSpecStalk_bot z₁ p hp, ← M.pt_apply (closedPoint Ω)]
    exact h₁.symm
  · rw [← cancel_mono (pullback.fst C.z (spMap C.b)), Category.assoc, hζ, hev']

end GlobalTheory.USep.Setup
