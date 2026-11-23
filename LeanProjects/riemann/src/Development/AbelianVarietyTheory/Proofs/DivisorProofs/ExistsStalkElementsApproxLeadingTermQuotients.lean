import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationNormalisedBlowupSiegelModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlowupChartIdealSheafEqSpanMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoverElements

theorem spMap_comp₁ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_extend_algClosed {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] (g : A →+* B)
    (hg : Function.Injective g) (hi : g.IsIntegral) (ψ : A →+* K) : ∃ φ : B →+* K, φ.comp g = ψ := by
  letI := g.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) (RingHom.ker ψ) ⊥ (by
    intro x hx
    have : x = 0 := hg ((Ideal.mem_bot.1 hx).trans (map_zero g).symm)
    simp [this])
  haveI : Q.LiesOver (RingHom.ker ψ) := ⟨hQ'.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ψ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ψ) (B ⧸ Q) := inferInstance
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ψ] K := IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  exact l.commutes (Ideal.Quotient.mk _ a)

section Points

variable {K : Type} [Field K] {k₀ : Subfield K} {X Y : Scheme.{0}}

theorem mem_of_isIntegralElem {O : Type} [CommRing O] (hk : IsAlgClosed k₀) (θ : O →+* K) (hθ : ∀ a, θ a ∈ k₀) {z : K}
    (hz : θ.IsIntegralElem z) : z ∈ k₀ := by
  have h₁ : IsIntegral k₀ z := by
    obtain ⟨P, hP, hPz⟩ := hz
    refine ⟨P.map (θ.codRestrict k₀ hθ), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPz
  obtain ⟨w, hw⟩ := minpoly.mem_range_of_degree_eq_one k₀ z
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h₁))
  exact hw ▸ w.2

theorem mem_of_defOver {y : Y} (θ : Y.presheaf.stalk y →+* K) (h : DefOver k₀ (spMap θ ≫ Y.fromSpecStalk y)) (a) :
    θ a ∈ k₀ := by
  obtain ⟨P₀, hP⟩ := h
  have hs : P₀ (closedPoint k₀) ⤳ y := by
    have h₁ : (spMap k₀.subtype ≫ P₀) (closedPoint K) ∈ Set.range (Y.fromSpecStalk y) := by
      rw [hP]; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecStalk] at h₁
    have h₃ : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg P₀ (Subsingleton.elim _ _))
    exact h₃ ▸ h₁
  have h₂ : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of k₀) P₀ ≫
      CommRingCat.ofHom k₀.subtype) ≫ Y.fromSpecStalk y = spMap θ ≫ Y.fromSpecStalk y := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hP]
  rw [cancel_mono] at h₂
  have h₃ := congrArg (fun f => f.hom a) (Spec.map_injective h₂)
  exact (h₃ ▸ (Scheme.stalkClosedPointTo (R := .of k₀) P₀ (Y.presheaf.stalkSpecializes hs a)).2 : θ a ∈ k₀)

theorem values_of_finite (hk : IsAlgClosed k₀) (f : X ⟶ Y) [IsFinite f] {x : X} (θ : X.presheaf.stalk x →+* K)
    (hc : (spMap θ ≫ X.fromSpecStalk x ≫ f) (closedPoint K) = f x)
    (h : DefOver k₀ (spMap θ ≫ X.fromSpecStalk x ≫ f)) : IsLocalHom θ ∧ ∀ a, θ a ∈ k₀ := by
  have hs : X.fromSpecStalk x (spMap θ (closedPoint K)) ⤳ x := by
    have h₁ : X.fromSpecStalk x (spMap θ (closedPoint K)) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h₁
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have e : f (X.fromSpecStalk x (spMap θ (closedPoint K))) = f x := hc
  have h2 : (⟨_, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr hs
  have h3 : X.fromSpecStalk x (spMap θ (closedPoint K)) = X.fromSpecStalk x (closedPoint _) :=
    (congrArg Subtype.val h2.eq).trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 : spMap θ (closedPoint K) = closedPoint _ := (X.fromSpecStalk x).isEmbedding.injective h3
  have hl : IsLocalHom θ := (isLocalHom_iff_comap_closedPoint θ).2 h4
  refine ⟨hl, fun a => ?_⟩
  have h₁ : ∀ a, θ.comp (f.stalkMap x).hom a ∈ k₀ := mem_of_defOver _ (by
    have e₁ : spMap (f.stalkMap x).hom ≫ Y.fromSpecStalk (f x) = X.fromSpecStalk x ≫ f :=
      Scheme.SpecMap_stalkMap_fromSpecStalk f
    rw [spMap_comp₁, Category.assoc, e₁]
    exact h)
  refine mem_of_isIntegralElem hk _ h₁ ?_
  have hf := (GlobalTheory.residueField_map_finite_of_quasiFinite (f.stalkMap x).hom (f.quasiFiniteAt x)).to_isIntegral
  have hi := (RingHom.isIntegral_of_surjective _ (residue_surjective (R := Y.presheaf.stalk (f x)))).trans _ _ hf (residue _ a)
  exact hi.map (ResidueField.lift θ)

end Points

theorem exists_stalk_of_map {S Z : Scheme.{0}} (p : S ⟶ Z) (I : S.IdealSheafData) {z : Z} {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ S) (ev : Z.presheaf.stalk z →+* R) [IsLocalHom ev]
    (h : ξ ≫ p = spMap ev ≫ Z.fromSpecStalk z) {f : Z.presheaf.stalk z} (hf : f ∈ FinalTheorems.stalkId (I.map p) z) :
    ∃ u ∈ FinalTheorems.stalkId I (ξ (closedPoint R)), (Scheme.stalkClosedPointTo ξ).hom u = ev f := by
  have hz : z = p (ξ (closedPoint R)) := by
    have h1 : (ξ ≫ p) (closedPoint R) = z := by
      rw [h]
      exact (congrArg (Z.fromSpecStalk z) (comap_closedPoint ev)).trans Scheme.fromSpecStalk_closedPoint
    exact h1.symm
  subst hz
  refine ⟨(p.stalkMap _).hom f, ?_, ?_⟩
  · have h1 : FinalTheorems.stalkId ((I.map p).comap p) (ξ (closedPoint R)) ≤ FinalTheorems.stalkId I (ξ (closedPoint R)) :=
      iSup₂_mono fun U hx => Ideal.map_mono (Scheme.IdealSheafData.comap_map_le I p U)
    refine h1 ?_
    rw [GlobalTheory.VanStalk.stalkId_comap]
    exact Ideal.mem_map_of_mem _ hf
  · have h₂ : Spec.map (p.stalkMap _ ≫ Scheme.stalkClosedPointTo (R := .of R) ξ) ≫ Z.fromSpecStalk _ =
        spMap ev ≫ Z.fromSpecStalk _ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, h]
    rw [cancel_mono] at h₂
    exact congrArg (fun g => g.hom f) (Spec.map_injective h₂)

theorem mem_of_map_mem {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I : Ideal R} {a : R}
    (h : f a ∈ I.map f) : a ∈ I := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I]
  exact h

theorem effCartier_pow {X : Scheme.{0}} {I : X.IdealSheafData} (h : FinalTheorems.EffCartier I) (k : ℕ) : FinalTheorems.EffCartier (I ^ k) := by
  intro x
  obtain ⟨U, f, hx, hf, hI⟩ := h x
  refine ⟨U, f ^ k, hx, pow_mem hf k, ?_⟩
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI, Ideal.span_singleton_pow]

theorem flat_of_dominant {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω)
    {S : Scheme.{0}} [IsIntegral S] (p : S ⟶ M.Z) [IsDominant p] (π : S ⟶ Sp ℤ) : Flat π := by
  have hx : p (genericPoint S) = genericPoint M.Z := by
    refine ((genericPoint_spec S).image p.continuous).eq ?_
    rw [Set.image_univ, p.denseRange.closure_range]
    exact genericPoint_spec M.Z
  have h0 : CharZero (M.Z.presheaf.stalk (M.pt (closedPoint Ω))) :=
    (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom.charZero
  rw [M.pt_apply (closedPoint Ω), ← hx] at h0
  have hF : IsField (M.Z.presheaf.stalk (p (genericPoint S))) := by
    rw [hx]; exact Field.toIsField M.Z.functionField
  have hinj : Function.Injective (p.stalkMap (genericPoint S)).hom := by
    letI := hF.toField
    exact RingHom.injective _
  have : CharZero S.functionField := ((p.stalkMap (genericPoint S)).hom.charZero_iff hinj).1 h0
  refine GlobalTheory.ZH.ClosureLifting.flat_of_charZero (K := S.functionField) (S.fromSpecStalk (genericPoint S)) ?_ π
  rw [Scheme.range_fromSpecStalk]
  ext y
  exact ⟨fun h => (h.antisymm (genericPoint_specializes y)).eq, fun h => h ▸ specializes_rfl⟩

theorem evalZ_eq_of_addEquiv (φ : InvFun ℤ) {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (mX : Module ℤ X)
    (fX : @Module.Finite ℤ X _ _ mX) [Module.Finite ℤ Y] (e : X ≃+ Y)
    {β : @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X)} {β' : LinearMap.BilinForm ℤ Y} (h : ∀ a b, β a b = β' (e a) (e b)) :
    @InvFun.evalZ ℤ _ φ X _ mX fX β = φ.evalZ β' := by
  obtain rfl : mX = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective β']
  congr 1
  exact LinearMap.ext₂ h

theorem jK_spMap_apply {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ρ : A →+* B)
    (hρ : Function.Injective ρ) (w : Sp (FractionRing B)) : (jK B ≫ spMap ρ) w = (⊥ : PrimeSpectrum A) := by
  rw [← spMap_comp₁]
  refine PrimeSpectrum.ext ?_
  have : w.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ w.isPrime
  change w.asIdeal.comap _ = ⊥
  rw [this]
  exact Ideal.comap_bot_of_injective _ ((IsFractionRing.injective B (FractionRing B)).comp hρ)

theorem exists_reg_open {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (R : Subalgebra o Ω)
    (hR : R.FG) : ∃ U : M.Z.Opens, genericPoint M.Z ∈ U ∧ ∀ w ∈ U, ∀ a ∈ R, a ∈ M.O w := by
  obtain ⟨s, hs⟩ := hR
  refine ⟨⟨⋂ x ∈ s, {w | x ∈ M.O w}, isOpen_biInter_finset fun x _ => M.isOpen_setOf_mem_O x⟩, ?_, ?_⟩
  · refine Set.mem_iInter₂.2 fun x _ => ?_
    obtain ⟨U, f, hU, hf⟩ := M.onto x
    exact ⟨U, f, (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem, hf⟩
  · intro w hw a ha
    rw [← hs] at ha
    refine (Algebra.adjoin_le (S := M.O w) ?_) ha
    intro x hx
    exact Set.mem_iInter₂.1 hw x hx

theorem exists_mem_of_ordGe {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z} [IsOpenImmersion i]
    {W : Matrix (Fin 8) (Fin 8) ℤ} {φ : InvFun ℤ} {d : ℕ} {J : Z.IdealSheafData} (hval : ValOn F i φ J d) {N₁ : ℕ}
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁)) (hT : HasTraitsR X₁ z₁ Φ.pre)
    {S₁ : Scheme.{0}} [IsIntegral S₁] (p₁ : S₁ ⟶ X₁.M.Z) [IsProper p₁] [IsDominant p₁]
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁) (hE : FinalTheorems.EffCartier (J.comap (p₁ ≫ X₁.π))) (D k : ℕ) :
    ∃ e : ℕ, ∀ f, Φ.OrdGe φ (D * d) e f →
      f ∈ FinalTheorems.stalkId ((J.comap (p₁ ≫ X₁.π) ^ D).map p₁) z₁ ⊔ maximalIdeal _ ^ k := by
  have := X₁.ar.char
  have := X₁.M.lft
  have := X₁.M.qc
  have : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 X₁.ar.ft)
  have := flat_of_dominant X₁.M p₁ (p₁ ≫ X₁.M.s ≫ spMap (algebraMap ℤ X₁.o₁))
  obtain ⟨E, hE'⟩ := EffCartierData.exists_idealSheaf_eq (effCartier_pow hE D)
  obtain ⟨V₀, hg₀, hV₀⟩ := exists_reg_open X₁.M X₁.S.R X₁.S.fg
  have hU : ((p₁ ⁻¹ᵁ (V₀ ⊓ X₁.π ⁻¹ᵁ i.opensRange) : S₁.Opens) : Set S₁).Nonempty := by
    obtain ⟨x, hx⟩ := p₁.denseRange.exists_mem_open (V₀ ⊓ X₁.π ⁻¹ᵁ i.opensRange).isOpen ⟨genericPoint _, hg₀, by
      rw [← X₁.M.pt_apply (closedPoint _)]
      change (X₁.M.pt ≫ X₁.π) (closedPoint _) ∈ Set.range i
      rw [X₁.comp]
      exact ⟨_, rfl⟩⟩
    exact ⟨x, hx⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_correction_approximate_ideal_sections X₁.M.Z S₁ (X₁.M.s ≫ spMap (algebraMap ℤ X₁.o₁)) p₁ hn _ hU E z₁ k
  refine ⟨e, fun f hf => hE' ▸ he f fun V _ _ _ _ hc ξ ev hev hξ hr => ?_⟩
  have hr' : Set.range (jK V ≫ ξ ≫ p₁ ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    exact (hr ⟨w, rfl⟩).2
  obtain ⟨T, f₁, fK, hf₁, hl₁, -, hfK, hy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V
    ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩ inferInstance (IsOpenImmersion.lift i _ hr')
  have hsq : jK T.V ≫ spMap f₁ = spMap fK ≫ jK V := by
    rw [← spMap_comp₁, ← spMap_comp₁]
    congr 1
    exact RingHom.ext fun a => (hfK a).symm
  have hgen : jK T.V ≫ spMap f₁ ≫ ξ ≫ p₁ ≫ X₁.π = T.y ≫ i := by
    rw [hy, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hsq, Category.assoc]
  have hreg : RegAt X₁ z₁ (f₁.comp ev) := by
    intro a ha
    have e : jK T.V ≫ spMap (f₁.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ = spMap fK ≫ jK V ≫ ξ ≫ p₁ := by
      rw [spMap_comp₁, Category.assoc, hξ, ← Category.assoc, hsq, Category.assoc]
    rw [e]
    exact hV₀ _ (hr ⟨_, rfl⟩).1 a ha
  obtain ⟨y, f₂, e₂, hm, hP, hf₂, hl₂, hev₂, hδ⟩ : ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X),
      Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧ Function.Injective f ∧ IsLocalHom f ∧ f.comp (f₁.comp ev) = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b) := hT T (f₁.comp ev) inferInstance hreg (by
    rw [← hgen, spMap_comp₁, Category.assoc, ← Category.assoc (spMap ev), hξ, Category.assoc])
  obtain ⟨a, ha, hJ⟩ := valOn_pow F i φ J d D hval T _ hgen
  let k₀ : Fin (Φ.m y) := ⟨0, by omega⟩
  have hm := hf.mem y hP hm k₀ a (by
    rw [ha]
    congr 1
    exact (evalZ_eq_of_addEquiv φ _ _ e₂ (hδ k₀).2).symm)
  refine mem_of_map_mem (f₂.comp f₁) (hf₂.comp hf₁) ?_
  have hpow : ∀ {Y : Scheme.{0}} (I : Y.IdealSheafData) (χ : Sp V ⟶ Y), idlAlong (I ^ D) χ = idlAlong I χ ^ D := by
    intro Y I χ
    rw [idlAlong, stalkId_pow', Ideal.map_pow, ← idlAlong]
  have h1 : (idlAlong E.idealSheaf ξ).map (f₂.comp f₁) = Ideal.span {Φ.t y k₀ ^ a} := by
    rw [hE', hpow, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hpow, ← Ideal.map_map, ← GlobalTheory.TraitOrder.idlAlong_comp, hJ,
      Ideal.map_span, Set.image_singleton, map_pow, (hδ k₀).1]
  rw [Ideal.map_sup, h1, Ideal.map_pow, Ideal.map_map, RingHom.comp_assoc, hev₂, ← RingHom.comp_apply,
    RingHom.comp_assoc, hev₂]
  exact hm

theorem exists_elements : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), 1 ≤ M → IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∀ (N₁ : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), HasTraitsR X₁ z₁ Φ.pre → IsChartMember X₁ z₁ Φ Q (ξ ≫ π) t δ y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → ∀ ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga' k a b = ga (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ Elements Φ y φ d ga' ev₁ k₀ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW φ d J S π j hJ hval hbl hji hpf V _ _ _ Q m t δ hrk ht hsym hnn
    hdef hmono ga M hM hcone hδ ξ hU N₁ X₁ z₁ Φ y ρ e h hT hC K _ _ ev k₀ hk hcen hdo ga' hga'
  obtain ⟨hρi, hρf, hsq, htδ, -⟩ := hC
  obtain ⟨b, hb, hJb⟩ := GlobalTheory.T.blowup_chart_idealSheaf_eq_span_monomial g hg n hn hodd F Z z i hproj hnorm hiz hdense W φ d J S π j hJ hval hbl hji hpf V Q m t δ
    hrk ht hsym hnn hdef hmono ga M hcone hδ ξ hU
  obtain ⟨S₁, _, p₁, ν, hn₁, _, _, _, hν, -, hE, hlift⟩ :=
    GlobalTheory.T.exists_normalisation_normalisedBlowup_siegelModel g hg n hn hodd F Z z i hproj hnorm hiz hdense W J S π hJ hbl X₁
  have hgen : (ξ ≫ π) (⊥ : PrimeSpectrum V) ∈ Set.range i := by
    obtain ⟨R', _, _, _, ρ', r, D, e', hCN', hρi', hρf', -, -, hrefn, -⟩ :=
      GlobalTheory.PolDeg.refine_monomial_of_polarised V Q m t δ hU.1 hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hdef
    obtain ⟨_, _, _, _, _, y', _, _, -, hy', -⟩ := hU.2 R' ρ' hCN' hρi' hρf' D e' hrefn
    refine ⟨y' (closedPoint _), ?_⟩
    rw [← jK_spMap_apply ρ' hρi' (closedPoint _), ← hji]
    exact congrArg (fun u => (u ≫ π) (closedPoint (FractionRing R'))) hy'
  have := (Φ.cn y).2.1
  have := Φ.ev_loc y
  obtain ⟨ξ₁, hξν, hξp⟩ := hlift (Φ.V y) (spMap ρ ≫ ξ) (spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁)
    (by simp only [Category.assoc]; exact hsq.symm) (by
      rintro _ ⟨w, rfl⟩
      rw [Category.assoc, hsq, ← Category.assoc, Scheme.Hom.comp_apply, jK_spMap_apply ρ hρi]
      exact hgen)
  obtain ⟨ev₁, hev₁⟩ := exists_extend_algClosed ρ hρi hρf.to_isIntegral ev
  let s := (Scheme.stalkClosedPointTo (R := .of (Φ.V y)) ξ₁).hom
  have hsl : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' (R := Φ.V y) ξ₁
  have hs : spMap s ≫ S₁.fromSpecStalk _ = ξ₁ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of (Φ.V y)) ξ₁
  have hP : spMap (ev₁.comp s) ≫ S₁.fromSpecStalk _ ≫ ν = spMap ev ≫ ξ := by
    rw [spMap_comp₁, Category.assoc, ← Category.assoc (spMap s), hs, hξν, ← Category.assoc, ← spMap_comp₁, hev₁]
  have hρl : IsLocalHom ρ := hρf.to_isIntegral.isLocalHom hρi
  obtain ⟨hθl, hθ⟩ := values_of_finite hk ν (ev₁.comp s) (by
    rw [hP]
    refine (hcen _).trans ?_
    change _ = (ξ₁ ≫ ν) (closedPoint _)
    rw [hξν]
    exact congrArg ξ (comap_closedPoint ρ).symm) (hP ▸ hdo)
  obtain ⟨U, f, hxU, -, hf⟩ := hE (ξ₁ (closedPoint _))
  have hst : FinalTheorems.stalkId (J.comap (p₁ ≫ X₁.π)) (ξ₁ (closedPoint _)) =
      Ideal.span {(S₁.presheaf.germ U.1 _ hxU).hom f} := by
    rw [ds_stalkId_eq_map _ U _ hxU, hf, Ideal.map_span, Set.image_singleton]
  generalize (S₁.presheaf.germ U.1 _ hxU).hom f = f₀ at hst
  refine ⟨ev₁, hev₁, s.range, s f₀, fun k => b (h k), ?_, fun k => ?_, ?_, fun D l a ha c e₀ => ?_⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨hθ u, fun hu => ?_⟩
    by_contra h0
    exact (mem_maximalIdeal _).1 hu (((isUnit_map_iff (ev₁.comp s) u).1 (Ne.isUnit h0)).map s)
  · rw [hb]
    congr 1
    exact (evalZ_eq_of_addEquiv φ _ _ e (htδ k).2).symm
  · rw [← Ideal.span_singleton_eq_span_singleton]
    have h1 : idlAlong (J.comap (p₁ ≫ X₁.π)) ξ₁ = Ideal.span {s f₀} := by
      rw [idlAlong, hst, Ideal.map_span, Set.image_singleton]
    rw [← h1, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hν, ← Category.assoc, hξν, Category.assoc,
      GlobalTheory.TraitOrder.idlAlong_comp, ← GlobalTheory.PullAlong.idlAlong_comap_eq, hJb, Ideal.map_span, Set.image_singleton, map_prod,
      ← Equiv.prod_comp h]
    simp only [map_pow, (htδ _).1]
  · have hle : ∀ {R : Type} [CommRing R] (I J : Ideal R) {a b : ℕ}, a ≤ b → J ⊔ I ^ b ≤ J ⊔ I ^ a :=
      fun I J _ _ h => sup_le_sup_left (Ideal.pow_le_pow_right h) J
    obtain ⟨e₁, he₁⟩ := exists_mem_of_ordGe hval X₁ z₁ Φ hT p₁ hn₁ hE D e₀
    obtain ⟨fe, hord, hlead⟩ := GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem ℤ id bddAct_int_and_cm.1 g φ hpf 8 W Φ.posW N₁ _ Φ y ga' M hM
      (fun k => LinearMap.ext₂ fun u v => by
        rw [(htδ k).2, hδ]
        simp [hga']) (D * d) l a ha c (max e₀ e₁)
    have hmem := he₁ fe fun y' hP' hm' k =>
      hle _ _ (le_max_right e₀ e₁) (hord y' hP' hm' k)
    obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨u, hu, hu'⟩ := exists_stalk_of_map p₁ _ ξ₁ (Φ.ev y) hξp hf₁
    rw [stalkId_pow', hst, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu
    obtain ⟨v, rfl⟩ := hu
    refine ⟨s v, ⟨v, rfl⟩, ?_⟩
    have h1 : Φ.ev y r ∈ maximalIdeal (Φ.V y) ^ e₀ := by
      have := Ideal.mem_map_of_mem (Φ.ev y) hr
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono ((Ideal.map_le_iff_le_comap (f := Φ.ev y) (K := maximalIdeal (Φ.V y))).2 fun x hx =>
        map_nonunit (Φ.ev y) x hx) _ this
    have h2 := hle _ _ (le_max_left e₀ e₁) hlead
    have h3 : s v * s f₀ ^ D = Φ.ev y f₁ := by rw [← hu', ← map_pow, ← map_mul]
    have h4 := sub_mem h2 (Ideal.mem_sup_right h1)
    rw [h3]
    convert h4 using 1
    rw [map_add]
    ring

end GlobalTheory.CoverElements
