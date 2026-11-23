import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemClassSumsUnboundedLevelsOneIndeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemExactOfGeometricUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberOfUnitaryMonomialUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsIsThetaTermsTorsionFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinkedThetaSystemRegularMonomialFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemUniversalUnitaryDeepTowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.GSep.UAssembly

theorem posW_one : PosW (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i; fin_cases j; simp
  rw [this, Matrix.posDef_diagonal_iff]
  intro _; norm_num

theorem projective_of_free (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (c : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc0)
    have h0 : r • x = 0 := by
      rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul]
      rw [← Submonoid.smul_def, hc, smul_zero]
    exact hx ((smul_eq_zero.1 h0).resolve_left hr)
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem jK_spMap {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (fK : FractionRing V →+* FractionRing V₁) (h : ∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) :
    jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext a
  simp [h]

theorem isUnit_natCast_of_spec {A : Type} [CommRing A] [Nontrivial A] {K : Type} [Field K] [CharZero K] (g : Sp A ⟶ Sp K)
    (m : ℕ) (hm : m ≠ 0) : IsUnit (m : A) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hm : (m : K) ≠ 0)).map (Spec.preimage g).hom
  simpa using this

end GlobalTheory.GSep.UAssembly

namespace GlobalTheory.GSep.UAssembly
open GlobalTheory.GSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem nonempty_gMem_trait (hpq : 1 ≤ Dw.p + Dw.q) (C : UCompact Xo c) (X₁ : GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (hlink : ULink C X₁ act u π) (z₁ : X₁.M.Z)
    (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b))
    (hcov₃ : ζ ≫ pullback.fst _ _ = X₁.M.Z.fromSpecStalk z₁ ≫ π) (U : X₁.M.Z.Opens)
    (hU : ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z) (T : UTrait Xo c) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V']
    (f : T.V →+* V') (t : V') (hcn : IsCN V') (hinj : Function.Injective f) (hf : IsLocalHom f) (ht : t ^ 2 = f T.ϖ)
    (e : X₁.M.Z.presheaf.stalk z₁ →+* T.V) (he : IsLocalHom e) (hc : jK T.V ≫ spMap e ≫ ζ = T.y ≫ C.iF)
    (hrg : Set.range (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) ⊆ (U : Set X₁.M.Z)) :
    Nonempty (GMem X₁ z₁ act V' (f.comp e) (Fin 1 → T.P.D.toPre.X) (mono !![(1 : ℤ)] ![t] ![T.be])
      (fun a mu => a • mu)) := by
  have hcnT : IsCN T.V := by
    haveI := T.cdvr.1
    exact ⟨inferInstance, inferInstance, T.cdvr.2.1, T.cdvr.2.2⟩
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (S := FractionRing T.V) (FractionRing V') f
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hinj)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hjk := jK_spMap f fK hfK
  have key : jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁ =
      spMap fK ≫ (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) := by
    rw [show spMap (f.comp e) = spMap f ≫ spMap e from Spec.map_comp _ _]
    simp only [← Category.assoc]
    rw [hjk]
  have hloc : IsLocalHom (f.comp e) := RingHom.isLocalHom_comp f e
  have hreg : RegAt X₁ z₁ (f.comp e) := by
    intro a ha
    rw [key]
    exact hU _ (hrg ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩) ha
  have hcmp : jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ T.y ≫ C.i := by
    calc _ = (jK V' ≫ spMap (f.comp e) ≫ X₁.M.Z.fromSpecStalk z₁) ≫ π := by simp only [Category.assoc]
      _ = spMap fK ≫ (jK T.V ≫ spMap e ≫ ζ) ≫ pullback.fst _ _ := by
        rw [key]; simp only [Category.assoc, hcov₃]
      _ = _ := by rw [hc]; simp only [Category.assoc]
  have hr : ∀ k : Fin 1, ![t] k ^ 2 = f (![T.ϖ] k) := fun k => by
    rw [Subsingleton.elim k 0]; exact ht
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation E H Dw hpq l Xo c C X₁ act u π hlink z₁ T.V hcnT T.t T.y T.P T.gen 1 ![T.ϖ] ![T.be]
    T.mono V' f fK ![t] hcn hinj hf hfK hr (f.comp e) hloc hreg hcmp
  exact ⟨𝔪⟩

end GlobalTheory.GSep.UAssembly

open GlobalTheory.GSep.UAssembly in

theorem GlobalTheory.GSep.exists_vPre_traitsOn_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (U : X₁.M.Z.Opens) (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (c₀ : Φ.Q), j₀ ≤ j ∧ IsCov C π z₁ ζ ∧ (U : Set X₁.M.Z).Nonempty ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ U ∧ GlobalTheory.GSep.IsMemberP ζ Φ ((n ^ j) ^ 2) Cm ξ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((n ^ j) ^ 2) ∧ Φ.ClassSums ((n ^ j) ^ 2) := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hB ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, act, u, π, z₁, ζ, V₁, _, _, _, ρ₁, ev₁, r, hj, hN, hlink, hcov, hcn₁, hinj, hfin, hloc, hreg, hcomp, hr⟩ :=
    GlobalTheory.T.exists_linked_thetaSystem_regular_monomialFamily E H Dw hpq l Xo c C φ V Cm hB ξ hξ n hn hodd j₀
  obtain ⟨U, hUne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X₁
  have hdom := (GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁).1
  have hact : GlobalTheory.GSep.IsAct X₁ act := hlink.1
  have hdeep := GlobalTheory.T.thetaSystem_universalUnitary_deep_towers E H Dw hpq l Xo c C X₁ act u π hlink
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hunit : ∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁) := fun m hm =>
    isUnit_natCast_of_spec (ζ ≫ pullback.snd C.z (spMap C.b)) m hm
  have hρ : IsLocalHom ρ₁ := by
    letI := ρ₁.toAlgebra
    haveI : Module.Finite V V₁ := hfin
    haveI : FaithfulSMul V V₁ := (faithfulSMul_iff_algebraMap_injective V V₁).2 hinj
    exact (inferInstance : IsLocalHom (algebraMap V V₁))
  have hcnV : IsCN V := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  let fK₁ : FractionRing V →+* FractionRing V₁ := IsLocalization.map (S := FractionRing V) (FractionRing V₁) ρ₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₁ hinj)
  have hfK₁ : ∀ a, fK₁ (algebraMap V _ a) = algebraMap V₁ _ (ρ₁ a) := fun a => IsLocalization.map_eq _ a
  have key₀ := jK_spMap ρ₁ fK₁ hfK₁
  have hcov₃ : ζ ≫ pullback.fst _ _ = X₁.M.Z.fromSpecStalk z₁ ≫ π := hcov.2.2.1
  obtain ⟨𝔪₀, p₀, hp₀⟩ := GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation E H Dw hpq l Xo c C X₁ act u π hlink z₁ V hcnV Cm.t Cm.y Cm.P Cm.gen Cm.m Cm.s
    (fun i => (l.M' : ℤ) • Cm.δ i) Cm.mono V₁ ρ₁ fK₁ r hcn₁ hinj hρ hfK₁ hr ev₁ hloc hreg (by
      calc _ = (jK V₁ ≫ (spMap ev₁ ≫ ζ)) ≫ pullback.fst _ _ := by simp only [Category.assoc, hcov₃]
        _ = (jK V₁ ≫ spMap ρ₁) ≫ ξ ≫ pullback.fst _ _ := by rw [hcomp]; simp only [Category.assoc]
        _ = spMap fK₁ ≫ (jK V ≫ ξ) ≫ pullback.fst _ _ := by rw [key₀]; simp only [Category.assoc]
        _ = _ := by rw [← hξ]; simp only [Category.assoc])

  have hcnT : ∀ T : UTrait Xo c, IsCN T.V := fun T => by
    haveI := T.cdvr.1
    exact ⟨inferInstance, inferInstance, T.cdvr.2.1, T.cdvr.2.2⟩
  have hsq := fun T : UTrait Xo c => GlobalTheory.T.exists_finite_ext_sqrt_uniformiser_complete_dvr T.V (hcnT T) (by haveI := T.cdvr.1; infer_instance) T.ϖ T.irr
  choose VT iRT iDT iLT fT tT hcnW hpirW hinjW hlocW hfinW htW using hsq
  let Tr : Type 1 := Σ T : UTrait Xo c, {e : X₁.M.Z.presheaf.stalk z₁ →+* T.V // IsLocalHom e ∧
    jK T.V ≫ spMap e ≫ ζ = T.y ≫ C.iF ∧ Set.range (jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁) ⊆ (U : Set X₁.M.Z)}
  have hmT : ∀ T : Tr, Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act (VT T.1) ((fT T.1).comp T.2.1) (Fin 1 → T.1.P.D.toPre.X)
      (mono !![(1 : ℤ)] ![tT T.1] ![T.1.be]) (fun a mu => a • mu)) := by
    rintro ⟨T, e, he, hc, hrg⟩
    exact nonempty_gMem_trait hpq C X₁ act u π hlink z₁ ζ hcov₃ U hU T (VT T) (fT T) (tT T) (hcnW T) (hinjW T)
      (hlocW T) (htW T) e he hc hrg

  let VV : Option Tr → Type := fun y => match y with | none => V₁ | some T => VT T.1
  letI iR : ∀ y, CommRing (VV y) := fun y => match y with
    | none => inferInstanceAs (CommRing V₁) | some T => iRT T.1
  haveI iD : ∀ y, IsDomain (VV y) := fun y => match y with
    | none => inferInstanceAs (IsDomain V₁) | some T => iDT T.1
  haveI iL : ∀ y, IsLocalRing (VV y) := fun y => match y with
    | none => inferInstanceAs (IsLocalRing V₁) | some T => iLT T.1
  let EV : ∀ y, X₁.M.Z.presheaf.stalk z₁ →+* VV y := fun y => match y with
    | none => ev₁ | some T => (fT T.1).comp T.2.1
  let XX : Option Tr → Type := fun y => match y with | none => Cm.P.D.toPre.X | some T => T.1.P.D.toPre.X
  letI iA : ∀ y, AddCommGroup (XX y) := fun y => match y with
    | none => inferInstanceAs (AddCommGroup Cm.P.D.toPre.X) | some T => inferInstanceAs (AddCommGroup T.1.P.D.toPre.X)
  letI iM : ∀ y, Module (𝓞 E) (XX y) := fun y => match y with
    | none => inferInstanceAs (Module (𝓞 E) Cm.P.D.toPre.X) | some T => inferInstanceAs (Module (𝓞 E) T.1.P.D.toPre.X)
  haveI iFZ : ∀ y, Module.Free ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Free ℤ Cm.P.D.toPre.X) | some T => inferInstanceAs (Module.Free ℤ T.1.P.D.toPre.X)
  haveI iGZ : ∀ y, Module.Finite ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Finite ℤ Cm.P.D.toPre.X) | some T => inferInstanceAs (Module.Finite ℤ T.1.P.D.toPre.X)
  haveI iFO : ∀ y, Module.Finite (𝓞 E) (XX y) := fun y => Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI iPO : ∀ y, Module.Projective (𝓞 E) (XX y) := fun y => projective_of_free E (XX y)
  let MM : Option Tr → ℕ := fun y => match y with | none => Cm.m | some _ => 1
  let tt : ∀ y, Fin (MM y) → VV y := fun y => match y with | none => r | some T => ![tT T.1]
  let dd : ∀ y, Fin (MM y) → LinearMap.BilinForm ℤ (XX y) := fun y => match y with
    | none => fun k => (l.M' : ℤ) • Cm.δ k | some T => ![T.1.be]
  let 𝔪 : ∀ y, GlobalTheory.GSep.GMem X₁ z₁ act (VV y) (EV y) (Fin 1 → XX y) (mono !![(1 : ℤ)] (tt y) (dd y))
      (fun a mu => a • mu) := fun y => match y with
    | none => 𝔪₀
    | some T => (hmT T).some
  have hlab : Set.range (Subtype.val : X₁.S.HH X₁.M z₁ → X₁.S.Gam) = X₁.S.HH X₁.M z₁ := Subtype.range_val
  choose uu hu₁ hu₂ hu₃ using fun y => GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift (𝓞 E) X₁ z₁ act x₀ hx₀ (VV y) (EV y) (Fin 1 → XX y) _ _ (𝔪 y)
    (X₁.S.HH X₁.M z₁) Subtype.val hlab
  have ht₀ : ∀ k, r k ∈ maximalIdeal V₁ ∧ r k ≠ 0 := fun k => by
    refine ⟨(mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_), fun h0 => ?_⟩
    · have h1 : IsUnit (ρ₁ (Cm.s k)) := (hr k) ▸ hu.pow 2
      exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 (Cm.s_mem k))) ((isUnit_map_iff ρ₁ _).1 h1)
    · apply Cm.s_ne_zero k
      apply hinj
      rw [map_zero, ← hr k, h0]
      ring
  have htT : ∀ T : UTrait Xo c, tT T ∈ maximalIdeal (VT T) ∧ tT T ≠ 0 := fun T => by
    haveI := hlocW T
    refine ⟨(mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_), fun h0 => ?_⟩
    · have h1 : IsUnit (fT T T.ϖ) := (htW T) ▸ hu.pow 2
      exact T.irr.not_isUnit ((isUnit_map_iff (fT T) _).1 h1)
    · apply T.irr.ne_zero
      apply hinjW T
      rw [map_zero, ← htW T, h0]
      ring
  let Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁) :=
    { posW := posW_one
      Y := Option Tr
      V := VV
      cn := fun y => (𝔪 y).cn
      ev := EV
      ev_loc := fun y => (𝔪 y).loc
      X := XX
      rank_le := fun y => match y with
        | none => Cm.rank
        | some T => UTrait.finrank_le_min E H Dw l Xo c T.1
      m := MM
      t := tt
      t_mem := fun y => match y with
        | none => ht₀
        | some T => fun k => by rw [Subsingleton.elim k 0]; exact htT T.1
      δ := dd
      bal := fun y => match y with
        | none => fun k => Submodule.smul_mem _ _ (Cm.cone.mem k)
        | some T => fun k => by
            rw [Subsingleton.elim k 0]
            exact ⟨T.1.lev.1, T.1.lev.2.1⟩
      nonneg := fun y => match y with
        | none => fun k x => Cm.mono.nonneg k x
        | some T => fun k x => T.1.mono.nonneg k x
      pos := fun y => match y with
        | none => fun x hx => Cm.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (Dd := Cm.P.D) hx
        | some T => fun x hx => T.1.mono.exists_pos (maximalIdeal.isMaximal T.1.V).ne_top (Dd := T.1.P.D) hx
      Q := X₁.S.HH X₁.M z₁
      u := uu
      u_unit := hu₂ }
  have hgeo : GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ Subtype.val := ⟨hx₀, hlab, fun y => ⟨𝔪 y, hu₁ y⟩⟩
  refine ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, none, ρ₁, LinearEquiv.refl _ _, Equiv.refl _,
    ⟨x₀, AddSubgroup.subset_closure hx₀⟩, hj, hcov, hUne, ?_, ?_, fun y => hu₃ y _ rfl, ?_, ?_, ?_⟩
  · intro T e h₁ h₂ h₃
    refine ⟨some ⟨T, e, h₁, h₂, h₃⟩, fT T, LinearEquiv.refl _ _, rfl, hpirW T, hinjW T, hlocW T, rfl, fun k => ?_⟩
    rw [Subsingleton.elim k 0]
    exact ⟨htW T, fun _ _ => rfl⟩
  · refine ⟨hinj, hfin, hcomp, fun k => ⟨hr k, fun _ _ => rfl⟩, 𝔪₀.D.toPre, p₀, ?_⟩
    have hth := GlobalTheory.T.thetaMember_terms_isThetaTerms_torsionFrames (𝓞 E) X₁ z₁ act x₀ hx₀ V₁ ev₁ (Fin 1 → Cm.P.D.toPre.X) _ _ 𝔪₀ _ Subtype.val hlab _ (hu₁ none)
    rw [← hN]
    obtain ⟨th, g, b, w, h1, h2, h3, h4, h5⟩ := hth
    refine ⟨th, g, b, w, h1, h2, h3, h4, fun mu c => ?_⟩
    have e1 : p₀.xe.symm mu = 𝔪₀.e₈ (fun _ => mu) := p₀.xe.symm_apply_eq.2 (hp₀ (fun _ => mu)).symm
    rw [e1]
    exact h5 (fun _ => mu) c
  · rintro (_ | T) h
    · rfl
    · exact absurd rfl h
  · rw [← hN]
    exact GlobalTheory.T.fourierTermSystem_exact_of_geometric_uniformisation (𝓞 E) _ _ _ _ X₁ z₁ act x₀ Φ _ hgeo
  · rw [← hN]
    exact GlobalTheory.T.fourierTermSystem_class_sums_unbounded_levels_one_index (𝓞 E) _ _ _ X₁ z₁ act hact hdeep hunit x₀ Φ _ hgeo
