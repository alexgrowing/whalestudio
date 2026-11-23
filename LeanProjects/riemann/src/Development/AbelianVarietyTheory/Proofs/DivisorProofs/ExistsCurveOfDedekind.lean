import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfIsDomain
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FbarCurve

open TopologicalSpace GlobalTheory.CechPic

theorem degLB_pull_comp {k : Type} [Field k] {X Y Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] [IsIntegral Z] (a : Z ⟶ Y)
    (b : Y ⟶ X) {L : LB X} (hL : L.IsLB) : degLB k (L.pull (a ≫ b)) = degLB k ((L.pull b).pull a) :=
  degLB_congr (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL b) a)
    ((cls_eq_iff _ _).1 (pull_comp a b (cls L hL)))

open GlobalTheory.NormCurve in

theorem exists_normal_finite :
    ∀ (k : Type) [Field k] [PerfectField k] (Z : Scheme.{0}) [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      IsProper (strHom k Z) → topologicalKrullDim Z = 1 →
      ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ Z), IsFinite f ∧
        f (genericPoint C) = genericPoint Z ∧ topologicalKrullDim C = 1 ∧
        ∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U) := by
  intro k _ _ Z _ _ hp hd
  let s := strHom k Z
  let f := Z.fromSpecResidueField (genericPoint Z)
  let c := f.fromNormalization
  haveI : IsFinite c := isFinite_fromNormalization f s
  have htr : letI := (constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (Z.residueField (genericPoint Z)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(Z, U) := finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (Z.residueField (genericPoint Z))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (isField_sections (⊤ : (Spec (Z.residueField (genericPoint Z))).Opens)).toField
    letI := (constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(Z, U) Γ(Spec (Z.residueField (genericPoint Z)), ⊤) :=
      .of_algebraMap_eq' (appLE_comp_constHom s f U ⊤ e).symm
    exact (finite_integralClosure k (surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint Z ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization,
      Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint Z := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm
      (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    fun U hU _ => isDedekindDomain_sections f s htr U hU⟩

theorem chi_tower {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
  have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
    refine ⟨fun a b x => ?_⟩
    change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
      cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
    rw [Algebra.smul_def, map_mul, map_mul, hk]
    rfl
  have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
    rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
    push_cast
    ring
  rw [chi_def, chi_def]
  simp_rw [e]
  exact (mul_finsum _ _).symm

theorem interNum_tower {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    {ι : Type} [Fintype ι] (F : X.Modules) (L : ι → LB X) :
    interNum k F L = (Module.finrank k K : ℤ) * interNum K F L := by
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [chi_tower k K hk]
  ring

theorem connectedSpace_pullback {K k : Type} [Field K] [Field k] (c : K →+* k) {Y : Scheme.{0}} (f : Y ⟶ Sp K)
    [QuasiCompact f] [IsSeparated f] [IsIso f.appTop] : ConnectedSpace (pullback f (spMap c) : Scheme.{0}) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace Y := (quasiSeparated_iff_quasiSeparatedSpace f).1 inferInstance
  have H := IsPullback.of_hasPullback f (spMap c)
  have h1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _) isCompact_univ isQuasiSeparated_univ
  have h2 := (isIso_pushoutSection_iff ..).1 h1
  have h3 : IsIso (f.appLE ⊤ ⊤ le_top) := by
    have : f.appLE ⊤ ⊤ le_top = f.appTop := (Scheme.Hom.app_eq_appLE f).symm
    rw [this]; infer_instance
  have h4 := h2.isIso_inr_of_isIso h3
  have : IsDomain Γ(pullback f (spMap c), ⊤) :=
    (asIso ((pullback.snd f (spMap c)).appLE ⊤ ⊤ _)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact ConnDvr.connectedSpace_of_isDomain _

theorem exists_curve_of_dedekind (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (Y : Scheme.{0}) [IsIntegral Y] [Algebra (ZMod p) Γ(Y, ⊤)] (hd : topologicalKrullDim Y = 1)
    (hP : IsProper (strHom (ZMod p) Y))
    (hD : ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(Y, U)) :
    ∃ (C : Scheme.{0}) (_ : Algebra k Γ(C, ⊤)) (_ : IsIntegral C) (g : C ⟶ Y) (n : ℕ), IsSmoothProjCurve k C ∧ 0 < n ∧
      ∀ L : LB Y, L.IsLB → (n : ℤ) * degLB k (L.pull g) = interNum (ZMod p) (structureModule Y) ![L] := by
  have hF : IsField Γ(Y, ⊤) := isField_of_universallyClosed (ZMod p) (strHom (ZMod p) Y)
  letI : Field Γ(Y, ⊤) := hF.toField
  letI iK : Algebra Γ(Y, ⊤) Γ(Y, ⊤) := Algebra.id _
  have hfin : Module.Finite (ZMod p) Γ(Y, ⊤) := by
    have h1 := finite_appTop_of_universallyClosed (ZMod p) (strHom (ZMod p) Y)
    have h2 : (algebraMap (ZMod p) Γ(Y, ⊤)) =
        (strHom (ZMod p) Y).appTop.hom.comp (Scheme.ΓSpecIso (.of (ZMod p))).inv.hom :=
      RingHom.ext fun r => algebraMap_eq_strHom (ZMod p) Y r
    rw [← RingHom.finite_algebraMap, h2]
    exact h1.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).symm.commRingCatIsoToRingEquiv.surjective)
  have hcomp : strHom (ZMod p) Y = strHom Γ(Y, ⊤) Y ≫ spMap (algebraMap (ZMod p) Γ(Y, ⊤)) := by
    rw [strHom, strHom, Category.assoc, ← Spec.map_comp]
    rfl
  have hPK : IsProper (strHom Γ(Y, ⊤) Y) := by
    have : IsProper (strHom Γ(Y, ⊤) Y ≫ spMap (algebraMap (ZMod p) Γ(Y, ⊤))) := hcomp ▸ hP
    exact IsProper.of_comp _ (spMap (algebraMap (ZMod p) Γ(Y, ⊤)))
  haveI : Finite Γ(Y, ⊤) := Module.finite_of_finite (ZMod p)
  haveI : PerfectField Γ(Y, ⊤) := inferInstance
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra Γ(Y, ⊤) k := (IsAlgClosed.lift (R := ZMod p) (S := Γ(Y, ⊤)) (M := k)).toRingHom.toAlgebra
  let t : Sp k ⟶ Sp Γ(Y, ⊤) := spMap (algebraMap Γ(Y, ⊤) k)
  let f := strHom Γ(Y, ⊤) Y
  have h1 : SmoothOfRelativeDimension 1 f := CurveSmooth.smoothOfRelativeDimension_one _ Y inferInstance hd hD
  have h2 : IsProjOver f := ProperCurve.isProjOver_of_isProper _ hd
  haveI : IsIso f.appTop := by
    have e : (Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv ≫ f.appTop = 𝟙 _ := by
      ext r
      exact (algebraMap_eq_strHom Γ(Y, ⊤) Y r).symm
    haveI : IsIso ((Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv ≫ f.appTop) := by rw [e]; infer_instance
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv _
  haveI : ConnectedSpace (pullback f t : Scheme.{0}) := connectedSpace_pullback _ f
  letI A' : Algebra k Γ(pullback f t, ⊤) := algebraΓOfHom (pullback.snd f t)
  have hs : strHom k (pullback f t) = pullback.snd f t := strHom_eq fun _ => rfl
  have h3 : SmoothOfRelativeDimension 1 (pullback.snd f t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback f t) h1
  haveI h4 : Smooth (pullback.snd f t) := SmoothOfRelativeDimension.smooth 1 _
  haveI hI : IsIntegral (pullback f t) := isIntegral_of_smooth_field (pullback.snd f t)
  have hC : IsSmoothProjCurve k (pullback f t) :=
    ⟨⟨hI, by simpa using GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (pullback.snd f t) 1 h3,
      by rw [hs]; exact GlobalTheory.ProjSpace.isProjOver_pullback_snd _ h2⟩, by rw [hs]; exact h4⟩
  refine ⟨pullback f t, A', hI, pullback.fst f t, Module.finrank (ZMod p) Γ(Y, ⊤), hC, Module.finrank_pos,
    fun L hL => ?_⟩
  have hinst : iK = algebraΓOfHom f := Algebra.algebra_ext _ _ (algebraMap_eq_strHom Γ(Y, ⊤) Y)
  have P := FieldChangeInter.interNum_pull (f := f) (f' := pullback.snd f t) (π := pullback.fst f t)
    (IsPullback.of_hasPullback f t) (L := ![L]) (isLB_vecOne hL)
  have e₃ : (fun j => ((![L] : Fin 1 → LB Y) j).pull (pullback.fst f t)) = ![L.pull (pullback.fst f t)] :=
    funext fun j => by fin_cases j; rfl
  rw [e₃, ← hinst] at P
  rw [interNum_tower (ZMod p) Γ(Y, ⊤) (fun _ => rfl), hC.toIsProjCurve.degLB_eq_interNum (LB.isLB_pull hL _), P]

theorem exists_curve_alg_closed (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (Y : Scheme.{0}) [IsIntegral Y] [Algebra (ZMod p) Γ(Y, ⊤)] (hd : topologicalKrullDim Y = 1)
    (hP : IsProper (strHom (ZMod p) Y)) :
    ∃ (C : Scheme.{0}) (_ : Algebra k Γ(C, ⊤)) (_ : IsIntegral C) (g : C ⟶ Y) (n d : ℕ), IsSmoothProjCurve k C ∧ 0 < n ∧
      0 < d ∧ ∀ L : LB Y, L.IsLB →
        (n : ℤ) * degLB k (L.pull g) = (d : ℤ) * interNum (ZMod p) (structureModule Y) ![L] := by
  obtain ⟨Yn, _, ν, hν, hη, hdn, hD⟩ := exists_normal_finite (ZMod p) Y hP hd
  letI : Algebra (ZMod p) Γ(Yn, ⊤) := algebraΓAlong (ZMod p) ν
  have hPn : IsProper (strHom (ZMod p) Yn) := by
    rw [← comp_strHom (k := ZMod p) (g := ν) (fun _ => rfl)]; infer_instance
  obtain ⟨C, _, _, g, n, hC, hn, hg⟩ := exists_curve_of_dedekind p k Yn hdn hPn hD
  have hdeg : 0 < ν.residueDegree (genericPoint Yn) := by
    obtain ⟨w, hw, hw'⟩ := NefDescent.fibre_point Yn Y ν (genericPoint Y) ⟨_, hη⟩
    have : w = genericPoint Yn :=
      (ν.isDiscrete_preimage_singleton (genericPoint Y)).eq_of_specializes (genericPoint_specializes w) hη hw |>.symm
    rwa [this] at hw'
  refine ⟨C, inferInstance, inferInstance, g ≫ ν, n, _, hC, hn, hdeg, fun L hL => ?_⟩
  rw [degLB_pull_comp g ν hL, hg _ (LB.isLB_pull hL ν), ← ProjFin.interNumOn_eq_residueDegree_mul (ZMod p) Y Yn ν
    (ProperCurve.isProjOver_of_isProper _ hd) hd hη L hL]
  exact ((interNumOn_eq_interNum_pull (fun _ => rfl) (isLB_vecOne hL)).trans
      (congrArg _ (funext fun j => by fin_cases j; rfl))).symm

theorem exists_smooth_curve_over : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)) (a : W ⟶ X), IsProjOver p → IsProjOver (a ≫ p) → Surjective a →
  ∀ (q : ℕ) [Fact q.Prime] (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
    topologicalKrullDim Z = 1 →
    ∃ (C : Scheme.{0}) (_ : Algebra (AlgebraicClosure (ZMod q)) Γ(C, ⊤)) (_ : IsIntegral C) (g : C ⟶ W) (μ : ℝ),
      IsSmoothProjCurve (AlgebraicClosure (ZMod q)) C ∧ 0 < μ ∧ ∀ L : LB X, L.IsLB →
        (degLB (AlgebraicClosure (ZMod q)) (L.pull (g ≫ a)) : ℝ) = μ * (topSelfIntersection (ZMod q) (L.pull i) 1 : ℝ) := by
  intro F _ _ X Y p π hp hq hsurj r _ Z i _ _ _ hd
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper (π ≫ p) := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper π := IsProper.of_comp π p
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := NefDescent.fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := NefDescent.red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := NefDescent.dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := NefDescent.isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have hZP : IsProper (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom (𝓞 F))) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := 𝓞 F)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom (𝓞 F)) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    exact IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
  have hproj : IsProjOver (strHom (ZMod r) Z) := ProperCurve.isProjOver_of_isProper _ hd
  have hCP : IsProper (strHom (ZMod r) (Scheme.IdealSheafData.vanishingIdeal C).subscheme) := by
    rw [← comp_strHom (k := ZMod r) (g := f) (fun _ => rfl)]; infer_instance
  obtain ⟨C₀, _, _, g₀, n, d, hC₀, hn, hd0, hg₀⟩ := exists_curve_alg_closed r (AlgebraicClosure (ZMod r)) _ hd' hCP
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨C₀, inferInstance, inferInstance, g₀ ≫ i', (d : ℝ) * (f.residueDegree (genericPoint _) : ℝ) / n, hC₀,
    div_pos (mul_pos (by exact_mod_cast hd0) (by exact_mod_cast hdeg')) hn', fun L hL => ?_⟩
  have hN : (L.pull i).IsLB := LB.isLB_pull hL i
  have e1 : interNum (ZMod r) (structureModule _) ![(L.pull i).pull f] = interNumOn (ZMod r) f ![L.pull i] :=
    ((interNumOn_eq_interNum_pull (fun _ => rfl) (isLB_vecOne hN)).trans
      (congrArg _ (funext fun j => by fin_cases j; rfl))).symm
  have e4 := ProjFin.interNumOn_eq_residueDegree_mul (ZMod r) Z _ f hproj hd hη (L.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.pull i] = topSelfIntersection (ZMod r) (L.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have e6 := hg₀ _ (LB.isLB_pull hN f)
  rw [e1, e4, e5, ← degLB_pull_comp g₀ f hN, ← degLB_pull_comp _ i hL, Category.assoc, ← hcomm,
    ← Category.assoc] at e6
  have e7 : (n : ℝ) * (degLB (AlgebraicClosure (ZMod r)) (L.pull ((g₀ ≫ i') ≫ π)) : ℝ) =
      (d : ℝ) * ((f.residueDegree (genericPoint _) : ℝ) * (topSelfIntersection (ZMod r) (L.pull i) 1 : ℝ)) := by exact_mod_cast e6
  rw [div_mul_eq_mul_div, eq_div_iff hn'.ne', mul_comm, e7, mul_assoc]

end GlobalTheory.FbarCurve
