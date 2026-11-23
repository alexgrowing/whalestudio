import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemThetaDomainIffIsSiegelAddTranspose
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnThetaProdOfNormal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ClassicalThetaLevelAndLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesTangentVectors
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqMulOfMemSpan
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RelAmpleThetaBundleProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfExpThetaLinForm

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real

namespace GlobalTheory.ThetaVeryAmple

open ProjModelDim TangentOrigin

theorem formallyUnramified_of_derivations {A B : Type} [CommRing A] [CommRing B] (c : ℂ →+* B) (hc : c.FiniteType)
    (β : A →+* B) (hβ : β.FiniteType)
    (H : ∀ e : B →+* ℂ, (∀ a, e (c a) = a) → ∀ D : B →+ ℂ, (∀ f f', D (f * f') = e f * D f' + e f' * D f) →
      (∀ a, D (β a) = 0) → D = 0) : β.FormallyUnramified := by
  algebraize [β, c]
  refine ⟨?_⟩
  by_contra hne
  have : Nontrivial Ω[B⁄A] := not_subsingleton_iff_nontrivial.1 hne
  obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule B Ω[B⁄A])).resolve_left bot_ne_top
  obtain ⟨I, hI, ⟨ψ⟩⟩ := isSimpleModule_iff_quot_maximal.1 (isSimpleModule_iff_isCoatom.2 hN)
  let := Ideal.Quotient.field I
  have : Module.Finite ℂ (B ⧸ I) := finite_of_finite_type_of_isJacobsonRing _ _
  let ε : ℂ ≃+* B ⧸ I := RingEquiv.ofBijective (algebraMap ℂ (B ⧸ I)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χ : Ω[B⁄A] →ₗ[B] B ⧸ I := ψ.toLinearMap ∘ₗ N.mkQ
  let D : B →+ ℂ := ε.symm.toAddMonoidHom.comp
    (χ.toAddMonoidHom.comp (KaehlerDifferential.D A B).toLinearMap.toAddMonoidHom)
  have hD : ∀ f, D f = ε.symm (χ (KaehlerDifferential.D A B f)) := fun _ => rfl
  have h0 := H (ε.symm.toRingHom.comp (Ideal.Quotient.mk I)) (fun a => ε.symm_apply_apply a) D
    (fun f f' => by
      rw [hD, hD, hD, Derivation.leibniz, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, map_add,
        map_mul, map_mul]
      rfl)
    (fun a => by
      rw [hD, show β a = algebraMap A B a from rfl, Derivation.map_algebraMap, map_zero, map_zero])
  have h1 : χ = 0 := LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A B) fun f =>
    ε.symm.map_eq_zero_iff.1 ((hD f).symm.trans (DFunLike.congr_fun h0 f))
  refine hN.1 (top_le_iff.1 fun x _ => ?_)
  exact (Submodule.Quotient.mk_eq_zero N).1 (ψ.map_eq_zero_iff.1 (DFunLike.congr_fun h1 x))

def dualHom {B : Type} [CommRing B] (e : B →+* ℂ) (D : B →+ ℂ)
    (hD : ∀ f f', D (f * f') = e f * D f' + e f' * D f) : B →+* DualNumber ℂ where
  toFun f := (e f, D f)
  map_one' := TrivSqZeroExt.ext e.map_one (by
    have := hD 1 1
    rw [_root_.mul_one, e.map_one, _root_.one_mul] at this
    exact left_eq_add.1 this)
  map_zero' := TrivSqZeroExt.ext e.map_zero D.map_zero
  map_add' f f' := TrivSqZeroExt.ext (e.map_add f f') (D.map_add f f')
  map_mul' f f' := TrivSqZeroExt.ext (e.map_mul f f')
    (((hD f f').trans (congrArg _ (mul_comm _ _))).trans (DualNumber.snd_mul (e f, D f) (e f', D f')).symm)

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X Y : Scheme.{0}} {ex : E → (Sp ℂ ⟶ X)}

theorem isHolFamily_comp (h : IsHolFamily ex) (φ : X ⟶ Y) : IsHolFamily fun z => ex z ≫ φ := fun V b => by
  simpa only [← valAt'_comp, top_le_preimage_comp] using h (φ ⁻¹ᵁ V) ((φ.app V).hom b)

theorem der_appLE (h : IsHolFamily ex) (φ : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (e : U ≤ φ ⁻¹ᵁ V) {z : E}
    (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (ξ : E) (b : Γ(Y, V)) :
    h.der hz ξ ((φ.appLE V U e).hom b) = fderiv ℂ (fun y => valAt' (ex y ≫ φ) V b) z ξ := by
  have : (fun y => valAt' (ex y) U ((φ.appLE V U e).hom b)) =ᶠ[𝓝 z] fun y => valAt' (ex y ≫ φ) V b :=
    (h.eventually hz).mono fun y hy => valAt'_appLE _ φ V U e b hy
  rw [IsHolFamily.der_apply, this.fderiv_eq]

theorem der_res (h : IsHolFamily ex) {U V : X.Opens} (e : U ≤ V) {z : E}
    (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (hV : ⊤ ≤ ex z ⁻¹ᵁ V) (ξ : E) (b : Γ(X, V)) :
    h.der hz ξ (resG X e b) = h.der hV ξ b := by
  have : (fun y => valAt' (ex y) U (resG X e b)) =ᶠ[𝓝 z] fun y => valAt' (ex y) V b :=
    (h.eventually hz).mono fun y hy => valAt'_res _ e b hy
  rw [IsHolFamily.der_apply, IsHolFamily.der_apply, this.fderiv_eq]

theorem fst_evalPt {w : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X} (hw : spMap fstC ≫ w = x) {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) : (evalPt w U h f).fst = valAt' x U f := by
  subst hw
  rw [valAt'_eq_evalPt _ _ ((top_le_preimage_iff w U).1 h), evalPt_spMap_comp fstC w U h]
  rfl

theorem snd_evalPt_eq_der (h : IsHolFamily ex) {w : Sp (DualNumber ℂ) ⟶ X} {z : E} (hw : spMap fstC ≫ w = ex z)
    {U V : X.Opens} (hU : IsAffineOpen U) (hz : ⊤ ≤ ex z ⁻¹ᵁ U) (hV : ⊤ ≤ ex z ⁻¹ᵁ V) (hwU : ⊤ ≤ w ⁻¹ᵁ U)
    (hwV : ⊤ ≤ w ⁻¹ᵁ V) (ξ : E) (h0 : ∀ f, (evalPt w U hwU f).snd = h.der hz ξ f) (r : Γ(X, V)) :
    (evalPt w V hwV r).snd = h.der hV ξ r := by
  obtain ⟨s, hsV, hs⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (top_le_preimage_iff_mem _ _).1 hV⟩
    ((top_le_preimage_iff_mem _ _).1 hz)
  have hB : ⊤ ≤ ex z ⁻¹ᵁ X.basicOpen s := (top_le_preimage_iff_mem _ _).2 hs
  have hwB : ⊤ ≤ w ⁻¹ᵁ X.basicOpen s := (top_le_preimage_iff w _).2 (hw ▸ hB)
  have := hU.isLocalization_basicOpen s
  have heq : evalPt w _ hwB = dualHom (valAtHom _ _ hB) (h.der hB ξ) (fun f f' => by
      rw [h.der_mul, valAt'_eq_valAtHom _ hB, valAt'_eq_valAtHom _ hB]) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ?_)
    · exact (fst_evalPt hw hwB _).trans (valAt'_eq_valAtHom _ hB _)
    · exact (congrArg TrivSqZeroExt.snd (evalPt_res w (X.basicOpen_le s) hwU hwB f)).trans
        ((h0 f).trans (der_res h (X.basicOpen_le s) hB hz ξ f).symm)
  rw [← evalPt_res w hsV hwV hwB, heq]
  exact der_res h hsV hB hV ξ r

end Family

theorem veryAmpleAt_of_isClosedImmersion {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {N K : ℕ}
    (s : Fin (K + 1) → (lbPow L N).Sec) (hs : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (h : IsClosedImmersion (ProjSpace.toProj A.hom s hs)) : Out.VeryAmpleAt A L N := by
  have h1 : AmpleSpan.EmbedsBy A.hom s := (ProjSpace.veryAmpleBy_comp_iff A.hom (𝟙 _) s).1 (by
    rw [Category.comp_id]; exact (ProjSpace.veryAmpleBy_iff _ s).2 ⟨hs, h⟩)
  intro U hU
  have : IsAffine U := hU
  choose s' hs' _ using fun i => AmpleSpan.existsUnique_secScal hL (φ := fun _ : PUnit => 𝟙 A.left)
    (ε := fun _ => N) (h := (A.hom ⁻¹ᵁ U).ι)
    (AmpleSpan.formEq_const (K' := Fin N) (ε' := fun _ => 1) (Category.comp_id _) (by simp)) (s i)
  exact ⟨K, s', AmpleSpan.EmbedsBy.secScal hL (isPullback_morphismRestrict A.hom U).flip h1 hs'⟩

section Criterion

variable {g : ℕ} {X : Over (Sp ℂ)} {Y : Scheme.{0}} {ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
  {φ : X.left ⟶ Y} {p : Y ⟶ Sp ℂ}

theorem constFn_eq_appLE (hp : φ ≫ p = X.hom) {U : X.left.Opens} {V : Y.Opens} (e : U ≤ φ ⁻¹ᵁ V) (a : ℂ) :
    constFn X.hom U a = (φ.appLE V U e).hom (constFn p V a) := by
  rw [← hp]
  exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE φ p ⊤ V U le_top e)).symm

theorem resG_constFn' {Z : Scheme.{0}} (q : Z ⟶ Sp ℂ) {U V : Z.Opens} (e : U ≤ V) (a : ℂ) :
    resG Z e (constFn q V a) = constFn q U a :=
  congrArg (fun r => r.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_map q (le_top : V ≤ q ⁻¹ᵁ ⊤) (homOfLE e).op)

theorem formallyUnramified_of_fderiv (hsm : SmoothOfRelativeDimension g X.hom) [LocallyOfFiniteType φ]
    (hex : Function.Surjective ex) (hol : IsHolFamily fun z => (ex z).left) (hp : φ ≫ p = X.hom)
    (htan : ∀ z ξ, (∀ (V : Y.Opens) (b : Γ(Y, V)), ⊤ ≤ ((ex z).left ≫ φ) ⁻¹ᵁ V →
      fderiv ℂ (fun y => valAt' ((ex y).left ≫ φ) V b) z ξ = 0) → ξ = 0) : FormallyUnramified φ := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  refine ⟨fun {V} hV {U} hU hUV => ?_⟩
  refine formallyUnramified_of_derivations
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top).hom
    ((X.hom.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)) _
    (φ.finiteType_appLE hV hU hUV) fun e he D hD hD0 => ?_
  obtain ⟨x, ⟨hz, hx⟩, -⟩ := existsUnique_point_of_ringHom X U hU e he
  obtain ⟨z, rfl⟩ := hex x
  obtain ⟨w, hwU, hwe⟩ := exists_evalPt_eq hU (dualHom e D hD)
  have hw : spMap fstC ≫ w = (ex z).left := by
    refine ext_evalPt hU ((top_le_preimage_iff w U).1 hwU) hz (RingHom.ext fun f => ?_)
    rw [evalPt_spMap_comp fstC w U hwU, hwe]
    exact (hx f).symm.trans (valAt'_eq_evalPt _ _ hz f)
  obtain ⟨W, σ, U₀, t, -, hW0, hσ, hU₀, -, ht, -, hdet⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale X g hsm (ex z)
  have hz₀ : ⊤ ≤ (ex z).left ⁻¹ᵁ U₀ := hσ ▸ (ht 0 hW0).1
  have hw₀ : ⊤ ≤ w ⁻¹ᵁ U₀ := (top_le_preimage_iff w _).2 (hw ▸ hz₀)
  have hc : ∀ ξ a, hol.der hz₀ ξ (constFn X.hom U₀ a) = 0 := fun ξ a =>
    hol.der_constFn hz₀ ξ X.hom (fun y => Over.w (ex y)) a
  let T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun y => valAt' (ex y).left U₀ (t i)) z).toLinearMap
  have hT : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    have h0 := hdet _ (hc ξ) (hol.der_mul hz₀ ξ) fun i => congrFun hξ i
    refine htan z ξ fun V' b hV' => ?_
    have := hol.fderiv_eq_zero hU₀ hz₀ ((top_le_preimage_comp _ φ V').1 hV') (ξ := ξ)
      (fun f => DFunLike.congr_fun h0 f) ((φ.app V').hom b)
    simpa only [valAt'_comp] using this
  let D₀ : Γ(X.left, U₀) →+ ℂ :=
    (TrivSqZeroExt.sndHom ℂ ℂ).toAddMonoidHom.comp (evalPt w U₀ hw₀).toAddMonoidHom
  have hD₀ : ∀ f, D₀ f = (evalPt w U₀ hw₀ f).snd := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := LinearMap.injective_iff_surjective.1 hT fun i => D₀ (t i)
  have h1 : D₀ - hol.der hz₀ ξ = 0 := by
    refine hdet _ (fun a => ?_) (fun f f' => ?_) fun i => sub_eq_zero.2 (congrFun hξ i).symm
    · have hi : ⊤ ≤ w ⁻¹ᵁ (U ⊓ U₀) := le_inf hwU hw₀
      rw [AddMonoidHom.sub_apply, hc, sub_zero, hD₀, ← evalPt_res w inf_le_right hw₀ hi, resG_constFn',
        ← resG_constFn' X.hom (inf_le_left : U ⊓ U₀ ≤ U), evalPt_res w inf_le_left hwU hi, hwe,
        constFn_eq_appLE hp hUV]
      exact hD0 _
    · simp only [AddMonoidHom.sub_apply, hD₀, map_mul, DualNumber.snd_mul, fst_evalPt hw, hol.der_mul]
      ring
  have h2 : ∀ f, D f = hol.der hz ξ f := fun f =>
    (congrArg (fun q => (q f).snd) hwe).symm.trans (snd_evalPt_eq_der hol hw hU₀ hz₀ hz hw₀ hwU ξ
      (fun f => sub_eq_zero.1 (DFunLike.congr_fun h1 f)) f)
  have hzV : ⊤ ≤ ((ex z).left ≫ φ) ⁻¹ᵁ V := (top_le_preimage_comp _ φ V).2 (top_le_preimage_mono _ hUV hz)
  obtain rfl : ξ = 0 := htan z ξ fun V' b hV' => (isHolFamily_comp hol φ).fderiv_eq_zero hV hzV hV'
    (fun b => (der_appLE hol φ hUV hz ξ b).symm.trans ((h2 _).symm.trans (hD0 b))) b
  ext f
  rw [h2, IsHolFamily.der_apply, map_zero]
  rfl

theorem isClosedImmersion_of_fderiv (hsm : SmoothOfRelativeDimension g X.hom) [IsProper X.hom] [IsProper p]
    (hex : Function.Surjective ex) (hol : IsHolFamily fun z => (ex z).left) (hp : φ ≫ p = X.hom)
    (hinj : ∀ z z', (ex z).left ≫ φ = (ex z').left ≫ φ → ex z = ex z')
    (htan : ∀ z ξ, (∀ (V : Y.Opens) (b : Γ(Y, V)), ⊤ ≤ ((ex z).left ≫ φ) ⁻¹ᵁ V →
      fderiv ℂ (fun y => valAt' ((ex y).left ≫ φ) V b) z ξ = 0) → ξ = 0) : IsClosedImmersion φ := by
  have : IsProper (φ ≫ p) := hp ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ p
  have := formallyUnramified_of_fderiv hsm hex hol hp htan
  have hs : (pullback.diagonal φ).opensRange = ⊤ := by
    refine top_le_iff.1 (ThetaAmple.opens_le_of_points (pullback.fst φ φ ≫ X.hom) fun y hy _ => ?_)
    obtain ⟨z, hz⟩ := hex (Over.homMk (y ≫ pullback.fst φ φ) ((Category.assoc _ _ _).trans hy))
    obtain ⟨z', hz'⟩ := hex (Over.homMk (y ≫ pullback.snd φ φ) ((Category.assoc _ _ _).trans (by
      rw [← hp, ← pullback.condition_assoc, hp]; exact hy)))
    have e := hinj z z' (by
      rw [hz, hz']
      exact (Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : y ≫ pullback.fst φ φ = y ≫ pullback.snd φ φ := congrArg CommaMorphism.left (hz.symm.trans (e.trans hz'))
    have e'' : (y ≫ pullback.fst φ φ) ≫ pullback.diagonal φ = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e']
    intro a _
    exact ⟨(y ≫ pullback.fst φ φ) a, congrArg (fun q => q a) e''⟩
  have : IsIso (pullback.diagonal φ) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ hs
  have : Mono φ := (pullback.isIso_diagonal_iff φ).1 this
  exact (IsClosedImmersion.iff_isProper_and_mono φ).2 ⟨inferInstance, inferInstance⟩

end Criterion

section Lefschetz

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (a b : Fin g → ℝ) {M : ℕ} (hM : 3 ≤ M)
include hτ hM

theorem lefschetz_char :
    (∀ z, ∃ f ∈ thetaLevelChar a b M τ, f z ≠ 0) ∧
    (∀ z z' κ, (∀ f ∈ thetaLevelChar a b M τ, f z = κ * f z') → z - z' ∈ periodLattice τ) ∧
    (∀ z ξ κ, (∀ f ∈ thetaLevelChar a b M τ, fderiv ℂ f z ξ = κ * f z) → ξ = 0) := by
  have f0 := @GlobalTheory.siegelSubDomain_and_domainOpen
  have f1 := @GlobalTheory.thetaMTest_and_thetaSummable
  have f2 := @GlobalTheory.thetaHolo_of_domainOpen_of_mTest f0.2 f1.1
  have f3 := @GlobalTheory.classicalTheta_level_and_linearIndependent f0.1 f2 f1.1
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero f3
  have f9 := @GlobalTheory.exists_level_apply_ne_zero_of_two_le f8
  have f10 := @GlobalTheory.periodLattice_isLattice_of_mem_siegelH
  have f11 := @GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul f8 f10
  have f12 := @GlobalTheory.ThetaSeparation.level_three_separates_points f8 f11
  have f13 := @GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors f8 f11 f10
  let v := τ *ᵥ ofRealVec a + ofRealVec b
  let E : (Fin g → ℂ) → ℂ := fun z =>
    eC (M * (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b)))
  have hE : Differentiable ℂ E := by
    simp only [E, eC, dotProduct]
    fun_prop
  have hE0 : ∀ z, E z ≠ 0 := fun z => GlobalTheory.eC_ne_zero _
  have hs : ∀ f ∈ thetaLevel M τ, (fun z => E z * f (z + v)) ∈ thetaLevelChar a b M τ := fun f hf => by
    have := (thetaLevelEquivChar a b M hτ.1 ⟨f, hf⟩).2
    rw [thetaLevelEquivChar_apply] at this
    convert this using 1
    funext z
    rw [thetaShift_apply, add_assoc z]
  refine ⟨fun z => ?_, fun z z' κ h => ?_, fun z ξ κ h => ?_⟩
  · obtain ⟨f, hf, h0⟩ := f9 g τ hτ M (by omega) (z + v)
    exact ⟨_, hs f hf, mul_ne_zero (hE0 z) h0⟩
  · have := f12 g τ hτ M hM (z + v) (z' + v) (κ * E z' / E z) fun f hf => by
      have h1 : E z * f (z + v) = κ * (E z' * f (z' + v)) := h _ (hs f hf)
      have := hE0 z
      field_simp
      linear_combination h1
    rwa [add_sub_add_right_eq_sub] at this
  · refine f13 g τ hτ M hM (z + v) ξ (κ - fderiv ℂ E z ξ / E z) fun f hf => ?_
    have h1 := h _ (hs f hf)
    have h2 : HasFDerivAt (fun z => f (z + v)) (fderiv ℂ f (z + v)) z :=
      (hasFDerivAt_comp_add_right v).2 (hf.1 (z + v)).hasFDerivAt
    rw [((hE z).hasFDerivAt.fun_mul h2).fderiv] at h1
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at h1
    have := hE0 z
    field_simp
    linear_combination h1

end Lefschetz

section Sections

variable {X : Over (Sp ℂ)} [GrpObj X] {L : LB X.left} {g : ℕ} (u : HolUnif X L g) (hL : L.IsLB) {M : ℕ}
include hL

theorem exists_chart_pow (M : ℕ) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L M).U (fun _ => i) ∧ u.fr i z ≠ 0 := by
  obtain ⟨i, hi⟩ := (ThetaAmple.top_le_preimage_iSup (u.ex z).left L.U).1 (by rw [hL.cover]; exact le_top)
  exact ⟨i, fun q hq => Set.mem_iInter.2 fun _ => hi hq, u.fr_ne i z hi⟩

theorem mem_nonzeroLocus_iff {s : (lbPow L M).Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFnPow M s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  refine (ThetaAmple.top_le_preimage_iSup _ _).trans ⟨fun ⟨j, hj⟩ => ?_, fun h0 => ?_⟩
  · have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hj
    exact left_ne_zero_of_mul ((h j z (top_le_preimage_of_valAt'_ne_zero _ h1)).symm.trans_ne h1)
  · obtain ⟨i, hi, hf⟩ := exists_chart_pow u hL M z
    exact ⟨fun _ => i, (top_le_preimage_basicOpen_iff _ _ _).2
      ((h _ z hi).trans_ne (mul_ne_zero h0 (pow_ne_zero _ hf)))⟩

theorem valAt'_secRatio {s s' : (lbPow L M).Sec} {θ θ' : (Fin g → ℂ) → ℂ} (h : u.IsFnPow M s θ)
    (h' : u.IsFnPow M s' θ') {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ (ProjSpace.secRatio s s') = θ' z / θ z := by
  obtain ⟨i, hi, hf⟩ := exists_chart_pow u hL M z
  have hm := (top_le_preimage_inf _ _ _).2 ⟨(mem_nonzeroLocus_iff u hL h z).2 hz, hi⟩
  have e := congrArg (valAt' (u.ex z).left _) (ProjSpace.secRatio_spec s s' fun _ => i)
  rw [valAt'_mul, valAt'_res _ _ _ hm, valAt'_res _ _ _ hm, valAt'_res _ _ _ hm, h _ z hi, h' _ z hi,
    ← _root_.mul_assoc] at e
  rw [eq_div_iff hz]
  exact (mul_right_cancel₀ (pow_ne_zero _ hf) e).symm

theorem veryAmpleAt_of_separation [IsProper X.hom] (hsm : SmoothOfRelativeDimension g X.hom) {K : ℕ}
    (s : Fin (K + 1) → (lbPow L M).Sec) (θ : Fin (K + 1) → (Fin g → ℂ) → ℂ) (hθ : ∀ j, Differentiable ℂ (θ j))
    (hs : ∀ j, u.IsFnPow M (s j) (θ j))
    (h₀ : ∀ z, ∃ f ∈ Submodule.span ℂ (Set.range θ), f z ≠ 0)
    (h₁ : ∀ z z' κ, (∀ f ∈ Submodule.span ℂ (Set.range θ), f z = κ * f z') → u.ex z = u.ex z')
    (h₂ : ∀ z ξ κ, (∀ f ∈ Submodule.span ℂ (Set.range θ), fderiv ℂ f z ξ = κ * f z) → ξ = 0) :
    Out.VeryAmpleAt X L M := by
  have hsp : ∀ z z' κ, (∀ j, θ j z = κ * θ j z') → ∀ f ∈ Submodule.span ℂ (Set.range θ), f z = κ * f z' := by
    intro z z' κ h f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨j, rfl⟩ := hf; exact h j
    | zero => simp
    | add f f' _ _ e e' => rw [Pi.add_apply, Pi.add_apply, e, e', mul_add]
    | smul c f _ e => rw [Pi.smul_apply, Pi.smul_apply, e, smul_eq_mul, smul_eq_mul, mul_left_comm]
  have hne : ∀ z, ∃ j, θ j z ≠ 0 := fun z => by
    by_contra! h
    obtain ⟨f, hf, h0⟩ := h₀ z
    exact h0 ((hsp z z 0 (fun j => (h j).trans (zero_mul _).symm) f hf).trans (zero_mul _))
  have hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤ := by
    refine top_le_iff.1 (ThetaAmple.opens_le_of_points X.hom fun x hx _ => ?_)
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    obtain rfl : (u.ex z).left = x := congrArg CommaMorphism.left hz
    exact (ThetaAmple.top_le_preimage_iSup _ _).2
      ((hne z).imp fun j hj => (mem_nonzeroLocus_iff u hL (hs j) z).2 hj)
  refine veryAmpleAt_of_isClosedImmersion hL s hcov ?_
  set φ := ProjSpace.toProj X.hom s hcov
  have hch : ∀ i z, ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ ProjSpace.chart ℂ K i ↔ θ i z ≠ 0 := fun i z => by
    rw [top_le_preimage_comp, ProjSpace.toProj_preimage_chart]
    exact mem_nonzeroLocus_iff u hL (hs i) z
  have hval : ∀ i j z, θ i z ≠ 0 →
      valAt' ((u.ex z).left ≫ φ) _ (ProjSpace.ratio ℂ K i j) = θ j z / θ i z := fun i j z hz => by
    rw [← valAt'_secRatio u hL (hs i) (hs j) hz, ← ProjSpace.pullRatio_toProj X.hom s hcov]
    exact (valAt'_appLE _ φ _ _ _ _ ((mem_nonzeroLocus_iff u hL (hs i) z).2 hz)).symm
  have := isProper_str ℂ K
  refine isClosedImmersion_of_fderiv hsm u.ex_onto u.hol (ProjSpace.toProj_str X.hom s hcov)
    (fun z z' e => ?_) fun z ξ h => ?_
  · obtain ⟨i, hi⟩ := hne z
    have hi' : θ i z' ≠ 0 := (hch i z').1 (e ▸ (hch i z).2 hi)
    refine h₁ z z' (θ i z / θ i z') (hsp _ _ _ fun j => ?_)
    have := (hval i j z hi).symm.trans ((congrArg (fun q => valAt' q _ (ProjSpace.ratio ℂ K i j)) e).trans
      (hval i j z' hi'))
    field_simp at this ⊢
    linear_combination this
  · obtain ⟨i, hi⟩ := hne z
    exact h₂ z ξ _ (fderiv_eq_mul_of_ratio θ hθ i z ξ hi _ (hval i) fun j => h _ _ ((hch i z).2 hi))

end Sections

end GlobalTheory.ThetaVeryAmple

namespace GlobalTheory

theorem thetaBundle_veryAmpleAt : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ) → ∀ M : ℕ, 3 ≤ M → Out.VeryAmpleAt X L M := by
  rintro g τ hτ N - X ex D ⟨-, hprop, -, hex, -⟩ - - _ - a b - - L u hL ⟨rfl, -⟩ - hsm hsec M hM
  obtain ⟨h₀, h₁, h₂⟩ := ThetaVeryAmple.lefschetz_char hτ a b hM
  have := finiteDimensional_thetaLevelChar (a := a) (b := b) (N := M) hτ.1 (by omega)
  have hK : Module.finrank ℂ (thetaLevelChar a b M τ) = (M ^ g - 1) + 1 := by
    rw [finrank_thetaLevelChar hτ (by omega), Fintype.card_fin, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
  let B := Module.finBasisOfFinrankEq ℂ _ hK
  have hB : Submodule.span ℂ (Set.range fun j => (B j).1) = thetaLevelChar a b M τ := by
    have := congrArg (Submodule.map (thetaLevelChar a b M τ).subtype) B.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at this
  choose s hs _ using fun j => (hsec M).2 _ (B j).2
  rw [← hB] at h₀ h₁ h₂
  exact ThetaVeryAmple.veryAmpleAt_of_separation u hL hsm s _ (fun j => (B j).2.1) hs h₀
    (fun z z' κ h => (hex z z').2 (h₁ z z' κ h)) h₂

end GlobalTheory
