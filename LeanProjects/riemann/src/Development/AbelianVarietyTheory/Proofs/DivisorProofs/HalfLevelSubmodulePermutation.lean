import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin

noncomputable section

namespace GlobalTheory.DefSplit

section Alg

open scoped TensorProduct

variable {K L B W : Type} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B] [AddCommGroup W] [Module K W]

def part (m : B →ₐ[K] Module.End K W) (χ : B →ₐ[K] L) : Submodule L (L ⊗[K] W) :=
  ⨅ b : B, Module.End.eigenspace ((m b).baseChange L) (χ b)

theorem mem_part (m : B →ₐ[K] Module.End K W) (χ : B →ₐ[K] L) (v : L ⊗[K] W) :
    v ∈ part m χ ↔ ∀ b, (m b).baseChange L v = χ b • v := by
  simp only [part, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem indep_part (m : B →ₐ[K] Module.End K W) : iSupIndep (part (L := L) m) := by
  have hc : ∀ a b : B, Commute ((m a).baseChange L) ((m b).baseChange L) := fun a b => by
    show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have h := (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => (m b).baseChange L)
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ).comp
      (f := fun χ : B →ₐ[K] L => (χ : B → L)) DFunLike.coe_injective
  exact h.mono fun χ => iInf_mono fun b => Module.End.eigenspace_le_maxGenEigenspace

theorem iSup_part [IsSepClosed L] [Algebra.Etale K B] (m : B →ₐ[K] Module.End K W) : ⨆ χ, part (L := L) m χ = ⊤ := by
  classical
  haveI : Module.Finite L (L ⊗[K] B) := Algebra.FormallyUnramified.finite_of_free L _
  haveI : IsArtinianRing (L ⊗[K] B) := isArtinian_of_tower L inferInstance
  letI : Fintype (PrimeSpectrum (L ⊗[K] B)) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] B)
  let M : L ⊗[K] B →ₐ[L] Module.End L (L ⊗[K] W) :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ((Module.End.baseChangeHom K L W).comp m)
      fun a b => Algebra.commutes a _
  have hM : ∀ b, M (1 ⊗ₜ b) = (m b).baseChange L := fun b => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ 1 b).trans ?_
    rw [map_one, one_mul]
    rfl
  let χ : PrimeSpectrum (L ⊗[K] B) → (B →ₐ[K] L) := fun i =>
    (((Pi.evalAlgHom L (fun _ => L) i).comp e.toAlgHom).restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hχ : ∀ i b, χ i b = e (1 ⊗ₜ b) i := fun _ _ => rfl
  refine eq_top_iff.2 fun v _ => ?_
  have h1 : v = ∑ i, M (e.symm (Pi.single i 1)) v := by
    rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, Finset.univ_sum_single (fun _ => (1 : L))]
    have : e.symm (fun _ => (1 : L)) = 1 := map_one e.symm
    rw [this, map_one]
    rfl
  rw [h1]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (χ i) ((mem_part m _ _).2 fun b => ?_)
  have h2 : (1 ⊗ₜ b) * e.symm (Pi.single i 1) = χ i b • e.symm (Pi.single i 1) := by
    apply e.injective
    rw [map_mul, map_smul, e.apply_symm_apply, hχ]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← hM, ← Module.End.mul_apply, ← map_mul, h2, map_smul, LinearMap.smul_apply]

theorem split_of_free [IsSepClosed L] [Algebra.Etale K B] (m : B →ₐ[K] Module.End K W) {G : Type} [Group G]
    (τ : G →* (B →ₐ[K] B)) (T : G → W →ₗ[K] W) (hT : ∀ g b, T g * m b = m (τ g b) * T g)
    (hf : ∀ g (χ : B →ₐ[K] L), χ.comp (τ g) = χ → g = 1) :
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction G X) (A : X → Submodule L (L ⊗[K] W)),
      (∀ (h : G) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : G) (y : X), ∀ v ∈ A y, (T h).baseChange L v ∈ A (h • y) := by
  classical
  haveI : Module.Finite K B := Algebra.FormallyUnramified.finite_of_free K _
  letI act : MulAction G (B →ₐ[K] L) :=
    { smul := fun g χ => χ.comp (τ g⁻¹)
      one_smul := fun χ => by
        show χ.comp (τ 1⁻¹) = χ
        rw [inv_one, map_one]; rfl
      mul_smul := fun g h χ => by
        show χ.comp (τ (g * h)⁻¹) = (χ.comp (τ h⁻¹)).comp (τ g⁻¹)
        rw [mul_inv_rev, map_mul]; rfl }
  refine ⟨B →ₐ[K] L, Fintype.ofFinite _, inferInstance, act, part m, fun h y hy => inv_eq_one.1 (hf _ y hy),
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨indep_part m, iSup_part m⟩,
    fun h y v hv => (mem_part m _ _).2 fun b => ?_⟩
  have e1 : τ h (τ h⁻¹ b) = b := by
    rw [← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have e2 := hT h (τ h⁻¹ b)
  rw [e1] at e2
  rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← e2, LinearMap.baseChange_mul, Module.End.mul_apply,
    (mem_part m _ _).1 hv, map_smul]
  rfl

theorem split_complex [Algebra.Etale K B] (σ : K →+* ℂ) (m : B →ₐ[K] Module.End K W) {G : Type} [Group G]
    (τ : G →* (B →ₐ[K] B)) (T : G → W →ₗ[K] W) (hT : ∀ g b, T g * m b = m (τ g b) * T g)
    (hf : ∀ g (χ : B →+* ℂ), (∀ k, χ (algebraMap K B k) = σ k) → (∀ b, χ (τ g b) = χ b) → g = 1) :
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction G X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC σ W)),
      (∀ (h : G) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : G) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin σ (T h) v ∈ A (h • y) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact split_of_free (L := ℂ) m τ T hT fun g χ hχ => hf g χ.toRingHom χ.commutes (AlgHom.congr_fun hχ)

end Alg

section Geo

open CategoryTheory Limits AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient (fnAt basePt)
open GlobalTheory.LevelCoverCompare (fnRule fnRule_mem fnRule_injective fnAt_comp)

theorem fnAt_appTop {X Y : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (r : X ⟶ Y) (b : Γ(Y, ⊤)) :
    fnAt y (r.appTop.hom b) = fnAt (y ≫ r) b := by
  rw [fnAt, fnAt, Scheme.Hom.comp_appTop]
  rfl

theorem eq_of_fnAt {X : Scheme.{0}} [IsAffine X] {S : Type} [CommRing S] {y z : Sp S ⟶ X}
    (h : ∀ b, fnAt y b = fnAt z b) : y = z :=
  ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun b =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1 (h b)))

theorem exists_pt {X : Scheme.{0}} [IsAffine X] {S : Type} [CommRing S] (χ : Γ(X, ⊤) →+* S) :
    ∃ y : Sp S ⟶ X, ∀ b, fnAt y b = χ b := by
  refine ⟨spMap χ ≫ X.isoSpec.inv, fun b => ?_⟩
  rw [fnAt_comp]
  congr 1
  have h : X.isoSpec.hom.appTop.hom (X.isoSpec.inv.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h
  exact h

theorem fnAt_toΓ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : R) : fnAt (spMap φ) (toΓ R k) = φ k := by
  have h := fnAt_comp φ (𝟙 (Sp R)) (toΓ R k)
  rw [Category.comp_id] at h
  rw [h]
  congr 1
  simp [fnAt, toΓ]

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def cst : c.F →+* Γ(Xo.XF c, ⊤) := (strK (Xo := Xo) (c := c)).appTop.hom.comp (toΓ c.F)

theorem fnAt_cst {S : Type} [CommRing S] (y : Sp S ⟶ Xo.XF c) (k : c.F) :
    fnAt y (cst Xo c k) = fnAt (y ≫ strK) (toΓ c.F k) := fnAt_appTop y _ _

theorem fnRule_cst (k : c.F) (f : Rul Xo c) : fnRule (cst Xo c k) * f = k • f := by
  funext p y
  show fnAt (basePt y) (cst Xo c k) * f p y = k • f p y
  rw [fnAt_cst, basePt, pullback.lift_snd, fnAt_toΓ, Algebra.smul_def]

theorem fnRule_mul (a b : Γ(Xo.XF c, ⊤)) : fnRule (a * b) = fnRule a * fnRule b := by
  funext p y
  show fnAt (basePt y) _ = fnAt (basePt y) _ * fnAt (basePt y) _
  simp only [fnAt, map_mul]

theorem fnRule_add (a b : Γ(Xo.XF c, ⊤)) : fnRule (a + b) = fnRule a + fnRule b := by
  funext p y
  show fnAt (basePt y) _ = fnAt (basePt y) _ + fnAt (basePt y) _
  simp only [fnAt, map_add]

theorem fnRule_one : fnRule (1 : Γ(Xo.XF c, ⊤)) = 1 := by
  funext p y
  show fnAt _ _ = 1
  simp only [fnAt, map_one]

theorem fnRule_zero : fnRule (0 : Γ(Xo.XF c, ⊤)) = 0 := by
  funext p y
  show fnAt _ _ = 0
  simp only [fnAt, map_zero]

theorem finite_strK (hq : Dw.q = 0) : IsFinite (strK (Xo := Xo) (c := c)) := by
  haveI := GlobalTheory.FlatLine.DefinitePoint.etale_strK Xo c hq
  haveI := CompFin.quasiCompact_alt Xo
  haveI : LocallyQuasiFinite (strK (Xo := Xo) (c := c)) := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := (strK (Xo := Xo) (c := c)).formallyUnramified_appLE hU hV e
    have h₂ := (strK (Xo := Xo) (c := c)).finiteType_appLE hU hV e
    algebraize [((strK (Xo := Xo) (c := c)).appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact IsFinite.of_locallyQuasiFinite _

theorem isAffine_XF (hq : Dw.q = 0) : IsAffine (Xo.XF c) := by
  haveI := finite_strK (Xo := Xo) (c := c) hq
  exact isAffine_of_isAffineHom (strK (Xo := Xo) (c := c))

theorem etale_cst (hq : Dw.q = 0) : (cst Xo c).Etale := by
  haveI := isAffine_XF (Xo := Xo) (c := c) hq
  have h := (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := strK (Xo := Xo) (c := c))).1
    (GlobalTheory.FlatLine.DefinitePoint.etale_strK Xo c hq)
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv)) h

variable {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem exists_map (hL : ActLev (Xo := Xo) c lev) (g : G) : ∃ r : Xo.XF c ⟶ Xo.XF c, r ≫ strK = strK ∧
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (lev g) y y' → basePt y' = basePt y ≫ r := by
  by_cases h : ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧ IsLevMove ρ ν (lev g).1 (lev g).2
  · obtain ⟨ρ, ν, hi, hm⟩ := h
    refine ⟨pullback.lift (pullback.fst _ _ ≫ ρ) (pullback.snd _ _) (by rw [Category.assoc, hm.1, pullback.condition]),
      pullback.lift_snd _ _ _, fun S _ _ y y' hy => ?_⟩
    obtain ⟨z, hz⟩ := (GlobalTheory.exists_unique_frMove D.host.E H Dw l Xo c ρ ν hm.1 S y).1
    have h1 : z.x = spMap (AlgHom.id c.F S).toRingHom ≫ y'.x := (hL.func g S y y' z hy ⟨ρ, ν, hi, hm, hz⟩).1
    have h2 : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _ := Spec.map_id _
    rw [h2, Category.id_comp, hz.1] at h1
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h1]
    · rw [Category.assoc, pullback.lift_snd, basePt, basePt, pullback.lift_snd, pullback.lift_snd]
  · exact ⟨𝟙 _, Category.id_comp _, fun S _ _ y y' ⟨ρ, ν, hi, hm, _⟩ => absurd ⟨ρ, ν, hi, hm⟩ h⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem split_rules (hq : Dw.q = 0) (hL : ActLev (Xo := Xo) c lev) (hF : GlobalTheory.DefPt.FreePt Xo c lev)
    (W : Submodule c.F (Rul Xo c)) (hW : ∀ b, ∀ f ∈ W, fnRule b * f ∈ W) (T : G → W →ₗ[c.F] W)
    (hT : ∀ g f, (T g f : Rul Xo c) = actLev c lev g f) (σ : c.F →+* ℂ) :
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction G X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC σ W)),
      (∀ (h : G) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : G) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin σ (T h) v ∈ A (h • y) := by
  haveI := isAffine_XF (Xo := Xo) (c := c) hq
  letI : Algebra c.F Γ(Xo.XF c, ⊤) := (cst Xo c).toAlgebra
  haveI : Algebra.Etale c.F Γ(Xo.XF c, ⊤) := etale_cst hq
  choose r hr hr' using exists_map hL
  have hact : ∀ g b, actLev c lev g (fnRule b) = fnRule ((r g).appTop.hom b) := fun g b => by
    funext p y
    show fnAt (basePt _) b = fnAt (basePt y) _
    rw [fnAt_appTop, ← hr' g p.R y _ (mvPt_spec hL.total g y)]
  let t : G → Γ(Xo.XF c, ⊤) →ₐ[c.F] Γ(Xo.XF c, ⊤) := fun g =>
    { (r g).appTop.hom with
      commutes' := fun k => by
        show (r g).appTop.hom ((strK (Xo := Xo) (c := c)).appTop.hom (toΓ c.F k)) = strK.appTop.hom (toΓ c.F k)
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hr] }
  have ht : ∀ g b, fnRule (t g b) = actLev c lev g (fnRule b) := fun g b => (hact g b).symm
  let τ : G →* (Γ(Xo.XF c, ⊤) →ₐ[c.F] Γ(Xo.XF c, ⊤)) :=
    { toFun := t
      map_one' := AlgHom.ext fun b => fnRule_injective
        ((ht 1 b).trans (actL_one _ _ _ hL.total hL.func hL.one (fnRule_mem b).1))
      map_mul' := fun g h => AlgHom.ext fun b => fnRule_injective (by
        show fnRule (t (g * h) b) = fnRule (t g (t h b))
        rw [ht, ht, ht]
        exact actL_mul _ _ _ hL.total hL.func hL.mul g h (fnRule_mem b).1) }
  let m : Γ(Xo.XF c, ⊤) →ₐ[c.F] Module.End c.F W :=
    { toFun := fun b => (LinearMap.mulLeft c.F (fnRule b)).restrict (hW b)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show fnRule (1 : Γ(Xo.XF c, ⊤)) * (f : Rul Xo c) = f
        rw [fnRule_one, one_mul])
      map_mul' := fun a b => LinearMap.ext fun f => Subtype.ext (by
        show fnRule (a * b) * (f : Rul Xo c) = fnRule a * (fnRule b * f)
        rw [fnRule_mul, mul_assoc])
      map_zero' := LinearMap.ext fun f => Subtype.ext (by
        show fnRule (0 : Γ(Xo.XF c, ⊤)) * (f : Rul Xo c) = 0
        rw [fnRule_zero, zero_mul])
      map_add' := fun a b => LinearMap.ext fun f => Subtype.ext (by
        show fnRule (a + b) * (f : Rul Xo c) = fnRule a * f + fnRule b * f
        rw [fnRule_add, add_mul])
      commutes' := fun k => LinearMap.ext fun f => Subtype.ext (by
        show fnRule (cst Xo c k) * (f : Rul Xo c) = k • (f : Rul Xo c)
        exact fnRule_cst k _) }
  refine split_complex σ m τ T (fun g b => LinearMap.ext fun f => Subtype.ext ?_) fun g χ hχ₀ hχ => ?_
  · show (T g (m b f) : Rul Xo c) = fnRule (t g b) * T g f
    rw [hT, hT, ht]
    rfl
  · letI : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨x, hx⟩ := exists_pt χ
    have hx0 : x ≫ strK = spMap (algebraMap c.F ℂ) := eq_of_fnAt fun b => by
      obtain ⟨k, rfl⟩ : ∃ k, toΓ c.F k = b :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv).2 b
      rw [← fnAt_cst, hx, fnAt_toΓ]
      exact hχ₀ k
    obtain ⟨y, hy⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (GlobalTheory.FlatLine.prX_over hx0)
    have hb : basePt y = x := pullback.hom_ext (by rw [basePt, pullback.lift_fst, hy])
      (by rw [basePt, pullback.lift_snd]; exact hx0.symm)
    obtain ⟨y', hy'⟩ := hL.total g ℂ y
    have h1 : x ≫ r g = x := eq_of_fnAt fun b => by
      rw [← fnAt_appTop, hx, hx]
      exact hχ b
    have h2 := hr' g ℂ y y' hy'
    rw [hb, h1, ← hb] at h2
    have h3 := congrArg (· ≫ pullback.fst _ _) h2
    simp only [basePt, pullback.lift_fst] at h3
    exact hF g ℂ y y' hy' h3

end Geo

section Main

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem split_lift : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : RowsT p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.actC p i hp.1 (φ h)) v ∈ A (h • y) := by
  intro _ _
  have hw : WtN := GlobalTheory.CovTop.WtShape.wtN
  unfold WtN Lifts at *
  refine Closed.imp hw ?_
  rintro eps Fm CH - ⟨C, hC, x0, ha⟩
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi hp' Hg _ _ φ hF => ?_⟩
  have hW := ha x hx hle ι p hp i
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hi.le⟩
  have hq : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = (Fm.D x ι).R.m - ((i : ℕ) + 1) := by rw [hW.sig.2.1]; rfl
    simpa [dat, hi] using this
  have hU := p.fw.laws.unf _ hj
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  have hL : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : Hg => (p.O i).lev2 (φ g)) :=
    ⟨fun g => h.total (φ g), fun g => h.func (φ g), fun S _ _ y => by
        have := h.one S y
        rw [← map_one φ] at this
        exact this,
      fun g g' S _ _ y y' y'' a b => by
        have := h.mul (φ g) (φ g') S y y' y'' a b
        rw [← map_mul φ] at this
        exact this,
      fun g => h.nat (φ g), fun g => h.bor (φ g)⟩
  refine split_rules hq hL hF (GlobalTheory.DefHalf.CF p i) (fun b f hf => ?_) (fun g => GlobalTheory.DefHalf.actC p i hp'.1 (φ g))
    (fun g f => rfl) _
  refine GlobalTheory.DefPt.ReadsPt.mem_cusp_of_sec hq hU hW.dom ?_
  have := sec_mul _ _ _ _ _ _ (GlobalTheory.LevelCoverCompare.fnRule_mem b) (cusp_le_sec _ _ _ _ _ hf)
  rwa [zero_add, zero_add] at this

end Main

end GlobalTheory.DefSplit
