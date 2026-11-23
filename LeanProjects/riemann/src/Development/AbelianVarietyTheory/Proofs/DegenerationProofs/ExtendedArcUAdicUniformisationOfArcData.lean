import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataDescendsFromCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedFibreSplitOfArcDataFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitOverOfHasArcData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem polAt_of_point {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem admissible_maximal_ideal_of_complete_dvr_char_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) :
    admitted V (IsLocalRing.maximalIdeal V) ∧ IsPrincipalIdealRing (V ⧸ IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  exact ⟨⟨⟨inferInstance, inferInstance, inferInstance, h₂⟩, h₂, h₃, inferInstance, inferInstance⟩, inferInstance⟩

theorem cdvr_powerSeries (K : Type) [Field K] [CharZero K] : CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

theorem powerSeries_dvr_admissible_X_ideal (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal O) O) :
    admitted (PowerSeries O) (Ideal.span {PowerSeries.X}) ∧
      IsPrincipalIdealRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) := by
  have hk : Ideal.span {(PowerSeries.X : PowerSeries O)} = RingHom.ker (PowerSeries.constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) ≃+* O :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
  refine ⟨⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := O)), hk ▸ RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv e.symm⟩, IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective⟩
  infer_instance

theorem hasArcData_trait (h₁ : Laws) (h₂ : Laws2) (h₃ : Laws3) (h₄ : Laws4) (h₅ : Laws5) (h₆ : Laws6) (hE : Ega)
    (hU : USt) (hP : PelSt) (hH : HomExtSt) {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    {b : c.V W₀ →+* O'} (a : ArcIn D l (c.V W₀).subtype O' b) (hp : PushInvertible Y.t.G Y.t.PP.L)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X) (hχ : jK _ ≫ χ = y ≫ Y.j)
    (hT : TraitData Y a (RingHom.id _) y) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (φ : PowerSeries O' →+* V) (hφ : Function.Injective φ) (hX : ¬ IsUnit (φ PowerSeries.X))
    (hC : ∀ x, x ≠ 0 → IsUnit (φ (PowerSeries.C x))) :
    Y.HasArcData a (IsLocalRing.maximalIdeal V) (φ.comp (PowerSeries.C (R := O'))) (φ PowerSeries.X) (spMap φ ≫ χ) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp φ) := (IsFractionRing.injective V _).comp hφ
  let gam : FractionRing (PowerSeries O') →+* FractionRing V := IsFractionRing.lift hinj
  have hg : ∀ r, gam (algebraMap _ _ r) = algebraMap V _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ y ≫ Y.j = jK V ≫ spMap φ ≫ χ := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hg r
  obtain ⟨W, _, _, _, io, hW, hio, hfin, hA⟩ := (hT.2 V hV φ gam hg _ hsq).2 hX
  have hA' : Y.HasArcData a (IsLocalRing.maximalIdeal W) (io.comp (φ.comp (PowerSeries.C (R := O'))))
    (io (φ PowerSeries.X)) (spMap io ≫ spMap φ ≫ χ) := hA
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap φ ≫ χ) Y.t
  have hsq' : (spMap gam ≫ y) ≫ Y.j = jK V ≫ spMap φ ≫ χ := (Category.assoc _ _ _).trans hsq
  have hS := GlobalTheory.T.closedFibre_split_of_arcData_finite_extension h₁ h₂ h₃ h₄ h₅ h₆ E H D l Xo c W₀ Y O' b a V hV _ _ hC hX _ _ hsq' t m W hW io hio hfin hA'
  obtain ⟨hadm, hpid⟩ := admissible_maximal_ideal_of_complete_dvr_char_zero hV
  obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H V _ hadm hpid t (polAt_of_point Y m _ _ hsq') hS
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp V _ t m)
  have := hV.2.2
  have hloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  exact GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a V _ _ _ hadm.1
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (hφ.comp PowerSeries.C_injective) _ _ hsq' t m P hPt W hW io hio
    (IsLocalRing.map_maximalIdeal_le io) (fun h => hX (isUnit_of_map_unit io _ h)) (fun x hx => (hC x hx).map io) hA'

theorem hasArcData_of_traitData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb hp y χ hχ hT
  rcases hb with ⟨hf, -⟩ | ⟨hd, hϖ, hc⟩
  · letI := hf.toField
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT (cdvr_powerSeries O') (RingHom.id _)
      Function.injective_id PowerSeries.X_prime.not_unit (fun x hx => (IsUnit.mk0 x hx).map (PowerSeries.C (R := O')))
    have e : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp, PowerSeries.maximalIdeal_eq_span_X] at h
    exact h
  · have hi := IsFractionRing.injective O' (FractionRing O')
    have hX : ¬ IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) PowerSeries.X) := by
      rw [PowerSeries.map_X]
      exact PowerSeries.X_prime.not_unit
    have hC : ∀ x, x ≠ 0 → IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) (PowerSeries.C x)) := fun x hx => by
      rw [PowerSeries.map_C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 hx)).map _
    have hV := cdvr_powerSeries (FractionRing O')
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT hV _
      (PowerSeries.map_injective _ hi) hX hC
    obtain ⟨t, ⟨m⟩⟩ := exists_sab χ Y.t
    have hS := GlobalTheory.splitOver_of_hasArcData h₁ h₂ h₃ hH E H D l Xo c W₀ Y O' b a hd χ t m (by
      have e : (PowerSeries.map (algebraMap O' (FractionRing O'))).comp (PowerSeries.C (R := O')) =
          (PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _) := RingHom.ext fun x => PowerSeries.map_C (algebraMap O' (FractionRing O')) x
      rw [e, PowerSeries.map_X] at h
      exact h)
    obtain ⟨hadm, hpid⟩ := powerSeries_dvr_admissible_X_ideal O' (hϖ.maximalIdeal_eq ▸ hc)
    obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H _ _ hadm hpid t (polAt_of_point Y m _ _ hχ.symm) hS
      (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp _ _ t m)
    have := hadm.2.2.1
    refine GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a _ _ _ _ hadm.1 hadm.2.2.2.1.ne_top
      PowerSeries.C_injective _ _ hχ.symm t m P hPt _ hV _ (PowerSeries.map_injective _ hi) ?_ hX hC h
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hX

end GlobalTheory.ArcData
