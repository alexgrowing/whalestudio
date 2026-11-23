import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.RealPlaceCentraliser

section Gen
open scoped Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [Field k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem nondeg (hJ : IsHermND σ J) (b : Fin n → k ⊗[F] E)
    (hb : ∀ a, Formalism.UG.hform (sigR k σ) (JR k J) a b = 0) : b = 0 := by
  have hv : JR (F := F) k J *ᵥ b = 0 := by
    funext i
    have := hb (Pi.single i 1)
    simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have hdet : IsUnit (JR (F := F) k J).det := by
    have : (JR (F := F) k J).det = inclR (F := F) k J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hJ.2).map _
  calc b = ((JR (F := F) k J)⁻¹ * JR (F := F) k J) *ᵥ b := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem zero_of_hx (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) (z : k ⊗[F] Fld P)
    (hz : ∀ y', hx P k x z y' = 0) : z = 0 := by
  have : φ z = 0 := nondeg hJ _ fun a => by
    obtain ⟨y', rfl⟩ := φ.surjective a
    rw [h]; exact hz y'
  simpa using this

theorem isUnit_of_isIsom [Module.Finite F (Fld P)] (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) : IsUnit x := by
  haveI : Module.Finite k (k ⊗[F] Fld P) := Module.Finite.base_change F k (Fld P)
  have hinj : Function.Injective (LinearMap.mulLeft k x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    refine zero_of_hx hJ h y fun y' => ?_
    simp only [LinearMap.mulLeft_apply] at hy
    simp [hx, hy]
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] E) : sigR k σ (sigR k σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem hform_herm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (a b : Fin n → k ⊗[F] E) :
    sigR k σ (Formalism.UG.hform (sigR k σ) (JR k J) a b) = Formalism.UG.hform (sigR k σ) (JR k J) b a := by
  have hG : ∀ i j, sigR k σ (JR (F := F) k J i j) = JR (F := F) k J j i := by
    intro i j
    simp only [JR, Matrix.map_apply, inclR]
    change sigR k σ (1 ⊗ₜ J i j) = 1 ⊗ₜ J j i
    simp [sigR, hJ.1]
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, sigR_sigR hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofBijective σ (Function.Involutive.bijective hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofBijective (star' P) (Algebra.IsAlgebraic.algHom_bijective _)
  have he : (algebraMap E (Fld P)).comp (e₁ : E →+* E) = (e₂ : Fld P →+* Fld P).comp (algebraMap E (Fld P)) :=
    RingHom.ext fun e => (star'_algebraMap P e).symm
  have := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  have h2 := congrArg e₁ this
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.symm

theorem trBase_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] Fld P) :
    trBase P k (sigR k (star' P) z) = sigR k σ (trBase P k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => simp [trBase, sigR, trace_star hσ]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]

theorem plusUnits_gen [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ∃ u : plusUnits P k, u.1.1 = x := by
  have hu := isUnit_of_isIsom hJ h
  have hsym : ∀ y, trBase P k ((x - sigR k (star' P) x) * sigR k (star' P) y) = 0 := by
    intro y
    have h1 := h 1 y
    have h2 := h y 1
    have h3 := hform_herm hσ hJ (φ 1) (φ y)
    rw [h2, h1] at h3
    simp only [hx, map_one, mul_one] at h3
    rw [← trBase_star hσ, map_mul] at h3
    rw [sub_mul, map_sub, ← h3, sub_self]
  have hd : x - sigR k (star' P) x = 0 := by
    obtain ⟨v, hv⟩ := hu
    have h0 := zero_of_hx hJ h (↑v⁻¹ * (x - sigR k (star' P) x)) fun y' => by
      simp only [hx]
      rw [show x * (↑v⁻¹ * (x - sigR k (star' P) x)) * sigR k (star' P) y' =
          (x - sigR k (star' P) x) * sigR k (star' P) y' by
        rw [← mul_assoc, ← hv, Units.mul_inv, one_mul]]
      exact hsym y'
    have := congrArg (fun w => (v : k ⊗[F] Fld P) * w) h0
    simpa [← mul_assoc] using this
  refine ⟨⟨hu.unit, ?_⟩, rfl⟩
  show Units.map (sigR k (star' P)).toMonoidHom hu.unit = MonoidHom.id _ hu.unit
  ext
  simpa using (sub_eq_zero.mp hd).symm

end Gen

theorem plusUnits_of_isIsom {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) :
    ∃ u : plusUnits P (placeOf D ρ).Completion, u.1.1 = x := by
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  exact plusUnits_gen (fun e => star_star e) (GlobalTheory.DefiniteQuotient.gram_hermND V) h

theorem topGrp {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borel {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

theorem torComm {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (s t : HA R σ J) : s * t = t * s := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  change (s.1.1 * t.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0 = (t.1.1 * s.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0
  simp [Matrix.mul_apply, mul_comm]

theorem measFacts {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : G, a * b = b * a) (e : G ≃ₜ* H) (dt : Measure G) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant ∧ (dt.map e).real univ = dt.real univ ∧
      (CompactSpace H ↔ CompactSpace G) := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have := congrArg e (hc (e.symm a) (e.symm b))
    simpa [map_mul] using this
  haveI hH : (dt.map e).IsHaarMeasure := e.isHaarMeasure_map dt
  refine ⟨hH, ⟨fun g => ?_⟩, ?_, ?_⟩
  · have : (fun a : H => a * g) = (fun a => g * a) := funext fun a => hcomm a g
    rw [this]
    exact map_mul_left_eq_self _ g
  · rw [Measure.real, Measure.real, Measure.map_apply (show Measurable (e : G → H) from e.continuous.measurable) MeasurableSet.univ, Set.preimage_univ]
  · exact ⟨fun hc => e.toHomeomorph.symm.compactSpace, fun hc => e.toHomeomorph.compactSpace⟩

theorem centMeas_real_place : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  intro D V P ρ dt _ x φ h
  obtain ⟨u, rfl⟩ := plusUnits_of_isIsom V P ρ h
  have H := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure D.host.F D.host.E D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.rank P V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) (placeOf D ρ).Completion u φ h
  obtain ⟨e, H2⟩ := H
  have hm := H2.2
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  haveI := topGrp (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := topGrp (placeOf D ρ).Completion (star' P) (one₁ P)
  haveI := borel (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := borel (placeOf D ρ).Completion (star' P) (one₁ P)

  simp only [hm dt]
  have hc := torComm (placeOf D ρ).Completion (star' P) (one₁ P)
  have hf := measFacts (G := Tor P (placeOf D ρ).Completion) (H := cent (gam h)) hc e dt
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  rw [isCompact_iff_compactSpace]
  exact hf.2.2.2

end GlobalTheory.RealPlaceCentraliser
