import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

theorem sigma_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem star'_star' (h : IsCMExt F E σ) (P : PPol σ r) (x : Fld P) : star' P (star' P x) = x := by
  have hE : ∀ e : E, star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e := by
    intro e
    rw [star'_algebraMap, star'_algebraMap, sigma_invol h]
  have hα : star' P (star' P (alpha P)) = alpha P := by
    rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  obtain ⟨p, rfl⟩ : ∃ p, AdjoinRoot.mk P.1 p = x := AdjoinRoot.mk_surjective x
  let g : Fld P →+* Fld P := ((star' P).comp (star' P)).toRingHom
  have hg : g.comp (algebraMap E (Fld P)) = algebraMap E (Fld P) := RingHom.ext hE
  have hgα : g (alpha P) = alpha P := hα
  have key : AdjoinRoot.mk P.1 p = Polynomial.eval₂ (algebraMap E (Fld P)) (alpha P) p := by
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    rfl
  change g (AdjoinRoot.mk P.1 p) = AdjoinRoot.mk P.1 p
  rw [key, Polynomial.hom_eval₂, hg, hgα]

instance finiteFE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance finiteFL (P : PPol σ r) : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)

theorem normBounded (h : IsCMExt F E σ) (P : PPol σ r) : GlobalTheory.RegSS.NormBounded F (Fld P) (star' P) :=
  GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice GlobalTheory.RegSSLattice.tensorLattice F (Fld P) (star' P)
    (GlobalTheory.RegSS.fieldUnitBounded_of_packing GlobalTheory.RegSS.normOnePacking GlobalTheory.RegSSLattice.tensorLattice
      F (Fld P) (star' P) (Field.toIsField _) (star'_star' h P))

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def swapE (P : PPol σ r) : Fld P ⊗[F] AF F ≃ₐ[F] AF F ⊗[F] Fld P := Algebra.TensorProduct.comm F _ _

theorem continuous_swapE (P : PPol σ r) :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)) (topTens (F := F) (E := Fld P) (AF F))
      (swapE P) := by
  letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)
  haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] Fld P) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] Fld P) := ModuleTopology.continuousAdd (AF F) (AF F ⊗[F] Fld P)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] Fld P) := ModuleTopology.continuousSMul (AF F) (AF F ⊗[F] Fld P)
  let f : (Fld P ⊗[F] AF F) →ₗ[AF F] (AF F ⊗[F] Fld P) :=
    { toFun := swapE P
      map_add' := map_add _
      map_smul' := fun c u => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1 }
  exact IsModuleTopology.continuous_of_linearMap f

theorem swapE_sigR (P : PPol σ r) (u : Fld P ⊗[F] AF F) :
    swapE P (Formalism.UG.sigR (star' P) (AF F) u) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (swapE P u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [swapE, Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem swapE_inclE (P : PPol σ r) (β : Fld P) :
    swapE P (Formalism.UG.inclE (F := F) (AF F) β) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) β := by
  simp [swapE, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem scalar_mem_UJ {S : Type} [CommRing S] (s : S →+* S) (w : Sˣ) (hw : s w * w = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) w ∈ Formalism.UG.UJ s (1 : Matrix (Fin 1) (Fin 1) S) := by
  simp only [Formalism.UG.UJ, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk]
  ext i j
  fin_cases i
  fin_cases j
  simp [Formalism.UG.cT, Matrix.GeneralLinearGroup.scalar, hw]

theorem JR_one (P : PPol σ r) : JR (F := F) (AF F) (one₁ P) = 1 := by
  show (1 : Matrix (Fin 1) (Fin 1) (Fld P)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) = 1
  exact Matrix.map_one _ (map_zero _) (map_one _)

def torOf (P : PPol σ r) (w : (AF F ⊗[F] Fld P)ˣ) (hw : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) w * w = 1) :
    Tor P (AF F) :=
  (⟨Matrix.GeneralLinearGroup.scalar (Fin 1) w, by
    change _ ∈ Formalism.UG.UJ _ (JR (AF F) (one₁ P))
    rw [JR_one]
    exact scalar_mem_UJ _ w hw⟩ : HR (AF F) (star' P) (one₁ P))

theorem torUnit_torOf (P : PPol σ r) (w : (AF F ⊗[F] Fld P)ˣ) (hw) : torUnit (torOf P w hw) = w := by
  apply Units.ext
  show Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 1) w).1) = (w : AF F ⊗[F] Fld P)
  rw [Matrix.det_fin_one]
  simp [Matrix.GeneralLinearGroup.scalar]

theorem torUnit_injective (P : PPol σ r) : Function.Injective (torUnit (P := P) (k := AF F)) := by
  intro a b hab
  have hv : Matrix.det (Subtype.val a).1 = Matrix.det (Subtype.val b).1 := congrArg Units.val hab
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at hv
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  exact hv

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

theorem sigR_inclR (P : PPol σ r) (x : Fld P) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (star' P x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

def ratOf (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) : Tor P (AF F) :=
  torOf P (Units.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) : Fld P →+* _).toMonoidHom
    (Units.mkOfMulEqOne β (star' P β) hβ)) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β) *
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β = 1
      rw [sigR_inclR, ← map_mul, mul_comm, hβ, map_one])

theorem ratOf_mem (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) :
    ratOf P β hβ ∈ ratPts (star' P) (one₁ P) := by
  have hu : Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mkOfMulEqOne β (star' P β) hβ) ∈
      Formalism.UG.UJ (star' P : Fld P →+* Fld P) (one₁ P) :=
    scalar_mem_UJ _ _ (by simpa [mul_comm] using hβ)
  change Subtype.val (ratOf P β hβ) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (AF F) (star' P) (one₁ P)
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map]
  refine ⟨_, hu, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [ratOf, torOf, Formalism.UG.bc, Matrix.GeneralLinearGroup.scalar, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem torUnit_ratOf (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) :
    (torUnit (ratOf P β hβ)).1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β := by
  simp [ratOf, torUnit_torOf]

theorem exists_compact (h : IsCMExt F E σ) (P : PPol σ r) :
    ∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C := by
  obtain ⟨D, hD, hDu⟩ := normBounded h P
  letI tL : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)
  obtain ⟨hTR, -, hT2, -, -, -, -⟩ := GlobalTheory.RegSSLattice.tensorLattice F (Fld P)
  haveI := hTR
  haveI := hT2
  letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩
  haveI : ContinuousAdd (Fld P ⊗[F] AF F) := ModuleTopology.continuousAdd (AF F) (Fld P ⊗[F] AF F)
  haveI : ContinuousSMul (AF F) (Fld P ⊗[F] AF F) := ModuleTopology.continuousSMul (AF F) (Fld P ⊗[F] AF F)
  have hsig : Continuous (Formalism.UG.sigR (star' P) (AF F)) := by
    let f : (Fld P ⊗[F] AF F) →ₗ[AF F] (Fld P ⊗[F] AF F) :=
      { toFun := Formalism.UG.sigR (star' P) (AF F)
        map_add' := map_add _
        map_smul' := fun c u => by
          rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          show Formalism.UG.sigR (star' P) (AF F) ((1 : Fld P) ⊗ₜ[F] c) = (1 : Fld P) ⊗ₜ[F] c
          simp [Formalism.UG.sigR] }
    exact IsModuleTopology.continuous_of_linearMap f
  have hsw := continuous_swapE P
  let N : Set (Fld P ⊗[F] AF F) := {u | u * Formalism.UG.sigR (star' P) (AF F) u = 1}
  have hN : IsClosed N := isClosed_eq (continuous_id.mul hsig) continuous_const
  have hK : IsCompact (D ∩ N) := hD.inter_right hN
  have hmul : ∀ x : N, swapE P x.1 * swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) = 1 := fun x => by
    rw [← map_mul, x.2, map_one]
  have hmul' : ∀ x : N, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) * swapE P x.1 = 1 := fun x => by
    rw [mul_comm, hmul]
  let uN : N → (AF F ⊗[F] Fld P)ˣ := fun x =>
    ⟨swapE P x.1, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1), hmul x, hmul' x⟩
  have hwN : ∀ x : N, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (uN x) * uN x = 1 := fun x => by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (swapE P x.1) * swapE P x.1 = 1
    rw [← swapE_sigR]
    exact hmul' x
  let Ψ : N → Tor P (AF F) := fun x => torOf P (uN x) (hwN x)
  have hΨ : Continuous Ψ := by
    have hsc : Continuous fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have he : (Units.val ∘ fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x)) =
            fun x => Matrix.diagonal fun _ => swapE P x.1 := by
          funext x
          ext i j
          fin_cases i
          fin_cases j
          simp [uN, Matrix.GeneralLinearGroup.scalar]
        rw [he]
        exact (continuous_pi fun _ => hsw.comp continuous_subtype_val).matrix_diagonal
      · have he : (fun x : N => (((Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x))⁻¹ : GL (Fin 1) _) :
              Matrix (Fin 1) (Fin 1) _)) =
            fun x => Matrix.diagonal fun _ => swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) := by
          funext x
          ext i j
          fin_cases i
          fin_cases j
          simp [uN, Matrix.GeneralLinearGroup.scalar]
        rw [he]
        exact (continuous_pi fun _ => hsw.comp (hsig.comp continuous_subtype_val)).matrix_diagonal
    exact hsc.subtype_mk _
  let Ks : Set N := Subtype.val ⁻¹' (D ∩ N)
  have hKs : IsCompact Ks := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_comm, Set.inter_assoc, Set.inter_self]
    exact hK
  refine ⟨Ψ '' Ks, hKs.image hΨ, fun t => ?_⟩
  have hwn := torUnit_norm t
  let u := (swapE P).symm (torUnit t).1
  have hsu : swapE P u = (torUnit t).1 := (swapE P).apply_symm_apply _
  have hu : u * Formalism.UG.sigR (star' P) (AF F) u = 1 := by
    apply (swapE P).injective
    rw [map_mul, swapE_sigR, hsu, map_one]
    exact hwn
  obtain ⟨β, hβ, hβD⟩ := hDu u hu
  have hiβ : Formalism.UG.sigR (star' P) (AF F) (Formalism.UG.inclE (F := F) (AF F) β) =
      Formalism.UG.inclE (F := F) (AF F) (star' P β) := by
    apply (swapE P).injective
    rw [swapE_sigR, swapE_inclE, swapE_inclE, sigR_inclR]
  have hmem : u * Formalism.UG.inclE (F := F) (AF F) β ∈ N := by
    show _ * _ = _
    rw [map_mul, hiβ, mul_mul_mul_comm, hu, one_mul, ← map_mul, hβ, map_one]
  refine ⟨ratOf P β hβ, ratOf_mem P β hβ, ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩, ⟨hβD, hmem⟩, ?_⟩
  apply torUnit_injective P
  rw [show Ψ ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩ = torOf P (uN ⟨_, hmem⟩) (hwN ⟨_, hmem⟩) from rfl,
    torUnit_torOf, map_mul]
  apply Units.ext
  rw [Units.val_mul]
  show swapE P (u * Formalism.UG.inclE (F := F) (AF F) β) = _
  rw [map_mul, swapE_inclE, hsu, torUnit_ratOf, mul_comm]

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

theorem torus_compact_finiteVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C) ∧ ∀ dt : Measure (Tor P (AF F)), dt.IsHaarMeasure → torVol P dt ≠ ⊤ := by
  intro F E _ _ _ _ _ σ h r P
  refine ⟨exists_compact h P, fun dt hdt => ?_⟩
  obtain ⟨C, hC, hCt⟩ := exists_compact h P
  have hs := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
  haveI : Countable (ratPts (star' P) (one₁ P)) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  rw [torVol, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hs]
  refine ne_top_of_le_ne_top (hC.measure_lt_top (μ := dt)).ne ?_
  calc dt (GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P)))
      ≤ dt (⋃ g : ratPts (star' P) (one₁ P),
          (fun y => g • y) '' C ∩ GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P))) := by
        apply measure_mono
        intro x hx
        obtain ⟨γ, hγ, hγx⟩ := hCt x
        refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ⟨γ * x, hγx, ?_⟩, hx⟩
        all_goals simp [Subgroup.smul_def]
    _ ≤ ∑' g : ratPts (star' P) (one₁ P),
          dt ((fun y => g • y) '' C ∩ GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P))) :=
        measure_iUnion_le _
    _ = dt C := (hs.measure_eq_tsum C).symm

end GlobalTheory.TorCompact
