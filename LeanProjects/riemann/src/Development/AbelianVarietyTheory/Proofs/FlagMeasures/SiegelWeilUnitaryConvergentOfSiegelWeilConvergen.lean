import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SiegelWeilGramDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Topology
open HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.SiegelWeilConvCompare

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

theorem exists_coord_tup (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (n M : ℕ) :
    ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  exact exists_coord_pi e1 h1 (Fin n)

section Zero

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [Subsingleton V]

end Zero

theorem measure_fundamentalDomain_pos (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ) (hμ : IsHaarH F E σ M J μ)
    (𝓕) (h : IsFDH F E σ M J μ 𝓕) : 0 < μ 𝓕 := by
  haveI : μ.IsHaarMeasure := hμ
  haveI : Countable E := (Module.Free.chooseBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  haveI : Countable (HFin (AF F) σ J) := by
    have : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin; rw [Subgroup.coe_map]; exact (Set.to_countable _).image _
    exact this
  haveI : Countable (HFinIn (AF F) σ J) := by
    have : Function.Injective (fun x : HFinIn (AF F) σ J => (⟨x.1.1, x.2⟩ : HFin (AF F) σ J)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : HFin (AF F) σ J => z.1) hxy))
    exact this.countable
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
    ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
  exact pos_iff_ne_zero.2 (IsFundamentalDomain.measure_ne_zero (NeZero.ne μ) h)

section HermTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensHomeo {κ : Type} [Finite κ] (b : Module.Basis κ F E) : R ⊗[F] E ≃ₜ (κ → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

end HermTop

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelWeilGramDensity in

def SiegelFormulaCc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ), 1 ≤ n → 2 * n < M →
    ∀ (T : Matrix (Fin n) (Fin n) E) (hT : IsHermND σ T),
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (b : Module.Basis (Fin 2) F E)
      (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsProdInfFin Φ Φinf Φf → IsSmoothCc F E Φinf → IsPureFin b Φf Φv →
      AllSome (fun μ : Measure (HA (AF F) σ J) => IsHaarH F E σ M J μ) fun μ =>
      AllSome (fun 𝓕 : Set (HA (AF F) σ J) => IsFDH F E σ M J μ 𝓕) fun 𝓕 =>
      AllSome (fun dX : Measure (Fin n → Fin M → Ainf F ⊗[F] E) =>
          SdW F E σ M J (Ainf F) (psiInf F ψ) n dX) fun dXinf =>
      AllSome (fun dS : Measure (HermR (Ainf F) σ n) =>
          SdHerm F E σ (Ainf F) (psiInf F ψ) n dS) fun dSinf =>
      AllSome (fun dX : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
          ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (dX v)) fun dXv =>
      AllSome (fun dS : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
          ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (dS v)) fun dSv =>
      AllSome (fun g : HermR (Ainf F) σ n → ℂ =>
          IsGramDensity (Ainf F) σ J dXinf dSinf Φinf g) fun ginf =>
      AllSome (fun g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ =>
          ∀ v, IsGramDensity (Fv F v) σ J (dXv v) (dSv v) (Φv v) (g v)) fun gv =>
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT.1)) ∧
        meanC μ 𝓕 (thetaS F E σ M J Φ (gramFibre σ J T)) =
          ginf (hermOf (Ainf F) σ T hT.1) * ∏' v, gv v (hermOf (Fv F v) σ T hT.1)

end GlobalTheory.SiegelWeilConvCompare
