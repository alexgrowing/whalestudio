import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantPartial

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.IkSchwartz

open GlobalTheory.SchwartzBruhatTensor GlobalTheory.PartialIntegral

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

theorem exists_split {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (m n : ℕ) :
    ∃ e : Mx D m n ≃ₜ+ (D.what₂.Tau → Fin m → Fin n → ℂ) × (Fin m → Fin n → AEf D),
      ∀ x, e x = (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j)) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  refine ⟨{ toFun := fun x => (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j))
            invFun := fun p => s.mapMatrix (Matrix.of p.2) + chartM σ m n p.1
            left_inv := fun x => (decomp hσ hsf hsi x).symm
            right_inv := fun p => Prod.ext ?_ ?_
            map_add' := fun x y => Prod.ext ?_ ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · funext τ i j
    show θ τ (infPart D (s (p.2 i j) + σ fun τ => p.1 τ i j)) = p.1 τ i j
    rw [RingHom.map_add, RingHom.map_add, hsi, hσ.comp, RingHom.map_zero, zero_add]
  · funext i j
    show finPart D (s (p.2 i j) + σ fun τ => p.1 τ i j) = p.2 i j
    rw [RingHom.map_add, hsf, hσ.fin, add_zero]
  · funext τ i j
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add]
  · funext i j
    exact (finPart D).map_add _ _
  · exact (continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j)).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))
  · haveI := (lattice_Mx D m n).1
    refine Continuous.add ?_ ((continuous_chartM hσ.cont m n).comp continuous_fst)
    exact continuous_pi fun i => continuous_pi fun j =>
      hsc.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

def lmul {R : Type} [CommRing R] {m t : ℕ} (n : ℕ) (J : Matrix (Fin m) (Fin t) R) (x : Fin t → Fin n → R) :
    Fin m → Fin n → R := J ⬝ Matrix.of x

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m t : ℕ} (n : ℕ)
    (J : Matrix (Fin m) (Fin t) R) : Continuous (lmul n J) :=
  Continuous.matrix_mul (A := fun _ => J) (B := fun x : Matrix (Fin t) (Fin n) R => x) continuous_const continuous_id

def lmulC {ι : Type} {m t : ℕ} (n : ℕ) (J : ι → Matrix (Fin m) (Fin t) ℂ) :
    (ι → Fin t → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) where
  toFun c τ := lmul n (J τ) (c τ)
  map_add' c c' := funext fun τ => Matrix.mul_add (J τ) (Matrix.of (c τ)) (Matrix.of (c' τ))
  map_smul' r c := funext fun τ => Matrix.mul_smul (J τ) r (Matrix.of (c τ))

variable {D : D7} {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {R : Type} [CommRing R] (φ : AE D →+* R) {n : ℕ}

theorem map_emb (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => φ ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map φ) (fun i j => φ (x i j)) + lmul n (d.j0.map φ) (fun i j => φ (a i j)) := by
  show (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n).map φ = d.jX.map φ ⬝ x.map φ + d.j0.map φ ⬝ a.map φ
  rw [Matrix.map_add _ φ.map_add, Matrix.map_mul, Matrix.map_mul]

theorem pX_emb (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.pX.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = x := by
  show d.pX.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of x
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.pX_jX, d.pX_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem wittHyperbolic_projAnisotropic_leftMul_embedding (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.p0.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = a := by
  show d.p0.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of a
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.p0_jX, d.p0_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem map_emb_fin (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => finPart D ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map (finPart D)) (fun i j => finPart D (x i j)) +
        lmul n (d.j0.map (finPart D)) (fun i j => finPart D (a i j)) := map_emb d (finPart D) x a

set_option maxHeartbeats 800000 in

theorem pure {θ : InfFam D} (hθ : IsInfFam θ) (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure]
    (f : SchwartzMap (D.what₂.Tau → Fin T.rank → Fin n → ℂ) ℂ) (g : (Fin T.rank → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin T.rank → Fin n → AEf D)) (Φ : Mx D T.rank n → ℂ)
    (hΦ : Φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) :
    (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin t → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin t → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := (lattice_Mx D t n).1
  obtain ⟨e, he⟩ := exists_split hθ t n
  let μr : Measure (D.what₂.Tau → Fin t → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin t → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  let φ : D.what₂.Tau → AE D →+* ℂ := fun τ => (θ τ).comp (infPart D)
  obtain ⟨hf1, h, hh⟩ := schwartz_partial μr f (lmulC n fun τ => d.jX.map (φ τ)) (lmulC n fun τ => d.j0.map (φ τ))
    (fun x a hxa => by
      refine ⟨funext fun τ => ?_, funext fun τ => ?_⟩
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← pX_emb d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← wittHyperbolic_projAnisotropic_leftMul_embedding d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _)
  obtain ⟨hg1, hg2, hg3⟩ := locallyConstant_partial ν hg.1 hg.2 (continuous_lmul n (d.jX.map (finPart D)))
    (continuous_lmul n (d.j0.map (finPart D))) (continuous_lmul n (d.pX.map (finPart D)))
    (continuous_lmul n (d.p0.map (finPart D))) (pX_emb d (finPart D)) (wittHyperbolic_projAnisotropic_leftMul_embedding d (finPart D))
  have key : ∀ a : Mx D T'.rank n, (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) = fun x =>
      f (lmulC n (fun τ => d.jX.map (φ τ)) (e x).1 + lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j) *
      g (lmul n (d.jX.map (finPart D)) (e x).2 + lmul n (d.j0.map (finPart D)) fun i j => finPart D (a i j)) := by
    intro a
    funext x
    have h2 : (fun τ i j => compAt θ τ (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j) =
        lmulC n (fun τ => d.jX.map (φ τ)) (fun τ i j => compAt θ τ x i j) +
          lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j := funext fun τ => map_emb d (φ τ) x a
    rw [hΦ, he]
    exact congrArg₂ (· * ·) (congrArg f h2) (congrArg g (map_emb_fin d x a))
  refine ⟨fun a => by rw [key a]; exact (hc _ _ (hf1 _) (hg1 _)).1, ?_⟩
  have e2 : ikS d μ Φ = c • fun a : Mx D T'.rank n => h (fun τ i j => compAt θ τ a i j) *
      (fun b => ∫ y, g (lmul n (d.jX.map (finPart D)) y + lmul n (d.j0.map (finPart D)) b) ∂ν)
        (fun i j => finPart D (a i j)) := by
    funext a
    refine (congrArg (fun F => ∫ x, F x ∂μ) (key a)).trans ?_
    refine (hc _ _ (hf1 _) (hg1 _)).2.trans ?_
    rw [← hh]
    rfl
  rw [e2]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨h, _, ⟨hg2, hg3⟩, rfl⟩)

theorem ikS_mem_schwartzA : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  intro D θ hθ T T' t n d μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  suffices h : (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n from h.2
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact pure d hθ μ f g hg Φ h
  | zero =>
    refine ⟨fun a => integrable_zero _ _ _, ?_⟩
    have : ikS d μ (0 : Mx D T.rank n → ℂ) = 0 := funext fun a => integral_zero _ _
    rw [this]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun a => (h1.1 a).add (h2.1 a), ?_⟩
    have : ikS d μ (Φ + Ψ) = ikS d μ Φ + ikS d μ Ψ := funext fun a => integral_add (h1.1 a) (h2.1 a)
    rw [this]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h =>
    refine ⟨fun a => (h.1 a).smul c, ?_⟩
    have : ikS d μ (c • Φ) = c • ikS d μ Φ := funext fun a => integral_smul c _
    rw [this]
    exact Submodule.smul_mem _ c h.2

end GlobalTheory.RegSch.IkSchwartz

end
