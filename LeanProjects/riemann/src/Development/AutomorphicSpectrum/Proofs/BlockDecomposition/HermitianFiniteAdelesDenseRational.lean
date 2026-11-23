import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem sig_sig_of_isCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (h : F) (t : R ⊗[F] E) :
    sigR R σ (h • t) = h • sigR R σ t :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id F R) σ) h t

theorem inclR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (h : F) (e : E) : inclR (F := F) R (h • e) = h • inclR (F := F) R e :=
  map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) h e

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem denseRange_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] (hd : DenseRange (algebraMap F R)) :
    DenseRange (inclR R : E →+* R ⊗[F] E) := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have hφ := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ b
  let φ := hφ.homeomorph
  have hpi : DenseRange (Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    DenseRange.piMap fun _ => hd
  have hc : DenseRange (φ.symm ∘ Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    φ.symm.surjective.denseRange.comp hpi φ.symm.continuous
  refine hc.mono ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨b.equivFun.symm a, ?_⟩
  apply φ.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (b.equivFun.symm a)) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, apply_ite]

theorem hermE_dense_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  intro F E _ _ _ _ _ σ hCM n U hU g
  obtain ⟨hlc, hsc, ht2, -, -, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hTR, -, -, -, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  have hincl := denseRange_inclR F E σ hCM (Af F) hden
  have hσ := sig_sig_of_isCM σ hCM

  have hmat : DenseRange (fun c : Matrix (Fin n) (Fin n) E => c.map (inclR (Af F))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hincl))

  let h : F := 1 / 2
  let Pm : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun m a b => h • (m a b + sigR (Af F) σ (m b a))
  have hPm : ∀ m, Pm m ∈ HermR (Af F) σ n := by
    intro m a b
    show sigR (Af F) σ (h • (m b a + sigR (Af F) σ (m a b))) = h • (m a b + sigR (Af F) σ (m b a))
    rw [sigR_smul, map_add, sigR_sigR _ _ hσ, add_comm]
  have hsmul : Continuous fun x : Af F ⊗[F] E => h • x := by
    simp_rw [Algebra.smul_def]
    exact continuous_const.mul continuous_id
  have hPc : Continuous Pm := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact hsmul.comp ((continuous_id.matrix_elem a b).add
      (hsig.comp (continuous_id.matrix_elem b a)))
  let P : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → HermR (Af F) σ n := fun m => ⟨Pm m, hPm m⟩
  have hP : Continuous P := hPc.subtype_mk hPm
  have hW : IsOpen {m | g - P m ∈ U} :=
    hU.preimage (continuous_const.sub hP)
  have hg : P g.1 = g := by
    apply Subtype.ext
    ext a b
    show h • (g.1 a b + sigR (Af F) σ (g.1 b a)) = g.1 a b
    rw [g.2 a b, ← two_smul F, smul_smul]
    norm_num [h]
  have hne : ({m | g - P m ∈ U} : Set _).Nonempty := ⟨g.1, by simp [hg, U.zero_mem]⟩
  obtain ⟨c₀, hc₀⟩ := hmat.exists_mem_open hW hne
  let c : Matrix (Fin n) (Fin n) E := fun a b => h • (c₀ a b + σ (c₀ b a))
  have hc : c ∈ hermE σ n := by
    intro a b
    show σ (h • (c₀ b a + σ (c₀ a b))) = h • (c₀ a b + σ (c₀ b a))
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, map_add, hσ, add_comm]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hcP : hermIn (Af F) σ n ⟨c, hc⟩ = P (c₀.map (inclR (Af F))) := by
    apply Subtype.ext
    ext a b
    show inclR (Af F) (h • (c₀ a b + σ (c₀ b a))) =
      h • (inclR (Af F) (c₀ a b) + sigR (Af F) σ (inclR (Af F) (c₀ b a)))
    rw [inclR_smul, map_add, sigR_inclR]
  rw [hcP]
  exact hc₀

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
