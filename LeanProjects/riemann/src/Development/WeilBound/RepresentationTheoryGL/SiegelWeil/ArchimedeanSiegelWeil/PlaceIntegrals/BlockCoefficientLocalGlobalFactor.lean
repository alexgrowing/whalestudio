import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasureStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.AdelicSiegelWeilCoefficientEqStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WhitFree

theorem pure_identity {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_almost_all_standard F E M n d b I 1 _ _ hI
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adelic_siegelWeil_coefficient_eq F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn hM d b laminf hinf minf hminf (hermOf (Ainf F) σ T hT) φ hφ
  have hfin := fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn hM d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2
  have hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) :=
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb _ hΦSB
  have hlimC := GlobalTheory.T.siegel_weil_stabilizer_integrable F E σ hCM M J hJ n hn hM ψ hψ dx db d b _ hstar T
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hI.2.1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  obtain ⟨Sb, hSb⟩ : ∃ S, S₀ ∪ S₁ ∪ S₂ ⊆ S := ⟨_, subset_rfl⟩
  have hEu : ∀ S, S₀ ∪ S₁ ∪ S₂ ⊆ S → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = ((1 : NNReal) : ℂ) * (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
      (∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ)) *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) := by
    intro S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    exact hS₁ S hs1 φ hφm hφi A (fun v => (hfin v).1) (fun v => (hfin v).2.1)
      (fun v hv => hAl v fun h => hv (hs0 h))
  refine ⟨(hEu Sb hSb).1, ?_⟩
  have hlim2 : Filter.Tendsto (fun S => coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    rw [hS₂ S hs2 φ hφ A hA (fun v hv => hAl v fun h => hv (hs0 h)), (hEu S hS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

theorem coefN_eq_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂I := by
  obtain ⟨k, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_factorizable_decomposition F E σ hCM M J hJ n hn hM d b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hP := fun i => pure_identity σ hCM J hJ hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT I hI S
    (φ i) (hφ i) (A i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, pureN (φ i) (A i) X := funext hsum
  rw [hΦe, GlobalTheory.T.siegel_weil_orbital_integral_formula F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb T k _ hSB, integral_finset_sum _ fun i _ => (hP i).1]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end GlobalTheory.CompanionTheory.WhitFree

namespace GlobalTheory.CompanionTheory.WhitFree

theorem whit_eq_integral : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  intro D r V ψ θ μ lam ν φ hyp t β hβ d b laminf lamv minf m hinf hlamv hminf hm I hI _
  obtain ⟨hr, hψ, hθ, hμ, hlam, -, hφ, -⟩ := hyp
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  obtain ⟨ht, -⟩ := hβ
  rw [hW φ β]
  exact coefN_eq_integral D.sp.cm.sig hCM V.gram hJ (by omega) hr ψ hψ dx hdx db hdb d b laminf lamv hinf hlamv minf hminf
    m hm β.1 (hermE_symm β) I hI _ (GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ)

end GlobalTheory.CompanionTheory.WhitFree
