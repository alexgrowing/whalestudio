import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDNegGram
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit GlobalTheory.SWLink
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWACase.Model

section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def HypsMet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n m : ℕ) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
  ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ J₂ = dblGram finSumFinEquiv J ∧
  ∃ T : GL (Fin (n + n)) E, IsWittBasis σ J l T ∧
  ∃ (κ : Type) (_ : Fintype κ) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co ∧
  ∃ (_ : MeasurableSpace (κ → AF F)) (_ : BorelSpace (κ → AF F)) (μ : Measure (κ → AF F)), IsTamagawa F κ μ ∧
  ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m ∧
  ∃ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om ∧
  ∃ K : Subgroup (UA σ J₂), IsStdK σ T K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K ∧
  ∃ Φ ∈ schA F κ, Φ ≠ 0 ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ∧
  ∃ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ JV) 𝓕 ν
end

set_option maxHeartbeats 4000000 in
theorem hypsMet_of (D : D7) (A V : HSp D) (han : IsAniso V) :
    HypsMet D.host.F D.host.E D.sp.cm.sig A.rank V.rank := by
  obtain ⟨ψ, χ, θ, μ, 𝓕, ω, H, ν, Φ, hψ, hχ, hres, hθ, hμ, hω, hH, hν, hΦ, hΦ0, -⟩ := GlobalTheory.AnisoStdModel.data D A V
  let n := A.rank
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨δ, hδ0, hδ⟩ := skew_xi D
  let J : Matrix (Fin n) (Fin n) D.host.E := δ • 1
  have hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j := fun i j => by
    by_cases h : i = j
    · subst h; simp [J, hδ]
    · simp [J, h, Ne.symm h]
  have hJ0 : J.det ≠ 0 := by simp [J, hδ0]
  obtain ⟨T, K, hT, hK, -⟩ := GlobalTheory.T.exists_witt_basis_compact_stabiliser D.host.F D.host.E D.sp.cm.sig hCM n 1 J _ one_ne_zero hJ0 rfl
  have hG := gram_witt hJ hT
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.witt_change_basis_unitary_iso D n _ T hG
  obtain ⟨hP, ha⟩ := GlobalTheory.T.siegel_parabolic_chart_levi_block D n _ T κ hκ J hT
  have hK' := GlobalTheory.T.standard_compact_under_witt_chart D n _ T κ hκ K hK
  obtain ⟨ι, hι, hιQ⟩ := GlobalTheory.T.unitary_group_conj_hermitian_automorphisms D V
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let ε := Module.finBasis D.host.F D.host.E
  obtain ⟨co, had, hco⟩ := GlobalTheory.T.darboux_basis_adapted_coordinates D n V J _ T hT hG _ ε
  letI : MeasurableSpace (Fin V.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := borel _
  haveI : BorelSpace (Fin V.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := ⟨rfl⟩
  obtain ⟨μ', hμ', hint⟩ := GlobalTheory.T.tamagawa_measure_matrix_adeles D V.rank n _ ε μ 𝓕 hμ
  obtain ⟨om, hom⟩ := GlobalTheory.T.weil_representation_seesaw_schwartz D n V ψ χ θ hθ μ 𝓕 hμ ω hω _ _ ε ι κ
  obtain ⟨ν', 𝓖, hν', h𝓖, -⟩ := GlobalTheory.T.haar_average_fundamental_domain_descent D V ι hιQ ν hν
  obtain ⟨⟨φ, hφ⟩, e⟩ := GlobalTheory.SchwartzCoord.exists_schA_comp_coord_eq D θ hθ V.rank n _ ε Φ.1 Φ.2
  obtain ⟨hI, -⟩ := height hH hP ha hK'
  have hF := formulas hθ hω hT hG hκ hι hco hint hom
  have hR := GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 χ V.rank hres
  have h0 : φ ≠ 0 := fun h => hΦ0 (Subtype.ext (by
    have e' : φ ∘ coord ε = Φ.1 := e
    rw [← e', h]; rfl))
  exact ⟨hCM, unramified_host D, ψ, hψ, 1, -V.gram, J, _, one_ne_zero, isHermND_neg_gram V, aniso_neg_gram han,
    by rw [inv_one, one_smul]; exact hJ, rfl, T, hT, _, inferInstance, co, had, inferInstance, inferInstance, μ', hμ', χ, hχ, hR,
    om, hF, K, hK, hI, φ, hφ, h0, kfin hom hK' hφ Φ e hΦ, ν', 𝓖, hν', h𝓖⟩

theorem hypsMet (D : D7) (n m : ℕ) : HypsMet D.host.F D.host.E D.sp.cm.sig n m := by
  obtain ⟨A, V, rfl, rfl, h⟩ := GlobalTheory.AnisoStdModel.ranks D n m
  exact hypsMet_of D A V h

theorem ranges_met (D : D7) (n : ℕ) (hn : 1 ≤ n) :
    (∃ m, 1 ≤ m ∧ 2 * n < m ∧ HypsMet D.host.F D.host.E D.sp.cm.sig n m) ∧
    (∃ m, 1 ≤ m ∧ (n < m ∧ m ≤ 2 * n) ∧ HypsMet D.host.F D.host.E D.sp.cm.sig n m) ∧
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ HypsMet D.host.F D.host.E D.sp.cm.sig n m :=
  ⟨⟨2 * n + 1, by omega, by omega, hypsMet D _ _⟩, ⟨2 * n, by omega, by omega, hypsMet D _ _⟩,
    ⟨n, hn, le_rfl, hypsMet D _ _⟩⟩

theorem exists_field : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E), ∀ n m, HypsMet F E σ n m := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  exact ⟨_, _, _, _, _, _, _, D.sp.cm.sig, hypsMet D⟩

end GlobalTheory.SWACase.Model

end
