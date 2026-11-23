import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetNeZeroOfIsWittBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

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

namespace GlobalTheory.SWInt

section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

def HasWeilModel (ψ : AddChar (AF F) ℂ) (χ : Chr F E) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)
    (K : Subgroup (UA σ J₂)) (JV : Matrix (Fin m) (Fin m) E) (P : Submodule ℂ (UA σ J₂ → ℂ) → Prop) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co ∧
  ∃ (_ : MeasurableSpace (κ → AF F)) (_ : BorelSpace (κ → AF F)) (μ : Measure (κ → AF F)), IsTamagawa F κ μ ∧
  ∃ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om ∧ P (secSpace om K)

def ComplMet (m t : ℕ) (b : Prop) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
  ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin (m + t)) (Fin (m + t)) E)
    (J₂ : Matrix (Fin (m + t + (m + t))) (Fin (m + t + (m + t))) E),
    l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ J₂ = dblGram finSumFinEquiv J ∧
  ∃ T : GL (Fin (m + t + (m + t))) E, IsWittBasis σ J l T ∧
  ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m ∧
  ∃ K : Subgroup (UA σ J₂), IsStdK σ T K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K ∧
    (∃ w : UA σ J₂, IsWeylElt σ T w) ∧ (∃ νN : Measure (GlobalTheory.SWWeil.unipN σ J₂), IsNormN σ νN) ∧
    HasWeilModel σ ψ χ T K JV (fun R => b → R ≠ ⊥) ∧ HasWeilModel σ ψ χ T K (complGram l JV t) fun R => b → R ≠ ⊥

end

theorem exists_frame_hyp (D : D7) (t : ℕ) : ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
    ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 i j := by
  let P : Matrix (Fin (t + t)) (Fin (t + t)) D.host.E := blk 1 (-((2 : D.host.E)⁻¹ • 1)) 1 ((2 : D.host.E)⁻¹ • 1)
  have hP : P * blk ((2 : D.host.E)⁻¹ • 1) ((2 : D.host.E)⁻¹ • 1) (-1) 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg] <;>
      match_scalars <;> norm_num
  let f := (GlobalTheory.OrthSumSp.hypSp D t).frame
  let b := f.map (Matrix.toLinearEquiv f P (Matrix.isUnit_det_of_right_inverse hP))
  have hb : ∀ j, b j = ∑ i, P i j • f i := fun j => by
    simp only [b, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hG : ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (f i) (f j) =
      dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) i j := fun i j => by
    have := gram_hdbl (GlobalTheory.OrthSumSp.posSp D t)
    rw [GlobalTheory.OrthSumSp.posSp_gram D t] at this
    exact congrFun (congrFun this i) j
  refine ⟨b, fun i j => ?_⟩
  have e : (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) =
      (Pᴴ * dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) * P) i j := by
    simp only [hb, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hG, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e1 : Pᴴ = blk 1 1 (-((2 : D.host.E)⁻¹ • 1)) ((2 : D.host.E)⁻¹ • 1) := by
    simp [P, blk, Matrix.fromBlocks_conjTranspose]
  have e2 : dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) = blk 1 0 0 (-1) := rfl
  have e3 : -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 = blk 0 (-1) (-1) 0 := by
    change (-Matrix.fromBlocks (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0).submatrix _ _ = _
    rw [Matrix.fromBlocks_neg, neg_zero, blk]
  rw [e, ← Matrix.neg_apply, e3, e1, e2, WittModel.blk_mul, WittModel.blk_mul]
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_zero, add_zero, zero_add] <;>
    match_scalars <;> norm_num

theorem exists_compl_space (D : D7) (V : HSp D) (t : ℕ) :
    ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
      -(hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }).gram = complGram 1 (-V.gram) t := by
  obtain ⟨b, hb⟩ := exists_frame_hyp D t
  refine ⟨b, ?_⟩
  have e : HSpace.gram { GlobalTheory.OrthSumSp.hypSp D t with frame := b } = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 :=
    Matrix.ext hb
  rw [gram_hsum, e, complGram, inv_one, one_smul]
  change (-Matrix.fromBlocks V.gram 0 0 (-blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0)).submatrix _ _ = _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_zero, neg_neg, blkMat]

set_option maxHeartbeats 4000000 in

theorem complMet_of (D : D7) (V : HSp D) (han : IsAniso V) (t : ℕ) : ComplMet D.sp.cm.sig V.rank t False := by
  let n := V.rank + t
  obtain ⟨-, ψ, χ, omh, -, -, -, -, hω, -, -, -⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair V V
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨lam, hlam, hψ, -⟩ :=
    GlobalTheory.StdUnn.shift_char_realPar D ψ hω.std θ hθ D.host.xi0 ⟨hxi, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D⟩
  have hl : lam ≠ 0 := fun h => by
    rw [h, map_zero] at hlam
    exact div_ne_zero (neg_ne_zero.2 hxi) hxi hlam.symm
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨δ, hδ0, hδ⟩ := skew_xi D
  let J : Matrix (Fin n) (Fin n) D.host.E := δ • 1
  have hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j := fun i j => by
    by_cases h : i = j
    · subst h; simp [J, hδ]
    · simp [J, h, Ne.symm h]
  have hJ' : ∀ i j, D.sp.cm.sig (((1 : D.host.E)⁻¹ • J) j i) = -((1 : D.host.E)⁻¹ • J) i j := by
    rw [inv_one, one_smul]; exact hJ
  have hJ0 : J.det ≠ 0 := by simp [J, hδ0]
  obtain ⟨T, K, hT, hK, -⟩ := GlobalTheory.T.exists_witt_basis_compact_stabiliser D.host.F D.host.E D.sp.cm.sig hCM n 1 J _ one_ne_zero hJ0 rfl
  have hG := gram_witt hJ hT
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.witt_change_basis_unitary_iso D n _ T hG
  obtain ⟨hP, ha⟩ := GlobalTheory.T.siegel_parabolic_chart_levi_block D n _ T κ hκ J hT
  have hK' := GlobalTheory.T.standard_compact_under_witt_chart D n _ T κ hκ K hK
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D n
  obtain ⟨hI, -⟩ := height hH hP ha hK'
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let ε := Module.finBasis D.host.F D.host.E
  have key : ∀ B : HSp D, ResEta D χ B.rank →
      HasWeilModel D.sp.cm.sig (GlobalTheory.StdUnn.shift ψ lam) χ T K (-B.gram) fun R => False → R ≠ ⊥ := fun B hB => by
    obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank n
    obtain ⟨ω, hW⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D n B ψ hω.std lam hl χ hω.hecT hB θ hθ μ 𝓕 hμ
    obtain ⟨ι, hι, -⟩ := GlobalTheory.T.unitary_group_conj_hermitian_automorphisms D B
    obtain ⟨co, had, hco⟩ := GlobalTheory.T.darboux_basis_adapted_coordinates D n B J _ T hT hG _ ε
    letI : MeasurableSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := borel _
    haveI : BorelSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := ⟨rfl⟩
    obtain ⟨μ', hμ', hint⟩ := GlobalTheory.T.tamagawa_measure_matrix_adeles D B.rank n _ ε μ 𝓕 hμ
    obtain ⟨om, hom⟩ := GlobalTheory.T.weil_representation_seesaw_schwartz D n B _ χ θ hθ μ 𝓕 hμ ω hW _ _ ε ι κ
    exact ⟨_, inferInstance, co, had, inferInstance, inferInstance, μ', hμ', om, formulas hθ hW hT hG hκ hι hco hint hom,
      False.elim⟩
  obtain ⟨b, hb⟩ := exists_compl_space D V t
  have hres : ResEta D χ (V.rank + (t + t)) := resEta_parity hω.resT (by omega)
  have h2 := key (hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }) hres
  rw [hb] at h2
  obtain ⟨w, -, hw⟩ := exists_isWeylElt (GlobalTheory.SiegelSet.sigma_sigma hCM) one_ne_zero hJ' rfl hT
  exact ⟨hCM, unramified_host D, _, hψ, 1, -V.gram, J, _, one_ne_zero, isHermND_neg_gram V, aniso_neg_gram han, hJ', rfl,
    T, hT, χ, hω.hecT, GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 χ V.rank hω.resT, K, hK, hI, ⟨w, hw⟩,
    (existsUnique_isNormN hCM one_ne_zero hJ' hJ0 rfl).exists, key V hω.resT, h2⟩

theorem exists_complMet : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E), ∀ m t, ComplMet σ m t False := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  refine ⟨D.host.F, D.host.E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D.sp.cm.sig,
    fun m t => ?_⟩
  obtain ⟨-, V, -, rfl, h⟩ := GlobalTheory.AnisoStdModel.ranks D 0 m
  exact complMet_of D V h t

end GlobalTheory.SWInt

end
