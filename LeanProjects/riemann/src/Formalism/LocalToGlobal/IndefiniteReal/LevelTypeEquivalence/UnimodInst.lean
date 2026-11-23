import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped Matrix

namespace Formalism.IndefR.Eqv.UI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (V : HSp D)

abbrev crd : (Fin V.rank → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm

def Lv : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.comap ((crd D V).toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_Lv (x : Fin V.rank → D.host.E) : x ∈ Lv D V ↔ (∑ i, x i • V.frame i) ∈ V.L0 := by
  simp only [Lv, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap, crd, Module.Basis.equivFun_symm_apply]

theorem hform_eq (x y : Fin V.rank → D.host.E) :
    Formalism.UG.hform (starRingEnd D.host.E) V.gram x y = V.hT (∑ i, x i • V.frame i) (∑ j, y j • V.frame j) := by
  simp only [Formalism.UG.hform, Formalism.BasicNotions.HSpace.gram, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem J_herm : Formalism.UG.IsHerm (starRingEnd D.host.E) V.gram := by
  show Formalism.UG.cT _ V.gram = V.gram
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Formalism.BasicNotions.HSpace.gram]
  exact V.herm.eq _ _

theorem J_det : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hy0
  have hrow : ∀ i, V.hT (V.frame i) (∑ j, y j • V.frame j) = 0 := by
    intro i
    have hi := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, Pi.zero_apply] at hi
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hw : (∑ j, y j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun v => ?_
    generalize (∑ j, y j • V.frame j) = w at hrow ⊢
    rw [← V.frame.sum_repr v, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, hrow, smul_zero]
  funext i
  exact Fintype.linearIndependent_iff.mp V.frame.linearIndependent y hw i

theorem Lv_eq_map : Lv D V = V.L0.map ((crd D V).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  ext x
  simp only [Lv, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap]
  constructor
  · intro h
    exact ⟨_, h, (crd D V).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem L_fg : (Lv D V).FG := by
  rw [Lv_eq_map]
  exact V.standardTuple_isLattice.fg.map _

theorem L_span : Submodule.span D.host.E ((Lv D V : Set (Fin V.rank → D.host.E))) = ⊤ := by
  rw [Lv_eq_map, Submodule.map_coe]
  change Submodule.span D.host.E (⇑((crd D V).symm.toLinearMap) '' (V.L0 : Set V.V)) = ⊤
  rw [Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top]
  exact (crd D V).symm.range

theorem L_dual (x : Fin V.rank → D.host.E) : x ∈ Lv D V ↔
    ∀ y ∈ Lv D V, Formalism.UG.hform (starRingEnd D.host.E) V.gram y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  rw [mem_Lv]
  have hL : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  constructor
  · intro hx y hy
    rw [mem_Lv] at hy
    rw [hform_eq]
    rw [← hL] at hx
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one] at hx
    obtain ⟨a, ha⟩ := hx _ hy
    exact RingHom.mem_range.mpr ⟨a, ha⟩
  · intro h
    rw [← hL]
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    intro w hw
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (h (V.frame.equivFun w) (by rw [mem_Lv]; simpa using hw))
    rw [hform_eq, Module.Basis.sum_equivFun] at ha
    exact ⟨a, ha⟩

def phiV (v : InfinitePlace D.host.F) : D.host.E →+* ℂ := tauE D ((Formalism.L2.Host.tauPl D).symm v)

theorem phiV_over (v : InfinitePlace D.host.F) (a : D.host.F) :
    phiV D v (algebraMap D.host.F D.host.E a) = v.embedding a := by
  unfold phiV tauE
  simp only [Formalism.L2.Host.tauPl, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  set ψ := (Equiv.ofBijective (Formalism.L2.Host.realPl D.host) (Formalism.L2.Host.realPlBij D.host)).symm v with hψ
  have hv : Formalism.L2.Host.realPl D.host ψ = v := Equiv.ofBijective_apply_symm_apply _ _ v
  unfold Formalism.L2.Host.realPl at hv
  have hreal := NumberField.IsTotallyReal.isReal v
  rw [NumberField.InfinitePlace.isReal_iff] at hreal
  have hemb : v.embedding = (D.host.emb ψ).comp D.host.F.subtype := by
    rcases NumberField.InfinitePlace.embedding_mk_eq ((D.host.emb ψ).comp D.host.F.subtype) with h | h
    · rw [← hv, h]
    · rw [← hv, h] at hreal ⊢
      unfold NumberField.ComplexEmbedding.IsReal at hreal
      refine RingHom.ext fun x => ?_
      have hx := RingHom.congr_fun hreal x
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at hx ⊢
      exact hx.symm
  rw [hemb]
  rfl

structure Frames where
  ε : InfinitePlace D.host.F → Fin V.rank → Bool
  P : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ
  unit : ∀ v, IsUnit (P v)
  spec : ∀ v, (P v)ᴴ * V.gram.map (phiV D v) * P v = Formalism.REAL.Jm (ε v)
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  Λ_fg : Λ.FG
  Λ_span : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤
  Λ_dual : ∀ x : Fin V.rank → D.host.E, x ∈ Λ ↔
    ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd D.host.E) V.gram y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

variable {D V}

def instV (fr : Frames D V) : AutInst :=
  let hT := Formalism.MainNotions.S.Inh.aut_HTop_holds D.sp.cm V.gram fr.Λ fr.Λ_fg fr.Λ_span
  { F := D.host.F, E := D.host.E, cm := D.sp.cm, n := V.rank, J := V.gram
    J_herm := J_herm D V
    J_det := J_det D V
    L := fr.Λ
    L_span := fr.Λ_span
    L_fg := fr.Λ_fg
    L_dual := fr.Λ_dual
    ε := fr.ε
    φ := phiV D
    φ_over := phiV_over D
    P := fr.P
    P_unit := fr.unit
    P_spec := fr.spec
    topf := hT.choose
    topf_group := hT.choose_spec.1
    topf_open := hT.choose_spec.2.1
    topf_basis := hT.choose_spec.2.2 }

def brg (fr : Frames D V) : (instV fr).GA ≃ₜ* GA D V :=
  Formalism.L2.SG.AdBridge.toHA (instV fr) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (instV fr)).1

theorem brg_isBridge (fr : Frames D V) : Formalism.L2.SG.AdBridge.IsBridge (instV fr) (brg fr) := by
  exact (Formalism.L2.SG.Closed.adelic_isomorphism_statement (instV fr)).1.choose_spec

theorem frame_of_sig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {p q : ℕ} (h : Formalism.UG.HasSignature M p q) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * M * P = Formalism.REAL.Jm ε := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨fun i => (e i).isLeft, (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
  · have hM : M = (M.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hM]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * M.reindex e e * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
    rw [hP']
    ext i j
    simp only [Matrix.submatrix_apply, Formalism.REAL.Jm, Matrix.diagonal_apply, Formalism.UG.Jpq]
    have hd : ∀ s : Fin p ⊕ Fin q, Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) s s = if s.isLeft then 1 else -1 := by
      rintro (a | a)
      · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq]; rfl
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq]; rfl
    have ho : ∀ s t : Fin p ⊕ Fin q, s ≠ t → Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) s t = 0 := by
      rintro (a | a) (b | b) hst
      · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_ne (fun h => hst (by rw [h]))]
      · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_ne (fun h => hst (by rw [h])), neg_zero]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact hd (e i)
    · rw [if_neg hij]
      exact ho _ _ fun h => hij (e.injective h)

theorem gram_map_herm (v : InfinitePlace D.host.F) :
    Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map (phiV D v)) := by
  have hJ : Formalism.UG.cT (starRingEnd D.host.E) V.gram = V.gram := J_herm D V
  show Formalism.UG.cT _ _ = _
  ext i j
  have hij := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [← hij]
  exact (NumberField.IsCMField.complexEmbedding_complexConj D.host.E (phiV D v) _).symm

theorem gram_map_det (v : InfinitePlace D.host.F) : IsUnit (V.gram.map (phiV D v)).det := by
  have h := RingHom.map_det (phiV D v) V.gram
  rw [RingHom.mapMatrix_apply] at h
  rw [isUnit_iff_ne_zero, ← h]
  exact (map_ne_zero_iff _ (phiV D v).injective).mpr (J_det D V)

variable (D V)

theorem real_frames : ∀ v : InfinitePlace D.host.F, ∃ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit P ∧ Pᴴ * V.gram.map (phiV D v) * P = Formalism.REAL.Jm ε := by
  intro v
  have h' : Formalism.UG.cT (starRingEnd ℂ) (V.gram.map (phiV D v)) = V.gram.map (phiV D v) := gram_map_herm v
  have hA : (V.gram.map (phiV D v)).IsHermitian :=
    Matrix.IsHermitian.ext fun i j => by simpa [Formalism.UG.cT] using congrFun (congrFun h' i) j
  have hdet : (V.gram.map (phiV D v)).det ≠ 0 := (gram_map_det v).ne_zero
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hsp := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  try simp only [Unitary.coe_star] at hsp
  have hUU : star (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := (hA.eigenvectorUnitary).2.1
  obtain ⟨U, hUu, hD⟩ : ∃ U : Matrix (Fin V.rank) (Fin V.rank) ℂ, star U * U = 1 ∧
      star U * V.gram.map (phiV D v) * U = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    refine ⟨_, hUU, ?_⟩
    calc _ = star (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) * ((hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ)) * (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by rw [← hsp]
      _ = (star (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ)) * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (star (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin V.rank) (Fin V.rank) ℂ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨d, hd⟩ : ∃ d : Fin V.rank → ℝ, ∀ i, d i = (Real.sqrt |hA.eigenvalues i|)⁻¹ := ⟨_, fun _ => rfl⟩
  have key : ∀ x : ℝ, x ≠ 0 → (Real.sqrt |x|)⁻¹ * x * (Real.sqrt |x|)⁻¹ = if 0 < x then 1 else -1 := by
    intro x hx
    have h1 : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
    rw [show (Real.sqrt |x|)⁻¹ * x * (Real.sqrt |x|)⁻¹ = x / (Real.sqrt |x| * Real.sqrt |x|) by
      rw [div_eq_mul_inv, mul_inv]; ring, h1]
    split_ifs with h
    · rw [abs_of_pos h, div_self hx]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg, div_self hx]
  refine ⟨fun i => decide (0 < hA.eigenvalues i), U * Matrix.diagonal (fun i => (d i : ℂ)), ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul]
    refine (Matrix.isUnit_det_of_left_inverse hUu).mul ?_
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    rw [hd, Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero (abs_nonneg _)]
    exact abs_ne_zero.mpr (hne i)
  · have hsD : (Matrix.diagonal fun i => (d i : ℂ))ᴴ = Matrix.diagonal fun i => (d i : ℂ) := by
      rw [Matrix.diagonal_conjTranspose]; congr 1; funext i; simp
    rw [Matrix.star_eq_conjTranspose] at hD
    rw [Matrix.conjTranspose_mul, hsD]
    have hre : (Matrix.diagonal fun i => (d i : ℂ)) * Uᴴ * V.gram.map (phiV D v) * (U * Matrix.diagonal fun i => (d i : ℂ))
        = Matrix.diagonal (fun i => (d i : ℂ)) * (Uᴴ * V.gram.map (phiV D v) * U) * Matrix.diagonal (fun i => (d i : ℂ)) := by
      simp only [Matrix.mul_assoc]
    rw [hre, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    unfold Formalism.REAL.Jm
    congr 1
    funext i
    have hk := key _ (hne i)
    rw [← hd] at hk
    simp only [Function.comp_apply, decide_eq_true_eq]
    change ((d i : ℝ) : ℂ) * ((hA.eigenvalues i : ℝ) : ℂ) * ((d i : ℝ) : ℂ) = _
    split_ifs at hk ⊢ with h
    · exact_mod_cast hk
    · exact_mod_cast hk

def framesL (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hfg : Λ.FG)
    (hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤)
    (hdual : ∀ x : Fin V.rank → D.host.E, x ∈ Λ ↔
      ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd D.host.E) V.gram y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    Frames D V where
  ε v := (real_frames D V v).choose
  P v := (real_frames D V v).choose_spec.choose
  unit v := (real_frames D V v).choose_spec.choose_spec.1
  spec v := (real_frames D V v).choose_spec.choose_spec.2
  Λ := Λ
  Λ_fg := hfg
  Λ_span := hspan
  Λ_dual := hdual

def framesV : Frames D V := framesL D V (Lv D V) (L_fg D V) (L_span D V) (L_dual D V)

theorem frames_nonempty : Nonempty (Frames D V) := by
  exact ⟨framesV D V⟩

end Formalism.IndefR.Eqv.UI

end
