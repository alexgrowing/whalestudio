import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000

open Classical

variable (D : D7)

theorem glueA_eq_homeo (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    glueA D y z = (G5.tensCoordH (basE D) (AF D.host.F)).symm
      (fun k => pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k)) := by
  apply (G5.tensCoordH (basE D) (AF D.host.F)).injective
  rw [Homeomorph.apply_symm_apply]
  funext k
  rw [G5.tensCoordH_apply]
  exact repr_glueA D y z k

theorem continuous_glueA (z : Af D.host.F ⊗[D.host.F] D.host.E) : Continuous fun y => glueA D y z := by
  have e : (fun y => glueA D y z) = fun y => (G5.tensCoordH (basE D) (AF D.host.F)).symm
      (fun k => pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k)) := funext fun y => glueA_eq_homeo D y z
  rw [e]
  have hp : Continuous fun p : Ainf D.host.F × Af D.host.F => pairA D.host.F p.1 p.2 := continuous_id
  exact (G5.tensCoordH (basE D) (AF D.host.F)).symm.continuous.comp
    (continuous_pi fun k => hp.comp ((continuous_repr D k).prodMk continuous_const))

theorem continuous_splitInv : Continuous (splitInv D) := by
  rw [← splitEquiv_symm]; exact continuous_splitEquiv_symm D

variable (V : HSp D)

theorem continuous_atM (τ : D.what₂.Tau) : Continuous (atM D V τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact (continuous_apply j).comp (continuous_apply i)
  · simp only [h, if_false]; exact continuous_const

theorem unitary_mul (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) (hg' : g'ᴴ * gramAt D V τ * g' = gramAt D V τ) :
    (g * g')ᴴ * gramAt D V τ * (g * g') = gramAt D V τ := by
  rw [Matrix.conjTranspose_mul,
    show g'ᴴ * gᴴ * gramAt D V τ * (g * g') = g'ᴴ * (gᴴ * gramAt D V τ * g) * g' by
      simp only [Matrix.mul_assoc],
    hg, hg']

theorem unitary_one (τ : D.what₂.Tau) : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ := by
  simp

theorem atTau_eq (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    atTau (thetaC D) V τ g = atH D V τ g hg := by
  have hex : ∃ x, IsAtTau (thetaC D) V τ g x := ⟨_, isAtTau_atH D V τ g hg⟩
  unfold atTau
  rw [dif_pos hex]
  exact matA_inj D V ((matA_of_isAtTau D V hex.choose_spec).trans (matA_atH D V τ g hg).symm)

theorem atH_one (τ : D.what₂.Tau) : atH D V τ 1 (unitary_one D V τ) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show atM D V τ 1 = 1
  rw [atM_one]

theorem atH_mul (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) (hg' : g'ᴴ * gramAt D V τ * g' = gramAt D V τ) :
    atH D V τ (g * g') (unitary_mul D V τ hg hg') = atH D V τ g hg * atH D V τ g' hg' := by
  apply Subtype.ext
  apply Units.ext
  show atM D V τ (g * g') = atM D V τ g * atM D V τ g'
  rw [atM_mul]

theorem continuous_atH (τ : D.what₂.Tau) :
    Continuous fun u : {g : Matrix (Fin V.rank) (Fin V.rank) ℂ // gᴴ * gramAt D V τ * g = gramAt D V τ} =>
      atH D V τ u.1 u.2 := by
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atM D V τ).comp continuous_subtype_val
  · have hi : Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ => ginv D V τ g :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    exact (continuous_atM D V τ).comp (hi.comp continuous_subtype_val)

theorem atTauHom_holds : AtTauHom D := by
  intro θ hθ V τ
  rw [eq_thetaC D hθ]
  refine ⟨?_, fun g g' hg hg' => ?_, ?_⟩
  · rw [atTau_eq D V τ 1 (unitary_one D V τ), atH_one]
  · rw [atTau_eq D V τ _ (unitary_mul D V τ hg hg'), atTau_eq D V τ g hg, atTau_eq D V τ g' hg', atH_mul]
  · rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {g | gᴴ * gramAt D V τ * g = gramAt D V τ} (atTau (thetaC D) V τ) =
        fun u => atH D V τ u.1 u.2 := funext fun u => atTau_eq D V τ u.1 u.2
    rw [e]
    exact continuous_atH D V τ

section Line

variable {m n : ℕ}

def lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) : Datum.Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then (t : ℂ) * z i j else 0) 0

theorem psi_lineF (τ τ' : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    (lineF D τ z t).map (psiT D τ') = if τ' = τ then (t : ℂ) • z else 0 := by
  ext i j
  simp only [lineF, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  split_ifs <;> simp

theorem fin_lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) : (lineF D τ z t).map (finPart D) = 0 := by
  ext i j
  simp [lineF, finPart_glueA]

def lineL (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : ℝ →+ Datum.Mx D m n where
  toFun := lineF D τ z
  map_zero' := by
    apply mat_ext D
    · intro τ'
      rw [psi_lineF, Matrix.map_zero _ (map_zero _)]
      split_ifs <;> simp
    · rw [fin_lineF, Matrix.map_zero _ (map_zero _)]
  map_add' s t := by
    apply mat_ext D
    · intro τ'
      rw [Matrix.map_add _ (map_add _), psi_lineF, psi_lineF, psi_lineF]
      split_ifs
      · push_cast; rw [add_smul]
      · simp
    · rw [Matrix.map_add _ (map_add _), fin_lineF, fin_lineF, fin_lineF, add_zero]

theorem continuous_lineF (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) : Continuous (lineF D τ z) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact Complex.continuous_ofReal.mul continuous_const
  · simp only [h, if_false]; exact continuous_const

theorem compAt_thetaC (τ : D.what₂.Tau) (w : Datum.Mx D m n) : Datum.compAt (thetaC D) τ w = w.map (psiT D τ) := rfl

theorem isLineAt_lineL (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    Datum.IsLineAt (thetaC D) τ z (lineL D τ z) :=
  ⟨continuous_lineF D τ z, fun t => fin_lineF D τ z t, fun t τ' => by
    rw [compAt_thetaC]; exact psi_lineF D τ τ' z t⟩

end Line

theorem lineAtExists_holds : Datum.LineAtExists D := by
  intro θ hθ m n τ z
  rw [eq_thetaC D hθ]
  exact ⟨lineL D τ z, isLineAt_lineL D τ z⟩

theorem lineAtUnique_holds : Datum.LineAtUnique D := by
  intro θ hθ m n τ z L L' h h'
  rw [eq_thetaC D hθ] at h h'
  ext1 t
  apply mat_ext D
  · intro τ'
    rw [← compAt_thetaC, ← compAt_thetaC, h.2.2 t τ', h'.2.2 t τ']
  · rw [h.2.1 t, h'.2.1 t]

section Fam

variable (V : HSp D)

def famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ => gs τ i j)
    ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    (famM D V gs).map (psiT D τ) = gs τ := by
  ext i j
  simp [famM, psiT_glueA]

theorem fin_famM (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : (famM D V gs).map (finPart D) = 1 := by
  ext i j
  simp [famM, finPart_glueA]

theorem famM_mul (gs gs' : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    famM D V (gs * gs') = famM D V gs * famM D V gs' := by
  apply mat_ext D
  · intro τ
    rw [Matrix.map_mul, psi_famM, psi_famM, psi_famM]
    rfl
  · rw [Matrix.map_mul, fin_famM, fin_famM, fin_famM, mul_one]

theorem famM_one : famM D V 1 = 1 := by
  apply mat_ext D
  · intro τ
    rw [psi_famM, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  · rw [fin_famM, Matrix.map_one _ (map_zero _) (map_one _)]

def IsUnitFam (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, (gs τ)ᴴ * gramAt D V τ * gs τ = gramAt D V τ

theorem famM_unitary (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (famM D V gs) * JR (AF D.host.F) V.gram * famM D V gs =
      JR (AF D.host.F) V.gram := by
  apply mat_ext D
  · intro τ
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_famM]
    exact hgs τ
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_famM, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

def famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) : GA D V :=
  (⟨⟨famM D V gs, famM D V (fun τ => ginv D V τ (gs τ)),
      by rw [← famM_mul]; convert famM_one D V; funext τ; exact mul_ginv D V τ (gs τ) (hgs τ),
      by rw [← famM_mul]; convert famM_one D V; funext τ; exact ginv_mul D V τ (gs τ) (hgs τ)⟩,
    famM_unitary D V gs hgs⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem matA_famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    matA D V (famH D V gs hgs) = famM D V gs := rfl

theorem infMat_famH (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (famH D V gs hgs) = gs τ := by
  rw [infMat_thetaC, matA_famH, psi_famM]

theorem famH_mem_GinfC (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) :
    famH D V gs hgs ∈ GinfC V :=
  (mem_GinfC D V _).mpr (fin_famM D V gs)

theorem famH_unique (gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hgs : IsUnitFam D V gs) (h : GA D V)
    (h1 : h ∈ GinfC V) (h2 : ∀ τ, infMat D.sp.cm.sig V.gram (thetaC D τ) h = gs τ) : h = famH D V gs hgs := by
  apply matA_inj D V
  rw [matA_famH]
  apply mat_ext D
  · intro τ; rw [← infMat_thetaC, h2, psi_famM]
  · rw [fin_famM]; exact (mem_GinfC D V h).mp h1

theorem infMat_unitary' (h : GA D V) : IsUnitFam D V fun τ => infMat D.sp.cm.sig V.gram (thetaC D τ) h := by
  intro τ
  have hu := congrArg (fun M => M.map (psiT D τ)) (matA_unitary D V h)
  simp only [Matrix.map_mul, cT_map_psiT, JR_map_psiT] at hu
  show (infMat D.sp.cm.sig V.gram (thetaC D τ) h)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (thetaC D τ) h = _
  rw [infMat_thetaC]
  exact hu

def infOnly (h : GA D V) : GA D V := famH D V _ (infMat_unitary' D V h)

theorem infMat_infOnly (h : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (infOnly D V h) = infMat D.sp.cm.sig V.gram (thetaC D τ) h :=
  infMat_famH D V _ _ τ

theorem infOnly_mem_GinfC (h : GA D V) : infOnly D V h ∈ GinfC V := famH_mem_GinfC D V _ _

end Fam

end Formalism.IndefR.Eqv

end
