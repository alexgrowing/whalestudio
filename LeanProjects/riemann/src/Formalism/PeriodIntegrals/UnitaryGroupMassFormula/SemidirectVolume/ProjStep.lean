import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SemiDefs

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

theorem HA_ext {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g g' : HA R σ J}
    (h : ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) : g = g' :=
  Subtype.ext (Units.ext h)

theorem lin_eq_toLin' {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  rw [lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

theorem tupH_alt {E : Type} {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_last]

theorem tupH_e {E : Type} {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]

theorem tupH_f {E : Type} {M r : ℕ} (P : Frame E M r) (b : Fin r) :
    tupH P (Fin.natAdd (r + 1) b) = P.f b := by
  simp [tupH, Fin.append_right]

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hCM.2.2.2 τ (σ x), hCM.2.2.2 τ x, star_star]

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem fix_f_of_H {g : HA R σ J} (hg : g ∈ Hsub R σ J P) (b : Fin r) :
    lin R σ J g (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  rw [Hsub, mem_stabT] at hg
  have := hg (Fin.natAdd (r + 1) b)
  rwa [tupH_f] at this

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_piG]
  have H := datR_hyp (R := R) hσσ hJ hP
  refine Fin.addCases (fun b0 => ?_) (fun b1 => ?_) b
  · refine Fin.lastCases ?_ (fun a => ?_) b0
    · rw [tupH_alt]; exact PG.Dat.unipotent_proj_fixes_normal H _
    · rw [tupH_e]; exact PG.Dat.Pi_e H _ a
  · rw [tupH_f]; exact PG.Dat.Pi_f H _ b1

theorem mat_one : ((HA.mat R σ J (1 : HA R σ J) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1 := rfl

theorem mat_mul (g g' : HA R σ J) : ((HA.mat R σ J (g * g') : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) * ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) := rfl

theorem piG_mat (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    ((HA.mat R σ J (piG hσσ hJ hP g hg) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = piMat (P := P) (T := T) g := rfl

theorem piG_one : piG hσσ hJ hP (1 : HA R σ J) (S0 R σ J P).one_mem = 1 := by
  apply HA_ext
  rw [piG_mat, mat_one hσσ hJ hP, piMat, Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    piG hσσ hJ hP (g * g') ((S0 R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  apply HA_ext
  rw [mat_mul hσσ hJ hP, piG_mat, piG_mat, piG_mat, piMat, piMat, piMat, Pi_lin_mul hσσ hJ hP hg hg',
    LinearMap.toMatrix'_comp]

def piHom : S0 R σ J P →* Hsub R σ J P where
  toFun s := ⟨_, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩
  map_one' := Subtype.ext (piG_one hσσ hJ hP)
  map_mul' s s' := Subtype.ext (piG_mul hσσ hJ hP s.2 s'.2)

theorem piHom_coe (s : S0 R σ J P) :
    ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J) = piG hσσ hJ hP s s.2 := rfl

theorem piHom_H (s : S0 R σ J P) (hs : (s : HA R σ J) ∈ Hsub R σ J P) :
    ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J) = s := by
  rw [piHom_coe]
  apply HA_ext
  show piMat (P := P) (T := T) (s : HA R σ J) = _
  have e : (datR R σ J P T).Pi (lin R σ J s) = lin R σ J s := LinearMap.ext fun v =>
    PG.Dat.Pi_of_fix (datR_hyp hσσ hJ hP) (stabilizer_fixes_frame_and_normal s.2) (fix_f_of_H hσσ hJ hP hs)
      (uni_lin _) v
  rw [piMat, e, lin_eq_toLin']

theorem spanR_eq {m : ℕ} (Y : Fin m → Fin M → E) :
    spanR (F := F) R Y Set.univ = Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  rw [spanR, Set.image_univ]

theorem piHom_N (s : S0 R σ J P) (hs : (s : HA R σ J) ∈ FrameUnipotentSubgroup R σ J P) : piHom hσσ hJ hP s = 1 := by
  apply Subtype.ext
  rw [piHom_coe]
  apply HA_ext
  show piMat (P := P) (T := T) (s : HA R σ J) = 1
  have hN := (Subgroup.mem_inf.1 hs).1
  have e : (datR R σ J P T).Pi (lin R σ J s) = LinearMap.id := LinearMap.ext fun v =>
    PG.Dat.Pi_of_N (datR_hyp hσσ hJ hP) (fun w hw => by
      have := hN.2 w hw
      rwa [spanR_eq hσσ hJ hP] at this) v
  rw [piMat, e, LinearMap.toMatrix'_id]

theorem piHom_S (s : S0 R σ J P) :
    (s : HA R σ J) * ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J)⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by
  have hinv : ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J)⁻¹ =
      ((piHom hσσ hJ hP s⁻¹ : Hsub R σ J P) : HA R σ J) := by
    rw [map_inv]; rfl
  rw [hinv, piHom_coe]
  have hS0 : (s : HA R σ J) * piG hσσ hJ hP (s⁻¹ : S0 R σ J P) (s⁻¹ : S0 R σ J P).2 ∈ S0 R σ J P :=
    (S0 R σ J P).mul_mem s.2 (heisenberg_le_stabilizer R σ J P (piG_mem_H hσσ hJ hP _ _))
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf]
  refine ⟨?_, hS0⟩
  show UniC R σ J P.e _ ∧ ∀ v, InXperp R σ J P v → _
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [stabilizer_fixes_frame_vector R σ J P hS0 b, sub_self]
    exact Submodule.zero_mem _
  · rw [lin_mul, lin_piG, spanR_eq hσσ hJ hP]
    have hsi : ((s⁻¹ : S0 R σ J P) : HA R σ J) = (s : HA R σ J)⁻¹ := rfl
    have := PG.Dat.Pi_N_part (datR_hyp hσσ hJ hP) (stabilizer_fixes_frame_and_normal s.2)
      (stabilizer_fixes_frame_and_normal (s⁻¹ : S0 R σ J P).2) (uni_lin _) (fun w => by rw [hsi, lin_lin_inv]) v hv
    exact this

end R

def PiCont : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (r : ℕ) (P : Frame E M r) (T : F)
    (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T),
    Continuous fun s : S0 (AF F) σ J P => piG hσσ hJ hP (s : HA (AF F) σ J) s.2

def PiRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (r : ℕ) (P : Frame E M r) (T : F)
    (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (g : HA (AF F) σ J) (hg : g ∈ S0 (AF F) σ J P),
    g ∈ HFinIn (AF F) σ J → piG hσσ hJ hP g hg ∈ HFinIn (AF F) σ J

theorem projStep_of (hC : PiCont) (hR : PiRat) : ProjStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP
  have hσσ := sigma_invol hCM
  refine ⟨piHom hσσ hJ hP, ?_, fun s hs => piHom_H hσσ hJ hP s hs,
    fun s hs => piHom_N hσσ hJ hP s hs, fun s => piHom_S hσσ hJ hP s,
    fun s hs => hR F E σ M J r P T hσσ hJ hP s s.2 hs⟩
  exact (hC F E σ M J r P T hσσ hJ hP).subtype_mk _

end PI.VolSemiDirect.W
