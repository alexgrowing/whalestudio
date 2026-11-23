import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.AdelicPointsAt

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH)

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem map_smul_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (f : R →ₐ[F] R') (u : R) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (u • x) =
      (f u ⊗ₜ[F] (1 : E)) * Algebra.TensorProduct.map f (AlgHom.id F E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  | tmul a e => simp [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, map_mul]

theorem tens_eq_zero (x : AF F ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (evFin F w) (AlgHom.id F E) x = 0) :
    x = 0 := by
  have hs : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0 := by
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    rw [map_zero, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    exact h2 w
  let P := TensorProduct.prodLeft F F (Ainf F) (Af F) E
  have e1 : ∀ y : (Ainf F × Af F) ⊗[F] E,
      (P y).1 = Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Prod.fst_add, ha, hb]
    | tmul a e => obtain ⟨a1, a2⟩ := a; simp [P]
  have e2 : ∀ y : (Ainf F × Af F) ⊗[F] E,
      (P y).2 = Algebra.TensorProduct.map (AlgHom.snd F (Ainf F) (Af F)) (AlgHom.id F E) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Prod.snd_add, ha, hb]
    | tmul a e => obtain ⟨a1, a2⟩ := a; simp [P]
  have : P x = P 0 := by
    rw [map_zero]
    exact Prod.ext ((e1 x).trans h1) ((e2 x).trans hs)
  exact P.injective this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mapH_eq_one_iff {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (h : HA R σ J) :
    mapH σ J φ h = 1 ↔ ∀ r s, Algebra.TensorProduct.map φ (AlgHom.id F E)
      (((HA.mat R σ J h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - 1) r s) = 0 := by
  have key : ((HA.mat R' σ J (mapH σ J φ h)) : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) =
      (HA.mat R σ J h : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) :=
    Matrix.ext fun r s => GlobalTheory.AutFunCompare.mat_mapH σ J φ h r s
  have ent : ∀ r s, Algebra.TensorProduct.map φ (AlgHom.id F E)
      (((HA.mat R σ J h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - 1) r s) =
      (((HA.mat R' σ J (mapH σ J φ h)) : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) - 1) r s := by
    intro r s
    rw [key]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  simp_rw [ent]
  constructor
  · intro e r s
    rw [e]
    change ((GlobalTheory.AdelicU.matHom R' σ J 1 : GL (Fin n) (R' ⊗[F] E)) : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) r s - _ = 0
    rw [map_one]
    simp
  · intro e
    have e' : ((HA.mat R' σ J (mapH σ J φ h)) : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) = 1 :=
      sub_eq_zero.1 (Matrix.ext e)
    exact GlobalTheory.AdelicU.matHom_injective R' σ J (Units.ext (by rw [map_one]; exact e'))

variable {σ J}

theorem mem_range_emb_iff (v : HeightOneSpectrum (𝓞 F)) (g : GlobalTheory.AdelicU.GAd σ J) :
    g ∈ (GlobalTheory.AdelicU.emb σ J v).range ↔
      ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) = 0 := by
  rw [GlobalTheory.AdelicU.range_emb, GlobalTheory.AdelicU.mem_atPts, GlobalTheory.AdelicU.mem_finPts]
  have hI : GlobalTheory.AdelicU.projInf σ J g = mapH σ J (fstA F) g := rfl
  have hP : ∀ w, GlobalTheory.AdelicU.proj σ J w g = mapH σ J (evFin F w) g := fun _ => rfl
  simp only [hI, hP, mapH_eq_one_iff]
  constructor
  · rintro ⟨hinf, hfin⟩ u hu
    ext r s
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine tens_eq_zero _ ?_ fun w => ?_
    · rw [map_smul_tens, hinf r s, mul_zero]
    · rw [map_smul_tens]
      by_cases hw : w = v
      · subst hw; rw [hu, TensorProduct.zero_tmul, zero_mul]
      · rw [hfin w (by simpa using hw) r s, mul_zero]
  · intro H
    refine ⟨fun r s => ?_, fun w hw r s => ?_⟩
    · obtain ⟨u, hu0⟩ : ∃ u : AF F, u = LinearMap.inl F (Ainf F) (Af F) 1 := ⟨_, rfl⟩
      have hu : evFin F v u = 0 := by subst hu0; exact map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
      have := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))
        (congrFun (congrFun (H _ hu) r) s)
      rw [Matrix.smul_apply, map_smul_tens, Matrix.zero_apply, map_zero] at this
      have h1 : fstA F u = 1 := by subst hu0; rfl
      rwa [h1, Algebra.TensorProduct.one_def.symm, one_mul] at this
    · have hwv : w ≠ v := by simpa using hw
      obtain ⟨u, hu0⟩ : ∃ u : AF F, u = LinearMap.inr F (Ainf F) (Af F) (GlobalTheory.AdelicU.singleFin w 1) := ⟨_, rfl⟩
      have hu : evFin F v u = 0 := by subst hu0; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hwv) 1
      have := congrArg (Algebra.TensorProduct.map (evFin F w) (AlgHom.id F E))
        (congrFun (congrFun (H _ hu) r) s)
      rw [Matrix.smul_apply, map_smul_tens, Matrix.zero_apply, map_zero] at this
      have h1 : evFin F w u = 1 := by subst hu0; exact GlobalTheory.AdelicU.evalV_singleFin_self w 1
      rwa [h1, Algebra.TensorProduct.one_def.symm, one_mul] at this

end Helpers

end GlobalTheory.AdelicPointsAt

theorem GlobalTheory.AdelicPointsAt.range_emb_iff_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : GAd σ J), g ∈ (emb σ J v).range ↔
      ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) = 0 :=
  fun _ _ _ _ _ _ _ _ _ _ v g => GlobalTheory.AdelicPointsAt.mem_range_emb_iff v g
