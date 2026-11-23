import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField MeasureTheory Topology
open scoped TensorProduct

section Gen

variable {P Q : Type} [CommRing P] [CommRing Q] {n : ℕ}

def prM (a : Matrix (Fin n) (Fin n) P) (b : Matrix (Fin n) (Fin n) Q) :
    Matrix (Fin n) (Fin n) (P × Q) :=
  Matrix.of fun i j => (a i j, b i j)

theorem prM_mul (a a' : Matrix (Fin n) (Fin n) P) (b b' : Matrix (Fin n) (Fin n) Q) :
    prM a b * prM a' b' = prM (a * a') (b * b') := by
  ext i j : 1
  refine Prod.ext ?_ ?_ <;> simp [prM, Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum]

theorem prM_one : prM (1 : Matrix (Fin n) (Fin n) P) (1 : Matrix (Fin n) (Fin n) Q) = 1 := by
  ext i j : 1
  by_cases h : i = j
  · subst h; simp [prM]
  · simp [prM, Matrix.one_apply_ne h]

end Gen

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {n : ℕ}

theorem fst_splR_symm (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) :
    tensMap (E := E) (fstA F) (splR.symm y) = y.1 := by
  have h := congrArg Prod.fst (splR.apply_symm_apply y)
  rw [splR_apply, splT_apply] at h
  exact h

theorem snd_splR_symm (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) :
    tensMap (E := E) (sndA F) (splR.symm y) = y.2 := by
  have h := congrArg Prod.snd (splR.apply_symm_apply y)
  rw [splR_apply, splT_apply] at h
  exact h

def glM (a : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  (prM a b).map (splR (F := F) (E := E)).symm

theorem glM_mul (a a' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b b' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    glM a b * glM a' b' = glM (a * a') (b * b') := by
  unfold glM
  rw [← prM_mul]
  exact (Matrix.map_mul (f := ((splR (F := F) (E := E)).symm : (Ainf F ⊗[F] E) × (Af F ⊗[F] E) →+* AF F ⊗[F] E))).symm

theorem glM_one : glM (1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) = 1 := by
  unfold glM
  rw [prM_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem glM_fst (a : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    (glM a b).map (tensMap (E := E) (fstA F)) = a := by
  ext i j
  simp [glM, prM, fst_splR_symm]

theorem glM_snd (a : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    (glM a b).map (tensMap (E := E) (sndA F)) = b := by
  ext i j
  simp [glM, prM, snd_splR_symm]

theorem mat_ext_spl {X Y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    (h1 : X.map (tensMap (E := E) (fstA F)) = Y.map (tensMap (E := E) (fstA F)))
    (h2 : X.map (tensMap (E := E) (sndA F)) = Y.map (tensMap (E := E) (sndA F))) : X = Y := by
  ext i j
  apply splT_bijective.1
  rw [splT_apply, splT_apply]
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def glPair (g₁ : GL (Fin n) (Ainf F ⊗[F] E)) (g₂ : GL (Fin n) (Af F ⊗[F] E)) :
    GL (Fin n) (AF F ⊗[F] E) where
  val := glM (g₁ : Matrix _ _ _) (g₂ : Matrix _ _ _)
  inv := glM ((g₁⁻¹ : GL (Fin n) _) : Matrix _ _ _) ((g₂⁻¹ : GL (Fin n) _) : Matrix _ _ _)
  val_inv := by rw [glM_mul, Units.mul_inv, Units.mul_inv, glM_one]
  inv_val := by rw [glM_mul, Units.inv_mul, Units.inv_mul, glM_one]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem JR_map (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') :
    (JR R J).map (tensMap (E := E) φ) = JR R' J := by
  ext i j
  simp [JR, tensMap_inclR]

theorem unit_map (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    (Formalism.UG.cT (sigR R σ) X * JR R J * X).map (tensMap (E := E) φ) =
      Formalism.UG.cT (sigR R' σ) (X.map (tensMap φ)) * JR R' J * X.map (tensMap φ) := by
  rw [Matrix.map_mul, Matrix.map_mul, ← Formalism.UG.P.incl_cT_map (sigR R σ) (sigR R' σ) (tensMap φ)
    (tensMap_sigR φ σ), JR_map]

theorem glPair_mem (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J) :
    glPair (HA.mat _ σ J g₁) (HA.mat _ σ J g₂) ∈ HR (AF F) σ J := by
  have h1 : Formalism.UG.cT (sigR (Ainf F) σ) (HA.mat _ σ J g₁ : Matrix (Fin n) (Fin n) _) * JR (Ainf F) J *
      (HA.mat _ σ J g₁ : Matrix (Fin n) (Fin n) _) = JR (Ainf F) J := g₁.2
  have h2 : Formalism.UG.cT (sigR (Af F) σ) (HA.mat _ σ J g₂ : Matrix (Fin n) (Fin n) _) * JR (Af F) J *
      (HA.mat _ σ J g₂ : Matrix (Fin n) (Fin n) _) = JR (Af F) J := g₂.2
  show Formalism.UG.cT (sigR (AF F) σ) (glM _ _) * JR (AF F) J * glM _ _ = JR (AF F) J
  apply mat_ext_spl
  · rw [unit_map, glM_fst, h1, JR_map]
  · rw [unit_map, glM_snd, h2, JR_map]

def haPair (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J) : HA (AF F) σ J :=
  (⟨glPair (HA.mat _ σ J g₁) (HA.mat _ σ J g₂), glPair_mem σ J g₁ g₂⟩ : HR (AF F) σ J)

theorem haMap_fst_haPair (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J) :
    haMap σ J (fstA F) (haPair σ J g₁ g₂) = g₁ := by
  apply Subtype.ext
  apply Units.ext
  exact glM_fst _ _

theorem haMap_snd_haPair (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J) :
    haMap σ J (sndA F) (haPair σ J g₁ g₂) = g₂ := by
  apply Subtype.ext
  apply Units.ext
  exact glM_snd _ _

theorem splitA_haPair (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J) :
    splitA σ J (haPair σ J g₁ g₂) = (g₁, g₂) :=
  Prod.ext (haMap_fst_haPair σ J g₁ g₂) (haMap_snd_haPair σ J g₁ g₂)

theorem continuous_HA_iff {R X : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [TopologicalSpace X] {f : X → HA R σ J} :
    Continuous f ↔ Continuous (fun x => Units.val (HA.mat R σ J (f x))) ∧
      Continuous (fun x => Units.val (HA.mat R σ J (f x))⁻¹) := by
  have hi : Topology.IsInducing (fun g : HA R σ J => HA.mat R σ J g) :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : HR R σ J → _))
  rw [hi.continuous_iff]
  exact Units.continuous_iff

theorem continuous_haPair :
    Continuous (fun p : HA (Ainf F) σ J × HA (Af F) σ J => haPair σ J p.1 p.2) := by
  have hm1 : Continuous fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
      Units.val (HA.mat _ σ J p.1) :=
    ((continuous_HA_iff σ J).1 continuous_id).1.comp continuous_fst
  have hm2 : Continuous fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
      Units.val (HA.mat _ σ J p.2) :=
    ((continuous_HA_iff σ J).1 continuous_id).1.comp continuous_snd
  have hi1 : Continuous fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
      Units.val (HA.mat _ σ J p.1)⁻¹ :=
    ((continuous_HA_iff σ J).1 continuous_id).2.comp continuous_fst
  have hi2 : Continuous fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
      Units.val (HA.mat _ σ J p.2)⁻¹ :=
    ((continuous_HA_iff σ J).1 continuous_id).2.comp continuous_snd
  have hglM : ∀ {X : Type} [TopologicalSpace X] {a : X → Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)}
      {b : X → Matrix (Fin n) (Fin n) (Af F ⊗[F] E)}, Continuous a → Continuous b →
      Continuous fun x => glM (a x) (b x) := by
    intro X _ a b ha hb
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x => (splH (F := F) (E := E)).symm (a x i j, b x i j)
    exact splH.symm.continuous.comp
      (((continuous_apply j).comp ((continuous_apply i).comp ha)).prodMk
        ((continuous_apply j).comp ((continuous_apply i).comp hb)))
  rw [continuous_HA_iff]
  exact ⟨hglM hm1 hm2, hglM hi1 hi2⟩

variable {σ J}

theorem splitEquiv (K₁ : Subgroup (HA (Ainf F) σ J)) (K₂ : Subgroup (HA (Af F) σ J))
    (K : Subgroup (HA (AF F) σ J)) (hinj : Function.Injective (splitA σ J))
    (hc1 : Continuous (haMap σ J (fstA F))) (hc2 : Continuous (haMap σ J (sndA F)))
    (hmem : ∀ g, g ∈ K ↔ haMap σ J (fstA F) g ∈ K₁ ∧ haMap σ J (sndA F) g ∈ K₂) :
    ∃ e : (K₁ × K₂) ≃ₜ* K,
      ∀ p, splitA σ J (e p : HA (AF F) σ J) = ((p.1 : HA (Ainf F) σ J), (p.2 : HA (Af F) σ J)) := by
  have hK : ∀ p : K₁ × K₂, haPair σ J p.1 p.2 ∈ K := fun p =>
    (hmem _).2 ⟨by rw [haMap_fst_haPair]; exact p.1.2, by rw [haMap_snd_haPair]; exact p.2.2⟩
  let e : (K₁ × K₂) ≃ₜ* K :=
    { toFun := fun p => ⟨haPair σ J p.1 p.2, hK p⟩
      invFun := fun k => (⟨haMap σ J (fstA F) k, ((hmem k).1 k.2).1⟩,
        ⟨haMap σ J (sndA F) k, ((hmem k).1 k.2).2⟩)
      left_inv := fun p => Prod.ext (Subtype.ext (haMap_fst_haPair σ J _ _))
        (Subtype.ext (haMap_snd_haPair σ J _ _))
      right_inv := fun k => Subtype.ext (hinj (by rw [splitA_haPair]; rfl))
      map_mul' := fun p q => Subtype.ext (hinj (by
        rw [Subgroup.coe_mul, map_mul, splitA_haPair, splitA_haPair, splitA_haPair]
        rfl))
      continuous_toFun := ((continuous_haPair σ J).comp
        (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _
      continuous_invFun := ((hc1.comp continuous_subtype_val).subtype_mk _).prodMk
        ((hc2.comp continuous_subtype_val).subtype_mk _) }
  exact ⟨e, fun p => splitA_haPair σ J _ _⟩

end Split

end PI.UnitaryGroupMassFormula.MeasWCore
