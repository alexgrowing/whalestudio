import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct Matrix

section E

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def datE : PG.Dat E (Fin M) r where
  σA := (σ : E →+* E)
  JA := J
  e := P.e
  f := P.f
  z := P.z
  tz := (algebraMap F E (-T))⁻¹

variable {σ J P T}

theorem datE_hyp (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datE σ J P T).Hyp := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hP
  refine ⟨fun x => ?_, fun i j => ?_, hee, hff, hef, hez, hfz, ?_⟩
  · show σ (σ x) = x
    exact hσσ x
  · show σ (J j i) = J i j
    exact hJ.1 i j
  · show (algebraMap F E (-T))⁻¹ * hE σ J P.z P.z = 1
    rw [hzz, inv_mul_cancel₀]
    rw [Ne, map_eq_zero_iff _ (algebraMap F E).injective, neg_eq_zero]
    exact hT

variable (R : Type) [CommRing R] [Algebra F R]

theorem ratV_sub' (x y : Fin M → E) :
    ratV (F := F) R (x - y) = ratV (F := F) R x - ratV (F := F) R y := by
  funext i; simp [ratV]

theorem ratV_add' (x y : Fin M → E) :
    ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV]

theorem ratV_pX (v : Fin M → E) :
    (datR R σ J P T).pX (ratV (F := F) R v) = ratV (F := F) R ((datE σ J P T).pX v) := by
  rw [PG.Dat.pX_apply, PG.Dat.pX_apply]
  show ∑ a, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R v) • ratV (F := F) R (P.e a) =
    ratV (F := F) R (∑ a, hE σ J (P.f a) v • P.e a)
  simp only [hR_ratV]
  funext i
  simp [ratV, Finset.sum_apply, map_sum]

theorem ratV_pXv (v : Fin M → E) :
    (datR R σ J P T).pXv (ratV (F := F) R v) = ratV (F := F) R ((datE σ J P T).pXv v) := by
  rw [PG.Dat.pXv_apply, PG.Dat.pXv_apply]
  show ∑ a, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R v) • ratV (F := F) R (P.f a) =
    ratV (F := F) R (∑ a, hE σ J (P.e a) v • P.f a)
  simp only [hR_ratV]
  funext i
  simp [ratV, Finset.sum_apply, map_sum]

theorem ratV_pz (v : Fin M → E) :
    (datR R σ J P T).pz (ratV (F := F) R v) = ratV (F := F) R ((datE σ J P T).pz v) := by
  rw [PG.Dat.pz_apply, PG.Dat.pz_apply]
  show (inclR (F := F) R ((algebraMap F E (-T))⁻¹) * hR R σ J (ratV (F := F) R P.z)
      (ratV (F := F) R v)) • ratV (F := F) R P.z =
    ratV (F := F) R (((algebraMap F E (-T))⁻¹ * hE σ J P.z v) • P.z)
  simp only [hR_ratV]
  funext i
  simp [ratV, map_mul]

theorem ratV_pU (v : Fin M → E) :
    (datR R σ J P T).pU (ratV (F := F) R v) = ratV (F := F) R ((datE σ J P T).pU v) := by
  rw [PG.Dat.pU_apply, PG.Dat.pU_apply, ratV_pX, ratV_pXv, ratV_pz, ratV_add', ratV_add']

theorem ratV_pW (v : Fin M → E) :
    (datR R σ J P T).pW (ratV (F := F) R v) = ratV (F := F) R ((datE σ J P T).pW v) := by
  rw [PG.Dat.pW_apply, PG.Dat.pW_apply, ratV_pU, ratV_sub']

theorem ratV_mulVec' (Q : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    ratV (F := F) R (Q *ᵥ x) = (Q.map (inclR (F := F) R)) *ᵥ ratV (F := F) R x := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) R) Q x i

theorem lin_rat (g : HA R σ J) (γ : GL (Fin M) E)
    (hγ : Formalism.UG.bc (inclR (F := F) R) γ = (g : HR R σ J).1) (x : Fin M → E) :
    lin R σ J g (ratV (F := F) R x) = ratV (F := F) R ((γ : Matrix (Fin M) (Fin M) E) *ᵥ x) := by
  rw [ratV_mulVec']
  show (((g : HR R σ J).1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ _ = _
  rw [← hγ]
  rfl

theorem Pi_rat (g : HA R σ J) (γ : GL (Fin M) E)
    (hγ : Formalism.UG.bc (inclR (F := F) R) γ = (g : HR R σ J).1) (v : Fin M → E) :
    (datR R σ J P T).Pi (lin R σ J g) (ratV (F := F) R v) =
      ratV (F := F) R ((datE σ J P T).Pi (Matrix.mulVecLin (γ : Matrix (Fin M) (Fin M) E)) v) := by
  rw [PG.Dat.Pi_apply, PG.Dat.Pi_apply, ratV_pW, lin_rat R g γ hγ, ratV_pW, ratV_pU, ratV_add']
  rfl

theorem single_rat (j : Fin M) :
    (Pi.single j 1 : Fin M → R ⊗[F] E) = ratV (F := F) R (Pi.single j 1) := by
  funext k
  by_cases h : k = j
  · subst h; simp [ratV]
  · simp [ratV, h]

end E

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem piG_rat (hinj : Function.Injective (inclR (F := F) R : E →+* R ⊗[F] E))
    (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (g : HA R σ J) (hg : g ∈ S0 R σ J P) (hr : g ∈ HFinIn R σ J) :
    piG hσσ hJ hP g hg ∈ HFinIn R σ J := by
  obtain ⟨γ, hγU, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hr)
  have H := datE_hyp hσσ hJ hP
  have hrinj : Function.Injective (ratV (F := F) R : (Fin M → E) → Fin M → R ⊗[F] E) := by
    intro x y h
    funext i
    exact hinj (congrFun h i)
  have hUJ : ∀ δ ∈ Formalism.UG.UJ (σ : E →+* E) J,
      (datE σ J P T).Uni (Matrix.mulVecLin (δ : Matrix (Fin M) (Fin M) E)) := by
    intro δ hδ x y
    show Formalism.UG.hform (σ : E →+* E) J (_ *ᵥ x) (_ *ᵥ y) = Formalism.UG.hform (σ : E →+* E) J x y
    rw [Formalism.UG.P.hform_mulVec]
    have : Formalism.UG.cT (σ : E →+* E) (δ : Matrix (Fin M) (Fin M) E) * J *
        (δ : Matrix (Fin M) (Fin M) E) = J := hδ
    rw [this]
  have hfix : ∀ w, lin R σ J g (ratV (F := F) R w) = ratV (F := F) R w →
      (γ : Matrix (Fin M) (Fin M) E) *ᵥ w = w := by
    intro w hw
    rw [lin_rat R g γ hγ] at hw
    exact hrinj hw
  have hFe : (datE σ J P T).FixEZ (Matrix.mulVecLin (γ : Matrix (Fin M) (Fin M) E)) :=
    ⟨fun a => hfix _ (stabilizer_fixes_frame_vector R σ J P hg a), hfix _ (stabilizer_fixes_normal_vector hg)⟩
  have hinv : ∀ w, (γ : Matrix (Fin M) (Fin M) E) *ᵥ w = w →
      ((γ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ w = w := by
    intro w hw
    conv_lhs => rw [← hw]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hFe' : (datE σ J P T).FixEZ
      (Matrix.mulVecLin ((γ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) :=
    ⟨fun a => hinv _ (hFe.1 a), hinv _ hFe.2⟩
  let S := Matrix.mulVecLin (γ : Matrix (Fin M) (Fin M) E)
  let S' := Matrix.mulVecLin ((γ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
  have hSS' : S ∘ₗ S' = LinearMap.id := by
    apply LinearMap.ext; intro v
    simp only [S, S', LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply]
  have hS'S : S' ∘ₗ S = LinearMap.id := by
    apply LinearMap.ext; intro v
    simp only [S, S', LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply]
  have hc1 : (datE σ J P T).Pi S ∘ₗ (datE σ J P T).Pi S' = LinearMap.id := by
    apply LinearMap.ext; intro v
    rw [LinearMap.comp_apply, PG.Dat.Pi_comp H hFe.1 hFe' (hUJ _ ((Formalism.UG.UJ _ J).inv_mem hγU)),
      hSS', PG.Dat.Pi_id H]
    rfl
  have hc2 : (datE σ J P T).Pi S' ∘ₗ (datE σ J P T).Pi S = LinearMap.id := by
    apply LinearMap.ext; intro v
    rw [LinearMap.comp_apply, PG.Dat.Pi_comp H hFe'.1 hFe (hUJ _ hγU), hS'S, PG.Dat.Pi_id H]
    rfl
  let γ' : GL (Fin M) E :=
    { val := LinearMap.toMatrix' ((datE σ J P T).Pi S)
      inv := LinearMap.toMatrix' ((datE σ J P T).Pi S')
      val_inv := by rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
      inv_val := by rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id] }
  have hγ'U : γ' ∈ Formalism.UG.UJ (σ : E →+* E) J := by
    show Formalism.UG.cT (σ : E →+* E) (LinearMap.toMatrix' ((datE σ J P T).Pi S)) * J *
      LinearMap.toMatrix' ((datE σ J P T).Pi S) = J
    apply uj_of_uni
    intro x y
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact PG.Dat.Pi_uni H hFe (hUJ _ hγU) x y
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ', hγ'U, Units.ext ?_⟩)
  show (LinearMap.toMatrix' ((datE σ J P T).Pi S)).map (inclR (F := F) R) =
    piMat (P := P) (T := T) g
  ext i j
  rw [Matrix.map_apply, piMat, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply,
    single_rat R j, Pi_rat R g γ hγ]
  rfl

end Main

theorem projection_preserves_rational : PiRat := by
  intro F E _ _ _ _ _ σ M J r P T hσσ hJ hP g hg hr
  have hinj : Function.Injective (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective _ _)
  exact piG_rat hinj hσσ hJ hP g hg hr

end PI.VolSemiDirect.W
