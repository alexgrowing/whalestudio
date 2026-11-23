import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRightStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def idemInf : AF F := LinearMap.inl F (Ainf F) (Af F) 1

def idemSet (S : Finset (Pl F)) : AF F := ∑ w ∈ S, idemAt w

theorem evI_eq (a : AF F) : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F a) := rfl

theorem evFin_idemInf (w : Pl F) : evFin F w (idemInf F) = 0 := by
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (0 : Af F) = 0
  exact map_zero _

theorem fstA_idemInf : fstA F (idemInf F) = 1 := rfl

theorem fstA_idemAt (w : Pl F) : fstA F (idemAt w) = 0 := rfl

theorem fstA_idemSet (S : Finset (Pl F)) : fstA F (idemSet S) = 0 := by
  unfold idemSet
  rw [map_sum]
  exact Finset.sum_eq_zero fun w _ => fstA_idemAt w

theorem evFin_idemAt_ne {w w' : Pl F} (h : w' ≠ w) : evFin F w' (idemAt w) = 0 := by
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w' (singleFin w 1) = 0
  exact evalV_singleFin_ne h 1

theorem idemAt_mul_ne {w w' : Pl F} (h : w' ≠ w) : idemAt w * idemAt w' = 0 :=
  mul_idemAt_of_evFin w' (evFin_idemAt_ne h)

theorem evFin_idemSet_mem {S : Finset (Pl F)} {w : Pl F} (hw : w ∈ S) : evFin F w (idemSet S) = 1 := by
  classical
  unfold idemSet
  rw [map_sum, Finset.sum_eq_single w (fun w' _ hne => evFin_idemAt_ne (Ne.symm hne)) (fun h => absurd hw h),
    evFin_idemAt]

theorem evFin_idemSet_not_mem {S : Finset (Pl F)} {w : Pl F} (hw : w ∉ S) : evFin F w (idemSet S) = 0 := by
  unfold idemSet
  rw [map_sum]
  exact Finset.sum_eq_zero fun w' hw' => evFin_idemAt_ne (by rintro rfl; exact hw hw')

theorem idemSet_mul_self (S : Finset (Pl F)) : idemSet S * idemSet S = idemSet S := by
  classical
  unfold idemSet
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single w (fun w' _ hne => idemAt_mul_ne hne) (fun h => absurd hw h),
    idemAt_mul_self]

theorem mul_idemSet_of {S : Finset (Pl F)} {u : AF F} (hu : ∀ w ∈ S, evFin F w u = 0) : u * idemSet S = 0 := by
  unfold idemSet
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun w hw => mul_idemAt_of_evFin w (hu w hw)

theorem idemInf_mul_idemSet (S : Finset (Pl F)) : idemInf F * idemSet S = 0 :=
  mul_idemSet_of fun w _ => evFin_idemInf w

theorem idemInf_mul_self : idemInf F * idemInf F = idemInf F :=
  Prod.ext (show (1 : Ainf F) * 1 = 1 from one_mul 1) (show (0 : Af F) * 0 = 0 from mul_zero 0)

theorem mul_idemInf_of_evI {u : AF F} (hu : evI F u = 0) : u * idemInf F = 0 := by
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ (show u.2 * (0 : Af F) = 0 from mul_zero _)
  change fstA F u * 1 = 0
  rw [h1, zero_mul]

end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mixM {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  e • G + (1 - e) • 1

theorem mixM_one_left {n : ℕ} (G : Matrix (Fin n) (Fin n) (AE F E)) : mixM 1 G = G := by
  simp [mixM]

theorem mixM_one_right {n : ℕ} (e : AF F) : mixM e (1 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [mixM, ← add_smul, add_sub_cancel, one_smul]

theorem mixM_sub_one {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : mixM e G - 1 = e • (G - 1) := by
  rw [mixM, smul_sub, sub_smul, one_smul]
  abel

theorem mixM_mul_same {n : ℕ} {e : AF F} (he : e * e = e) (G G' : Matrix (Fin n) (Fin n) (AE F E)) :
    mixM e G * mixM e G' = mixM e (G * G') := by
  rw [mixM, mixM, mixM, mix_mul he, mul_one]

theorem mixM_mul_orth {n : ℕ} {e f : AF F} (hef : e * f = 0) (G : Matrix (Fin n) (Fin n) (AE F E)) :
    mixM e G * mixM f G = mixM (e + f) G := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by rw [sub_mul, one_mul, mul_sub, mul_one, hef]; ring
  simp only [mixM, Matrix.add_mul, Matrix.mul_add, smul_mul_smul_comm, h1, h2, h3, hef, zero_smul, zero_add, mul_one,
    one_mul, add_smul]
  abel

theorem mixM_mul_of_smul {n d : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E))
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : e • γ = 0) : mixM (1 - e) G * γ = G * γ := by
  have h1 : e • (G * γ) = 0 := by rw [← Matrix.mul_smul, hγ, Matrix.mul_zero]
  rw [mixM, sub_sub_cancel, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hγ, add_zero, sub_smul, one_smul, h1,
    sub_zero]

theorem mul_mixM_of_smul {n d : ℕ} (e : AF F) (H : Matrix (Fin d) (Fin d) (AE F E))
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : e • γ = 0) : γ * (mixM (1 - e) H)ᵀ = γ * Hᵀ := by
  have h1 : e • (γ * Hᵀ) = 0 := by rw [← Matrix.smul_mul, hγ, Matrix.zero_mul]
  rw [mixM, sub_sub_cancel, transpose_add, transpose_smul, transpose_smul, transpose_one, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, hγ, add_zero, sub_smul, one_smul, h1, sub_zero]

variable {σ : E →ₐ[F] E}

theorem mixM_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AF F} (he : e * e = e) (g : UA σ J) :
    (mixM e (mat g))ᵀ * incM F J * (mixM e (mat g)).map (cA σ) = incM F J := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  have hT : (mixM e (mat g))ᵀ = e • (mat g)ᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mixM, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have hc : (mixM e (mat g)).map (cA σ) = e • (mat g).map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← AlgHom.mapMatrix_apply, mixM, map_add, map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
  rw [hT, hc, split (incM F J), mix_mul he, mix_mul he, hg, one_mul, mul_one]

def mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨mixM e (mat g), mixM e (mat g⁻¹),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.mul_inv g.1)).trans (mixM_one_right e),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.inv_mul g.1)).trans (mixM_one_right e)⟩,
    mixM_mem he g⟩

theorem mat_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g) = mixM e (mat g) := rfl

theorem mat_inv_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g)⁻¹ = mixM e (mat g⁻¹) := rfl

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) : mat (x * y) = mat x * mat y := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : UA σ J) : mat x⁻¹ * mat x = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_injective {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : UA σ J} (h : mat x = mat y) : x = y :=
  Subtype.ext (Units.ext h)

end GlobalTheory.UnitaryTriSplit

namespace GlobalTheory.UnitaryTriSplit
theorem finite_bad {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (M : Matrix (Fin n) (Fin n) (AE F E)) (N : Matrix (Fin d) (Fin d) (AE F E)) :
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, M * γ * Matrix.transpose N ∈ latAtV X Y w} := by
  refine (((GlobalTheory.T.lattice_stable_almost_all_places_left) F E n d X Y hX M).union ((GlobalTheory.T.lattice_stable_almost_all_places_right) F E n d X Y hY N)).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hw fun γ hγ => hc.2 _ (hc.1 γ hγ)
end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

theorem factor_away : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl F)) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh φ hφ
  classical
  have hX := hT.geo.hV'.lat
  have hY := hT.geo.hW.lat
  have hfin := ((Filter.eventually_cofinite.1 hφ).union (finite_bad G.V' G.W hX hY (mat g) (mat h))).union
    (finite_bad G.V' G.W hX hY (mat g⁻¹) (mat h⁻¹))
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Pl F), S = hfin.toFinset.erase v := ⟨_, rfl⟩
  have hout : ∀ w, w ≠ v → w ∉ S → w ∉ hfin.toFinset := fun w hwv hwS hm =>
    hwS (hSdef ▸ Finset.mem_erase.2 ⟨hwv, hm⟩)
  obtain ⟨e₁, e₂, h11, h22, h12, hI1, hS2, hfst1, hfst2, hevS, hevN⟩ : ∃ e₁ e₂ : AF F, e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧
      e₁ * e₂ = 0 ∧ (∀ u, evI F u = 0 → u * e₁ = 0) ∧ (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u * e₂ = 0) ∧
      fstA F e₁ = 1 ∧ fstA F e₂ = 0 ∧ (∀ w ∈ S, evFin F w (e₁ + e₂) = 1) ∧ (∀ w ∉ S, evFin F w (e₁ + e₂) = 0) :=
    ⟨idemInf F, idemSet S, idemInf_mul_self, idemSet_mul_self S, idemInf_mul_idemSet S, fun u hu => mul_idemInf_of_evI hu,
      fun u hu => mul_idemSet_of hu, fstA_idemInf, fstA_idemSet S,
      fun w hw => by rw [map_add, evFin_idemInf, evFin_idemSet_mem hw, zero_add],
      fun w hw => by rw [map_add, evFin_idemInf, evFin_idemSet_not_mem hw, zero_add]⟩
  obtain ⟨e, he⟩ : ∃ e, e₁ + e₂ = e := ⟨_, rfl⟩
  have hee : e * e = e := by
    rw [← he, add_mul, mul_add, mul_add, h11, h22, h12, mul_comm e₂ e₁, h12, zero_add, add_zero]
  have h33 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have he3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hevI : evI F (1 - e) = 0 := by
    rw [evI_eq, map_sub, map_one, ← he, map_add, hfst1, hfst2, add_zero, sub_self, map_zero]
  rw [he] at hevS hevN
  have hevS' : ∀ w ∈ S, evFin F w (1 - e) = 0 := fun w hw => by rw [map_sub, map_one, hevS w hw, sub_self]
  refine ⟨S, mixU e₁ h11 g, mixU e₂ h22 g, mixU (1 - e) h33 g, mixU e₁ h11 h, mixU e₂ h22 h, mixU (1 - e) h33 h,
    by rw [hSdef]; exact Finset.notMem_erase v _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mat_injective ?_
    rw [mat_mul, mat_mul, mat_mixU, mat_mixU, mat_mixU, mixM_mul_orth h12, he, mixM_mul_orth he3, add_sub_cancel,
      mixM_one_left]
  · refine mat_injective ?_
    rw [mat_mul, mat_mul, mat_mixU, mat_mixU, mat_mixU, mixM_mul_orth h12, he, mixM_mul_orth he3, add_sub_cancel,
      mixM_one_left]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hI1 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hI1 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hS2 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hS2 u hu, zero_smul]
  · intro u hu
    have h0 : (1 - e) • u = 0 := hu (1 - e) hevI
    rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · intro u hu
    have h0 : (1 - e) • u = 0 := hu (1 - e) hevI
    rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · rintro w (rfl | hw) u hu
    · rw [mat_mixU, mixM_sub_one, smul_smul]
      refine hg _ fun u' hu' => ?_
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u' u, hu u' hu', zero_mul]
    · have h0 : (1 - e) • u = 0 := hu (1 - e) (hevS' w hw)
      rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · rintro w (rfl | hw) u hu
    · rw [mat_mixU, mixM_sub_one, smul_smul]
      refine hh _ fun u' hu' => ?_
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u' u, hu u' hu', zero_mul]
    · have h0 : (1 - e) • u = 0 := hu (1 - e) (hevS' w hw)
      rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · intro w hwv hwS γ
    have hw' := hout w hwv hwS
    rw [Set.Finite.mem_toFinset] at hw'
    have good1 : ∀ γ ∈ latAtV G.V' G.W w, mat g * γ * (mat h)ᵀ ∈ latAtV G.V' G.W w := by
      by_contra hc; exact hw' (Or.inl (Or.inr hc))
    have good2 : ∀ γ ∈ latAtV G.V' G.W w, mat g⁻¹ * γ * (mat h⁻¹)ᵀ ∈ latAtV G.V' G.W w := by
      by_contra hc; exact hw' (Or.inr hc)
    have hsm : ∀ γ ∈ latAtV G.V' G.W w, e • γ = 0 := fun γ hγ =>
      (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1 γ hγ e (hevN w hwS)
    constructor
    · intro hδ
      have hδe := hsm _ hδ
      have key : γ = mat (mixU (1 - e) h33 g)⁻¹ * (mat (mixU (1 - e) h33 g) * γ * (mat (mixU (1 - e) h33 h))ᵀ) *
          (mat (mixU (1 - e) h33 h)⁻¹)ᵀ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
          ← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one, Matrix.mul_one]
      rw [key, mat_inv_mixU, mat_inv_mixU, mixM_mul_of_smul e _ hδe,
        mul_mixM_of_smul e _ (by rw [← Matrix.mul_smul, hδe, Matrix.mul_zero])]
      exact good2 _ hδ
    · intro hγ
      rw [mat_mixU, mat_mixU, mixM_mul_of_smul e _ (hsm γ hγ),
        mul_mixM_of_smul e _ (by rw [← Matrix.mul_smul, hsm γ hγ, Matrix.mul_zero])]
      exact good1 γ hγ
  · intro w hwv hwS
    have hw' := hout w hwv hwS
    rw [Set.Finite.mem_toFinset] at hw'
    by_contra hc
    exact hw' (Or.inl (Or.inl hc))

end GlobalTheory.UnitaryTriSplit
