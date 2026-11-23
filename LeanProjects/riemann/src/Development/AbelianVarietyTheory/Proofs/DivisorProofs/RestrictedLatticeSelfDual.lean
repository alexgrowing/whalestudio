import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRestrictDual

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_map_mulVec {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) (y : Fin b → R ⊗[F] E) :
    (fun i => sigR R σ ((A.map (inclR R) *ᵥ y) i)) =
      (fun k => sigR R σ (y k)) ᵥ* (Formalism.UG.cT (σ : E →+* E) A).map (inclR R) := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.map_apply,
    Matrix.transpose_apply, sigR_inclR, RingHom.coe_coe]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hLin_eq_dot {a : ℕ} (J : Matrix (Fin a) (Fin a) E) (y x : Fin a → R ⊗[F] E) :
    hLin σ J R y x = (fun i => sigR R σ (x i)) ⬝ᵥ (J.map (inclR R) *ᵥ y) := by
  simp only [hLin, hR, Formalism.UG.hform, JR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hLin_map_mulVec {a b c : ℕ} (J : Matrix (Fin a) (Fin a) E) (A : Matrix (Fin a) (Fin b) E)
    (C : Matrix (Fin a) (Fin c) E) (y : Fin c → R ⊗[F] E) (x : Fin b → R ⊗[F] E) :
    hLin σ J R (C.map (inclR R) *ᵥ y) (A.map (inclR R) *ᵥ x) =
      (fun i => sigR R σ (x i)) ⬝ᵥ ((Formalism.UG.cT (σ : E →+* E) A * J * C).map (inclR R) *ᵥ y) := by
  rw [hLin_eq_dot, sigR_map_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem map_mulVec_tmul {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) (c : R) (x : Fin b → E) :
    A.map (inclR R) *ᵥ (fun i => c ⊗ₜ[F] x i) = fun i => c ⊗ₜ[F] (A *ᵥ x) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

end Local

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_mulVec_mem_latLoc {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) {L : Submodule (𝓞 E) (Fin b → E)}
    {L' : Submodule (𝓞 E) (Fin a → E)} (hA : ∀ z ∈ L, A *ᵥ z ∈ L') (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {y : Fin b → Fv F v ⊗[F] E} (hy : y ∈ latLoc F L v) : A.map (inclR (Fv F v)) *ᵥ y ∈ latLoc F L' v := by
  refine latLoc_induction (p := fun y => A.map (inclR (Fv F v)) *ᵥ y ∈ latLoc F L' v)
    (fun c hc x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · rw [map_mulVec_tmul]; exact tmul_mem_latLoc hc (hA x hx)
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · rw [Matrix.mulVec_add]; exact add_mem hy hz
  · rw [Matrix.mulVec_neg]; exact neg_mem hy

end Lat

end GlobalTheory.EisRestrictDual

namespace GlobalTheory.EisRestrictDual

section Glob

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem hRight_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) : hRight σ J x z = hE σ J x z := rfl

theorem hE_sub_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z w u : Fin n → E) (c : E) :
    hE σ J (z - c • w) u = hE σ J z u - σ c * hE σ J w u := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, RingHom.coe_coe,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem hE_mulVec {a b c : ℕ} (J : Matrix (Fin a) (Fin a) E) (A : Matrix (Fin a) (Fin b) E)
    (C : Matrix (Fin a) (Fin c) E) (α : Fin b → E) (β : Fin c → E) :
    hE σ J (A *ᵥ α) (C *ᵥ β) = (fun i => σ (α i)) ⬝ᵥ ((Formalism.UG.cT (σ : E →+* E) A * J * C) *ᵥ β) := by
  have hs : (fun i => σ ((A *ᵥ α) i)) = (fun k => σ (α k)) ᵥ* Formalism.UG.cT (σ : E →+* E) A := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, map_sum, map_mul, Matrix.transpose_apply,
      Matrix.map_apply, RingHom.coe_coe]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hE_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem matrix_ext_of_hE {b c : ℕ} {M N : Matrix (Fin b) (Fin c) E}
    (h : ∀ (α : Fin b → E) (β : Fin c → E), (fun i => σ (α i)) ⬝ᵥ (M *ᵥ β) = (fun i => σ (α i)) ⬝ᵥ (N *ᵥ β)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have e : (fun k => σ ((Pi.single i 1 : Fin b → E) k)) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one, single_dotProduct, single_dotProduct] at this
  simpa using this

end Glob

end GlobalTheory.EisRestrictDual

namespace GlobalTheory.EisRestrictDual

open GlobalTheory.EisMidHt (firstColumn)

section Frame

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem sig_single_dotProduct {b c : ℕ} (M : Matrix (Fin b) (Fin c) E) (i : Fin b) (j : Fin c) :
    (fun k => σ ((Pi.single i 1 : Fin b → E) k)) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  have e : (fun k => σ ((Pi.single i 1 : Fin b → E) k)) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [e, Matrix.mulVec_single_one, single_dotProduct, one_mul]
  rfl

theorem hE_firstColumn {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin (r + 1)) E)
    (C : Matrix (Fin n) (Fin (s + 1)) E) :
    hE σ J (firstColumn A) (firstColumn C) = (Formalism.UG.cT (σ : E →+* E) A * J * C) 0 0 := by
  have := hE_mulVec σ J A C (Pi.single 0 1) (Pi.single 0 1)
  rw [sig_single_dotProduct, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  exact this

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)

def projOrthogonal : (Fin n → E) →ₗ[E] (Fin n → E) :=
  LinearMap.id - (hRight σ J (firstColumn Y)).smulRight (firstColumn X) - (hRight σ J (firstColumn X)).smulRight (firstColumn Y)

theorem projOrthogonal_apply (z : Fin n → E) :
    projOrthogonal σ J X Y z = z - hE σ J (firstColumn Y) z • firstColumn X - hE σ J (firstColumn X) z • firstColumn Y := rfl

def lInv : (Fin n → E) →ₗ[E] (Fin (dim σ J X Y) → E) :=
  (LinearMap.exists_leftInverse_of_injective (ι σ J X Y) (LinearMap.ker_eq_bot.2 (ι_injective σ J X Y))).choose

theorem lInv_ι (u : Fin (dim σ J X Y) → E) : lInv σ J X Y (ι σ J X Y u) = u :=
  LinearMap.congr_fun
    (LinearMap.exists_leftInverse_of_injective (ι σ J X Y) (LinearMap.ker_eq_bot.2 (ι_injective σ J X Y))).choose_spec u

def T : Matrix (Fin (dim σ J X Y)) (Fin n) E := LinearMap.toMatrix' ((lInv σ J X Y).comp (projOrthogonal σ J X Y))

theorem T_mulVec (z : Fin n → E) : T σ J X Y *ᵥ z = lInv σ J X Y (projOrthogonal σ J X Y z) :=
  LinearMap.toMatrix'_mulVec _ z

theorem projOrthogonal_incl (u : Fin (dim σ J X Y) → E) : projOrthogonal σ J X Y (ι σ J X Y u) = ι σ J X Y u := by
  have h := ι_mem σ J X Y u
  rw [mem_invariant_forms] at h
  rw [projOrthogonal_apply, h.1, h.2, zero_smul, zero_smul, sub_zero, sub_zero]

theorem T_mul_P : T σ J X Y * P σ J X Y = 1 := by
  have h : ∀ u, (T σ J X Y * P σ J X Y) *ᵥ u = u := fun u => by
    rw [← Matrix.mulVec_mulVec, ← ι_apply, T_mulVec, projOrthogonal_incl, lInv_ι]
  exact Matrix.toLin'.injective (LinearMap.ext fun u => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, h])

variable {σ J X Y}

section Witt

variable (hxx : hE σ J (firstColumn X) (firstColumn X) = 0) (hyy : hE σ J (firstColumn Y) (firstColumn Y) = 0)
  (hxy : hE σ J (firstColumn X) (firstColumn Y) = 1) (hyx : hE σ J (firstColumn Y) (firstColumn X) = 1)
include hxx hyy hxy hyx

theorem projOrthogonal_mem (z : Fin n → E) : projOrthogonal σ J X Y z ∈ V0 σ J X Y := by
  rw [mem_invariant_forms, projOrthogonal_apply]
  constructor
  · rw [← hRight_apply σ, map_sub, map_sub, map_smul, map_smul, hRight_apply, hRight_apply, hRight_apply, hxx, hxy]
    simp
  · rw [← hRight_apply σ, map_sub, map_sub, map_smul, map_smul, hRight_apply, hRight_apply, hRight_apply, hyx, hyy]
    simp

theorem incl_restrictionMatrix (z : Fin n → E) : ι σ J X Y (T σ J X Y *ᵥ z) = projOrthogonal σ J X Y z := by
  obtain ⟨u, hu⟩ := exists_ι_eq σ J X Y (projOrthogonal_mem hxx hyy hxy hyx z)
  rw [T_mulVec, ← hu, lInv_ι]

theorem conjTranspose_restriction_gram : Formalism.UG.cT (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) * J * P σ J X Y =
    Formalism.UG.cT (σ : E →+* E) (T σ J X Y) * J0 σ J X Y * (1 : Matrix (Fin (dim σ J X Y)) (Fin (dim σ J X Y)) E) := by
  refine matrix_ext_of_hE σ fun α β => ?_
  rw [← hE_mulVec σ J (1 : Matrix (Fin n) (Fin n) E) (P σ J X Y) α β,
    ← hE_mulVec σ (J0 σ J X Y) (T σ J X Y) (1 : Matrix (Fin (dim σ J X Y)) (Fin (dim σ J X Y)) E) α β, Matrix.one_mulVec,
    Matrix.one_mulVec, hE_J0, incl_restrictionMatrix hxx hyy hxy hyx, ← ι_apply, projOrthogonal_apply, hE_sub_smul_left, hE_sub_smul_left]
  have h := ι_mem σ J X Y β
  rw [mem_invariant_forms] at h
  rw [h.1, h.2]
  simp

end Witt

end Frame

end GlobalTheory.EisRestrictDual

namespace GlobalTheory.EisRestrictDual

open GlobalTheory.EisMidHt (firstColumn)

theorem isSelfDualAt_restrictedLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ v, IsSelfDualAt σ (J0 σ J X Y) (L0 σ J X Y L) v := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW L a hA v
  have hswap : ∀ z w : Fin n → E, hE σ J w z = σ (hE σ J z w) := fun z w => by
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, sigma_sigma hσ, hJ.1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hxx : hE σ J (firstColumn X) (firstColumn X) = 0 := by rw [hE_firstColumn, hW.xx]; rfl
  have hyy : hE σ J (firstColumn Y) (firstColumn Y) = 0 := by rw [hE_firstColumn, hW.yy]; rfl
  have hxy : hE σ J (firstColumn X) (firstColumn Y) = 1 := by rw [hE_firstColumn, hW.xy]; rfl
  have hyx : hE σ J (firstColumn Y) (firstColumn X) = 1 := by rw [hswap, hxy, map_one]
  have hmemP : ∀ z ∈ L0 σ J X Y L, P σ J X Y *ᵥ z ∈ L := fun z hz => hz
  have hmemT : ∀ z ∈ L, T σ J X Y *ᵥ z ∈ L0 σ J X Y L := fun z hz => by
    rw [mem_lattice_zeroTorus, ← ι_apply, incl_restrictionMatrix hxx hyy hxy hyx, projOrthogonal_apply]
    have h := hA.split z hz 0
    have e1 : ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z) 0 = hE σ J (firstColumn Y) z := by
      rw [← Matrix.mulVec_mulVec, hE_eq_dot]; rfl
    have e2 : ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z) 0 = hE σ J (firstColumn X) z := by
      rw [← Matrix.mulVec_mulVec, hE_eq_dot]; rfl
    have h1 : hE σ J (firstColumn Y) z • firstColumn X ∈ L := by rw [← e1]; exact h.1
    have h2 : hE σ J (firstColumn X) z • firstColumn Y ∈ L := by rw [← e2]; exact h.2
    exact sub_mem (sub_mem hz h1) h2
  have key1 : ∀ u u' : Fin (dim σ J X Y) → Fv F v ⊗[F] E, hLin σ (J0 σ J X Y) (Fv F v) u u' =
      hLin σ J (Fv F v) ((P σ J X Y).map (inclR (Fv F v)) *ᵥ u) ((P σ J X Y).map (inclR (Fv F v)) *ᵥ u') := by
    intro u u'
    rw [hLin_map_mulVec, hLin_eq_dot]
    rfl
  have key2 : ∀ (u : Fin (dim σ J X Y) → Fv F v ⊗[F] E) (x : Fin n → Fv F v ⊗[F] E),
      hLin σ J (Fv F v) ((P σ J X Y).map (inclR (Fv F v)) *ᵥ u) x =
        hLin σ (J0 σ J X Y) (Fv F v) u ((T σ J X Y).map (inclR (Fv F v)) *ᵥ x) := by
    intro u x
    have h1 := hLin_map_mulVec (Fv F v) σ J (1 : Matrix (Fin n) (Fin n) E) (P σ J X Y) u x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h1
    have h2 := hLin_map_mulVec (Fv F v) σ (J0 σ J X Y) (T σ J X Y)
      (1 : Matrix (Fin (dim σ J X Y)) (Fin (dim σ J X Y)) E) u x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h2
    rw [h1, h2, conjTranspose_restriction_gram hxx hyy hxy hyx]
  have hL := hA.dual v
  unfold IsSelfDualAt at hL ⊢
  ext u
  constructor
  · intro hu x hx
    rw [key1]
    have h1 := map_mulVec_mem_latLoc (P σ J X Y) hmemP v hu
    rw [hL] at h1
    exact h1 _ (map_mulVec_mem_latLoc (P σ J X Y) hmemP v hx)
  · intro hu
    have h1 : (P σ J X Y).map (inclR (Fv F v)) *ᵥ u ∈ latLoc F L v := by
      rw [hL]
      intro x hx
      rw [key2]
      exact hu _ (map_mulVec_mem_latLoc (T σ J X Y) hmemT v hx)
    have h2 := map_mulVec_mem_latLoc (T σ J X Y) hmemT v h1
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, T_mul_P, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at h2

end GlobalTheory.EisRestrictDual
