import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRestrict.LatLocPre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)

theorem mulVec_zero_eq (Z : Matrix (Fin n) (Fin (r + 1)) E) (z : Fin n → E) :
    ((Formalism.UG.cT (σ : E →+* E) Z * J) *ᵥ z) 0 = hE σ J (GlobalTheory.EisMidHt.firstColumn Z) z := by
  rw [hE_eq_dot, ← Matrix.mulVec_mulVec]
  simp [Formalism.UG.cT, Matrix.mulVec, dotProduct, GlobalTheory.EisMidHt.firstColumn]

theorem hE_col0v_apply (Z W : Matrix (Fin n) (Fin (r + 1)) E) :
    hE σ J (GlobalTheory.EisMidHt.firstColumn Z) (GlobalTheory.EisMidHt.firstColumn W) = (Formalism.UG.cT (σ : E →+* E) Z * J * W) 0 0 := by
  rw [← mulVec_zero_eq]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, GlobalTheory.EisMidHt.firstColumn]

def prj : (Fin n → E) →ₗ[E] (Fin n → E) :=
  LinearMap.id - LinearMap.smulRight (hRight σ J (GlobalTheory.EisMidHt.firstColumn Y)) (GlobalTheory.EisMidHt.firstColumn X) -
    LinearMap.smulRight (hRight σ J (GlobalTheory.EisMidHt.firstColumn X)) (GlobalTheory.EisMidHt.firstColumn Y)

theorem prj_apply (z : Fin n → E) : prj σ J X Y z =
    z - hE σ J (GlobalTheory.EisMidHt.firstColumn Y) z • GlobalTheory.EisMidHt.firstColumn X - hE σ J (GlobalTheory.EisMidHt.firstColumn X) z • GlobalTheory.EisMidHt.firstColumn Y :=
  rfl

theorem prj_of_mem {z : Fin n → E} (hz : z ∈ V0 σ J X Y) : prj σ J X Y z = z := by
  rw [prj_apply, (mem_invariant_forms σ J X Y).1 hz |>.1, (mem_invariant_forms σ J X Y).1 hz |>.2]
  simp

variable {σ J X Y}

theorem prj_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (z : Fin n → E) :
    prj σ J X Y z ∈ V0 σ J X Y := by
  have hxx : hRight σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0 := by
    change hE σ J _ _ = 0; rw [hE_col0v_apply, hW.xx]; rfl
  have hyy : hRight σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn Y) = 0 := by
    change hE σ J _ _ = 0; rw [hE_col0v_apply, hW.yy]; rfl
  have hxy : hRight σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1 := by
    change hE σ J _ _ = 1; rw [hE_col0v_apply, hW.xy]; rfl
  have hyx : hRight σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn X) = 1 := by
    change hE σ J _ _ = 1; rw [hE_col0v_apply, GlobalTheory.StdPar.yx h hJ hW]; rfl
  refine (mem_invariant_forms σ J X Y).2 ⟨?_, ?_⟩
  · change hRight σ J _ (prj σ J X Y z) = 0
    simp only [prj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul, hxx, hxy,
      smul_eq_mul]
    ring
  · change hRight σ J _ (prj σ J X Y z) = 0
    simp only [prj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul, hyy, hyx,
      smul_eq_mul]
    ring

variable (σ J X Y)

def crd (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    (Fin n → E) →ₗ[E] (Fin (dim σ J X Y) → E) :=
  (bas σ J X Y).equivFun.toLinearMap ∘ₗ (prj σ J X Y).codRestrict (V0 σ J X Y) (prj_mem h hJ hW)

variable {σ J X Y}

theorem ι_crd (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (z : Fin n → E) :
    ι σ J X Y (crd σ J X Y h hJ hW z) = prj σ J X Y z := by
  rw [ι_eq_sum, ← Module.Basis.equivFun_symm_apply]
  simp [crd]

theorem crd_ι (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (u : Fin (dim σ J X Y) → E) :
    crd σ J X Y h hJ hW (ι σ J X Y u) = u :=
  ι_injective σ J X Y (by rw [ι_crd, prj_of_mem σ J X Y (ι_mem σ J X Y u)])

theorem Q_mul_P (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    LinearMap.toMatrix' (crd σ J X Y h hJ hW) * P σ J X Y = 1 := by
  have e : P σ J X Y = LinearMap.toMatrix' (ι σ J X Y) := by
    have e' : ι σ J X Y = Matrix.toLin' (P σ J X Y) :=
      LinearMap.ext fun u => by rw [ι_apply, Matrix.toLin'_apply]
    rw [e', LinearMap.toMatrix'_toLin']
  rw [e, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  exact LinearMap.ext fun u => crd_ι h hJ hW u

theorem prj_mem_L {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    (hA : GlobalTheory.EisLine.IsAdapted σ J X Y L a) {z : Fin n → E} (hz : z ∈ L) : prj σ J X Y z ∈ L := by
  obtain ⟨h1, h2⟩ := hA.split z hz 0
  rw [mulVec_zero_eq] at h1 h2
  rw [prj_apply]
  exact sub_mem (sub_mem hz h1) h2

variable {a b : ℕ}

theorem map_mulVec_tmul {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (M : Matrix (Fin a) (Fin b) E) (c : Fv F v)
    (x : Fin b → E) : M.map (inclR (F := F) (Fv F v)) *ᵥ (fun i => c ⊗ₜ[F] x i) = fun j => c ⊗ₜ[F] (M *ᵥ x) j := by
  funext j
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]

theorem map_mulVec_mem_latLoc {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (M : Matrix (Fin a) (Fin b) E)
    {L : Submodule (𝓞 E) (Fin b → E)} {L' : Submodule (𝓞 E) (Fin a → E)} (hM : ∀ x ∈ L, M *ᵥ x ∈ L')
    {y : Fin b → Fv F v ⊗[F] E} (hy : y ∈ latLoc F L v) : M.map (inclR (F := F) (Fv F v)) *ᵥ y ∈ latLoc F L' v := by
  refine latLoc_induction (p := fun y => M.map (inclR (F := F) (Fv F v)) *ᵥ y ∈ latLoc F L' v) (fun c hc x hx => ?_)
    ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · rw [map_mulVec_tmul]; exact tmul_mem_latLoc hc (hM x hx)
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · rw [Matrix.mulVec_add]; exact add_mem hy hz
  · rw [Matrix.mulVec_neg]; exact neg_mem hy

end GlobalTheory.EisRestrict.LatLocPre

namespace GlobalTheory.EisRestrict

open LatLocPre in

theorem mem_localLattice_restricted_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : Fin (dim σ J X Y) → Fv F v ⊗[F] E),
      u ∈ latLoc F (L0 σ J X Y L) v ↔ (P σ J X Y).map (inclR (F := F) (Fv F v)) *ᵥ u ∈ latLoc F L v := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW L a hA v u
  constructor
  · exact map_mulVec_mem_latLoc _ (fun x hx => (mem_lattice_zeroTorus σ J X Y).1 hx)
  · intro hu
    have h1 := map_mulVec_mem_latLoc (L' := L0 σ J X Y L) (LinearMap.toMatrix' (crd σ J X Y h hJ hW))
      (fun x hx => by
        rw [mem_lattice_zeroTorus, LinearMap.toMatrix'_mulVec, ← ι_apply, ι_crd]
        exact prj_mem_L hA hx) hu
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Q_mul_P, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at h1

end GlobalTheory.EisRestrict
