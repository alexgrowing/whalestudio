import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcrisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedF

variable {l : ℕ} [Fact l.Prime]

theorem aw_injective (C : Core l) (a : ℕ) [NeZero a] :
    Function.Injective ((Per.aB l).comp (wA l a).toRingHom) := by
  haveI : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  haveI : Nontrivial (Per.Bcris l) := C.ι.domain_nontrivial
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (((l : ℕ) : Per.Bcris l) ^ m * ((Per.aB l).comp (wA l a).toRingHom) (b : Wq l a)) :=
    ((isUnit_l_Bcris l).pow m).mul (b.isUnit.map _)
  exact hu.ne_zero hx

theorem clear_den {d : ℕ} {R : Type} [CommRing R] (f : R →+* Per.Bcris l)
    (G : Matrix (Fin d) (Fin d) (Per.Bcris l))
    (h : ∀ i j, ∃ (n : ℕ) (w : R), ((l : ℕ) : Per.Bcris l) ^ n * G i j = f w) :
    ∃ (k : ℕ) (F : Matrix (Fin d) (Fin d) R), ((l : ℕ) : Per.Bcris l) ^ k • G = F.map f := by
  choose n w hw using h
  refine ⟨Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2),
    Matrix.of fun i j => ((l : ℕ) : R) ^ (Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) - n i j) * w i j, ?_⟩
  ext i j
  have hle : n i j ≤ Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) :=
    Finset.le_sup (f := fun p : Fin d × Fin d => n p.1 p.2) (Finset.mem_univ (i, j))
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_natCast, smul_eq_mul,
    ← hw]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem inv_entries {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hρ : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l)) = U' * U.map (Per.φB l) ∧
    (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l)) = U'.map (Per.φB l) * U := by
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hR : (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := hρ g
  have hσ1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσU' : U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
    calc U'.map (Per.σB (g : GQ l))
        = (U' * (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) * U'.map (Per.σB (g : GQ l)) := by
          rw [mul_assoc U', hR, hU'U, one_mul]
      _ = U' * (ρ g).map (Per.zB l) := by rw [mul_assoc, hσ1, mul_one]
  have hφR : ((ρ g).map (Per.zB l)).map (Per.φB l) = (ρ g).map (Per.zB l) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1]
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) (Per.Bcris l),
      (M.map (Per.φB l)).map (Per.σB (g : GQ l)) = (M.map (Per.σB (g : GQ l))).map (Per.φB l) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.1 _ _).symm
  constructor
  · calc (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l))
        = U'.map (Per.σB (g : GQ l)) * (U.map (Per.σB (g : GQ l))).map (Per.φB l) := by
          rw [Matrix.map_mul, hcomm]
      _ = U' * (((ρ g).map (Per.zB l)).map (Per.φB l) * (U.map (Per.σB (g : GQ l))).map (Per.φB l)) := by
          rw [hσU', hφR, mul_assoc]
      _ = U' * U.map (Per.φB l) := by rw [← Matrix.map_mul, hR]
  · calc (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l))
        = (U'.map (Per.σB (g : GQ l))).map (Per.φB l) * U.map (Per.σB (g : GQ l)) := by
          rw [Matrix.map_mul, hcomm]
      _ = U'.map (Per.φB l) * ((ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) := by
          rw [hσU', Matrix.map_mul, hφR, mul_assoc]
      _ = U'.map (Per.φB l) * U := by rw [hR]

theorem frob_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) →
    ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)),
      F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧
      (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  intro l _ K bk C hC d ρ U U' hUU hρ
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hent : ∀ G : Matrix (Fin d) (Fin d) (Per.Bcris l), (∀ g : ↥(GK K), G.map (Per.σB (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a),
        ((l : ℕ) : Per.Bcris l) ^ n * G i j = ((Per.aB l).comp (wA l bk.a).toRingHom) w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (G i j) fun g hg => by
      have := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simpa only [Matrix.map_apply] using this
    obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris l K bk C x hxK
    exact ⟨n, w, by rw [← hx, hw]; rfl⟩
  obtain ⟨k, F, hF⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).1)
  obtain ⟨k', F', hF'⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).2)
  have hGG : (U' * U.map (Per.φB l)) * (U'.map (Per.φB l) * U) = 1 := by
    rw [mul_assoc, ← mul_assoc (U.map _), ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _),
      one_mul, hU'U]
  refine ⟨k, k + k', F, F', ?_, ?_⟩
  · apply Matrix.map_injective (aw_injective C bk.a)
    change (F * F').map ((Per.aB l).comp (wA l bk.a).toRingHom) =
      (((l : ℕ) : Wq l bk.a) ^ (k + k') • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map
        ((Per.aB l).comp (wA l bk.a).toRingHom)
    rw [Matrix.map_mul, ← hF, ← hF', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hGG]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [← hF, Matrix.mul_smul, ← mul_assoc, hUU, one_mul]

end GlobalTheory.SeedF
