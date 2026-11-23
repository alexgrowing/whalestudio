import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.MidLineParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem nontrivial_AE : Nontrivial (AE F E) := (inclR_injective (F := F) (E := E)).nontrivial

theorem incV_injective {n : ℕ} : Function.Injective (incV F (n := n) (E := E)) := fun a b h =>
  funext fun i => inclR_injective (congrFun h i)

theorem incV_add {n : ℕ} (u v : Fin n → E) : incV F (u + v) = incV F u + incV F v := by
  funext i; simp [incV]

theorem incV_sub {n : ℕ} (u v : Fin n → E) : incV F (u - v) = incV F u - incV F v := by
  funext i; simp [incV]

theorem incV_smul {n : ℕ} (c : E) (u : Fin n → E) : incV F (c • u) = inclR (F := F) (AF F) c • incV F u := by
  funext i; simp [incV]

theorem incM_mulVec {m k : ℕ} (A : Matrix (Fin m) (Fin k) E) (z : Fin k → E) :
    incM F A *ᵥ incV F z = incV F (A *ᵥ z) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) A z i).symm

theorem incV_dot_form {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    incV F u ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F v i)) = inclR (F := F) (AF F) (form σ J u v) := by
  have e : (fun i => cA σ (incV F v i)) = incV F (fun i => σ (v i)) := funext fun i => GlobalTheory.PlaneLevi.cA_inclR σ (v i)
  rw [e, incM_mulVec, form]
  simp only [incV, dotProduct, map_sum, map_mul]

theorem mat_mul_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) (v : Fin n → AE F E) :
    mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]; rfl

theorem mat_inv_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {u v : Fin n → AE F E}
    (h : mat g *ᵥ u = v) : mat g⁻¹ *ᵥ v = u := by
  rw [← h, ← mat_mul_mulVec, inv_mul_cancel]; exact Matrix.one_mulVec u

theorem rat_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ Q : Matrix (Fin n) (Fin n) E, mat g = incM F Q ∧ Qᵀ * J * Q.map σ = J := by
  obtain ⟨q, hq⟩ := Subgroup.mem_subgroupOf.1 hg
  have hm : mat g = incM F (q : Matrix (Fin n) (Fin n) E) := by
    simp only [mat]; rw [← hq]; rfl
  refine ⟨q, hm, ?_⟩
  have hu : (mat g)ᵀ * incM F J * (mat g).map (cA σ).toRingHom = incM F J := g.2
  rw [hm] at hu
  exact GlobalTheory.LeviRat.unitary_of_map σ _ _ hu

theorem form_mulVec {n : ℕ} {J Q : Matrix (Fin n) (Fin n) E} (hQ : Qᵀ * J * Q.map σ = J) (a b : Fin n → E) :
    form σ J (Q *ᵥ a) (Q *ᵥ b) = form σ J a b := by
  have hσQb : (fun i => σ ((Q *ᵥ b) i)) = Q.map σ *ᵥ fun i => σ (b i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [form, form, hσQb, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hQ]

theorem rat_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ Q : Matrix (Fin n) (Fin n) E, (∀ v, mat g *ᵥ incV F v = incV F (Q *ᵥ v)) ∧
      ∀ a b, form σ J (Q *ᵥ a) (Q *ᵥ b) = form σ J a b := by
  obtain ⟨Q, hm, hQ⟩ := rat_mat hg
  exact ⟨Q, fun v => by rw [hm, incM_mulVec], form_mulVec hQ⟩

theorem mem_ratU_of_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J)
    (h : ∀ v : Fin n → E, ∃ w : Fin n → E, mat g *ᵥ incV F v = incV F w) : g ∈ ratU σ J := by
  haveI := nontrivial_AE (F := F) (E := E)
  choose W hW using h
  let Q : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => W (Pi.single j 1) i
  have hs : ∀ j : Fin n, incV F (Pi.single j (1 : E)) = Pi.single j 1 := fun j => by
    ext k; by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, Pi.single_apply, hk]
  have hm : mat g = incM F Q := by
    ext i j
    have := congrFun (hW (Pi.single j 1)) i
    rw [hs, Matrix.mulVec_single_one] at this
    simpa [Q, incM, incV] using this
  have hdet : Q.det ≠ 0 := by
    intro h0
    have hu : IsUnit (mat g).det := Matrix.isUnits_det_units g.1
    rw [hm, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    exact not_isUnit_zero hu
  refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Q hdet, ?_⟩
  apply Units.ext
  show Q.map (inclR (F := F) (AF F)) = mat g
  rw [hm]; rfl

theorem scal_rat {n : ℕ} {v w : Fin n → E} {l : AE F E} (hv : v ≠ 0) (h : incV F w = l • incV F v) :
    ∃ k : E, l = inclR (F := F) (AF F) k ∧ w = k • v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hv (funext hc)
  have hli : inclR (F := F) (AF F) (w i) = l * inclR (F := F) (AF F) (v i) := congrFun h i
  have hl : l = inclR (F := F) (AF F) (w i / v i) := by
    rw [div_eq_mul_inv, map_mul, hli, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  refine ⟨w i / v i, hl, incV_injective (F := F) ?_⟩
  rw [h, incV_smul, hl]

theorem exists_ratU_of_form {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (U : Matrix (Fin n) (Fin n) E)
    (hU : ∀ u v, form σ J (U *ᵥ u) (U *ᵥ v) = form σ J u v) : ∃ g ∈ ratU σ J, mat g = incM F U := by
  have h : Uᵀ * J * U.map σ = J := by
    ext i j
    have := GlobalTheory.PlaneLevi.entry_eq_form (σ := σ) (J := J) 1 i j
    rw [Matrix.one_mulVec, Matrix.one_mulVec, Matrix.transpose_one, Matrix.one_mul,
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one] at this
    rw [GlobalTheory.PlaneLevi.entry_eq_form, hU, this]
  have hd : U.det ≠ 0 := by
    intro h0
    apply hJ
    rw [← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
  exact ⟨GlobalTheory.PlaneLevi.toUA σ (Matrix.GeneralLinearGroup.mkOfDetNeZero U hd) h, Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩, rfl⟩

end GlobalTheory.MidLineParam

end
