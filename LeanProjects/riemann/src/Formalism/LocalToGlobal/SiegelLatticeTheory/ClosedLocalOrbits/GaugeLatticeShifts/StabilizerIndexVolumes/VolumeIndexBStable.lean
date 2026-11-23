import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexFiniteNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_zero {T : E} (F : FlagG S r T) (y : S.V) (hy : y ∈ Submodule.span E (Set.range F.e)) :
    S.hT y F.z = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact F.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem frame_indep {T : E} (F : FlagG S r T) (hT : T ≠ 0) : LinearIndependent E F.fvec := by
  rw [FlagG.fvec, linearIndependent_fin_snoc]
  refine ⟨F.e_indep, fun hz => hT ?_⟩
  have h := hT_span_zero F F.z hz
  rw [F.z_norm] at h
  exact neg_eq_zero.mp h

theorem z_mem_orth {T : E} (F : FlagG S r T) : F.z ∈ orth S F.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  exact hT_span_zero F x hx

theorem tri_exists {T : E} (F : FlagG S r T) (s : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j) (h2 : ∀ x ∈ orth S F.X, s x - x ∈ F.X) :
    ∃ uu : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni uu ∧ ∀ b, s (F.fvec b) = ∑ c, uu c b • F.fvec c := by
  classical
  have hcol : ∀ a : Fin r, ∃ l : Fin r → E, (∀ i : Fin r, ¬ i.val < a.val → l i = 0) ∧
      s (F.e a) - F.e a = ∑ i, l i • F.e i := by
    intro a
    have hmem : F.e a ∈ F.Xa (a.val + 1) :=
      Submodule.subset_span (Set.mem_image_of_mem F.e (show a ∈ {i : Fin r | i.1 < a.1 + 1} from Nat.lt_succ_self _))
    have h := h1 a.val (F.e a) hmem
    rw [FlagG.Xa, Finsupp.mem_span_image_iff_linearCombination] at h
    obtain ⟨l, hl, hlx⟩ := h
    refine ⟨fun i => l i, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  choose l hl0 hlsum using hcol
  have hz : ∃ c : Fin r → E, s F.z - F.z = ∑ i, c i • F.e i := by
    have h := h2 F.z (z_mem_orth F)
    rw [FlagG.X, Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.symm⟩
  obtain ⟨cz, hcz⟩ := hz
  refine ⟨fun c b => Fin.lastCases (Fin.lastCases 1 (fun i => cz i) c)
      (fun a => Fin.lastCases 0 (fun i => l a i + if i = a then 1 else 0) c) b, ?_, ?_⟩
  · intro i j
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp
      | cast i =>
        exact ⟨fun h => absurd h (lt_asymm (Fin.castSucc_lt_last i)), fun h => absurd h (Fin.castSucc_lt_last i).ne⟩
    | cast a =>
      induction i using Fin.lastCases with
      | last =>
        refine ⟨fun _ => by simp, fun h => absurd h.symm (Fin.castSucc_lt_last a).ne⟩
      | cast i =>
        simp only [Fin.lastCases_castSucc]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h' : a.val < i.val := h
          rw [hl0 a i (by omega), if_neg (by rintro rfl; omega)]
          simp
        · have h' : i = a := Fin.castSucc_injective _ h
          subst h'
          rw [hl0 i i (lt_irrefl _), if_pos rfl]
          simp
  · intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, one_smul]
      rw [← hcz]
      abel
    | cast a =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last,
        zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← hlsum a]
      abel

theorem coef_unique {n : ℕ} {f : Fin n → S.V} (hf : LinearIndependent E f) (v : Fin n → S.V)
    (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ b, v b = ∑ c, A c b • f c) (hB : ∀ b, v b = ∑ c, B c b • f c) :
    A = B := by
  ext c b
  have h : ∑ c, (A c b - B c b) • f c = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hA b, ← hB b, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf _ h c)

theorem zhat_conj {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (s : S.V ≃ₗ[E] S.V)
    (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y) (uu uu' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hu : ∀ b, s (F.fvec b) = ∑ c, uu c b • F.fvec c) (hu' : ∀ b, s (F'.fvec b) = ∑ c, uu' c b • F'.fvec c) :
    Zhat F F' = uu.conjTranspose * Zhat F F' * uu' := by
  ext a b
  have key : S.hT (F.fvec a) (F'.fvec b) = S.hT (s (F.fvec a)) (s (F'.fvec b)) := (hs _ _).symm
  simp only [Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [key, hu a, hu' b]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, Finset.mul_sum, Finset.sum_mul]
  first
  | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

end Frames

section Mat

variable {K : Type*} [Field K] {r : ℕ}

def sgnM (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1 : K) ^ (r - b.val)

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * sgnM r := by
  ext a b
  simp [ZhatOM, sgnM, Matrix.mul_diagonal, mul_comm]

theorem sgnM_sq : (sgnM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * sgnM r = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem up_sgn {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni M) :
    IsUpUni (sgnM r * M * sgnM r) := by
  intro i j
  have hs : ∀ b : Fin (r + 1), ((-1 : K) ^ (r - b.val)) * (-1) ^ (r - b.val) = 1 := fun b => by
    rw [← mul_pow]; simp
  simp only [sgnM, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine ⟨fun hij => by rw [(h i j).1 hij]; simp, fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, hs]

end Mat

theorem lo_conjT {E : Type} [Field E] [StarRing E] {n : ℕ} {M : Matrix (Fin n) (Fin n) E}
    (h : IsUpUni M) : IsLoUni M.conjTranspose := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  refine ⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, star_one]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volume_index_b_stable (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    BinSt D u u' F0 what₂ δ M := by
  intro hSt _hyps _hag t w F' L U _hrel _hgen hN hG
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  rw [zhatOM_eq] at hZ
  change Zhat F0 F'.fl * sgnM D.R.rS = L * ptMat w * U at hZ
  obtain ⟨h1, hmul, hinv⟩ := hSt D.host.E (D.R.rS + 1) (ptMat w)
  have hLu : IsUnit L.det := by rw [lo_det hL]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [up_det hU]; exact isUnit_one
  have hind : LinearIndependent D.host.E F0.fvec := by
    by_cases hT : ((Tu D u : ℕ) : D.host.E) = 0
    · have hG' : Gflag F0 F'.fl ≠ 0 := hG
      unfold Gflag at hG'
      simp only [hT, zero_mul, sub_zero] at hG'
      have hD : (Zhat F0 F'.fl).det ≠ 0 := by
        intro h0
        apply hG'
        have e : Dl F0 F'.fl (D.R.rS + 1) = 0 := by
          unfold Dl leadMinorE
          rw [dif_pos le_rfl]
          exact h0
        rw [e, zero_mul]
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      by_contra hgi
      apply hD
      rw [← Matrix.exists_vecMul_eq_zero_iff]
      refine ⟨fun a => star (g a), fun h => hgi (by simpa using congrFun h i), ?_⟩
      funext b
      have := congrArg (fun v => (VS D).hT v (F'.fl.fvec b)) hg
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, map_zero, LinearMap.zero_apply] at this
      simpa [Matrix.vecMul, dotProduct, Zhat, brS] using this
    · exact frame_indep F0 hT
  intro x hx
  have hx' : x ∈ Subgroup.closure (stabAutSet D u u' F0 what₂ t F' L) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs0, hs1⟩, uu, hu, hau⟩ := ha
    obtain ⟨hiso, hf1, hf2⟩ := hs0
    obtain ⟨_, g1, g2⟩ := hs1
    obtain ⟨uu0, huu0, hu0⟩ := tri_exists F0 s hf1 hf2
    have heq : uu = uu0 := coef_unique hind (fun b => s (F0.fvec b)) uu uu0 hu hu0
    subst heq
    obtain ⟨vv, hvv, hv⟩ := tri_exists F'.fl s g1 g2
    have hZc := zhat_conj F0 F'.fl s (fun x y => hiso.1 x y) uu vv hu hv
    have hW : ptMat w = L⁻¹ * (Zhat F0 F'.fl * sgnM D.R.rS) * U⁻¹ := by
      rw [hZ]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hLu, Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]
    refine ⟨?_, U * (sgnM D.R.rS * vv * sgnM D.R.rS) * U⁻¹, up_mul (up_mul hU (up_sgn hvv)) (up_inv hU), ?_⟩
    · rw [hau]
      exact lo_mul (lo_mul (lo_inv hL) (lo_conjT huu0)) hL
    · rw [hau, hW]
      have hS := sgnM_sq (K := D.host.E) (r := D.R.rS)
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hLu, Matrix.nonsing_inv_mul_cancel_left _ _ hUu,
        ← Matrix.mul_assoc (sgnM D.R.rS) (sgnM D.R.rS), hS, Matrix.one_mul,
        ← Matrix.mul_assoc (Zhat F0 F'.fl) vv, ← Matrix.mul_assoc uu.conjTranspose (Zhat F0 F'.fl * vv),
        ← Matrix.mul_assoc uu.conjTranspose (Zhat F0 F'.fl), ← hZc]
  | one => exact h1
  | mul a b _ _ ha hb => exact hmul a ha b hb
  | inv a _ ha => exact hinv a ha

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
