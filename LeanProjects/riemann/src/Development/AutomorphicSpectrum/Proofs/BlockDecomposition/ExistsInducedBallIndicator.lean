import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirLevi.Bump

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

def IntM (m : GL (Fin n) k) : Prop :=
  ∀ i, Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i) ∈ polyBall (k := k) n 1

theorem intM_one : IntM (1 : GL (Fin n) k) := by
  intro i j
  show valuation k (((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((1 : kˣ) : k)
  by_cases h : i = j
  · simp [h]
  · simp [one_apply, h]

theorem IntM.mulVec_mem {m : GL (Fin n) k} (hm : IntM m) {s : kˣ} {v : Fin n → k}
    (hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s) :
    Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v) ∈ polyBall (k := k) n s :=
  fun i => dotProduct_mem_cball (a := 1) (b := s) (c := s) (by simp) (hm i) hv

theorem isOpen_intM : IsOpen {m : GL (Fin n) k | IntM m} := by
  have h : {m : GL (Fin n) k | IntM m} = ⋂ i, (fun m : GL (Fin n) k =>
      Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i)) ⁻¹'
        (polyBall (k := k) n 1 : Set (Multiplicative (Fin n → k))) := by
    ext m
    simp [IntM]
  rw [h]
  refine isOpen_iInter_of_finite fun i => (isOpen_polyBall n 1).preimage ?_
  exact continuous_ofAdd.comp (continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_colv : Continuous (colv : Mir k n → Fin n → k) :=
  continuous_pi fun i => (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)

theorem continuous_mvec : Continuous (mvec : Mir k n → Fin n → k) := by
  have h1 : Continuous fun x : Mir k n =>
      (((mirabolicProjection k n x)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (continuous_inv.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n))
  exact h1.matrix_mulVec continuous_colv

theorem continuous_lv : Continuous (lv k n) :=
  continuous_induced_rng.2 (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n)

def bumpF (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E) (g : Mir k n) : E :=
  @ite _ (Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s) (Classical.propDecidable _)
    (ρ (lv k n (mirabolicProjection k n g)) e) 0

variable (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E)

theorem bumpF_levi_mul (m : GL (Fin n) k) (g : Mir k n) :
    bumpF ρ s e (levi k n m * g) = ρ (lv k n m) (bumpF ρ s e g) := by
  unfold bumpF
  rw [mvec_levi_mul, map_mul, mirProj_levi, map_mul, map_mul, Module.End.mul_apply]
  split_ifs <;> simp

theorem bumpF_equi (h : LH k n) (g : Mir k n) :
    bumpF ρ s e ((h : Mir k n) * g) = ρ h (bumpF ρ s e g) := by
  obtain ⟨m, hm⟩ := h.2
  have e1 : h = lv k n m := Subtype.ext hm.symm
  rw [e1]
  exact bumpF_levi_mul ρ s e m g

theorem bumpF_levi_uv (q : GL (Fin n) k) (w : Fin n → k) :
    bumpF ρ s e (levi k n q * uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _)
        (ρ (lv k n q) e) 0 := by
  unfold bumpF
  rw [mvec_levi_mul_uv, map_mul, mirProj_levi, mirProj_uv, mul_one]

theorem bumpF_uv (w : Fin n → k) :
    bumpF ρ s e (uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  have h := bumpF_levi_uv ρ s e 1 w
  rw [map_one (levi k n), one_mul, map_one (lv k n), map_one ρ] at h
  simpa using h

theorem mul_formula (p m : GL (Fin n) k) (v a : Fin n → k) :
    (levi k n p * uv n v) * (levi k n m * uv n a) = levi k n (p * m) *
      uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) := by
  rw [uv_add, map_mul, mul_assoc (levi k n p), ← mul_assoc (uv n v), uv_mul_levi]
  simp only [mul_assoc]

theorem bumpF_fix (p m : GL (Fin n) k) (v a : Fin n → k) (h1 : IntM m) (h2 : IntM m⁻¹)
    (hm : ρ (lv k n m) e = e) (ha : Multiplicative.ofAdd a ∈ polyBall (k := k) n s) :
    bumpF ρ s e ((levi k n p * uv n v) * (levi k n m * uv n a)) = bumpF ρ s e (levi k n p * uv n v) := by
  rw [mul_formula, bumpF_levi_uv, bumpF_levi_uv, map_mul, map_mul, Module.End.mul_apply, hm]
  have hiff : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) ∈
      polyBall (k := k) n s ↔ Multiplicative.ofAdd v ∈ polyBall (k := k) n s := by
    constructor
    · intro h
      have h3 : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ∈
          polyBall (k := k) n s := by
        have h4 := mul_mem h (inv_mem ha)
        rwa [ofAdd_add, mul_inv_cancel_right] at h4
      have h5 := h1.mulVec_mem h3
      rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h5
    · intro h
      rw [ofAdd_add]
      exact mul_mem (h2.mulVec_mem h) ha
  by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s
  · rw [if_pos hv, if_pos (hiff.2 hv)]
  · rw [if_neg hv, if_neg (fun c => hv (hiff.1 c))]

def nbhd : Set (Mir k n) :=
  {x | IntM (mirabolicProjection k n x) ∧ IntM (mirabolicProjection k n x)⁻¹ ∧ ρ (lv k n (mirabolicProjection k n x)) e = e ∧
    Multiplicative.ofAdd (mvec x) ∈ polyBall (k := k) n s}

theorem isOpen_nbhd (hρ : IsSmooth ρ) : IsOpen (nbhd ρ s e) := by
  have hp := GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n
  refine (isOpen_intM.preimage hp).inter ((isOpen_intM.preimage (continuous_inv.comp hp)).inter
    (((hρ e).preimage (continuous_lv.comp hp)).inter ?_))
  exact (isOpen_polyBall n s).preimage (continuous_ofAdd.comp continuous_mvec)

theorem one_mem_nbhd : (1 : Mir k n) ∈ nbhd ρ s e := by
  have hm : mvec (1 : Mir k n) = 0 := by
    have h := mvec_uv (k := k) n 0
    rwa [uv_zero] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one]; exact intM_one
  · rw [map_one, inv_one]; exact intM_one
  · simp
  · rw [hm]; exact one_mem _

theorem bumpF_mul_nbhd (g x : Mir k n) (hx : x ∈ nbhd ρ s e) :
    bumpF ρ s e (g * x) = bumpF ρ s e g := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have h := bumpF_fix ρ s e (mirabolicProjection k n g) (mirabolicProjection k n x) (mvec g) (mvec x) h1 h2 h3 h4
  rwa [← decomp g, ← decomp x] at h

theorem bumpF_mem : bumpF ρ s e ∈ indSpace (LH k n) ρ := fun h g => bumpF_equi ρ s e h g

theorem bumpF_smooth (hρ : IsSmooth ρ) :
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) ∈ smoothPart (ind (LH k n) ρ) := by
  have hfix : nbhd ρ s e ⊆ (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
      (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) : Set (Mir k n)) := by
    intro x hx
    apply Subtype.ext
    funext g
    exact bumpF_mul_nbhd ρ s e g x hx
  exact (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ)).isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset ((isOpen_nbhd ρ s e hρ).mem_nhds (one_mem_nbhd ρ s e)) hfix)

theorem bumpF_support : ∃ C : Set (Mir k n), IsCompact C ∧ ∀ g, bumpF ρ s e g ≠ 0 →
    ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c := by
  refine ⟨unipIn k n '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))),
    (isCompact_polyBall n s).image (continuous_unipIn n), fun g hg => ?_⟩
  have hL : Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s := by
    by_contra hc
    exact hg (if_neg hc)
  exact ⟨levi k n (mirabolicProjection k n g), ⟨_, rfl⟩, uv n (mvec g), ⟨_, hL, rfl⟩, decomp g⟩

theorem exists_bump_restr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E),
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v =
      @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  intro k _ _ _ _ n E _ _ ρ hρ s e
  exact ⟨⟨⟨⟨bumpF ρ s e, bumpF_mem ρ s e⟩, bumpF_smooth ρ s e hρ⟩, bumpF_support ρ s e⟩,
    fun v => bumpF_uv ρ s e v⟩

end GlobalTheory.CompanionTheory.MirLevi.Bump

end
