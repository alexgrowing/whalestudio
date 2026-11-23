import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HermitianIsotropicProjComplement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def datR : SemiG.Dat (R ⊗[F] E) (Fin M) r where
  σA := sigR R σ
  JA := JR R J
  e a := ratV (F := F) R (P.e a)
  f a := ratV (F := F) R (P.f a)
  z := ratV (F := F) R P.z
  tz := inclR (F := F) R ((algebraMap F E (-T))⁻¹)

theorem datR_h (x y : Fin M → R ⊗[F] E) : (datR R σ J P T).h x y = hR R σ J x y := rfl

theorem sigR_inclR (x : E) : sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  first
    | rfl
    | simp [sigR, inclR]

theorem hR_ratV (x y : Fin M → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR (F := F) R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, ratV, JR, sigR_inclR, map_sum, map_mul]

variable {R σ J P T}

theorem datR_hyp (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datR R σ J P T).Hyp := by
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hP
  obtain ⟨hJ1, -⟩ := hJ
  have hh : ∀ x y : Fin M → E, (datR R σ J P T).h (ratV (F := F) R x) (ratV (F := F) R y) =
      inclR (F := F) R (hE σ J x y) := by
    intro x y
    rw [datR_h, hR_ratV]
  have hne : algebraMap F E (-T) ≠ 0 := (map_ne_zero (algebraMap F E)).2 (neg_ne_zero.2 hT)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show sigR R σ (sigR R σ x) = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro i j
    show sigR R σ (JR R J j i) = JR R J i j
    simp only [JR, Matrix.map_apply, sigR_inclR, hJ1 i j]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
    rw [hh, hee, map_zero]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
    rw [hh, hff, map_zero]
  · intro a b
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
    rw [hh, hef]
    split_ifs <;> simp
  · intro a
    show (datR R σ J P T).h (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
    rw [hh, hez, map_zero]
  · intro a
    show (datR R σ J P T).h (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
    rw [hh, hfz, map_zero]
  · show inclR (F := F) R ((algebraMap F E (-T))⁻¹) *
        (datR R σ J P T).h (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hh, hzz, ← map_mul, inv_mul_cancel₀ hne, map_one]

theorem F0_castSucc (a : Fin r) : F0 P (Fin.castSucc a) = P.e a := by
  simp [F0]

theorem frameInitialVectors_last : F0 P (Fin.last r) = P.z := by
  simp [F0]

theorem span_frame_castSucc (b : Fin r) :
    spanR (F := F) R (F0 P) {c | c < Fin.castSucc b} = spanR (F := F) R P.e {a | a < b} := by
  unfold spanR
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcl : c ≠ Fin.last r := Fin.ne_last_of_lt hc
    refine ⟨c.castPred hcl, ?_, ?_⟩
    · show c.castPred hcl < b
      rw [← Fin.castSucc_lt_castSucc_iff, Fin.castSucc_castPred]
      exact hc
    · show ratV (F := F) R (P.e (c.castPred hcl)) = ratV (F := F) R (F0 P c)
      rw [← F0_castSucc, Fin.castSucc_castPred]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Fin.castSucc a, Fin.castSucc_lt_castSucc_iff.2 ha, ?_⟩
    simp only [F0_castSucc]

theorem span_frame_last :
    spanR (F := F) R (F0 P) {c | c < Fin.last r} = spanR (F := F) R P.e Set.univ := by
  unfold spanR
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcl : c ≠ Fin.last r := Fin.ne_of_lt hc
    refine ⟨c.castPred hcl, Set.mem_univ _, ?_⟩
    show ratV (F := F) R (P.e (c.castPred hcl)) = ratV (F := F) R (F0 P c)
    rw [← F0_castSucc, Fin.castSucc_castPred]
  · rintro ⟨a, -, rfl⟩
    refine ⟨Fin.castSucc a, Fin.castSucc_lt_last a, ?_⟩
    simp only [F0_castSucc]

theorem spanR_le (s : Set (Fin r)) :
    spanR (F := F) R P.e s ≤ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  apply Submodule.span_mono
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

theorem span_le_spanR :
    Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) ≤ spanR (F := F) R P.e Set.univ := by
  unfold spanR
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨a, Set.mem_univ _, rfl⟩

theorem S_e {g : HA R σ J} (hg : g ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈
      spanR (F := F) R P.e {a | a < b} := by
  have hu : UniC R σ J (F0 P) g := hg
  have h := hu (Fin.castSucc b)
  rw [F0_castSucc, span_frame_castSucc] at h
  exact h

theorem stabilizer_fixes_tail_coords {g : HA R σ J} (hg : g ∈ Ssub R σ J P) :
    lin R σ J g (ratV (F := F) R P.z) - ratV (F := F) R P.z ∈ spanR (F := F) R P.e Set.univ := by
  have hu : UniC R σ J (F0 P) g := hg
  have h := hu (Fin.last r)
  rw [frameInitialVectors_last, span_frame_last] at h
  exact h

theorem H_fix_e {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  have h1 := (mem_stabT (R := R) (σ := σ) (J := J) (tupH P) h).1 hh (Fin.castAdd r (Fin.castSucc a))
  simp only [tupH, Fin.append_left, F0_castSucc] at h1
  exact h1

theorem H_fix_f {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  have h1 := (mem_stabT (R := R) (σ := σ) (J := J) (tupH P) h).1 hh (Fin.natAdd (r + 1) a)
  simp only [tupH, Fin.append_right] at h1
  exact h1

theorem mapX_S {g : HA R σ J} (hg : g ∈ Ssub R σ J P) : (datR R σ J P T).MapX (lin R σ J g) := by
  intro a
  show lin R σ J g (ratV (F := F) R (P.e a)) ∈ _
  have h1 := spanR_le (σ := σ) (J := J) (T := T) _ (S_e hg a)
  have h2 : ratV (F := F) R (P.e a) ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
    Submodule.subset_span ⟨a, rfl⟩
  have h3 := Submodule.add_mem _ h1 h2
  rw [sub_add_cancel] at h3
  exact h3

theorem uni_lin (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  open Matrix in (
  intro x y
  have hmem : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR R J * ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
  show Formalism.UG.hform (sigR R σ) (JR R J)
      (((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      (((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) =
    Formalism.UG.hform (sigR R σ) (JR R J) x y
  generalize ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = N at hmem ⊢
  have hmem' : (N.map (sigR R σ))ᵀ * JR R J * N = JR R J := hmem
  have hf : ∀ u v : Fin M → R ⊗[F] E, Formalism.UG.hform (sigR R σ) (JR R J) u v =
      (fun i => sigR R σ (u i)) ⬝ᵥ (JR R J *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [hf, hf]
  have hs : (fun i => sigR R σ ((N *ᵥ x) i)) = (N.map (sigR R σ)) *ᵥ (fun i => sigR R σ (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [hs, ← vecMul_transpose (N.map (sigR R σ)), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [hmem'])

theorem mapW_S {g : HA R σ J} (hg : g ∈ Ssub R σ J P) : (datR R σ J P T).MapW (lin R σ J g) := by
  intro w hW
  obtain ⟨hWe, -, hWz⟩ := hW
  have hadd : ∀ u v, (datR R σ J P T).h (u + v) w = (datR R σ J P T).h u w + (datR R σ J P T).h v w := by
    intro u v
    simp only [SemiG.Dat.h, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : R ⊗[F] E) u, (datR R σ J P T).h (c • u) w =
      (datR R σ J P T).σA c * (datR R σ J P T).h u w := by
    intro c u
    simp only [SemiG.Dat.h, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  have hzero : (datR R σ J P T).h 0 w = 0 := by
    simp [SemiG.Dat.h, Formalism.UG.hform]
  have hspan : ∀ v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e),
      (datR R σ J P T).h v w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hWe a
    | zero => exact hzero
    | add x y _ _ hx hy => rw [hadd, hx, hy, add_zero]
    | smul c x _ hx => rw [hsmul, hx, mul_zero]
  have hinv : g⁻¹ ∈ Ssub R σ J P := inv_mem hg
  have hgi : ∀ u, lin R σ J g (lin R σ J g⁻¹ u) = u := by
    intro u
    have h0 := lin_inv_lin (R := R) (σ := σ) (J := J) g⁻¹ u
    rwa [inv_inv] at h0
  have hu : ∀ u, (datR R σ J P T).h u (lin R σ J g w) = (datR R σ J P T).h (lin R σ J g⁻¹ u) w := by
    intro u
    conv_lhs => rw [← hgi u]
    exact uni_lin (P := P) (T := T) g _ _
  refine ⟨fun b => ?_, ?_⟩
  · rw [hu]
    exact hspan _ (mapX_S (T := T) hinv b)
  · rw [hu]
    show (datR R σ J P T).h (lin R σ J g⁻¹ (ratV (F := F) R P.z)) w = 0
    have hWz' : (datR R σ J P T).h (ratV (F := F) R P.z) w = 0 := hWz
    have h2 := hspan _ (spanR_le (σ := σ) (J := J) (T := T) _ (stabilizer_fixes_tail_coords hinv))
    rw [← sub_add_cancel (lin R σ J g⁻¹ (ratV (F := F) R P.z)) (ratV (F := F) R P.z), hadd, h2, hWz', add_zero]

end R

end PI.LevelKSplit.W.SemiA
