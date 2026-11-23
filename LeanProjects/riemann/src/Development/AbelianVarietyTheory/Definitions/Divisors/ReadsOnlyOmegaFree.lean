import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

open Classical

def stdM (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem topL_stdM {κ : Type} [Zero κ] [One κ] {b a : ℕ} (h : a ≤ b) : topL a (stdM κ b a) = 1 := by
  ext i j
  have hi : i.val < b := lt_of_lt_of_le i.2 h
  simp [topL, stdM, hi, Matrix.one_apply, Fin.ext_iff]

theorem eq_stdM_iff {κ : Type} [Zero κ] [One κ] {b a : ℕ} (h : a ≤ b) (y : Matrix (Fin b) (Fin a) κ) :
    (LowZero a y ∧ topL a y = 1) ↔ y = stdM κ b a := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    by_cases hi : i.val < a
    · have := congrFun (congrFun h2 ⟨i.val, hi⟩) j
      simpa [topL, stdM, Matrix.one_apply, Fin.ext_iff] using this
    · have hne : i.val ≠ j.val := by have := j.2; omega
      simp [stdM, hne, h1 i j (by omega) j.2]
  · rintro rfl
    refine ⟨fun i j hi hj => ?_, topL_stdM h⟩
    have hne : i.val ≠ j.val := by omega
    simp [stdM, hne]

theorem rank_W_le_V : (Wc D i).rank ≤ (Vc D i).rank :=
  (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)

theorem readsOnly_omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    ReadsOnly (R.Pg ∪ Q) (omegaFree R i Q ξR y₀) := by
  intro y y' h
  have hg : ∀ PP ∈ R.Pg, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_left _ hp)
  have hq : ∀ PP ∈ Q, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_right _ hp)
  unfold omegaFree
  congr 1
  · exact if_congr ⟨fun H PP hp => (hg PP hp) ▸ H PP hp, fun H PP hp => (hg PP hp).symm ▸ H PP hp⟩ rfl rfl
  · by_cases H : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det
    · have H' : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun PP hp => (hq PP hp) ▸ H PP hp
      rw [dif_pos H, dif_pos H']
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (H PP.1 PP.2).unit = (H' PP.1 PP.2).unit := by
        ext; simp [hq PP.1 PP.2]
      rw [this]
    · have H' : ¬ ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun H' =>
        H fun PP hp => (hq PP hp).symm ▸ H' PP hp
      rw [dif_neg H, dif_neg H']

theorem omegaK_mul_omegaQ (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y =
      (if ∀ PP ∈ Q, LowZero (Wc D i).rank (y PP) then 1 else 0) * omegaFree R i Q ξR (fun PP => stdM (kP PP) _ _) y := by
  unfold omegaFree omegaK omegaQ
  simp only [eq_stdM_iff (rank_W_le_V i)]
  by_cases h1 : ∀ PP ∈ Q, LowZero (Wc D i).rank (y PP)
  · rw [if_pos h1, one_mul]
    congr 1
    by_cases H : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det
    · rw [dif_pos H, dif_pos (fun PP hp => ⟨h1 PP hp, H PP hp⟩)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp
    · rw [dif_neg H, dif_neg (fun H' => H fun PP hp => (H' PP hp).2)]
  · rw [if_neg h1, zero_mul, dif_neg (fun H' => h1 fun PP hp => (H' PP hp).1), mul_zero]

theorem omegaFree_ne_zero (Q : Finset (Pl D.host.E)) (hd : Disjoint R.Pg Q) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    ∃ y, omegaFree R i Q ξR y₀ y ≠ 0 := by
  refine ⟨fun PP => if PP ∈ Q then stdM (kP PP) _ _ else y₀ PP, ?_⟩
  unfold omegaFree
  have h1 : ∀ PP ∈ R.Pg, (if PP ∈ Q then stdM (kP PP) _ _ else y₀ PP) = y₀ PP := fun PP hp =>
    if_neg (Finset.disjoint_left.1 hd hp)
  have h2 : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (if PP ∈ Q then stdM (kP PP) _ _ else y₀ PP)).det := fun PP hp => by
    rw [if_pos hp, topL_stdM (rank_W_le_V i)]; simp
  rw [if_pos h1, dif_pos h2, one_mul]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

theorem phiOf_iff_phiIs (t : T0) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → ℂ) :
    PhiOf R i (R.Q t) (fun y => omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) ι N φ ↔
      PhiIs R i (RingHom.id ℂ) t ι N φ := Iff.rfl

theorem VecOf.smul {Q : Finset (Pl D.host.E)} {Ω : DatFn D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (h : VecOf R i Q Ω φ) (c : ℂ) :
    VecOf R i Q (c • Ω) (c • φ) := by
  obtain ⟨hv, e, he, hex, hall⟩ := h
  refine ⟨hv, e, he, hex, fun T hT => ?_⟩
  rw [hall T hT, ← map_smul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end GlobalTheory.OnCmp

end
