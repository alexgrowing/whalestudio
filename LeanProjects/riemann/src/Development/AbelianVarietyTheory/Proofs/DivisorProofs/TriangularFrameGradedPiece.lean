import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedPieceFrameOfFlagStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

set_option autoImplicit false

namespace GlobalTheory.TriFrame

theorem flag_inclusion_comp_eq {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (fl : Vert.Flag F r) (i : Fin r) (V : X.Opens)
    (x : Γ(fl.F i.castSucc, V)) :
    (fl.ι i.succ).app V ((fl.step i).app V x) = (fl.ι i.castSucc).app V x := by
  have := congrArg (fun φ => (Scheme.Modules.Hom.app φ V) x) (fl.step_ι i)
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using this

theorem flag_projection_of_inclusion_eq_zero {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (fl : Vert.Flag F r) (i : Fin r) (V : X.Opens)
    (x : Γ(fl.F i.castSucc, V)) :
    (fl.π i).app V ((fl.step i).app V x) = 0 := by
  have h : fl.step i ≫ fl.π i = 0 := cokernel.condition _
  have := congrArg (fun φ => (Scheme.Modules.Hom.app φ V) x) h
  simpa using this

end GlobalTheory.TriFrame

namespace GlobalTheory.TriFrame

theorem grTri : ∀ (X : Scheme.{0}) (A : X.Opens) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s)
    (L : Fin r → LB X) (ρ : ∀ i k, Γ(X, A ⊓ (L i).U k)) (fl : Vert.Flag F r), Tri hs L ρ →
    (∀ (V : X.Opens) (e : Fin r → Γ(F, V)), IsFrame e → IsTri hs e → Spans fl V e) →
    ∀ (i : Fin r) (t : Γ(fl.F i.succ, A)), (fl.ι i.succ).app A t = s i →
    ∃ hσ : IsFrame fun _ : Fin 1 => (fl.π i).app A t, Tri hσ (fun _ => L i) (fun _ => ρ i) := by
  intro X A F r s hs L ρ fl hT hSp i t ht
  have hσ : IsFrame fun _ : Fin 1 => (fl.π i).app A t :=
    GlobalTheory.T.graded_piece_frame_of_flag X F r fl A s (hSp A s hs (isTri_self hs)) i t ht
  refine ⟨hσ, fun x => ?_⟩
  obtain ⟨V, e, k, hk, hx, he, htri, hdiag⟩ := hT x
  have hSpV := hSp V e he htri
  obtain ⟨u', -, hu'⟩ := hSpV i.succ
  obtain ⟨u, -, hu⟩ := hSp A s hs (isTri_self hs) i.castSucc
  let te : Γ(fl.F i.succ, V) := u' ⟨i, by simp⟩
  have hte : (fl.ι i.succ).app V te = e i := by
    refine (hu' _).trans (congrArg e (Fin.ext rfl))
  have hσe := GlobalTheory.T.graded_piece_frame_of_flag X F r fl V e hSpV i te hte
  let W : X.Opens := V ⊓ A
  let c : Fin r → Γ(X, W) := coordIn hs e i
  let y : Fin r → Γ(fl.F i.succ, W) := fun l =>
    if h : l < i then resM _ inf_le_right ((fl.step i).app A (u ⟨l, h⟩)) else resM _ inf_le_right t
  have hy : ∀ l, c l • (fl.ι i.succ).app W (y l) = c l • resM F inf_le_right (s l) := by
    intro l
    by_cases h : l < i
    · simp only [y, dif_pos h]
      rw [Twist.app_resM, flag_inclusion_comp_eq, hu]
      rfl
    · simp only [y, dif_neg h]
      rw [Twist.app_resM, ht]
      rcases (not_lt.1 h).lt_or_eq with h' | h'
      · simp [c, htri i l h']
      · rw [h']
  have hsum : resM _ inf_le_left te = ∑ l, c l • y l := by
    apply QCoh.app_injective_of_mono (fl.ι i.succ) W
    rw [Twist.app_resM, hte]
    have h1 := ((hs.basis (inf_le_right : W ≤ A)).sum_repr (resM F inf_le_left (e i))).symm
    simp only [IsFrame.basis_apply] at h1
    refine h1.trans ?_
    rw [← QCoh.appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, QCoh.appLinear_apply, hy]
    rfl
  have hπ : resM _ inf_le_left ((fl.π i).app V te) = c i • resM _ inf_le_right ((fl.π i).app A t) := by
    rw [← Twist.app_resM, hsum, ← QCoh.appLinear_apply, map_sum, Finset.sum_eq_single i]
    · rw [map_smul, QCoh.appLinear_apply]
      simp only [y, lt_irrefl, dif_neg, not_false_eq_true, Twist.app_resM]
    · intro l _ hl
      rw [map_smul, QCoh.appLinear_apply]
      by_cases h : l < i
      · simp only [y, dif_pos h, Twist.app_resM, flag_projection_of_inclusion_eq_zero, map_zero, smul_zero]
      · simp [c, htri i l (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hl))]
    · simp
  refine ⟨V, fun _ => (fl.π i).app V te, fun _ => k i, fun _ => hk i, hx, hσe,
    fun a b hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b), fun j => ?_⟩
  rw [coordIn, hπ, ← hσ.basis_apply (inf_le_right : W ≤ A) j, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  exact hdiag i

end GlobalTheory.TriFrame
