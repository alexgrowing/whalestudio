import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorEabPreservesSmoothClassCCStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenRealToComplex
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

noncomputable section
namespace GlobalTheory
namespace CapelliModel

open Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_lev {g : B.Mat k r} : g ∈ Q.Glev k r 0 ∩ Set.univ ↔ g ∈ B.GV k r :=
  ⟨fun h => h.1.1, fun h => ⟨⟨h, fun a ha => absurd ha (by simp)⟩, trivial⟩⟩

theorem smooth_iff {f : B.Mat k r → F} :
    Q.SmoothLev k r 0 Set.univ f ↔ B.CkOn ⊤ (B.GV k r) f := by
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.2 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU (mem_lev.2 hgG).1⟩
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.1 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU hgG.1⟩

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → F) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → F) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem inCC_zero (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → F) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
  intro u v _ _ _ g _
  simp [dLR_zero]

abbrev Sm (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] := VS k r 0 Set.univ F

abbrev Eu (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (a b : Fin (2 * r + k + 1)) :
    Module.End ℂ (Sm k r F) := E0 isOpen_univ a b

theorem sm_ext (v v' : Sm k r F) (h : ∀ g ∈ B.GV k r, (v : B.Mat k r → F) g = (v' : B.Mat k r → F) g) :
    v = v' := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ Set.univ
  · exact h g (mem_lev.1 hg)
  · rw [v.2.2 g hg, v'.2.2 g hg]

theorem ev_Eu (a b : Fin (2 * r + k + 1)) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (Eu k r F a b v : B.Mat k r → F) g = Q.EH k r a b (v : B.Mat k r → F) g := by
  have := ev_E (i := 0) isOpen_univ (c0 a) (c0 b) v (mem_lev.2 hg)
  rwa [position_level_zero_coord, position_level_zero_coord] at this

theorem qminorOp_cast {n t t' : ℕ} (h : t = t')
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → F) → (Matrix (Fin n) (Fin n) ℂ → F))
    (a : Fin t' → Fin n) (a' : Fin t → Fin n) (ha : ∀ j, a' j = a (Fin.cast h j)) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → F) : qminorOp Eop a' a' u f = qminorOp Eop a a u f := by
  subst h
  have : a' = a := funext ha
  rw [this]

theorem CV_eq (Y : ℂ) (f : B.Mat k r → F) :
    Q.CV k r Y f = qminorOp (Q.EH k r) id id (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) f := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  unfold Q.CV Q.capL Q.uC
  rw [qminorOp_cast hm _ id _ (fun j => by ext; simp [Q.posL]), hm]

theorem ev_qdet (Y : ℂ) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (qdet (Eu k r F) (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v : B.Mat k r → F) g =
      Q.CV k r Y (v : B.Mat k r → F) g := by
  rw [CV_eq]
  exact quantum_minor_level_eq_hat isOpen_univ id id _ v g (mem_lev.2 hg)

def eig (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (χ : ℂ → ℂ) (A : ℝ) :
    Submodule ℂ (Sm k r F) where
  carrier := {v | (∀ m : ℕ, B.InCC A m (v : B.Mat k r → F)) ∧ ∀ u : ℂ, qdet (Eu k r F) u v = χ u • v}
  zero_mem' := ⟨fun m => inCC_zero A m, fun u => by simp⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_add, hv', hw', smul_add]⟩
    obtain ⟨c, hc⟩ := hv m
    obtain ⟨c', hc'⟩ := hw m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c' 1 hc hc').1⟩
  smul_mem' := by
    rintro a v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_smul, hv', smul_comm]⟩
    obtain ⟨c, hc⟩ := hv m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c a hc hc).2⟩

open Classical in

def mulOp (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (c : B.Mat k r → ℂ) :
    Module.End ℂ (Sm k r F) :=
  if h : B.CkOn ⊤ (B.GV k r) c then Mh isOpen_univ c (smooth_iff.2 h) else 0

theorem glRel_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V)
    (hι : Function.Injective ι) (h : ∀ a b w, ι (E' a b w) = E a b (ι w)) (hE : GlRel E) : GlRel E' := by
  intro a b c d
  refine LinearMap.ext fun w => hι ?_
  have := LinearMap.congr_fun (hE a b c d) (ι w)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h] at this ⊢
  rw [this]
  congr 1 <;> split_ifs <;> simp [h]

end CapelliModel

open CapelliModel Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG in

theorem capelli_module_model : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ), ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W) (_ : Module ℂ W) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V) (E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (ev : V →ₗ[ℂ] (B.Mat k r → (Wq →L[ℂ] Wp))) (mul : (B.Mat k r → ℂ) → Module.End ℂ V), GlRel E ∧ GlRel E' ∧ (∀ a b w, ι (E' a b w) = E a b (ι w)) ∧ (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))) • w) ∧ (∀ v, B.CkOn ⊤ (B.GV k r) (ev v)) ∧ (∀ v v', (∀ g ∈ B.GV k r, ev v g = ev v' g) → v = v') ∧ (∀ w, ∀ m : ℕ, B.InCC A m (ev (ι w))) ∧ (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ w, ∀ g ∈ B.GV k r, ev (ι w) g = f g) ∧ (∀ a b v, ∀ g ∈ B.GV k r, ev (E a b v) g = Q.EH k r a b (ev v) g) ∧ (∀ (Y : ℂ) v, ∀ g ∈ B.GV k r, ev (qdet E (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v) g = Q.CV k r Y (ev v) g) ∧ (∀ c : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) c → (∀ v, ∀ g ∈ B.GV k r, ev (mul c v) g = c g • ev v g) ∧ ∀ a b v, ∀ g ∈ B.GV k r, ev (E a b (mul c v)) g = c g • ev (E a b v) g + Q.EH k r a b c g • ev v g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam A
  let χ : ℂ → ℂ := fun u => ∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))
  have hgl : GlRel (Eu k r (Wq →L[ℂ] Wp)) := level_zero_derivation_relation isOpen_univ
  have hst : ∀ a b, ∀ v ∈ eig k r (Wq →L[ℂ] Wp) χ A, Eu k r (Wq →L[ℂ] Wp) a b v ∈ eig k r (Wq →L[ℂ] Wp) χ A := by
    rintro a b v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => ?_⟩
    · exact (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ (fun g hg => (ev_Eu a b v g hg).symm)).2 m
        ((GlobalTheory.T.operatorEab_preserves_smooth_classCC k r Wp Wq A a b _ ⟨smooth_iff.1 v.2.1, hv⟩).2 m)
    · have := LinearMap.congr_fun (qDetCentral _ _ _ hgl u a b) v
      rw [Module.End.mul_apply, Module.End.mul_apply, hv', map_smul] at this
      exact this
  have hint : ∀ a b (w : eig k r (Wq →L[ℂ] Wp) χ A),
      (eig k r (Wq →L[ℂ] Wp) χ A).subtype ((Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b) w) =
        Eu k r (Wq →L[ℂ] Wp) a b ((eig k r (Wq →L[ℂ] Wp) χ A).subtype w) := fun _ _ _ => rfl
  refine ⟨Sm k r (Wq →L[ℂ] Wp), eig k r (Wq →L[ℂ] Wp) χ A, inferInstance, inferInstance, inferInstance,
    inferInstance, Eu k r (Wq →L[ℂ] Wp), fun a b => (Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b),
    (eig k r (Wq →L[ℂ] Wp) χ A).subtype, (Sm k r (Wq →L[ℂ] Wp)).subtype, mulOp k r _, hgl,
    glRel_of_intertwine _ _ _ (Submodule.subtype_injective _) hint hgl, hint, ?_,
    fun v => smooth_iff.1 v.2.1, sm_ext, fun w => w.2.1, ?_, ev_Eu, ev_qdet, ?_⟩
  · intro u w
    apply Submodule.subtype_injective
    unfold qdet
    rw [qminor_intertwine _ _ _ _ _ _ _ hint, map_smul]
    exact w.2.2 u
  · rintro f ⟨hf, hfc⟩ hY
    have hcut : ∀ g ∈ B.GV k r, f g = (vK isOpen_univ f (smooth_iff.2 hf) : B.Mat k r → (Wq →L[ℂ] Wp)) g :=
      fun g hg => (cut_of_mem f (mem_lev.2 hg)).symm
    refine ⟨⟨vK isOpen_univ f (smooth_iff.2 hf), fun m => (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ hcut).2 m (hfc m),
      fun u => ?_⟩, fun g hg => (hcut g hg).symm⟩
    refine sm_ext _ _ fun g hg => ?_
    have h1 := ev_qdet (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) (vK isOpen_univ f (smooth_iff.2 hf)) g hg
    rw [sub_add_cancel] at h1
    have h2 := GlobalTheory.capelli_eigen_real_to_complex k r Wp Wq lam f hf hY (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) g hg
    rw [CV_eq] at h1 h2
    rw [h1, ← qminorOp_loc isOpen_univ id id _ f _ (fun x hx => hcut x (mem_lev.1 hx)) g (mem_lev.2 hg), h2,
      Submodule.coe_smul, Pi.smul_apply, ← hcut g hg]
    congr 1
    exact Finset.prod_congr rfl fun s _ => by ring
  · intro c hc
    simp only [mulOp, dif_pos hc]
    refine ⟨fun v g hg => ev_M isOpen_univ (smooth_iff.2 hc) v (mem_lev.2 hg), fun a b v g hg => ?_⟩
    have := ev_EM (i := 0) isOpen_univ (c0 a) (c0 b) (smooth_iff.2 hc) v (mem_lev.2 hg)
    rw [position_level_zero_coord, position_level_zero_coord, ← ev_Eu a b v g hg] at this
    exact this

end GlobalTheory
