import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovectorMultiplierShift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EhInvEntry
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliModuleModel

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_inv_entry (k r : ℕ) (c j : Fin (2 * r + k + 1)) :
    B.CkOn ⊤ (B.GV k r) (fun y : B.Mat k r => y⁻¹ c j) := by
  intro g₀ _
  refine ⟨Set.univ, fun g => Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c g, isOpen_univ, trivial,
    (Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c).contDiff.contDiffOn, fun g _ hg => ?_⟩
  show g⁻¹ c j = Matrix.mulVec (Hpk k r * g.conjTranspose * Hpk k r) (Pi.single j 1) c
  rw [← Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp

theorem inCC_inv_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (c j : Fin (2 * r + k + 1)) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A m F) :
    B.InCC (A - 1) m (fun g : B.Mat k r => g⁻¹ c j • F g) := by
  have hg : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => g⁻¹ c j) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_congr (fun g _ => by simp)
      (Formalism.FourierDecayAlt.P.JCx2.pd_good_inv (Wp := Wp) (Wq := Wq) (Pi.single j 1) c)
  obtain ⟨K, -, hK⟩ := hg.2 (A - 1) m
  obtain ⟨b, hb⟩ := hF
  exact ⟨K * b, hK F b (by rw [Nat.cast_one, sub_add_cancel]; exact hb)⟩

theorem inv_entry_smul_eigen_split : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  intro k r Wp Wq _ _ _ _ _ _ lam A i j f hlam hf heig
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hE, hE', hι, hq, hsm, hext, hcc, hex, -, hqC, hmul⟩ :=
    GlobalTheory.capelli_module_model k r Wp Wq lam A
  obtain ⟨w, hw⟩ := hex f hf heig
  let x : Fin (2 * r + k + 1) → Module.End ℂ V := fun c => mul (fun y : B.Mat k r => y⁻¹ c j)
  have hx : ∀ c v, ∀ g ∈ B.GV k r, ev (x c v) g = g⁻¹ c j • ev v g :=
    fun c => (hmul _ (ckOn_inv_entry k r c j)).1
  have hcomm : ∀ a b c, E a b * x c = x c * E a b - if a = c then x b else 0 := by
    intro a b c
    ext v
    refine hext _ _ fun g hg => ?_
    have h1 := (hmul _ (ckOn_inv_entry k r c j)).2 a b v g hg
    rw [GlobalTheory.eh_inv_entry k r a b c j g hg] at h1
    rw [Module.End.mul_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.mul_apply, hx _ _ g hg]
    refine h1.trans ?_
    split_ifs with h
    · rw [hx _ _ g hg, neg_smul, sub_eq_add_neg]
    · simp
  have hinj : Function.Injective
      (fun s => ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2)) := by
    intro s t h
    apply hlam
    have h' : (lam s : ℂ) = lam t := sub_left_inj.1 h
    exact_mod_cast h'
  obtain ⟨v, hv1, hv2⟩ := GlobalTheory.covector_multiplier_shift V W _ E E' ι x _ hE hE' hι hinj hq hcomm i w
  refine ⟨fun t => ev (∑ a, x a (ι (v t a))), fun t => ⟨hsm _, fun m => ?_⟩, fun t Y g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum (A := A - 1) (m := m) Finset.univ
      (fun a (g : B.Mat k r) => g⁻¹ a j • ev (ι (v t a)) g)
      (fun a _ => inCC_inv_entry_smul a j (hcc (v t a) m))
    refine ⟨b, Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => ?_) hb⟩
    beta_reduce
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hx _ _ g hg).symm
  · rw [← hqC _ _ g hg, hv2, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> ring
  · rw [← hw g hg, ← hx i _ g hg, hv1, map_sum, Finset.sum_apply]

end GlobalTheory
