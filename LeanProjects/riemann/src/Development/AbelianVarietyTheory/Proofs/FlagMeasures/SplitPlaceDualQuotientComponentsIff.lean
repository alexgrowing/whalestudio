import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.DualComp

section Form

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem expand (hσ : ∀ a, σ (σ a) = a) (x y : Fin n → Fin n → A)
    (hd : ∀ i j, hform σ J (x i) (y j) = if i = j then 1 else 0) (w : Fin n → A) :
    w = ∑ i, σ (hform σ J w (y i)) • x i := by
  let X : Matrix (Fin n) (Fin n) A := fun i k => σ (x i k)
  let Y : Matrix (Fin n) (Fin n) A := fun k j => ∑ l, J k l * y j l
  have h1 : X * Y = 1 := by
    ext i j
    rw [Matrix.one_apply, ← hd i j, Matrix.mul_apply]
    simp only [X, Y, hform, Finset.mul_sum, mul_assoc]
  have h2 : Y * X = 1 := mul_eq_one_comm.1 h1
  funext k
  have h3 : σ (w k) = ∑ i, hform σ J w (y i) * σ (x i k) := by
    have h4 : ∀ i, hform σ J w (y i) = ∑ l, σ (w l) * Y l i := by
      intro i
      simp only [Y, hform, Finset.mul_sum, mul_assoc]
    have h5 : ∀ l, ∑ i, σ (w l) * Y l i * σ (x i k) = σ (w l) * (Y * X) l k := by
      intro l
      rw [Matrix.mul_apply, Finset.mul_sum]
      simp only [mul_assoc, X]
    simp only [h4, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [h5, h2, Matrix.one_apply]
    simp
  rw [← hσ (w k), h3]
  simp only [map_sum, map_mul, hσ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J i j) = J j i) (x y : Fin n → A) :
    hform σ J y x = σ (hform σ J x y) := by
  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem mem_loc_of_pair (hJ : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L)
    (v : HeightOneSpectrum (𝓞 F))
    (hσ : ∀ a, sigR σ (v.adicCompletion F) (sigR σ (v.adicCompletion F) a) = a)
    (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : ∀ y ∈ loc v (dualL σ J L), hR σ J (v.adicCompletion F) w y ∈ intV E v) : w ∈ loc v L := by
  obtain ⟨x, yb, s, hs, hxL, hdu, -, hyL⟩ := Dual.exists_dual_basis σ J hJ L hL v
  obtain ⟨us, husO, hus⟩ := PI.SelfDualLoc.W.unitLoc F E v s hs
  have husO' : us ∈ intV E v := husO
  have hus' : inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) * us = 1 := hus
  have hy : ∀ j, (fun i => inclE (F := F) (v.adicCompletion F) (yb j i)) ∈ loc v (dualL σ J L) := by
    intro j
    have hg : (fun i => inclE (F := F) (v.adicCompletion F)
        ((algebraMap F E (s : F) • yb j) i)) ∈ loc v (dualL σ J L) :=
      Submodule.subset_span ⟨_, hyL j, rfl⟩
    have hmem := Submodule.smul_mem _ (⟨us, husO'⟩ : intV E v) hg
    rw [Subring.smul_def] at hmem
    convert hmem using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(inclE (F := F) (v.adicCompletion F) (yb j i))) * hus'
  have he := expand (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) hσ
    (fun j i => inclE (F := F) (v.adicCompletion F) (x j i))
    (fun j i => inclE (F := F) (v.adicCompletion F) (yb j i))
    (fun i j => by
      have h4 := Dual.hR_incl σ J (v.adicCompletion F) (x i) (yb j)
      unfold hR at h4
      rw [h4, hdu]
      split_ifs <;> simp) w
  rw [he]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hg : (fun i => inclE (F := F) (v.adicCompletion F) (x j i)) ∈ loc v L :=
    Submodule.subset_span ⟨_, hxL j, rfl⟩
  exact Submodule.smul_mem _ (⟨_, Dual.sig_int σ _ _ _ (hw _ (hy j))⟩ : intV E v) hg

end GlobalTheory.St.G.DualComp

namespace GlobalTheory.St.G

theorem dual_components_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L _ _ _ hT v _ sp hsig hdiag
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  have hσ : ∀ a, sigR cm.sig (v.adicCompletion F) (sigR cm.sig (v.adicCompletion F) a) = a := by
    intro a
    apply sp.injective
    rw [hsig, hsig]
    rfl
  have hJ' : ∀ i j, sigR cm.sig (v.adicCompletion F) (J.map (inclE (F := F) (v.adicCompletion F)) i j) =
      J.map (inclE (F := F) (v.adicCompletion F)) j i := by
    intro i j
    have h1 : cm.sig (J i j) = J j i := congrFun (congrFun hJ j) i
    rw [Matrix.map_apply, Matrix.map_apply, ← h1]
    exact PI.SelfDualLoc.W.sigR_inclE cm.sig _ _
  have h1 : ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 =
      ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro x y
    unfold hR hform
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have h2 : ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).2 =
      ∑ i, ∑ j, (sp (x i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro x y
    unfold hR hform
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have hp : ∀ y ∈ loc v (dualL cm.sig J L), ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) y z ∈ intV E v := by
    intro y hy z hz
    have h := Dual.sig_int cm.sig _ _ _ (Dual.fwd cm.sig J _ _ L y hy z hz)
    unfold hR at h ⊢
    rwa [DualComp.conj_symm _ _ hσ hJ' z y]
  constructor
  · intro h y hy
    refine ⟨fun b => sp.symm (0, (sp (y b)).2), ?_, fun b => by rw [sp.apply_symm_apply]⟩
    refine DualComp.mem_loc_of_pair cm.sig J hdet L hT.1 v hσ _ fun w hw => ?_
    obtain ⟨z, hz, e⟩ := h w hw
    have h3 := ((hint _).1 (hp y hy z hz)).1
    rw [hint, h1, h2]
    rw [h1] at h3
    simp only [sp.apply_symm_apply, zero_mul, Finset.sum_const_zero, ← e]
    exact ⟨h3, zero_mem _⟩
  · intro h y hy
    refine ⟨fun b => sp.symm ((sp (y b)).1, 0), ?_, fun b => by rw [sp.apply_symm_apply]⟩
    refine DualComp.mem_loc_of_pair cm.sig J hdet L hT.1 v hσ _ fun w hw => ?_
    obtain ⟨z, hz, e⟩ := h w hw
    have h3 := ((hint _).1 (hp y hy z hz)).2
    rw [hint, h1, h2]
    rw [h2] at h3
    simp only [sp.apply_symm_apply, zero_mul, Finset.sum_const_zero, ← e]
    exact ⟨zero_mem _, h3⟩

end GlobalTheory.St.G
