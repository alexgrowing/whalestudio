import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

namespace C

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

theorem hsum (r s : ℕ) : ∑ i, ![r, s] i = r + s := by simp [Fin.sum_univ_two]

abbrev eC (r s : ℕ) : (Σ i, Fin (![r, s] i)) ≃ Fin (r + s) := GlobalTheory.SmGL.stdBlocks ![r, s] (hsum r s)

theorem eC_zero (i : Fin r) : eC r s ⟨0, i⟩ = Fin.castAdd s i :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 0 i).trans (by simp))

theorem eC_one (j : Fin s) : eC r s ⟨1, j⟩ = Fin.natAdd r j :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 1 j).trans (by simp))

theorem lowLeft {p : GL (Fin (r + s)) (Cinf E)} (hp : p ∈ parab (Cinf E) (eC r s)) :
    ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (p : Matrix _ _ (Cinf E)) i j = 0 := by
  intro i j hi hj
  have h := GlobalTheory.SmGL.mem_parab_iff.1 hp 1 0 (show Fin s from ⟨i - r, by omega⟩) (show Fin r from ⟨j, hj⟩)
    (by decide)
  rw [eC_one, eC_zero] at h
  convert h using 2 <;> apply Fin.ext <;> simp; omega

theorem decomp (p : parab (Cinf E) (eC r s)) :
    ∃ (u : BlockIx (r + s) r → Cinf E) (m : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)),
      p.1 = unip u * lev (Cinf E) r s m :=
  IwaFin.exists_unip_mul_lev r s p.1 (lowLeft p.2) (lowLeft (inv_mem p.2))

theorem contDiff_cc : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (Cinf E) (Fin.castAdd s j)).comp (contDiff_apply ℝ (Fin (r + s) → Cinf E) (Fin.castAdd s i))

theorem contDiff_nn : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (Cinf E) (Fin.natAdd r j)).comp (contDiff_apply ℝ (Fin (r + s) → Cinf E) (Fin.natAdd r i))

end C

open C in
theorem exists_local (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) :
    ∃ (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E))
      (κ : Lie E (r + s) → Kinf E (r + s)) (u : Lie E (r + s) → BlockIx (r + s) r → Cinf E),
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (κ y).1) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧ κ (oneL E (r + s)) = 1 ∧
      ∀ᶠ y in nhds (oneL E (r + s)), Matrix.of y = (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1 := by
  obtain ⟨p, k, hp, hk, hp1, hk1, hpk⟩ := GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa E ![r, s] (eC r s)
  choose u m hm using fun y => decomp (E := E) (p y)
  have e1 : ∀ y, toL (m y).1.val = (fun i j => toL (p y).1.val (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
    fun y => by
      funext i j
      change ((m y).1 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.castAdd s i) (Fin.castAdd s j)
      rw [hm y, unip_lev_cc]
  have e2 : ∀ y, toL (m y).2.val = (fun i j => toL (p y).1.val (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
    fun y => by
      funext i j
      change ((m y).2 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.natAdd r i) (Fin.natAdd r j)
      rw [hm y, unip_lev_nn]
  refine ⟨fun y => (m y).1, fun y => (m y).2, k, u, ?_, ?_, hk, ?_, ?_, hk1, ?_⟩
  · simp only [e1]
    exact contDiff_cc.contDiffAt.comp _ hp
  · simp only [e2]
    exact contDiff_nn.contDiffAt.comp _ hp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e1 (oneL E (r + s))) i) j
    change ((m _).1 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e2 (oneL E (r + s))) i) j
    change ((m _).2 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.natAdd_inj]
  · filter_upwards [hpk] with y hy
    rw [hy, hm y]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
