import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellSum

theorem schurDir_eq_tsum_locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) :
    GlobalTheory.RSPole.schurDir q α x = ∑' ν : Fin n → ℤ, GlobalTheory.RSCell.locFac q α x ν := by
  let g : {l : Fin n → ℕ // Antitone l} → (Fin n → ℤ) := fun l i => (l.1 i : ℤ)
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa [g] using this
  have hs : Function.support (GlobalTheory.RSCell.locFac q α x) ⊆ Set.range g := by
    intro ν hν
    rw [Function.mem_support] at hν
    unfold GlobalTheory.RSCell.locFac at hν
    split_ifs at hν with h
    · refine ⟨⟨fun i => (ν i).toNat, fun i j hij => Int.toNat_le_toNat (h.1 hij)⟩, ?_⟩
      funext i
      simp [g, Int.toNat_of_nonneg (h.2 i)]
    · exact absurd rfl hν
  rw [← hg.tsum_eq hs, GlobalTheory.RSPole.schurDir]
  refine tsum_congr fun l => ?_
  have hA : Antitone (g l) ∧ ∀ i, 0 ≤ g l i :=
    ⟨fun i j hij => by simpa [g] using l.2 hij, fun i => by simp [g]⟩
  rw [GlobalTheory.RSCell.locFac, if_pos hA]
  simp [g]

theorem tsum_cellProd_sub_eq_eulD (E : Type) [Field E] [NumberField E] (n : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T) :
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  let sh : GlobalTheory.CellDec.abelian₂ E n T ≃ GlobalTheory.CellDec.abelian₂ E n T :=
    { toFun := fun l => ⟨l.1 - l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      invFun := fun l => ⟨l.1 + l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 :=
    sh.tsum_eq (fun l => GlobalTheory.RSCell.cellProd T α x l.1)
  rw [h1]
  have hsupp : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, ∀ w ∈ l.1.support, w ∉ T := fun l w hw hT =>
    (Finsupp.mem_support_iff.1 hw) (l.2 w hT)
  let e : GlobalTheory.CellDec.abelian₂ E n T ≃ ({w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin n → ℤ)) :=
    { toFun := fun l => l.1.subtypeDomain (fun w => w ∉ T)
      invFun := fun ν => ⟨ν.extendDomain, fun v hv => by simp [Finsupp.extendDomain_apply, hv]⟩
      left_inv := fun l => Subtype.ext (Finsupp.extendDomain_subtypeDomain l.1 (hsupp l))
      right_inv := fun ν => Finsupp.subtypeDomain_extendDomain ν }
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → (Fin n → ℤ) → ℝ≥0∞ :=
    fun w ν => GlobalTheory.RSCell.locFac (Ideal.absNorm w.1.asIdeal) (α w) x ν
  have hf0 : ∀ w, f w 0 = 1 := fun w => GlobalTheory.RSCell.locFac_zero _ _ _
  let h : HeightOneSpectrum (𝓞 E) → (Fin n → ℤ) → ℝ≥0∞ := fun w ν =>
    if hw : w ∈ T then 1 else GlobalTheory.RSCell.locFac (Ideal.absNorm w.asIdeal) (α ⟨w, hw⟩) x ν
  have h2 : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 = (e l).prod f := by
    intro l
    have : (e l).prod f = (l.1.subtypeDomain (fun w => w ∉ T)).prod (fun a b => h a.1 b) := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [h, dif_neg a.2, f]
      rfl
    rw [this, Finsupp.prod_subtypeDomain_index (hsupp l)]
    rfl
  rw [tsum_congr h2, e.tsum_eq (fun ν => ν.prod f),
    (GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
  refine tprod_congr fun w => ?_
  rw [schurDir_eq_tsum_locFac]

end GlobalTheory.RSCellSum
