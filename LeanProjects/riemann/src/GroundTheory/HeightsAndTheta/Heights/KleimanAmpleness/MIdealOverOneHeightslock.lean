import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

section Block

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {L : Type} [Field L] [Algebra F L]

theorem comap_mIdealOver_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    (mIdealOver F y).comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) := by
  have h1 : (mConeMapOver F y).comp (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      ((Polynomial.aeval (X k₀ : MvPolynomial K L)).restrictScalars F).comp
        (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have h2 : ∀ q : Polynomial L,
      aeval (fun _ : K => (Polynomial.X : Polynomial L)) (Polynomial.aeval (X k₀ : MvPolynomial K L) q) = q :=
    fun q => by rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver F y (rename _ f) = 0 ↔ _
  have h := AlgHom.congr_fun h1 f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [← h2 (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

theorem mIdealOver_oneBlock_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      baseComap F k₀ e (mIdealOver F y) := by
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := L) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F _ f = 0 ↔ mConeMapOver F y (rename _ f) = 0
  have h := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact rename_injective _ (fun a b _ => Subsingleton.elim a b) (h0.trans (map_zero _).symm)

end Block

theorem CurveNumModel.proof (hMP : ModelPoint.Statement) (hRR : RealiseRestrict.Statement)
    (hIR : Kleiman.InterNumRestrict.Statement.{0, 0}) (hNM : NumModel.Statement) (hMC : ModelCurves.Statement) :
    CurveNumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hm Q β hQ W hW hle hrel
  classical
  have := hW.isPrime
  have hWy : mIdealOver F (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F), hWy]
  have hy' : ∀ k, ∃ i, genPtOf W ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hW.relevant k
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hleW : mIdealOver F y ≤ mIdealOver F (genPtOf W) := hWy.symm ▸ hle
  have hm' := hMP F K ι Ω y k₀ hm _ (genPtOf W) hy' hleW
  have hxy : ∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0 := fun i h h0 => by
    rw [hx] at h0
    exact h ((hzero ⟨k₀, e.symm i⟩).mpr (hle ((X_mem_mIdealOver_iff y ⟨k₀, e.symm i⟩).mpr h0)))
  obtain ⟨Q', r, hR, hQ'⟩ := hRR F K ι Ω y k₀ N e x hx hm Q β hQ _ (genPtOf W) hm' hleW hxy
  have hpp : Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) =
      W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) := by
    rw [← comap_mIdealOver_block, hWy]
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)) 1 := by
    refine (isSubvar_iff_relDim _ 1).mpr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hy' k₀
      exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
    · rw [mIdealOver_oneBlock_block, hWy]
      exact ((hMC F K ι Ω y k₀ N e x hx hm 1).1 W hW hle hrel).2.2
  have hxx : Kleiman.primeOf (S := F) x ≤
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) := by
    rw [hx, ← comap_mIdealOver_block, ← comap_mIdealOver_block]
    exact Ideal.comap_mono hleW
  have h1 := hIR F Ω N x _ _ hxy hxx _ 1 hsub ![Q] ![Q'] (fun _ => r) (fun i => by fin_cases i; exact hR)
  have h2 := hNM F K ι _ (genPtOf W) k₀ N e _ rfl hm' 1 ![Q'] ![β] (fun i => by fin_cases i; exact hQ') hsub
  rw [hWy] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1, hpp]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
