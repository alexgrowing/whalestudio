import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacTypeVec

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock GlobalTheory.JacBlockTwo ValuativeRel Matrix

theorem exists_irreducible_subquotient_rel (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
          ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y :=
  _root_.GlobalTheory.QuotientGenerator.exists_irreducible_subquotient G V ρ x hx

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mulSingle_false_mem_KO {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (a : Bool) :
    (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) a ∈ KO F (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_same]; exact hg
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _

theorem deltaHalf_mulSingle_false {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) :
    deltaHalf F (Two (Fin r) (Fin t)) (Pi.mulSingle false g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow F _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_false_mem_KO (t := t) hg a)

theorem emb₂_one_eq {r t : ℕ} (g : GL (Fin r) F) :
    emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) =
      leviEmb F (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
  unfold emb₂
  rw [MonoidHom.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem jac_mulSingle_false {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin (r + t)) F) W) {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (v : W) :
    jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle false g) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v) := by
  rw [jac_mk, deltaHalf_mulSingle_false hg, inv_one, Units.val_one, one_smul, emb₂_one_eq]

theorem act_mulSingle_false_KOne {r t : ℕ} {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) F) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin r) F} (hg : g ∈ KOne F (Fin r)) :
    π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v = v := by
  set h := emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) with hdef
  have hval : ∀ i j, h.val i j = Matrix.reindex (stdSum (rfl : r + t = r + t)) (stdSum (rfl : r + t = r + t))
      (Matrix.fromBlocks g.val 0 0 (1 : GL (Fin t) F).val) i j := fun i j => by
    rw [hdef, val_emb₂]
  have hKO : h ∈ KO F (Fin (r + t)) := by
    have hg' : g ∈ KO F (Fin r) := GlobalTheory.StepData.KOne_le_KO hg
    have e : h = leviEmb F (two (stdSum (rfl : r + t = r + t)))
        (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
      rw [hdef, emb₂_one_eq]
    rw [e]
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_false_mem_KO hg' a), ?_⟩
    rw [← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_false_mem_KO hg' a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [hval, ← stdSum_inr', ← stdSum_inl']
    simp
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = g.val i j := fun i j => by
    rw [hval, ← stdSum_inl', ← stdSum_inl']
    simp
  have h2 : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, hval, ← stdSum_inr', ← stdSum_inr']
    simp
  have hg1 := GlobalTheory.StepData.mem_KOne.1 hg
  have key := hv h hKO (fun i j => by simp [h0]) (fun i j => by
      rw [h1]; have := hg1 i j; simpa [Matrix.sub_apply, Matrix.one_apply] using this) 1
    (by rw [h2, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

end Local

theorem exists_subquot_typeVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  intro hP F _ _ _ _ p _ r t χ W _ _ π z y ℓ hp hsm hirr hχ hy0 hy hℓ hz
  obtain ⟨hx0, hxt⟩ := jacquet_ne_zero_of_isBlockVec_two hP F r t χ W π y hsm hirr hχ hy0 hy
  set x : Jacquet π (unipRad F (two (stdSum (rfl : r + t = r + t)))) := Submodule.Quotient.mk y with hxdef
  obtain ⟨Y, _, _, τ, w, hτ, hsq, hw0, hrel⟩ :=
    exists_irreducible_subquotient_rel _ _ (jac (two (stdSum (rfl : r + t = r + t))) π) x hx0
  refine ⟨Y, inferInstance, inferInstance, τ, hτ, hsq, w, hw0, fun g hg => ?_, ?_, ℓ, hℓ, ?_⟩
  · have := hrel Unit {()} (fun _ => Pi.mulSingle true g) (fun _ => 1) _ (by
      simpa using hxt g hg)
    simpa using this
  · intro h hh
    have := hrel Unit {()} (fun _ => Pi.mulSingle false h) (fun _ => 1) 1 (by
      simp only [Finset.sum_singleton, one_smul]
      rw [hxdef, jac_mulSingle_false π (GlobalTheory.StepData.KOne_le_KO hh), act_mulSingle_false_KOne hy hh])
    simpa using this
  · have hsum : ∑ g ∈ z.coeff.support, z.coeff g • jac (two (stdSum (rfl : r + t = r + t))) π
        (Pi.mulSingle false (ℓ g)) x = (1 : ℂ) • x := by
      rw [one_smul, hxdef]
      have e : ∀ g ∈ z.coeff.support, z.coeff g • jac (two (stdSum (rfl : r + t = r + t))) π
          (Pi.mulSingle false (ℓ g)) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (z.coeff g • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) :=
        fun g _ => by rw [jac_mulSingle_false π ((hℓ g).mem_KO hp), Submodule.Quotient.mk_smul]
      rw [Finset.sum_congr rfl e]
      conv_rhs => rw [← hz, Finsupp.sum]
      exact (map_sum (Submodule.mkQ _) _ _).symm
    have := hrel _ z.coeff.support (fun g => Pi.mulSingle false (ℓ g)) z.coeff 1 hsum
    rw [one_smul] at this
    intro h0
    apply hw0
    rw [← this, ← h0, Finsupp.sum]
    rfl

end GlobalTheory.JacTypeVec
