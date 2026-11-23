import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineUnit

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped NNReal

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {k : ℕ}

theorem exists_lt_nnnorm (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : ∃ t : Fv F v, C < ‖t‖₊ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm (Fv F v) (C : ℝ)
  exact ⟨t, by exact_mod_cast ht⟩

theorem valBar_smul (τ : E →ₐ[F] FvBar F v) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    valBar F v (finEmb F v τ (t • y)) = ‖t‖₊ * valBar F v (finEmb F v τ y) := by
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  exact absBar_algebraMap F v t

theorem mem_intLoc_iff_valBar {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ ∀ τ : E →ₐ[F] FvBar F v, valBar F v (finEmb F v τ y) ≤ 1 :=
  mem_intLoc_iff_absFin_le_one.trans (absFin_le_iff F v)

theorem exists_valBar_ne_zero {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) (τ : E →ₐ[F] FvBar F v) :
    ∃ j, valBar F v (finEmb F v τ (u j)) ≠ 0 := by
  by_contra hc
  push Not at hc
  have := congrArg (finEmb F v τ) h
  rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by
    rw [map_mul, (Valuation.zero_iff _).1 (hc j), mul_zero]] at this
  exact zero_ne_one this

theorem mem_intLoc_of_stable {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, a * u j ∈ intLoc F E v) → ∀ j, c * a * u j ∈ intLoc F E v) : c ∈ intLoc F E v := by
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (Finset.univ.sup fun j => absFin F v (u j))
  have ht0 : ‖t‖₊ ≠ 0 := (lt_of_le_of_lt zero_le ht).ne'
  have h0 : ∀ j, (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun j => by
    rw [smul_mul_assoc, one_mul, mem_intLoc_iff_valBar]
    intro τ
    rw [valBar_smul, nnnorm_inv, inv_mul_le_iff₀ (pos_iff_ne_zero.2 ht0), mul_one]
    exact (le_absFin F v τ (u j)).trans
      ((Finset.le_sup (f := fun j => absFin F v (u j)) (Finset.mem_univ j)).trans ht.le)
  have hk : ∀ m : ℕ, ∀ j, c ^ m * (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun m => by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using h0
    | succ m ih =>
      intro j
      have := hc _ ih j
      rwa [← mul_assoc, ← pow_succ'] at this
  rw [mem_intLoc_iff_valBar]
  intro τ
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)) :=
    mul_pos (inv_pos.2 (pos_iff_ne_zero.2 ht0)) (pos_iff_ne_zero.2 hj)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)))⁻¹ hlt
  have h1 := mem_intLoc_iff_valBar.1 (hk m j) τ
  rw [mul_assoc, smul_mul_assoc, one_mul, map_mul, map_mul, map_pow, map_pow, valBar_smul, nnnorm_inv,
    ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 hm)

theorem isUnit_of_reflect {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, c * a * u j ∈ intLoc F E v) → ∀ j, a * u j ∈ intLoc F E v) : IsUnit c := by
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_left.2 fun a ha => ?_)
  refine absFin_eq_zero_iff.1 (le_antisymm ((absFin_le_iff F v).2 fun τ => ?_) zero_le)
  by_contra hne
  have hpa : 0 < valBar F v (finEmb F v τ a) := not_le.1 hne
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  have hpos : 0 < valBar F v (finEmb F v τ (a * u j)) := by
    rw [map_mul, map_mul]; exact mul_pos hpa (pos_iff_ne_zero.2 hj)
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (valBar F v (finEmb F v τ (a * u j)))⁻¹
  have h1 := mem_intLoc_iff_valBar.1
    (hc (t • a) (fun j => by rw [mul_smul_comm, ha, smul_zero, zero_mul]; exact zero_mem _) j) τ
  rw [smul_mul_assoc, valBar_smul, ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 ht)

theorem smul_mem_latLoc_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    {w l : Fin n → Fv F v ⊗[F] E} (h : l ⬝ᵥ w = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a : Fv F v ⊗[F] E, (c * a) • w ∈ latLoc F L v ↔ a • w ∈ latLoc F L v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ c • y ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := F) (Fv F v) h1
  set u := Φ.map (inclR (F := F) (Fv F v)) *ᵥ w with hu
  have hl : ∑ j, (l ᵥ* S.map (inclR (F := F) (Fv F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, hu, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, h]
  have key : ∀ a : Fv F v ⊗[F] E, a • w ∈ latLoc F L v ↔ ∀ j, a * u j ∈ intLoc F E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  simp only [key] at hc
  have hc1 := mem_intLoc_of_stable hl fun a => (hc a).2
  obtain ⟨c, rfl⟩ := isUnit_of_reflect hl fun a => (hc a).1
  have hc2 : ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v :=
    mem_intLoc_of_stable hl fun a ha => (hc _).1 fun j => by rw [Units.mul_inv_cancel_left]; exact ha j
  refine ⟨fun hy => (latLoc F L v).smul_mem ⟨_, hc1⟩ hy, fun hy => ?_⟩
  have := (latLoc F L v).smul_mem ⟨_, hc2⟩ hy
  change ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (c : Fv F v ⊗[F] E) • y ∈ _ at this
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end Local

set_option maxHeartbeats 1600000 in

theorem smul_mem_latV_iff : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Λ : GlobalTheory.FinPl.Lat V), Submodule.IsLattice D.host.E Λ → ∀ (v : GlobalTheory.FinPl.Pl D) (ε : Fin V.rank → D.host.E), ε ≠ 0 → ∀ (c : AE D) (s : Matrix (Fin V.rank) (Fin V.rank) (AE D)), IsUnit s → (∀ a ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (s) (fun i => c * (a * Formalism.L2.Theta.incA D (ε i))) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ Matrix.mulVec (s) (fun i => a * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V Λ (· = v))) → ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ c • y ∈ GlobalTheory.FinPl.latV V Λ (· = v)) := by
  intro D V Λ hΛ v ε hε c s hs h y hy
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  let π : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).comp (finPart D)
  have hπ : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ GlobalTheory.FinPl.idAt D (· = v)) →
      (z ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ (fun i => π (z i)) ∈ latLoc D.host.F Λ v) := fun z hz =>
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hfg v z hz
  let w : Fin V.rank → AE D := s *ᵥ fun i => Formalism.L2.Theta.incA D (ε i)
  have hw : ∀ a : AE D, (s *ᵥ fun i => a * Formalism.L2.Theta.incA D (ε i)) = a • w := fun a =>
    Matrix.mulVec_smul s a _
  obtain ⟨l, hl⟩ : ∃ l : Fin V.rank → AE D, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    obtain ⟨s', rfl⟩ := hs
    refine ⟨(Pi.single i (Formalism.L2.Theta.incA D (ε i)⁻¹)) ᵥ* (s'⁻¹).1, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hl' : (fun i => π (l i)) ⬝ᵥ (fun i => π (w i)) = 1 := by
    rw [← map_one π, ← hl]
    simp only [dotProduct, map_sum, map_mul]
  have hsm : ∀ (a : AE D) (z : Fin V.rank → AE D), (fun i => π ((a • z) i)) = π a • fun i => π (z i) :=
    fun a z => funext fun i => map_mul π a (z i)
  rw [hπ y hy, hπ (c • y) fun i => Ideal.mul_mem_left _ _ (hy i), hsm]
  refine smul_mem_latLoc_iff Λ hΛ hl' (fun b => ?_) _
  obtain ⟨a, ha, hab⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => b
  have hab' : π (a 0) = b := congrFun hab 0
  have h1 := h (a 0) (ha 0)
  simp only [← mul_assoc] at h1
  rw [hw, hw, hπ ((c * a 0) • w) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha 0)),
    hπ (a 0 • w) fun i => Ideal.mul_mem_right _ _ (ha 0), hsm, hsm, map_mul, hab'] at h1
  exact h1

end GlobalTheory.LineUnit

end
