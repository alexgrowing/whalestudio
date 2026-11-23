import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NestedStab

section Local

variable {K : Type} [Field K] (A : ValuationSubring K)

theorem conj_single_apply {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (hab : a * b = 1) (i j p q : Fin n) :
    (a * Matrix.transvection i j (1 : K) * b) p q = (1 : Matrix (Fin n) (Fin n) K) p q + a p i * b j q := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab, Matrix.add_apply]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem prod_mem_off {n : ℕ} (γ : GL (Fin n) K)
    (hγ : ∀ h : GL (Fin n) A, ∀ p q,
      ((γ * Matrix.GeneralLinearGroup.map (algebraMap A K) h * γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p q ∈ A)
    (p i j q : Fin n) (hij : i ≠ j) :
    (γ : Matrix (Fin n) (Fin n) K) p i * ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j q ∈ A := by
  let t : GL (Fin n) A := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
    by rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have h1 := hγ t p q
  have hm : ((Matrix.GeneralLinearGroup.map (algebraMap A K) t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transvection i j (1 : K) := by
    ext a b
    simp [t, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  have hab : (γ : Matrix (Fin n) (Fin n) K) * ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by simp
  rw [Units.val_mul, Units.val_mul, hm, conj_single_apply _ _ hab] at h1
  have h2 : (1 : Matrix (Fin n) (Fin n) K) p q ∈ A := by
    rw [Matrix.one_apply]; split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  have := A.sub_mem h1 h2
  simpa using this

theorem prod_mem {n : ℕ} (γ : GL (Fin n) K)
    (hγ : ∀ h : GL (Fin n) A, ∀ p q,
      ((γ * Matrix.GeneralLinearGroup.map (algebraMap A K) h * γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p q ∈ A)
    (p i j q : Fin n) :
    (γ : Matrix (Fin n) (Fin n) K) p i * ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j q ∈ A := by
  set a := (γ : Matrix (Fin n) (Fin n) K)
  set b := ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hab : a * b = 1 := by simp [a, b]
  have hba : b * a = 1 := by simp [a, b]
  by_cases hij : i = j
  · subst hij
    by_cases hk : ∃ k, k ≠ i
    · obtain ⟨k, hk⟩ := hk
      have e : a p i * b i q = ∑ r, (a p i * b k r) * (a r k * b i q) := by
        have : ∑ r, b k r * a r k = 1 := by
          have := congrFun (congrFun hba k) k
          simpa [Matrix.mul_apply] using this
        calc a p i * b i q = a p i * (∑ r, b k r * a r k) * b i q := by rw [this, mul_one]
          _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun r _ => by ring
      rw [e]
      exact A.sum_mem fun r _ => mul_mem (prod_mem_off A γ hγ p i k r (Ne.symm hk)) (prod_mem_off A γ hγ r k i q hk)
    · push_neg at hk
      rw [hk p, hk q]
      have : ∑ r, a i r * b r i = 1 := by
        have := congrFun (congrFun hab i) i
        simpa [Matrix.mul_apply] using this
      rw [Fintype.sum_eq_single i (fun r hr => absurd (hk r) hr)] at this
      rw [this]; exact A.one_mem
  · exact prod_mem_off A γ hγ p i j q hij

end Local

end GlobalTheory.NestedStab

namespace GlobalTheory.NestedStab

section Local

variable {K : Type} [Field K] (A : ValuationSubring K)

theorem exists_int_conj {n : ℕ} (γ : GL (Fin n) K)
    (hγ : ∀ h : GL (Fin n) A, ∀ p q,
      ((γ * Matrix.GeneralLinearGroup.map (algebraMap A K) h * γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p q ∈ A) :
    ∃ m₀ : GL (Fin n) A, ∀ X : GL (Fin n) K,
      γ * X * γ⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap A K) m₀ * X * (Matrix.GeneralLinearGroup.map (algebraMap A K) m₀)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun X => Subsingleton.elim _ _⟩
  set a := (γ : Matrix (Fin n) (Fin n) K) with ha
  set b := ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hb
  have hab : a * b = 1 := by simp [a, b]
  have hba : b * a = 1 := by simp [a, b]
  obtain ⟨⟨p0, i0⟩, -, hmax⟩ := Finset.univ.exists_max_image (fun x : Fin n × Fin n => A.valuation (a x.1 x.2))
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := a p0 i0 with hc_def
  have hc : c ≠ 0 := by
    intro hc
    have h0 : a = 0 := by
      ext p i
      have h1 := hmax (p, i) (Finset.mem_univ _)
      simp only [← hc_def, hc, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h2 : (1 : Matrix (Fin n) (Fin n) K) = 0 := by rw [← hab, h0, Matrix.zero_mul]
    have := congrFun (congrFun h2 ⟨0, hn⟩) ⟨0, hn⟩
    simp at this
  have hvc : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hM : ∀ p i, a p i / c ∈ A := by
    intro p i
    rw [← A.valuation_le_one_iff, map_div₀, div_eq_mul_inv]
    calc A.valuation (a p i) * (A.valuation c)⁻¹ ≤ A.valuation c * (A.valuation c)⁻¹ := by
          gcongr; exact hmax (p, i) (Finset.mem_univ _)
      _ = 1 := mul_inv_cancel₀ hvc
  have hN : ∀ j q, c * b j q ∈ A := fun j q => prod_mem A γ hγ p0 i0 j q
  let M : Matrix (Fin n) (Fin n) A := Matrix.of fun p i => ⟨a p i / c, hM p i⟩
  let N : Matrix (Fin n) (Fin n) A := Matrix.of fun j q => ⟨c * b j q, hN j q⟩
  have eM : (algebraMap A K).mapMatrix M = c⁻¹ • a := by
    ext p i; simp [M, div_eq_inv_mul]
  have eN : (algebraMap A K).mapMatrix N = c • b := by
    ext p i; simp [N]
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap A K)) := by
    intro x y hxy
    ext p i
    exact congrFun (congrFun hxy p) i
  have e1 : M * N = 1 := hinj (by
    rw [map_mul, map_one, eM, eN, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, hab])
  have e2 : N * M = 1 := hinj (by
    rw [map_mul, map_one, eM, eN, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, hba])
  refine ⟨⟨M, N, e1, e2⟩, fun X => Units.ext ?_⟩
  have f1 : ((Matrix.GeneralLinearGroup.map (algebraMap A K) (⟨M, N, e1, e2⟩ : GL (Fin n) A) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c⁻¹ • a := eM
  have f2 : (((Matrix.GeneralLinearGroup.map (algebraMap A K) (⟨M, N, e1, e2⟩ : GL (Fin n) A))⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • b := eN
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, f1, f2, ← ha, ← hb, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]

end Local

end GlobalTheory.NestedStab

namespace GlobalTheory.NestedStab

section Grp

variable {G : Type} [Group G]

theorem conj_of_conj_eq (a b h x : G) (e : b * h * b⁻¹ = a * x * a⁻¹) : a⁻¹ * b * h * (a⁻¹ * b)⁻¹ = x := by
  have hx : x = a⁻¹ * (a * x * a⁻¹) * a := by group
  rw [hx, ← e]; group

theorem eq_conj_of_conj_eq (a b x y : G) (e : a * y * a⁻¹ = b * x * b⁻¹) : y = a⁻¹ * b * x * (a⁻¹ * b)⁻¹ :=
  (conj_of_conj_eq a b x y e.symm).symm

end Grp

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl SplitProj IsProjAt IsIdemOf rdA grpCo frCo)

variable {D : D7}

theorem map_frGL {v : FinPl D} (φ : SplitProj D v) {n : ℕ}
    (ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F)
    (hρ : ∀ s, (ρ s : Fv D.host.F v) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s) (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (w : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (frGL β w) =
      frCo φ β * Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v))
        (Matrix.GeneralLinearGroup.map ρ w) * (frCo φ β)⁻¹ := by
  have h0 : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (intGL D.host.F D.host.E n w) =
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v))
        (Matrix.GeneralLinearGroup.map ρ w) := Units.ext (Matrix.ext fun i j => (hρ _).symm)
  rw [← h0]
  show Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (β * intGL D.host.F D.host.E n w * β⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

set_option maxHeartbeats 1000000 in

theorem conj_int {V : HSp D} {β₁ β₂ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β₁ Λ N) {e : Formalism.L2.Theta.AE D} {PP : Formalism.L2.DIV.Pl D.host.E}
    (hSt : ∀ κ ∈ GfC V, Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₁ → Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₂)
    {v : FinPl D} {φ : SplitProj D v} (hφe : IsIdemOf φ e) (hφP : IsProjAt φ PP) (r : v.adicCompletionIntegers D.host.F →+* kP PP)
    (hN : ∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, r ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩)
    (ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F)
    (hρ : ∀ s, (ρ s : Fv D.host.F v) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s)
    (h : GL (Fin V.rank) (v.adicCompletionIntegers D.host.F)) (p q : Fin V.rank) :
    (((frCo φ β₂)⁻¹ * frCo φ β₁ * Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) h *
        ((frCo φ β₂)⁻¹ * frCo φ β₁)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)) p q ∈
        v.adicCompletionIntegers D.host.F := by
  obtain ⟨κ, hs, hκ⟩ := GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq D V v φ e hφe (frCo φ β₁)
    (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) h)
  obtain ⟨hG, h1, -, -⟩ := GlobalTheory.DownLift.SplitIntLift.lift_of_integral D V β₁ Λ N hB PP v φ e hφP hφe r hN h κ hs hκ
  obtain ⟨w, hw⟩ := hSt κ hG h1
  have hx : Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.IndefR.Lev.finE V κ) =
      Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.SplitProjChart.rdE_toEAf φ _)
  have hg : grpCo φ V (frCo φ β₁) κ = (frCo φ β₁)⁻¹ * Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) *
      frCo φ β₁ := rfl
  have e1 : frCo φ β₁ * Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) h *
      (frCo φ β₁)⁻¹ = Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.IndefR.Lev.finE V κ) := by
    rw [hx, ← hκ, hg]; group
  have e2 := map_frGL φ ρ hρ β₂ w
  rw [hw, ← e1] at e2
  rw [conj_of_conj_eq _ _ _ _ e2]
  exact ((Matrix.GeneralLinearGroup.map ρ w).val p q).2

end GlobalTheory.NestedStab

namespace GlobalTheory.NestedStab

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl SplitProj IsProjAt IsIdemOf rdA grpCo frCo)

set_option maxHeartbeats 1000000 in

theorem redFn_conj_of_stab_le : ∀ (D : D7) (V : HSp D) (β₁ β₂ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), Formalism.IndefR.Lev.IsBaseFrame V β₁ Λ N → ∀ (e : Formalism.L2.Theta.AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → (∀ κ ∈ GfC V, Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₁ → Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₂) → ∃ m : GL (Fin V.rank) (Formalism.L2.DIV.kP PP), ∀ y, y ∈ Formalism.L2.DIV.St β₁ → y ∈ Formalism.L2.DIV.St β₂ → Formalism.L2.DIV.redFn β₂ PP y = m * Formalism.L2.DIV.redFn β₁ PP y * m⁻¹ := by
  intro D V β₁ β₂ Λ N hB e PP he hSt
  obtain ⟨v, φ, hφe, hφP⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 e PP he
  obtain ⟨⟨r, -, -, -, hN⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφP
  let ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict _ (fun s => (hN s.1 s.2).1)
  have hρK : ∀ s, (ρ s : Fv D.host.F v) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s := fun s => rfl
  have hρ : ∀ s, r (ρ s) = resS D.host.F PP s := fun s => (hN s.1 s.2).2
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin V.rank)
      (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v))) := by
    intro x y hxy
    refine Units.ext (Matrix.ext fun i j => Subtype.ext ?_)
    have := congrArg (fun g : GL (Fin V.rank) (Fv D.host.F v) => (g : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)) i j) hxy
    exact this
  obtain ⟨m₀, hm₀⟩ := exists_int_conj (v.adicCompletionIntegers D.host.F) ((frCo φ β₂)⁻¹ * frCo φ β₁)
    (conj_int hB hSt hφe hφP r hN ρ hρK)
  refine ⟨Matrix.GeneralLinearGroup.map r m₀, fun y hy1 hy2 => ?_⟩
  obtain ⟨w₁, rfl⟩ := hy1
  obtain ⟨w₂, hw⟩ := hy2
  have hl : redFn β₂ PP (frGL β₁ w₁) = Formalism.UG.bc (resS D.host.F PP) w₂ := by rw [← hw, redFn_frGL]
  rw [hl, redFn_frGL]
  have hbc : ∀ w : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      Formalism.UG.bc (resS D.host.F PP) w = Matrix.GeneralLinearGroup.map r (Matrix.GeneralLinearGroup.map ρ w) :=
    fun w => Units.ext (Matrix.ext fun i j => (hρ _).symm)
  have key : Matrix.GeneralLinearGroup.map ρ w₂ = m₀ * Matrix.GeneralLinearGroup.map ρ w₁ * m₀⁻¹ := by
    apply hinj
    have h2 := congrArg (Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ)) hw
    rw [map_frGL φ ρ hρK, map_frGL φ ρ hρK] at h2
    simp only [map_mul, map_inv]
    rw [← hm₀]
    exact eq_conj_of_conj_eq _ _ _ _ h2
  rw [hbc, hbc, key]
  simp only [map_mul, map_inv]

end GlobalTheory.NestedStab
