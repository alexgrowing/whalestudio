import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicSubLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameRedSplit

theorem conj_red_core {R K k ι : Type} [CommRing R] [Field K] [CommRing k] {m : ℕ} (S : Subring R) (O : ValuationSubring K)
    (pr : R →+* K) (φ : O →+* k) (res : S →+* k) (hres : ∀ z : S, ∃ h : pr z ∈ O, res z = φ ⟨_, h⟩)
    (β : GL (Fin m) R) (B B' : Matrix (Fin m) (Fin m) R) (hBB : B * B' = 1)
    (U : Set ι) (Km : ι → Matrix (Fin m) (Fin m) R) (Z : ∀ κ ∈ U, GL (Fin m) S)
    (hZ : ∀ κ (hκ : κ ∈ U), β.1 * (Z κ hκ).1.map S.subtype * (β⁻¹).1 = B * Km κ * B')
    (hsurj : ∀ u : GL (Fin m) O, ∃ κ, ∃ hκ : κ ∈ U, (Km κ).map pr = u.1.map O.subtype) :
    ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O), (Km κ).map pr = y.1.map O.subtype →
      (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin m) (Fin m) R, γ = (β⁻¹).1 * B := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Matrix (Fin m) (Fin m) R, γ' = B' * β.1 := ⟨_, rfl⟩
  have g1 : γ * γ' = 1 := by
    rw [hγ, hγ', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBB, Matrix.one_mul, Units.inv_mul]
  have g2 : γ' * γ = 1 := mul_eq_one_comm.mp g1
  have hZ' : ∀ κ (hκ : κ ∈ U), (Z κ hκ).1.map S.subtype = γ * Km κ * γ' := by
    intro κ hκ
    have e : γ * Km κ * γ' = (β⁻¹).1 * (B * Km κ * B') * β.1 := by
      rw [hγ, hγ']; simp only [Matrix.mul_assoc]
    rw [e, ← hZ κ hκ]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let c : GL (Fin m) K := ⟨γ.map pr, γ'.map pr, by rw [← Matrix.map_mul, g1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, g2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hc : ∀ κ (hκ : κ ∈ U), (c.1 * (Km κ).map pr * (c⁻¹).1) = ((Z κ hκ).1.map S.subtype).map pr := by
    intro κ hκ
    rw [hZ' κ hκ, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hent : ∀ u : GL (Fin m) O, ∀ a b, (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 a b ∈ O := by
    intro u a b
    obtain ⟨κ, hκ, hK⟩ := hsurj u
    have e : (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 = c.1 * (Km κ).map pr * (c⁻¹).1 := by
      rw [hK]; rfl
    rw [e, hc κ hκ, Matrix.map_apply, Matrix.map_apply]
    exact (hres _).1
  have hnorm : ∀ u ∈ Formalism.UG.GLint (Fin m) O.toSubring, c * u * c⁻¹ ∈ Formalism.UG.GLint (Fin m) O.toSubring := by
    rintro _ ⟨u, rfl⟩
    refine GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => hent u a b, fun a b => ?_⟩
    have e : (c * Formalism.UG.bc O.toSubring.subtype u * c⁻¹)⁻¹ = c * Matrix.GeneralLinearGroup.map O.subtype u⁻¹ * c⁻¹ := by
      rw [map_inv]
      group
      rfl
    rw [e]
    exact hent u⁻¹ a b
  obtain ⟨h, ⟨h₀, rfl⟩, hconj⟩ := GlobalTheory.HeckeStdFacts.exists_int_of_normalizes O.valuation O.toSubring
    (fun x => (O.valuation_le_one_iff x).symm) c hnorm
  suffices H : ∀ h₁ : GL (Fin m) O, (∀ x, c * x * c⁻¹ = Matrix.GeneralLinearGroup.map O.subtype h₁ * x *
      (Matrix.GeneralLinearGroup.map O.subtype h₁)⁻¹) → ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O),
      (Km κ).map pr = y.1.map O.subtype → (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 from H h₀ hconj
  intro h₁ hconj'
  refine ⟨Matrix.GeneralLinearGroup.map φ h₁, fun κ hκ y hy => ?_⟩
  ext a b
  obtain ⟨hm, hr⟩ := hres ((Z κ hκ).1 a b)
  have e1 : pr ((Z κ hκ).1 a b : R) = (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹).1 a b := by
    have := congrFun (congrFun (hc κ hκ) a) b
    rw [hy] at this
    exact this.symm
  have e2 : (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹) =
      Matrix.GeneralLinearGroup.map O.subtype (h₁ * y * h₁⁻¹) := by
    rw [hconj']
    simp only [map_mul, map_inv]
  have e3 : (⟨_, hm⟩ : O) = (h₁ * y * h₁⁻¹).1 a b := by
    apply Subtype.ext
    show pr _ = _
    rw [e1, e2]
    rfl
  have e4 : Matrix.GeneralLinearGroup.map φ h₁ * Matrix.GeneralLinearGroup.map φ y * (Matrix.GeneralLinearGroup.map φ h₁)⁻¹ =
      Matrix.GeneralLinearGroup.map φ (h₁ * y * h₁⁻¹) := by
    simp only [map_mul, map_inv]
  rw [Matrix.map_apply, hr, e3, e4]
  rfl

theorem resS_eq_phiR (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (y : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ h : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      resS D.host.F s.w y = GlobalTheory.MtRed.phiR s ⟨_, h⟩ := by
  have hmem : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s y.2)
  refine ⟨hmem, ?_⟩
  obtain ⟨a, ha, hφ⟩ := GlobalTheory.MtRed.exists_approx s ⟨_, hmem⟩
  rw [hφ]
  exact GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (y : EAf D) y (GlobalTheory.RowGood.tr_rfl _).symm a ha

set_option maxHeartbeats 1600000 in

theorem frameRed_exists : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  intro D V n hn hF P β Λ hP hβ s
  subst hn
  obtain ⟨⟨β₀, β₀', h01, h10, hmat⟩, hK⟩ := hP
  have hSt : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank, finE V (P.ψ κ) ∈ St β := fun κ hκ =>
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).2 ((hK κ).1 hκ)
  have hfin : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (finE V (P.ψ κ)).1 =
      β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
        β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ
    have e := congrArg (fun M => Matrix.map M (GlobalTheory.LevSplit.swp D.host.F D.host.E)) (hmat κ)
    refine e.trans ?_
    simp only [Matrix.map_mul]
    rfl
  have hBB : β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) = 1 := by
    rw [← Matrix.map_mul, h01, Matrix.map_one _ (map_zero _) (map_one _)]
  have hZ : ∀ (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hκ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank}),
      β.1 * (pullFr β ⟨_, hSt κ hκ⟩).1.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1 =
        β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
          β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ hκ
    exact (congrArg (fun g : GL (Fin V.rank) (EAf D) => g.1) (frGL_pullFr β ⟨_, hSt κ hκ⟩)).trans (hfin κ)
  have hpr : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj = (s.loc V.rank κ).1 := by
    intro κ
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RowGood.tr_rfl]
    rfl
  have hsurj : ∀ u : GL (Fin V.rank) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      ∃ κ : Formalism.AUTREP.GAf D.host.E V.rank, ∃ _ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank},
        (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
          u.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    intro u
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E V.rank s
      (Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype u)
    refine ⟨x, (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s hx).1 ⟨u, ?_⟩, ?_⟩
    · rw [hloc]; rfl
    · rw [hpr, hloc]; rfl
  obtain ⟨b, hb⟩ := conj_red_core (R := EAf D) (K := s.v.adicCompletion (maximalRealSubfield D.host.E)) (k := kP s.w)
    (ι := Formalism.AUTREP.GAf D.host.E V.rank) (m := V.rank) (S := Formalism.L2.Herm.intAf D.host.F D.host.E)
    (O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (pr := s.proj) (φ := GlobalTheory.MtRed.phiR s)
    (res := resS D.host.F s.w) (hres := resS_eq_phiR D s) (β := β) (hBB := hBB)
    (U := {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank})
    (Km := fun κ => κ.1.1.map (GlobalTheory.RowGood.tr hF))
    (Z := fun κ hκ => pullFr β ⟨_, hSt κ hκ⟩) (hZ := hZ) (hsurj := hsurj)
  refine ⟨GlobalTheory.MtRed.phiR s, b, ⟨GlobalTheory.MtRed.phiR_surj s, GlobalTheory.MtRed.phiR_eq_zero s⟩, fun κ hκ y hy a c => ?_⟩
  have hy' : (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
      y.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    rw [hpr]
    exact Matrix.ext fun i j => (hy i j).symm
  have e := congrFun (congrFun (hb κ hκ y hy') a) c
  have hr : redFn β s.w (finE V (P.ψ κ)) = Formalism.UG.bc (resS D.host.F s.w) (pullFr β ⟨_, hSt κ hκ⟩) := by
    have h1 := redFn_frGL β s.w (pullFr β ⟨_, hSt κ hκ⟩)
    rwa [frGL_pullFr] at h1
  rw [← e, hr]
  rfl

end GlobalTheory.FrameRedSplit
