import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowLocVec

variable {D : D7}

open GlobalTheory.HalfProd GlobalTheory.ExportSeries.RestrictHalfModel in

theorem prodHalf_halfInd {m n : ℕ} {a b : AE D} (ha : a * a = a) (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) :
    prodHalf a b (halfInd b Λ) (halfInd a Λ) = halfInd (a + b) Λ := by
  classical
  funext x
  rw [prodHalf_apply]
  by_cases hx : IsHalf (a + b) x
  · have hx' : a • x + b • x = x := by rw [← add_smul]; exact (isHalf_iff' _ _).1 hx
    rw [if_pos hx, mul_one]
    unfold halfInd
    by_cases hxΛ : x ∈ Λ
    · rw [if_pos ⟨hΛ a ha x hxΛ, isHalf_smul ha x⟩, if_pos ⟨hΛ b hb x hxΛ, isHalf_smul hb x⟩, if_pos ⟨hxΛ, hx⟩, one_mul]
    · rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hxΛ h.1)]
      by_cases h1 : a • x ∈ Λ
      · rw [if_neg (show ¬ (b • x ∈ Λ ∧ IsHalf b (b • x)) from fun h => hxΛ (hx' ▸ add_mem h1 h.1)), mul_zero]
      · rw [if_neg (show ¬ (a • x ∈ Λ ∧ IsHalf a (a • x)) from fun h => h1 h.1), zero_mul]
  · rw [if_neg hx, mul_zero]
    unfold halfInd
    rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hx h.2)]

theorem exists_compl_idem {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)} (hsub : P₀ ⊆ P) (he : IsIdemSum e P)
    (he₀ : IsIdemSum e₀ P₀) : ∃ b, e = e₀ + b ∧ b * b = b ∧ e₀ * b = 0 := by
  classical
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  obtain ⟨⟨es₀, h1₀, rfl⟩, -⟩ := he₀
  have heq : ∑ Q ∈ P₀, es₀ Q = ∑ Q ∈ P₀, es Q := Finset.sum_congr rfl fun Q hQ =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q (h1₀ Q hQ) (h1 Q (hsub hQ))).1 rfl
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' h =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q' (h1 Q hQ) (h1 Q' hQ')).2 h
  refine ⟨∑ Q ∈ P \ P₀, es Q, ?_, ?_, ?_⟩
  · rw [heq, ← Finset.sum_sdiff hsub, add_comm]
  · exact (⟨_, P \ P₀, es, fun Q hQ => (h1 Q (Finset.sdiff_subset hQ)).1,
      fun Q hQ Q' hQ' hne => horth Q (Finset.sdiff_subset hQ) Q' (Finset.sdiff_subset hQ') (Ne.symm hne), rfl⟩ :
        GlobalTheory.PlaceModelSum.IsOrthSum _) |> GlobalTheory.PlaceModelSum.IsOrthSum.idem
  · rw [heq, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun Q hQ => Finset.sum_eq_zero fun Q' hQ' =>
      horth Q (hsub hQ) Q' (Finset.sdiff_subset hQ') fun h => (Finset.mem_sdiff.1 hQ').2 (h ▸ hQ)

open GlobalTheory.HalfProd in

theorem isThetaAt_extend {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a b : AE D} {P : Finset (Pl D.host.E)} (hP : IsIdemSum (a + b) P)
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀)
    (hΦ : IsSBHalf a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) a
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    IsSBHalf (a + b) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) (a + b)
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) f := by
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ := fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu
  have hΨ := GlobalTheory.isSBHalf_halfInd b Λ
  refine ⟨isSBHalf_prodHalf ha hb hΛ hΨ hΦ, (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hP).exists_model hψ hS hT hP.2 hvac,
    fun T₀ hT₀ => ?_⟩
  have hm := isPlaceModel_prodHalf ha hb hab hΛ hΨ hT₀
  have key : T₀ (prodHalf a b (halfInd b Λ) (halfInd a Λ)) = f₀ := by
    rw [prodHalf_halfInd ha hb hΛ]
    have := hT₀.vac
    rwa [one_smul] at this
  rw [key] at hm
  exact hf.2 _ hm

end GlobalTheory.RowLocVec

namespace GlobalTheory.RowLocVec

theorem cosVec_isLocVec : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t i κ => ?_⟩⟩
  classical
  have hL := s.core.lev
  obtain ⟨e₀, he₀, hcos⟩ := ch.W.cosVec_is
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL ch.G t
  obtain ⟨b, rfl, hb, hab⟩ := exists_compl_idem (by unfold locPl; exact Finset.subset_union_left) he he₀
  have hS : IsSelfDualC (ch.G.pS (.chi (i : ℕ) 0)) (ch.G.latS (.chi (i : ℕ) 0)) :=
    isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) 0) ⟨i.2, Nat.zero_le _⟩).sd
  have hT : IsSelfDualC (ch.G.pT (.chi (i : ℕ) 0)) (ch.G.latT (.chi (i : ℕ) 0)) :=
    (node_isV ch.G hL (X := .grid (i : ℕ) 0) ⟨i.2.le, Nat.zero_le _⟩).sd
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  exact ⟨e₀ + b, he, _, isThetaAt_extend ch.W.ψ_std hS hT he ha hb hab (ch.W.vac_is i i.2).2.lat
    (GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (ch.G.pl.modul_ne_bot ch.sc) ha (GlobalTheory.PlaceDatum.infPart_idemSum he₀) κ)
    (hcos i i.2 κ)⟩

end GlobalTheory.RowLocVec
