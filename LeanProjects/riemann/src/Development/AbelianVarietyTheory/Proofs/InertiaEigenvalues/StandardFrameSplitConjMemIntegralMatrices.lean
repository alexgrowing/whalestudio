import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.SplitFrameKO

theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (y : v.adicCompletion F)
    (hy : Valued.v y ≤ 1) : Valued.v (c y) ≤ 1 := by
  by_contra hne
  push_neg at hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hne
    exact absurd hne (not_lt.2 zero_le')
  have h1 : Valued.v (c y⁻¹) < 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hne
  have h2 := GlobalTheory.FixedAtSplit.valued_lt_one_of_map c hc _ h1
  rw [map_inv₀] at h2
  have h3 : 1 < Valued.v y := by
    have hpos : 0 < Valued.v y := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hy0
    exact (inv_lt_one₀ hpos).1 h2
  exact absurd hy (not_le.2 h3)

theorem val_le_one_of_mem_KO {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) (hκ : κ ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) (a b : Fin n) :
    Valued.v ((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b) ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  exact he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 a b))

end GlobalTheory.SplitFrameKO

namespace GlobalTheory.SplitFrameKO

set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) ≤ 1 := by
  intro D V n hF P β hS s
  obtain ⟨⟨βs, βs', h1, h2, hfr⟩, -⟩ := hS
  obtain ⟨c, hc, hc', hci⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv D.host.E s
  obtain ⟨f, hf⟩ : ∃ f : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* s.w.adicCompletion D.host.E,
    f = (GlobalTheory.StdFrames.cpt s.w).comp (swapAE D) := ⟨_, rfl⟩
  have hn : V.rank = n := GlobalTheory.SplitFrameW.eq_of_mul_eq_one (βs.map f) (βs'.map f)
    (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)])
  subst hn
  obtain ⟨Φc, hΦc⟩ : ∃ Φc : Matrix (Fin V.rank) (Fin V.rank) (EAf D) →+*
      Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    Φc = (c.symm.toRingHom.comp (GlobalTheory.StdFrames.cpt s.w)).mapMatrix := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B = βs.map (swapAE D) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B' = βs'.map (swapAE D) := ⟨_, rfl⟩
  have hBB : B * B' = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : B' * B = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨X, hX⟩ : ∃ X, X = Φc ((β⁻¹).val * B) := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X', X' = Φc (B' * β.val) := ⟨_, rfl⟩
  have hXX : X * X' = 1 := by
    rw [hX, hX', ← map_mul, show (β⁻¹).val * B * (B' * β.val) = (β⁻¹).val * (B * B') * β.val by
      simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, Units.inv_mul, map_one]
  have hXX' : X' * X = 1 := by
    rw [hX, hX', ← map_mul, show B' * β.val * ((β⁻¹).val * B) = B' * (β.val * (β⁻¹).val) * B by
      simp only [Matrix.mul_assoc], Units.mul_inv, Matrix.mul_one, hBB', map_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    g = ⟨X', X, hXX', hXX⟩ := ⟨_, rfl⟩
  refine ⟨g, fun κ _ hk a b => ?_⟩
  have hK : Φc (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (swapAE D)) =
      ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) := by
    rw [hΦc]
    refine Matrix.ext fun i j => ?_
    change c.symm (((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) ((swapCast hF).symm (κ.1.val i j)) s.w) = s.proj (κ.1.val i j)
    rw [GlobalTheory.SplitFrameW.cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci]
    exact c.symm_apply_apply _
  have e1 : (finE V (P.ψ κ)).val = B * (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (swapCast hF).symm).map (swapAE D)) * B' := by
    change (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (swapAE D) = _
    rw [hfr κ, Matrix.map_mul, Matrix.map_mul, hB, hB']
  have hM : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) = X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [Units.val_mul, Units.val_mul, e1, ← hK, hX, hX', ← map_mul, ← map_mul]
    simp only [Matrix.mul_assoc]
  have e3 : (↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) =
      X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [hg]; rfl
  have hent : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) a b =
      c.symm (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) := by
    rw [hΦc]; rfl
  have e2 : GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b) =
      c ((↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) := by
    rw [e3, ← hM, hent, c.apply_symm_apply]
  rw [e2]
  exact valued_le_one_of_map c hc _ (val_le_one_of_mem_KO _ hk a b)

end GlobalTheory.SplitFrameKO
