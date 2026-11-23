import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

set_option maxHeartbeats 1000000 in

theorem ratDatum_comb_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ (comb ψ S T c f) := by
  intro D k _ _ _ _ p ψ hψ hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd ΛS ΛT hS hT hΛS hΛT Ξ Ξk hΞk c hc
    f₀ f hf₀ hvac hf
  have hL : stdHom S T = latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [hΛS, hΛT]
  have hf₁ := hf
  obtain ⟨Φ, hΦSB, hΦrat, -⟩ := hf₁
  have he1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have he2 : (e + p.e) * (e + p.e) = e + p.e := GlobalTheory.PlaceDatum.idemSum_mul_self hE'
  have hpe2 : p.e * p.e = p.e := p.split.1
  have horth : e * p.e = 0 := by
    have h2 : incA D 2 * (e * p.e) = 0 := by
      rw [map_ofNat]
      linear_combination he2 - he1 - hpe2
    have hu : incA D (1 / 2) * incA D 2 = 1 := by
      rw [← map_mul]
      norm_num
    calc e * p.e = incA D (1 / 2) * (incA D 2 * (e * p.e)) := by rw [← mul_assoc, hu, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hstabp : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T := fun u hu => by
    have := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hpe2])) u hu
    convert this using 1
    ext i j
    rfl
  have hsb := GlobalTheory.LocMod.Place.isSBHalf_tensorAt D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB Ξk hΞk
  have hpi1 : p.π p.e = 1 := by
    have h := p.ι_π 1
    rw [map_one, mul_one] at h
    rw [← h, p.π_ι]
  have hπe : p.π e = 0 := by
    have := congrArg p.π horth
    rwa [map_mul, hpi1, mul_one, map_zero] at this
  have hud : ∀ t : WO S T, p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := fun t => by
    unfold Place.up Place.down
    have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
        (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    rw [hM]
    ext i j
    simp only [Matrix.map_apply, p.ι_π]
  have hrat : ∀ γ, p.tensorAt FS FT Φ Ξk (γ.map fun a => (e + p.e) * incA D a) = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β) :=
    fun γ => by
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add, hπe, hpi1, zero_add, one_mul, Place.pr]
    have hs : ((γ.map fun a => (e + p.e) * incA D a : WO S T) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) : WO S T) =
        (γ.map fun a => e * incA D a : WO S T) := by
      rw [hud]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have hvac' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ := by
    rw [← hL]; exact hvac
  have hex := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT hS hT _ (e + p.e) hE' f₀ hf₀ hvac').1
  have hsb' : IsSBHalf (e + p.e) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (p.tensorAt FS FT Φ Ξk) := by
    rw [← hL]; exact hsb
  obtain ⟨f', hf'⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ hS hT he2 (GlobalTheory.PlaceDatum.infPart_idemSum hE') hex hsb'
  have hR : IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ f' :=
    ⟨p.tensorAt FS FT Φ Ξk, hsb, hrat, by rw [hL]; exact hf'⟩
  have key := GlobalTheory.T.rationalDatum_theta_factors_placeByPlace D k p ψ hψ hdense S T Y Y' FS FT P PP e hPP hIdemAt hE hE' hstd Ξ _ Ξk hΞk (fun _ => rfl) c hc
    f₀ f f' hf₀ hvac hf hR
  rw [← key]
  exact hR

end GlobalTheory.LocMod
