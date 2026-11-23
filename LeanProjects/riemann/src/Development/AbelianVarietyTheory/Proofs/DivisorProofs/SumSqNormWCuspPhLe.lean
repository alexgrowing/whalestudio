import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

theorem hasGram_norm_sum_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {N : (K →+* ℂ) → V → ℝ} (hN : GlobalTheory.AllWt.HasGram N) (σ : K →+* ℂ)
    (hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y) {ι : Type} (s : Finset ι) (y : ι → V) :
    N σ (∑ i ∈ s, y i) ≤ ∑ i ∈ s, N σ (y i) ∧ ∀ z, 0 ≤ N σ z := by
  obtain ⟨⟨n, ⟨b, X⟩, hbX⟩⟩ := hN
  letI : StarRing K := starRingOfComm
  let Φ : V →+ EuclideanSpace ℂ (Fin n) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X (InfinitePlace.mk σ) y)
      map_zero' := by rw [Formalism.HermitianLatticesTheory.fcoord_zero]; rfl
      map_add' := fun y z => by rw [Formalism.HermitianLatticesTheory.fcoord_add]; rfl }
  have hΦ : ∀ y, N σ y = ‖Φ y‖ := by
    intro y
    rw [← hτ, ← (hbX (InfinitePlace.mk σ)).2 y, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]
    rfl
  refine ⟨?_, fun z => (hΦ z).symm ▸ norm_nonneg _⟩
  rw [hΦ, map_sum]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun g _ => (hΦ _).symm))

theorem sum_sq_normW_cuspPh_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W) (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (B : ℝ), 0 ≤ B → GlobalTheory.AllWt.HasGram (GlobalTheory.AllWt.normW U x V dict (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g = GlobalTheory.AllWt.normW U x V dict (G + W) σ f) → (∀ (γ : LevelAut Dw l) (f : cuspW Xo c U G) (g : cuspW Xo c U (G + W)), (g : Rul Xo c) = f * pull Xo c γ u → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict G σ f) → ∀ (f : cuspW Xo c U G) (σ : c.F →+* ℂ), ∑ h : S, GlobalTheory.AllWt.normW U x V dict (G + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ^ 2 ≤ (Fintype.card S : ℝ) ^ 3 * B ^ 2 * GlobalTheory.AllWt.normW U x V dict G σ f ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hK hKW χ u B hB hGram hinv hbd f σ
  set N := GlobalTheory.AllWt.normW U x V dict (G + W) with hN
  have hconj : ∀ y, N ((starRingEnd ℂ).comp σ) y = N σ y := fun y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.petW, GlobalTheory.AllWt.petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y := by
    intro y
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      rw [h, e, hconj]
  have hnn : ∀ y, 0 ≤ N σ y := (hasGram_norm_sum_le hGram σ hτ (∅ : Finset S) (fun _ => 0)).2
  have hsum : ∀ (s : Finset S) (y : S → cuspW Xo c U (G + W)), N σ (∑ g ∈ s, y g) ≤ ∑ g ∈ s, N σ (y g) :=
    fun s y => (hasGram_norm_sum_le hGram σ hτ s y).1
  have hsmul : ∀ (a : c.F) (y : cuspW Xo c U (G + W)), N σ (a • y) = ‖σ a‖ * N σ y := fun a y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, Submodule.coe_smul, GlobalTheory.AllWt.petW_smul]
  have hunit : ∀ g : S, ‖σ (((χ g)⁻¹ : (c.F)ˣ) : c.F)‖ = 1 := by
    intro g
    have h1 : ((χ g)⁻¹) ^ (Fintype.card S) = 1 := by rw [← map_inv, ← map_pow, pow_card_eq_one, map_one]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card S) ?_ Fintype.card_ne_zero
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have hcomp : ∀ h : S, N σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
      (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ≤
        (Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f) := by
    intro h
    have hFm : (f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u ∈ cuspW Xo c U (G + W) :=
      GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW (h : LevelAut Dw l) _ u.2)
    have hP : ∀ g : S, pull Xo c (g : LevelAut Dw l) ((f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u) ∈
        cuspW Xo c U (G + W) := fun g => hK (g : LevelAut Dw l) _ hFm
    have he : ((GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
        (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h : cuspW Xo c U (G + W)) : Rul Xo c) =
          ((∑ g : S, (((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)) : cuspW Xo c U (G + W)) :
            Rul Xo c) := by
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      rfl
    rw [Subtype.ext he]
    refine (hsum _ _).trans ?_
    calc ∑ g : S, N σ ((((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)))
        ≤ ∑ _g : S, B * GlobalTheory.AllWt.normW U x V dict G σ f := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [hsmul, hunit, one_mul, hinv (g : LevelAut Dw l) ⟨_, hFm⟩ ⟨_, hP g⟩ rfl σ]
          exact hbd (h : LevelAut Dw l) f ⟨_, hFm⟩ rfl σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc _ ≤ ∑ _h : S, ((Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f)) ^ 2 :=
        Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (hnn _) (hcomp h) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GlobalTheory
