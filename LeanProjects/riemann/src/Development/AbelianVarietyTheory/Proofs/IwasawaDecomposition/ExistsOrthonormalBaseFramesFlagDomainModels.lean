import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.BaseFrame

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ} (hr : V.rank = r) (ρ : D.what₂.Tau)
    {p q : ℕ} (hpq : r = p + q) (hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
      (Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  have hp : p ≤ V.rank := by omega
  have hq : nNeg (M.ε ρ) = q := (nNeg_shape hp hε).trans (by omega)
  have h0 : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := fun x => by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      conjTranspose_apply, gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring
  have hinv : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have h1 : ((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
    rw [← M.fr_gram ρ]
    calc _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ =
      (((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) := rfl
  show ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) = _
  rw [h0, h2, h1, hq]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [transpose_apply, Matrix.neg_apply, submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem exists_baseFrame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hL hA hF
  classical
  let x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ := fun j s τ =>
    if h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau, j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2 then
      Matrix.reindex (finCongr (rank_Wc h.choose.1)) (finCongr (rank_Wc h.choose.1))
        (x0Mat (R.MW h.choose.1 h.choose.2.1) h.choose.2.2)
    else T.x₀ j s τ
  have key : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ)) := by
    intro i σ ρ
    have h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        (i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2 := ⟨(i, σ, ρ), rfl, rfl, rfl⟩
    have aux : ∀ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        ((i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2) →
        Matrix.reindex (finCongr (rank_Wc p.1)) (finCongr (rank_Wc p.1)) (x0Mat (R.MW p.1 p.2.1) p.2.2) =
          Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (x0Mat (R.MW i σ) ρ) := by
      rintro ⟨i', σ', ρ'⟩ ⟨h1, h2, h3⟩
      obtain rfl : i = i' := Fin.ext (Nat.add_right_cancel h1)
      obtain rfl : ρ = ρ' := tauE_injective h3
      rw [hF.1 i σ σ' h2 ρ]
    exact (dif_pos h).trans (aux _ h.choose_spec)
  refine ⟨x₀, fun i σ _ => key i σ, fun j hj s hs k τ hτ => ?_⟩
  by_cases h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
      j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2
  · obtain ⟨⟨i, σ, ρ⟩, rfl, rfl, rfl⟩ := h
    dsimp only at hj hs k hτ ⊢
    have hU := hL.unf _ hj _ hs
    have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hL.pins.2.2.2 _ hj).1
    have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) (res T σ)).X k) := by
      obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hs
      have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hL.spaceW _ hj _ hs
      have h1 := hm k
      revert hr
      rw [hV]
      exact fun _ _ h => h
    have hε : ∀ a, (R.MW i σ).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun a => by
      rw [hF.2 i σ (fun ρ' => (GlobalTheory.HolRead.good_iff_labE_and_lab_conj D T hL hA σ ρ').1.1 hs) ρ a, hdp,
        show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    rw [key i σ ρ, hM.1, (hU.2.1 k).1]
    exact gram_x0Mat _ _ ρ hU.1 hε
  · have e : x₀ j s τ = T.x₀ j s τ := dif_neg h
    rw [e]
    exact hL.familyUniformisationBasePointOrthogonal j hj s hs k τ hτ

end GlobalTheory.RealGeo.BaseFrame
