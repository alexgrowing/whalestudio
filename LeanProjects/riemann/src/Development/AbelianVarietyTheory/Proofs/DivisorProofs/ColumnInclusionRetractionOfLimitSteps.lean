import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem mv_sum_smul_X {C : Type} [Field C] {d : ℕ} {σ : Type} [Fintype σ] (A : Matrix (Fin d) (Fin d) C)
    (s : σ → C) (g : σ → Fin d → C) (e : Fin d) :
    mv A (fun e' => ∑ ℓ, (s ℓ * g ℓ e') • (MvPowerSeries.X ℓ : MvPowerSeries σ C)) e =
      ∑ ℓ, (s ℓ * A.mulVec (g ℓ) e) • (MvPowerSeries.X ℓ : MvPowerSeries σ C) := by
  simp only [mv, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [mul_left_comm]

theorem subst_expPt_sum_mv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : Fin n → Fin d → MvPowerSeries σ C) (hw : ∀ j e, constantCoeff (w j e) = 0)
    (r : κ → Fin n) (A : κ → Matrix (Fin d) (Fin d) C) (i : Fin d) :
    subst (fun q : Fin n × Fin d => expPt G (w q.1) q.2)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C))) i) =
      expPt G (fun e => ∑ b, mv (A b) (w (r b)) e) i := by
  have ht : HasSubst (fun q : Fin n × Fin d => expPt G (w q.1) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  have hl : ∀ b e, constantCoeff
      (lgPt G (fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C)) e) = 0 :=
    fun b => cc_lgPt G (by simp)
  rw [subst_expPt G ht (fun e => by
    rw [Finset.sum_apply, map_sum]; exact Finset.sum_eq_zero fun b _ => cc_mv _ (hl b) e)]
  congr 1
  funext e
  rw [Finset.sum_apply, ← coe_substAlgHom ht, map_sum, coe_substAlgHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv ht]
  congr 1
  funext e'
  rw [subst_lgPt G ht (by simp)]
  simp only [subst_X ht]
  exact congrFun (lgPt_expPt G (hw (r b))) e'

theorem retrSt_of : LimActSt → LimPtSt → InvSt → RetrSt := by
  intro hAct hPt hInv E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ X cx n B hB
  classical
  obtain ⟨blk, hblk⟩ := hB
  have key : ∀ f : {f : Lt1 Dw // cx f ≠ 0}, ∃ ρf : Fin (rk f.1) → Fin (chD Ch.ch) → PS X.C n (chD Ch.ch),
      (∀ β i, constantCoeff (ρf β i) = 0) ∧ (∀ β i, MvIsInt (vX_vp X) (ρf β i)) ∧
      ∀ β i, subst (colPt Ch X cx B) (ρf β i) = expH Ch X cx ⟨⟨f, β⟩, i⟩ := by
    intro f
    obtain ⟨hS, ⟨r, hr⟩, hx⟩ := hblk f
    obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c f.1.1))
    have inj := IsFractionRing.injective T.V T.Fr
    have hp0 : (p : T.V) ≠ 0 := fun h => by
      have h1 := congrArg (jX X) h
      rw [map_natCast, map_zero] at h1
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
    have hM : ∀ b b' (N : ℕ), ∃ a z,
        φ a = (Matrix.of fun b b' => B f.1 b (r b')) b b' + φ (p : 𝓞 E) ^ N * z := fun b b' N => by
      obtain ⟨x, -, hx2, -⟩ := hx N
      obtain ⟨z, hz⟩ := hx2 b (r b')
      exact ⟨x b (r b'), z, inj (by rw [hφ, map_natCast φ]; exact hz)⟩
    obtain ⟨M', hMM', hM'⟩ := hInv (𝓞 E) T.V φ (p : 𝓞 E) (by rw [map_natCast]; exact hp0)
      (by rw [map_natCast]; exact not_isUnit_p X) (rk f.1) _ hr hM
    obtain ⟨ε, hε⟩ := hAct E H Dw l Xo c hstar T io y Ch p X f.1.1
    choose x z hxz using hM'
    choose A hA1 hA2 using fun β' β => hε (M' β' β) (x β' β) fun N =>
      ⟨z β' β N, by rw [← map_natCast φ p, ← hxz, hφ]; rfl⟩
    have hint : ∀ β, IntLog (fgl Ch X) (∑ β', mv (A β' β)
        (lgPt (fgl Ch X) fun e => (MvPowerSeries.X (r β', e) : PS X.C n (chD Ch.ch)))) := fun β => by
      letI := io.toAlgebra
      letI : Algebra T.Fr X.C := X.ιF.toAlgebra
      exact hPt X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (Fin (rk f.1)) _
        (fun β' => intLog_lgPt_X (fgl Ch X) fun e => (r β', e)) (fun β' => A β' β)
        (fun N β' => ε N * x β' β N) fun N β' => hA1 β' β N
    have hz : ∀ f' : {f : Lt1 Dw // cx f ≠ 0}, f' ≠ f → ∀ b β', B f'.1 b (r β') = 0 := fun f' hf b β' => by
      refine (hblk f').1 b _ fun ⟨j', hj'⟩ => ?_
      by_cases hm : r β' ∈ Set.range fun j => blk ⟨f, j⟩
      · obtain ⟨j, hj⟩ := hm
        exact hf (congrArg Sigma.fst (blk.injective (hj'.trans hj.symm)))
      · rw [Matrix.det_eq_zero_of_column_eq_zero β' fun b => hS b _ hm] at hr
        exact not_isUnit_zero hr
    refine ⟨fun β => expPt (fgl Ch X) _, fun β => cc_expPt _ (hint β).1, fun β => (hint β).2, fun β i => ?_⟩
    refine (subst_expPt_sum_mv (fgl Ch X) (fun j e => ∑ ℓ : Let cx,
      (jX X (B ℓ.1.1.1 ℓ.1.2 j) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
      (fun j e => by simp) r (fun β' => A β' β) i).trans ?_
    show expPt _ _ i = expPt (fgl Ch X) (fun e => ∑ a, frame Ch X f.1 a e •
      (MvPowerSeries.X ⟨⟨f, β⟩, a⟩ : MvPowerSeries (Let cx) X.C)) i
    congr 1
    funext e
    simp only [mv_sum_smul_X]
    have hc : ∀ (b : Fin (rk f.1)) (a : Fin (rk f.1)),
        ∑ β', jX X (B f.1 b (r β')) * (A β' β).mulVec (frame Ch X f.1 a) e =
          if b = β then frame Ch X f.1 a e else 0 := fun b a => by
      have h1 := congrArg (jX X) (congrFun (congrFun hMM' b) β)
      rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h1
      simp only [frame, hA2, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, ← map_mul]
      rw [show ∑ β', jX X (B f.1 b (r β') * M' β' β) = _ from h1]
      split_ifs <;> simp
    rw [Finset.sum_comm, Fintype.sum_sigma, Finset.sum_eq_single (⟨f, β⟩ : Col cx)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, hc, if_pos rfl]
    · rintro ⟨f', b⟩ - hne
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_smul]
      by_cases hf : f' = f
      · subst hf
        rw [hc, if_neg fun h => hne (by rw [show b = β from h]), zero_smul]
      · simp [hz f' hf]
    · exact fun h => absurd (Finset.mem_univ _) h
  choose ρf h1 h2 h3 using key
  exact ⟨fun q => ρf q.1.1 q.1.2 q.2, fun q => h1 _ _ _, fun q => h2 _ _ _, fun q => h3 _ _ _⟩

end GlobalTheory.IsoTriv
