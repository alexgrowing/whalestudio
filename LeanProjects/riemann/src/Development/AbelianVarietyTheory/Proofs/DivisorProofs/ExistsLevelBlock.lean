import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial

namespace GlobalTheory.GammaLevel

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_one_of_block (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (m : Frame X.Ψ r) (hm : ∀ τ (a c : Fin r), (c : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → m τ a c = 0)
    (h : lact γ x = rmul x m) : γ = 1 := by
  have hp0 := X.p0_le
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : r - (r - X.p0) = X.p0 := by omega
  have hx' : lact γ x ∈ X.dom := FrameFibre.lact_mem_GG (X.Γ_stab γ hγ).1 hx
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - (r - X.p0) → ¬ (a : ℕ) < r - (r - X.p0) → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ mat m τ * b = b * t := by
    intro τ
    refine FreeOnDomain.exists_conj_block hj _ ?_
    ext a c
    refine hm τ _ _ ?_ ?_
    · rw [idx_symm_inr]; have := c.2; omega
    · rw [idx_symm_inl]; omega
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, h, ← Matrix.mul_assoc]
    rfl
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp] at hb0; exact hb0)) (fun τ => t τ)
    (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_rmul' X γ x _).trans (funext e')

omit [NumberField E] [IsCMField E] in

theorem lact_inv_mul {Ψ : Finset (E →+* ℂ)} {δ γ : GL (Fin r) E} {x m : Frame Ψ r}
    (h : lact γ x = rmul (lact δ x) m) : lact (δ⁻¹ * γ) x = rmul x m := by
  funext τ
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat m τ := congrFun h τ
  change ((δ⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat m τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_level_block {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (k : U.Comp) (x x' : (U.X k).dom)
    (hxx : (U.un k x').x = (U.un k x).x) :
    ∃ (δ : GL (Fin r) E) (m : Frame (U.X k).Ψ r), IsUStab (U.X k).Gm (U.X k).Λ δ ∧
      (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u') ∧
      x'.1 = rmul (lact δ x.1) m ∧
      ∀ τ (a c : Fin r), (c : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → m τ a c = 0 := by
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨hκ, -, -, hrk, hinj, hspan, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU h1 W k
  obtain ⟨hr, hX, -⟩ := hU
  obtain ⟨hp0, hty⟩ := hX k
  obtain ⟨idx, hi, hper⟩ := CompInj.exists_idx hσ hr W.e (U.X k) hp0 hty
  have hq : (W.F.Di (W.ik k)).q = Dw.q := (W.F.sig _).2
  have hξ : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ (U.X k).Ψ, 0 < (τ (-(U.X k).ξ0)).im := by
    intro τ hτ
    have := (U.X k).κ0_sign ⟨τ, hτ⟩
    rw [hκ, map_mul, map_ofNat] at this
    rw [map_neg, Complex.neg_im]
    simp at this
    linarith
  let Pf : Frame (U.X k).Ψ r → ((W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)) := fun y =>
    AddMonoidHom.mk' (fun v j => Formalism.L2.PjFree.perFr (U.X k) y (W.emb k v)
      (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2) (by
      intro a b
      funext j
      have he : ∀ τ : E →+* ℂ, Data.emb τ (W.emb k (a + b)) = Data.emb τ (W.emb k a) + Data.emb τ (W.emb k b) := by
        intro τ
        funext i
        simp [Data.emb]
      simp only [Pi.add_apply, hper, he]
      split_ifs
      · simp [hermC, mul_add, Finset.sum_add_distrib]
      · simp [Matrix.mulVec_add])
  have hpt : ∀ y : (U.X k).dom, (U.un k y).x = W.F.u (W.ik k) (Pf y.1) := by
    intro y
    obtain ⟨P, hP, -, hu, -⟩ := W.pt k y
    rw [hu]
    congr 1
    ext a j
    exact hP a j
  have hrange : LinearMap.range (W.emb k) = (U.X k).Λ := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k a).2
    · intro hv
      exact ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  obtain ⟨δ, m, hδ, hM, -, hm, hm0⟩ := FrameFibre.exists_level_block_of_eq E H Dw l Xo _ W.g _ W.F (W.ik k) r
    (-(U.X k).ξ0) (U.X k).Gm (W.emb k) (U.X k).Ψ idx Pf hty (by rw [hq]; exact hi) hξ hpos
    ⟨hinj, hspan, (U.X k).Gm_herm, (U.X k).Gm_det, W.isom k⟩ hrk
    (by rw [hq]; exact fun y v j => hper y _ j) x.1 (by rw [hq, ← hp0]; exact x.2) x'.1
    (by rw [hq, ← hp0]; exact x'.2) (by rw [← hpt, ← hpt, hxx])
  rw [hrange] at hδ
  rw [hq, ← hp0] at hm0
  refine ⟨δ, m, hδ, fun u hu => ?_, hm, hm0⟩
  obtain ⟨a, rfl⟩ : u ∈ LinearMap.range (W.emb k) := hrange ▸ hu
  obtain ⟨w, hw⟩ := hM a
  exact ⟨_, (W.φ k w).2, hw⟩

end

end GlobalTheory.GammaLevel

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GammaLevel.trivial_mod_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp), (∀ δ : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ δ → (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') → δ ∈ (U.X k).Γ) → ∀ γ ∈ (U.X k).Γ, (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 _ k hP γ hγ
  obtain ⟨x, hx⟩ := GlobalTheory.CompInj.dom_nonempty (U.X k)
  have hx' : lact γ x ∈ (U.X k).dom := GlobalTheory.FrameFibre.lact_mem_GG ((U.X k).Γ_stab γ hγ).1 hx
  obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ, hγ, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ),
    fun τ => ⟨by
      change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a c h => Matrix.one_apply_ne h.ne'⟩, by
      congr 1
      funext τ
      exact (Matrix.mul_one (mat (lact γ x) τ)).symm⟩
  obtain ⟨δ, m, hδ, hM, hm, hm0⟩ := GlobalTheory.GammaLevel.exists_level_block (U := Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) h1 k ⟨x, hx⟩ ⟨_, hx'⟩ ht.1
  have h := GlobalTheory.GammaLevel.eq_one_of_block (U.X k) (mul_mem (inv_mem (hP δ hδ hM)) hγ) hx m hm0
    (GlobalTheory.GammaLevel.lact_inv_mul hm)
  rw [inv_mul_eq_one] at h
  exact h ▸ hM
