import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrFrameCol

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule GlobalTheory.KappaHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_rat (p : Place D k) {l m r : ℕ} (N : Matrix (Fin r) (Fin l) k) (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι : Mx D r l) * rat M = (N * M.map p.pr).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, rat, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, BoxModel.incA_mul_ι, mul_comm]

theorem qB_β (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F) :
    B.o.qB.map p.pr * F.β = fromCols 0 (Matrix.of fun r _ => s * p.pr (B.ζ r)) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map p.pr = M.map (BoxModel.prH p) :=
    fun _ => rfl
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · have : (B.o.qB.map p.pr * F.β) r (Sum.inl a) = (B.o.qB.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      simp only [Matrix.mul_apply (M := B.o.qB.map p.pr), h.1]
    rw [this, ← Matrix.mul_assoc, ← BoxModel.map_pr_mul, B.o.qB_iA, hm]
    simp
  · have h1 : B.o.qB *ᵥ vecB B.o B.ζ = B.ζ := by
      rw [vecB, Matrix.mulVec_mulVec, B.o.qB_iB, Matrix.one_mulVec]
    have h2 : p.pr (B.ζ r) = ∑ j, p.pr (B.o.qB r j) * p.pr (vecB B.o B.ζ j) := by
      conv_lhs => rw [← h1]
      change BoxModel.prH p (∑ j, B.o.qB r j * vecB B.o B.ζ j) = ∑ j, BoxModel.prH p _ * BoxModel.prH p _
      simp only [map_sum, map_mul]
    rw [fromCols_apply_inr, Matrix.of_apply, h2, Finset.mul_sum, Matrix.mul_apply]
    simp only [h.2, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem line_γ_iA (p : Place D k) {n m : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F)
    (y : Matrix m Unit k) :
    fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr = 0 := by
  have h1 : fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β = 0 := by
    ext r a
    have : (fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β) r a
        = (fromCols (0 : Matrix m n k) y * F.γ * F.β) r (Sum.inl a) := by
      rw [Matrix.mul_assoc (_ * F.γ)]
      simp only [Matrix.mul_apply (M := fromCols (0 : Matrix m n k) y * F.γ), h.1]
    rw [this, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    simp
  rw [← Matrix.mul_one (_ * B.o.iA.map p.pr), ← FA.βγ, ← Matrix.mul_assoc, h1, Matrix.zero_mul]

theorem xi_mul_hO (L S : HSp D) (Y : WO L S) (z : Mx D L.rank S.rank) :
    incA D D.host.xi0 * hO L S Y (ofAdj L S z) = (z * Y).trace := by
  conv_rhs => rw [← starAdj_ofAdj L S z]
  rw [hO_eq_trace, starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem link_frames (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (s : k)
    {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) (h' : p.IsCoreFrame B' (s * p.xi) FA' F₀') :
    B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))
      = F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k) := by
  rw [qB_β p B' _ FA' F₀' h', ← Matrix.mul_assoc, ← BoxModel.map_pr_mul]
  have h1 : (B.o.iB * l.τ) *ᵥ B'.ζ = -vecB B.o B.ζ := by
    rw [← Matrix.mulVec_mulVec, l.map, Matrix.mulVec_neg, vecB]
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · have h2 : ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) = -p.pr (vecB B.o B.ζ r) := by
      have := congrArg (fun v => BoxModel.prH p (v r)) h1
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.neg_apply, map_neg] at this
      exact this
    have h3 : (F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k)) r (Sum.inr ())
        = F₀.β r (Sum.inr ()) * -p.xi := by
      simp [Matrix.mul_apply, Matrix.single_apply]
    rw [h3, h.2, Matrix.mul_apply]
    simp only [fromCols_apply_inr, Matrix.of_apply, Matrix.map_apply]
    calc _ = s * p.xi * ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h2]; ring

theorem frame_col : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s _ n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h h' y₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  have hτ : l.τ ≠ 0 := by
    intro h0
    have h1 := l.map
    rw [h0, Matrix.zero_mulVec, eq_comm, neg_eq_zero] at h1
    exact B.line.2 (by rw [h1, Matrix.mulVec_zero, dotProduct_zero])
  obtain ⟨τi, -, hi⟩ := LinkGram.exists_inv_of_rank_one B.line.1 B'.line.1 l.τ hτ
  set M : Matrix n (n' ⊕ Unit) k := fromCols 0 (Matrix.of fun r _ => y₀ r) with hM
  set Y : WO B.L S := p.up F₀ FS M * B.o.jB with hY
  have hYh : IsHalf p.e Y := isHalf_mul_right _ (GlobalTheory.LocSympl.up_half p F₀ FS M)
  have hκ : l.κ S (rat τi * starAdj B.L S Y) = Y := by
    rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hi, rat_one, Matrix.one_mul, LinkGram.ofAdj_starAdj]
  refine ⟨rat τi * starAdj B.L S Y, ?_, ?_, fun t => ?_⟩
  · rw [hκ, AddEquiv.eq_symm_apply, OrthDec.resS_apply]
    refine Prod.ext ?_ rfl
    change (FS.β * M * F₀.γ).map p.ι * rat B.o.iA = 0
    rw [ι_mul_rat, Matrix.mul_assoc FS.β, Matrix.mul_assoc FS.β, hM, line_γ_iA p B s FA F₀ h]
    simp
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (isHalf_mul_left _ (isHalf_smul _ (isHalf_mul_left _
      (isHalf_mul_right _ (isHalf_cA_adj hYh)))))
  · rw [GlobalTheory.LocSympl.psi_sympl_up p FS F₀' ψ ψk hk, OrthDec.hO_resT _ S, AddEquiv.apply_symm_apply,
      OrthDec.resT_apply]
    have hg := (LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
    have h0 : ∀ u : WO S B'.A, hO S B'.A u 0 = 0 := fun u => by
      rw [hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero]
    have h1 := GlobalTheory.LinkKappa.hO_ofAdj B.L B'.L S l.τ _ hg (rat τi * starAdj B.L S Y)
      (B'.o.pB * p.up FS F₀' t)
    rw [Int.cast_one, map_one, one_mul] at h1
    change hO B.L S (l.κ S _) _ = _ at h1
    rw [hκ] at h1
    have h2 := congrArg p.π (xi_mul_hO B.L S Y (rat l.τ * (B'.o.pB * p.up FS F₀' t)))
    rw [h1, map_mul] at h2
    have h3 : p.π (rat l.τ * (B'.o.pB * p.up FS F₀' t) * Y).trace = p.xi * -(t (Sum.inr ()) ⬝ᵥ y₀) := by
      have e1 : rat l.τ * (B'.o.pB * p.up FS F₀' t)
          = (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ))).map p.ι := by
        rw [← BoxModel.rat_mul_ι, ← BoxModel.rat_mul_ι]; rfl
      have e2 : Y = (FS.β * M * F₀.γ * B.o.iB.map p.pr).map p.ι := by
        rw [← ι_mul_rat]; rfl
      have e3 : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) k), (N.map p.ι).map p.π = N := fun N => by
        ext i j; exact p.π_ι _
      rw [AddMonoidHom.map_trace p.π, Matrix.map_mul, e1, e2, e3, e3, ← Matrix.mul_assoc _ _ (B.o.iB.map p.pr),
        Matrix.trace_mul_comm]
      have e4 : B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ)) * (FS.β * M * F₀.γ))
          = (B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))) * (t * (FS.γ * FS.β) * M) * F₀.γ := by
        simp only [Matrix.mul_assoc]
      rw [e4, link_frames p B B' l s FA F₀ FA' F₀' h h', FS.γβ, Matrix.mul_one, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc F₀.γ, ← Matrix.mul_assoc F₀.γ F₀.β, F₀.γβ, Matrix.one_mul, Matrix.trace_single_mul]
      simp [hM, Matrix.mul_apply, dotProduct]
    rw [h3] at h2
    rw [h0, zero_add, mul_left_cancel₀ hxi h2]

end GlobalTheory.ContrFrameCol
