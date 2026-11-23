import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SliceModelT

variable {D : D7}

theorem resT_symm_left {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) :
    (d.resT S).symm (u, 0) = GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank) u := by
  rw [OrthDec.resT_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem isThetaFunO_sliceT_left {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO S B) : IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v)) where
  quasi γ u := by
    have e0 : (d.resT S).symm (ratW A S γ, 0) = ratW T S (d.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW A S γ + u, v) : WO S A × WO S B) = (ratW A S γ, (0 : WO S B)) + (u, v) := by simp
    show f ((d.resT S).symm (ratW A S γ + u, v)) = ψ (-(symplOH S A (ratW A S γ) u)) * f ((d.resT S).symm (u, v))
    rw [e, map_add, e0, hf.quasi, ← e0, d.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (hk _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resT S).symm (w, v))
    rw [← resT_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero, d.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const))
  smooth m L hL h0 w := by
    have e : ∀ t, (d.resT S).symm (w + L t, v) =
        (d.resT S).symm (w, v) + ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resT_symm_left, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth m ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem ι_mul (a : AE D) (x : k) : p.ι (p.π a * x) = a * p.ι x := by
  have h1 : p.π a * x = p.π (a * p.ι x) := by rw [map_mul, p.π_ι]
  rw [h1, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem mul_map_ι {m l n : Type} [Fintype l] (N : Matrix m l (AE D)) (M : Matrix l n k) :
    N * M.map p.ι = (N.map p.π * M).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} (FS : Frame k S.rank n)

theorem beta_eq (hF : p.IsCoreFrame B s FA F₀) :
    F₀.β = fromCols (B.o.iA.map (prH p) * FA.β) (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) := by
  ext r (a | _)
  · exact hF.1 r a
  · exact hF.2 r

theorem col_eq : (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) =
    s • (B.o.iB.map (prH p) * Matrix.of fun j (_ : Unit) => prH p (B.ζ j)) := by
  ext r u
  simp [Matrix.mul_apply, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem qA_beta (hF : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [beta_eq p B hF, col_eq, Matrix.mul_fromCols, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, ← Matrix.map_mul, B.o.qA_iA, B.o.qA_iB, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, smul_zero]

theorem up_fromRows (hF : p.IsCoreFrame B s FA F₀) (x : Matrix n' n k) :
    p.up FS F₀ (fromRows x 0) = (B.o.resT S).symm (p.up FS FA x, 0) := by
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, mul_map_ι,
    beta_eq p B hF, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.map_map]
  simp only [Matrix.mul_assoc]
  rfl

theorem resT_up_fst (hF : p.IsCoreFrame B s FA F₀) (x : Matrix (n' ⊕ Unit) n k) :
    (B.o.resT S (p.up FS F₀ x)).1 = p.up FS FA x.toRows₁ := by
  rw [OrthDec.resT_apply]
  dsimp only
  rw [Place.up, Place.up, OrthDec.pA, rat, mul_map_ι, Matrix.map_map]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (B.o.qA.map (prH p) * F₀.β) * x * FS.γ = _
  rw [qA_beta p B hF]
  conv_lhs => rw [← fromRows_toRows x]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

def rowsH (n n' : Type) [Fintype n] [Fintype n'] : Matrix (n' ⊕ Unit) n k ≃ₜ Matrix n' n k × (n → k) where
  toFun x := (x.toRows₁, x (Sum.inr ()))
  invFun q := fromRows q.1 (Matrix.of fun _ => q.2)
  left_inv x := by
    ext (i | i) j <;> rfl
  right_inv q := by
    ext i j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_apply _)
    exact continuous_pi fun i => continuous_apply (Sum.inl i)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact continuous_snd

def tens (a : SB (n → k)) : SB (Matrix n' n k) →ₗ[ℂ] SB (Matrix (n' ⊕ Unit) n k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (rowsH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ a)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : SB (n → k)) (Ξ : SB (Matrix n' n k)) (x : Matrix (n' ⊕ Unit) n k) :
    (tens a Ξ).1 x = Ξ.1 x.toRows₁ * a.1 (x (Sum.inr ())) := rfl

end GlobalTheory.SliceModelT

open GlobalTheory.SliceModelT in

theorem GlobalTheory.SliceModelT.main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS hF T₀ hT a ha v
  let a' : SB (n → k) := ⟨a, ha⟩
  let T₁ : SB (Matrix n' n k) →ₗ[ℂ] (WO S B.A → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO S B.A => (B.o.resT S).symm (u, v))) ∘ₗ T₀ ∘ₗ tens a'
  have hT₁ : ∀ Ξ u, T₁ Ξ u = T₀ (tens a' Ξ) ((B.o.resT S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact isThetaFunO_sliceT_left B.o (hT.theta _) v
  · have h1 := hT.trans (fromRows x 0) (tens a' Φ) (tens a' Φ') (fun t => by
      have e1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
        ext i j; simp [Matrix.toRows₁, Matrix.fromRows_apply_inl]
      have e2 : (t + fromRows x (0 : Matrix Unit n k) : Matrix (n' ⊕ Unit) n k) (Sum.inr ()) = t (Sum.inr ()) := by
        funext j; simp [Matrix.fromRows_apply_inr]
      rw [tens_apply, tens_apply, hΦ, e1, e2])
    funext u
    rw [hT₁, h1, up_fromRows p B S FS hF]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · set Y : WO S B.V₀ := (B.o.resT S).symm (y, 0) with hYdef
    have hY : IsHalf (cA D p.e) Y := by
      intro i j
      rw [hYdef, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have h1 := hT.modul Y hY (tens a' Φ) (tens a' Φ') (fun t => by
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resT, resT_up_fst p B S FS hF, hYdef, AddEquiv.apply_symm_apply,
        symplO_zero_right', add_zero, mul_assoc])
    funext u
    rw [hT₁, h1]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a' Ξ := Subtype.ext (funext hΨ)
    rw [e, hT₁]
