import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.BlockRename

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  {f : γ' → γ} {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]

omit [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in

theorem blk_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (j : n) : blk e j = f (blk e₂ j) := by
  obtain ⟨⟨c', x⟩, rfl⟩ := e₂.surjective j
  have h1 : blk e₂ (e₂ ⟨c', x⟩) = c' := blk_apply e₂ c' x
  rw [h1, he, blk_apply]

omit [Fintype γ] [Fintype γ'] [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in

theorem mem_parab_rename (hf : StrictMono f) {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (g : GL n k) : g ∈ parab k e ↔ g ∈ parab k e₂ := by
  simp only [mem_parab, blk_rename he, hf.lt_iff_lt]

omit [∀ c, DecidableEq (m c)] in

theorem modExp_rename (hf : StrictMono f) (hs : Function.Surjective f) (c' : γ') :
    modExp (fun c' => m (f c')) c' = modExp m (f c') := by
  unfold modExp
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  congr 1
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl

theorem deltaHalf_rename (hf : StrictMono f) (hs : Function.Surjective f) (g : Levi k m) :
    deltaHalf k (fun c' => m (f c')) (fun c' => g (f c')) = deltaHalf k m g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  exact Fintype.prod_equiv E _ _ fun c' => by rw [modExp_rename hf hs]; rfl

theorem leviProj_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (p : parab k e₂) (q : parab k e) (hpq : (p : GL n k) = q) :
    leviProj k e₂ p = fun c' => leviProj k e q (f c') := by
  funext c'
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, leviProj_apply, he, he, hpq]

def kappa (hf : StrictMono f) (hs : Function.Surjective f) (X : γ → Type) [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] : (⨂[ℂ] c, X c) ≃ₗ[ℂ] ⨂[ℂ] c', X (f c') :=
  PiTensorProduct.reindex ℂ X (Equiv.ofBijective f ⟨hf.injective, hs⟩).symm

theorem kappa_tprod (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type} [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] (x : ∀ c, X c) :
    kappa hf hs X (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun c' => x (f c') := by
  exact PiTensorProduct.reindex_tprod (R := ℂ) (s := X) _ x

theorem piTensor_rename (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type}
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c))
    (g : Levi k m) (w : ⨂[ℂ] c, X c) :
    piTensor (fun c' => σ (f c')) (fun c' => g (f c')) (kappa hf hs X w) = kappa hf hs X (piTensor σ g w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [map_smul, kappa_tprod, piTensor_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.SmGL.BlockRename

namespace GlobalTheory.SmGL.BlockRename

theorem multiProd_rename : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  intro k _ _ _ _ γ γ' n _ _ _ _ _ _ f hf hs m _ _ e e₂ he X _ _ σ
  let κ := kappa hf hs X
  have key : ∀ (p : parab k e₂) (q : parab k e), (p : GL n k) = q → ∀ w,
      ((twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂)) p (κ w) =
        κ (((twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e)) q w) := by
    intro p q hpq w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, leviProj_rename he p q hpq, twist_apply, twist_apply,
      deltaHalf_rename hf hs, piTensor_rename hf hs]
    exact (map_smul κ _ _).symm
  have hP := mem_parab_rename (k := k) hf he
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (τ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (MonoidHom.id _) continuous_id κ.toLinearMap fun p => ⟨⟨p, (hP p).2 p.2⟩, rfl, fun w => key p _ rfl w⟩)
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (τ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (MonoidHom.id _) continuous_id κ.symm.toLinearMap fun q => ⟨⟨q, (hP q).1 q.2⟩, rfl, fun w =>
        κ.injective (by
          simp only [LinearEquiv.coe_coe]
          rw [LinearEquiv.apply_symm_apply, ← key ⟨q, (hP q).1 q.2⟩ q rfl, LinearEquiv.apply_symm_apply])⟩) ?_ ?_) fun g => ?_⟩
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.apply_symm_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.symm_apply_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => rfl))

end GlobalTheory.SmGL.BlockRename
