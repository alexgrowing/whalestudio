import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.MatGL
open GlobalTheory.SymBridge

def ordY (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin n :=
  ((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv) (Equiv.refl (Fin c))).trans
    finSumFinEquiv).trans (finCongr h)

theorem ordY_isOrd (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) :
    IsOrd (yPos xPos (κ + j + j * τ)) (ordY κ τ j c n h) := by
  rintro (((i | i) | ⟨p, r⟩) | i)
  all_goals simp [ordY, yPos, xPos, finProdFinEquiv]
  all_goals ring

theorem isOrd_unique {A : Type} {n : ℕ} (pos : A → ℕ) (e e' : A ≃ Fin n) (he : IsOrd pos e) (he' : IsOrd pos e') : e = e' :=
  Equiv.ext fun a => Fin.ext ((he a).trans (he' a).symm)

variable {E k : Type} [Field E] [Field k]

theorem toLoc_eq (ι : E →+* k) {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e' x = ((LinearMap.toMatrix' x).submatrix e e').map ι := by
  ext i j
  simp [toLoc, LinearMap.toMatrix'_apply]

theorem toLoc_comp (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a) (x y : (Fin a → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq, toLoc_eq, toLoc_eq, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ _ e, Matrix.map_mul]

theorem toLoc_id (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) :
    toLoc ι e e (LinearMap.id : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
  rw [toLoc_eq, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv, Matrix.map_one _ (map_zero ι) (map_one ι)]

def toLocGL (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) (γ : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
    GL A k where
  val := toLoc ι e e γ.toLinearMap
  inv := toLoc ι e e γ.symm.toLinearMap
  val_inv := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, toLoc_id]
  inv_val := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, toLoc_id]

end GlobalTheory.TwBridge.MatGL

namespace GlobalTheory.TwBridge
open GlobalTheory.SymBridge MatGL

theorem existsUnique_isGL : ∀ (X : Fields) (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (j c : ℕ), c = cOf R j → ∀ γ : AutY X R j,
    ∃! g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin c) k, IsGL ι γ g := by
  intro X R k _ _ _ _ ι j c hc γ
  subst hc
  have hN : R.k + j + j * R.t = R.N j := by simp only [Ranks.N]; ring
  have hn : R.k + j + j * R.t + cOf R j = R.N j + cOf R j := by rw [hN]
  have ho : IsOrdY (ordY R.k R.t j (cOf R j) _ hn) := by
    have := ordY_isOrd R.k R.t j (cOf R j) _ hn
    rwa [hN] at this
  refine ⟨toLocGL ι (ordY R.k R.t j (cOf R j) _ hn) γ, ⟨_, ho, rfl⟩, ?_⟩
  rintro g ⟨e, he, hg⟩
  obtain rfl := isOrd_unique _ _ _ he ho
  exact Units.ext hg

end GlobalTheory.TwBridge
