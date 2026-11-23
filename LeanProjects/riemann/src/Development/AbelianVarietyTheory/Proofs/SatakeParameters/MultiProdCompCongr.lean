import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

theorem eqv_trans (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

theorem eqv_symm (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

theorem eqv_refl (ρ : Representation ℂ G V) : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_placing {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e e' : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π)) :=
  (Placing.parInd_jac_placing k α n m e e' _).1 _

theorem ind₂_congr {r t N : ℕ} (h : r + t = N) {V V' W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {σ₁ : Representation ℂ (GL (Fin r) k) V'}
    {π₂ : Representation ℂ (GL (Fin t) k) W} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : Nonempty (π₁.Equiv σ₁)) (φ₂ : Nonempty (π₂.Equiv σ₂)) :
    Nonempty ((ind₂ (stdSum h) (extTensor π₁ π₂)).Equiv (ind₂ (stdSum h) (extTensor σ₁ σ₂))) := by
  subst h
  exact φ₁.elim fun a => φ₂.elim fun b => ⟨LocGL.prod₂Equiv a b⟩

theorem ind₂_assoc' {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M')
    (h₄ : r + M' = N) {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁)
    (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃) :
    Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h₁) (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ (stdSum h₄) (extTensor π₁ (ind₂ (stdSum h₃) (extTensor π₂ π₃))))) := by
  subst h₁ h₃ h₂
  exact Stages.prod₂_assoc k r s t V₁ V₂ V₃ π₁ π₂ π₃ s₁ s₂ s₃

theorem multiProd_head {s : ℕ} {d : Fin (s + 1) → ℕ} {X : Fin (s + 1) → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) {T N : ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) (h : d 0 + T = N) (e' : (Σ a : Fin s, Fin (d a.succ)) ≃ Fin T) :
    Nonempty ((multiProd e π).Equiv
      (ind₂ (stdSum h) (extTensor (π 0) (multiProd e' fun a : Fin s => π a.succ)))) := by
  have hT : T = ∑ a : Fin s, d a.succ := by
    have := Fintype.card_congr e'
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this.symm
  subst hT h
  have A := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) d (Fin.sum_univ_succ d) π
  have B := multiProd_placing (k := k) e (stdBlocks d (Fin.sum_univ_succ d)) π
  have C := multiProd_placing (k := k) (stdBlocks (fun i : Fin s => d i.succ) rfl) e' fun a => π a.succ
  exact A.elim fun A => B.elim fun B => C.elim fun C =>
    ⟨B.trans (A.symm.trans (LocGL.prod₂Equiv (Representation.Equiv.refl (π 0)) C))⟩

theorem multiProd_empty {d d' : Fin 0 → ℕ} {X X' : Fin 0 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] [iX' : ∀ a, AddCommGroup (X' a)] [mX' : ∀ a, Module ℂ (X' a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d' a)) k) (X' a))
    {t : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin t) (e' : (Σ a, Fin (d' a)) ≃ Fin t) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π')) := by
  obtain rfl : d = d' := funext fun a => a.elim0
  obtain rfl : X = X' := funext fun a => a.elim0
  obtain rfl : iX = iX' := funext fun a => a.elim0
  obtain rfl : mX = mX' := funext fun a => a.elim0
  obtain rfl : π = π' := funext fun a => a.elim0
  exact multiProd_placing e e' π

theorem ind₂_unit_right {r t : ℕ} (h : r + t = r) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) {d : Fin 0 → ℕ} {X : Fin 0 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor π (multiProd e τ))).Equiv π) := by
  let f : (Σ _ : Fin 1, Fin r) ≃ Fin r :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  let e' : (Σ a : Fin 0, Fin r) ≃ Fin t :=
    (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin r) (Σ a, Fin (d a))).trans e
  have A := LocGL.nonempty_equiv_multiProd_one hπ f fun _ _ => rfl
  have B := multiProd_head (k := k) (d := fun _ : Fin 1 => r) (fun _ => π) f h e'
  have C := ind₂_congr h (eqv_refl π) (multiProd_empty (k := k) (fun a : Fin 0 => π) τ e' e)
  exact eqv_symm (eqv_trans A (eqv_trans B C))

theorem multiProd_comp_congr {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {f g : Fin u → Fin s} (hfg : f = g)
    {T : ℕ} (e : (Σ i, Fin (d (f i))) ≃ Fin T) (e' : (Σ i, Fin (d (g i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (f i)).π).Equiv (multiProd e' fun i => (σ (g i)).π)) := by
  subst hfg
  exact multiProd_placing e e' _

def sigmaPart {s s₁ s₂ : ℕ} (d : Fin s → ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s)
    (hb : Function.Bijective (Sum.elim ι₁ ι₂)) :
    (Σ a, Fin (d a)) ≃ (Σ i, Fin (d (ι₁ i))) ⊕ (Σ j, Fin (d (ι₂ j))) :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) (Equiv.ofBijective _ hb)).symm.trans
    (Equiv.sumSigmaDistrib fun x => Fin (d (Sum.elim ι₁ ι₂ x)))

def Commutes {p q : ℕ} (x : Irr k p) (y : Irr k q) : Prop :=
  ∀ (N : ℕ) (h₁ : p + q = N) (h₂ : q + p = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π y.π)).Equiv (ind₂ (stdSum h₂) (extTensor y.π x.π)))

theorem Commutes.symm {p q : ℕ} {x : Irr k p} {y : Irr k q} (h : Commutes x y) : Commutes y x :=
  fun N h₁ h₂ => (h N h₂ h₁).map Representation.Equiv.symm

end GlobalTheory.ProdReorder
