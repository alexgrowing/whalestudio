import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivRealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPureTensor

section Generic

variable {ι κ V : Type} [DecidableEq κ] [AddCommGroup V] [Module ℂ V] {Pu : (κ → V) → V → Prop}

omit [DecidableEq κ] in

def IsMultiLin (Pu : (κ → V) → V → Prop) : Prop :=
  ∀ (x y z : κ → V) (f g : V) (q : κ) (c : ℂ), Pu x f → Pu y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) →
    z q = c • x q + y q → Pu z (c • f + g)

theorem IsMultiLin.upd (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a b f g : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) (h2 : Pu (Function.update x q b) g) :
    Pu (Function.update x q (c • a + b)) (c • f + g) := by
  refine h _ _ _ f g q c h1 h2 (fun p hp => ?_) (fun p hp => ?_) ?_
  · simp [hp]
  · simp [hp]
  · simp

theorem IsMultiLin.upd_smul (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a f : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) : Pu (Function.update x q (c • a)) (c • f) := by
  have h0 : Pu (Function.update x q 0) 0 := by
    simpa using h.upd (-1) h1 h1
  simpa using h.upd c h1 h0

theorem poly_step (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (q : κ) (s : Set ι)
    (hX : ∀ y ∈ s, ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) →
      Pu (Function.update x q (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : MvPolynomial ι ℂ} (hP : P ∈ MvPolynomial.supported ℂ s) :
    ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) → Pu (Function.update x q (L₀ (P * Q))) (L (P * R)) := by
  have hP' : P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' s) := by
    rwa [← MvPolynomial.supported_eq_adjoin_X]
  clear hP
  induction hP' using Algebra.adjoin_induction with
  | mem P hPs =>
    obtain ⟨y, hy, rfl⟩ := hPs
    exact hX y hy
  | algebraMap r =>
    intro x R Q hRQ
    rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]
    exact h.upd_smul r hRQ
  | add P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [add_mul] using h.upd 1 (ih₁ x R Q hRQ) (ih₂ x R Q hRQ)
  | mul P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [mul_assoc] using ih₁ x (P₂ * R) (P₂ * Q) (ih₂ x R Q hRQ)

theorem prod_step {α β : Type} [DecidableEq (α ⊕ β)] {Pu : (α ⊕ β → V) → V → Prop} (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (s : β → Set ι)
    (hX : ∀ τ, ∀ y ∈ s τ, ∀ x R Q, Pu (Function.update x (.inr τ) (L₀ Q)) (L R) →
      Pu (Function.update x (.inr τ) (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : β → MvPolynomial ι ℂ} (hP : ∀ τ, P τ ∈ MvPolynomial.supported ℂ (s τ)) {x : α ⊕ β → V}
    (hx : Pu x (L 1)) (hx0 : ∀ τ, x (.inr τ) = L₀ 1) (t : Finset β) :
    Pu (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) (L (∏ τ ∈ t, P τ)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have e : (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ (∅ : Finset β) then L₀ (P τ) else L₀ 1) = x := by
      funext p
      rcases p with v | τ
      · rfl
      · simp [hx0]
    rw [e, Finset.prod_empty]
    exact hx
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    set G := (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) with hG
    have hGa : G (.inr a) = L₀ 1 := by simp [hG, ha]
    have hfix : Function.update G (.inr a) (L₀ 1) = G := by
      rw [← hGa, Function.update_eq_self]
    have key := poly_step h L L₀ (.inr a) (s a) (hX a) (hP a) G (∏ τ ∈ t, P τ) 1 (by rw [hfix]; exact ih)
    have e : Function.update G (.inr a) (L₀ (P a * 1)) =
        Sum.elim (fun v => x (.inl v)) (fun τ => if τ ∈ insert a t then L₀ (P τ) else L₀ 1) := by
      funext p
      rcases p with v | τ
      · simp [hG]
      · by_cases hτ : τ = a
        · subst hτ
          simp
        · simp [hG, hτ]
    rw [← e]
    exact key

private theorem foldr_mem_of_invariant {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (l : List ι) {x : X} (hx : Pth x) :
    Pth (l.foldr (fun i g => A i g) x) := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact hth a _ ih

private theorem foldr_eq_of_perm_of_commute {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    {l l' : List ι} (hp : l.Perm l') {x : X} (hx : Pth x) :
    l.foldr (fun i g => A i g) x = l'.foldr (fun i g => A i g) x := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [List.foldr_cons, ih]
  | swap a b l => exact hc b a _ (foldr_mem_of_invariant A Pth hth l hx)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem opPow_single_one_add {X ι : Type} (A : ι → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    (y : ι) (u : ι →₀ ℕ) {x : X → ℂ} (hx : Pth x) :
    opPow A (Finsupp.single y 1 + u) x = A y (opPow A u x) := by
  unfold opPow
  have hp : ((Finsupp.toMultiset (Finsupp.single y 1 + u)).toList).Perm (y :: (Finsupp.toMultiset u).toList) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]
  rw [foldr_eq_of_perm_of_commute A Pth hth hc hp hx]
  rfl

private theorem constr_opPow_X_mul {X σ : Type} (A : σ → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hadd : ∀ f f', Pth f → Pth f' → Pth (f + f')) (hsm : ∀ (c : ℂ) f, Pth f → Pth (c • f))
    (hth : ∀ i f, Pth f → Pth (A i f)) (hc : ∀ i j f, Pth f → A i (A j f) = A j (A i f))
    (hA : ∀ i f f', Pth f → Pth f' → A i (f + f') = A i f + A i f')
    (hAs : ∀ i (c : ℂ) f, Pth f → A i (c • f) = c • A i f)
    {g : X → ℂ} (hg : Pth g) (y : σ) (Q : MvPolynomial σ ℂ) :
    ((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) (MvPolynomial.X y * Q) =
      A y (((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) Q) := by
  set Φ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g with hΦ
  have hmono : ∀ m a, Φ (MvPolynomial.monomial m a) = a • opPow A m g := by
    intro m a
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials σ ℂ m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smul, hΦ, Module.Basis.constr_basis]
  have hpow : ∀ m, Pth (opPow A m g) := fun m => by
    unfold opPow
    exact foldr_mem_of_invariant A Pth hth _ hg
  have hall : ∀ P, Pth (Φ P) := fun P =>
    MvPolynomial.induction_on' P (fun m a => by rw [hmono]; exact hsm a _ (hpow m))
      (fun p q hp hq => by rw [map_add]; exact hadd _ _ hp hq)
  refine MvPolynomial.induction_on' Q (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, hmono, hmono,
      opPow_single_one_add A Pth hth hc y u hg, hAs y a _ (hpow u)]
  · rw [mul_add, map_add, map_add, hp, hq, hA y _ _ (hall p) (hall q)]

end Generic

section Theta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem pureTensorO_X_mul (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) (y : FVar D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT g (MvPolynomial.X y * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT y (pureTensorO ψ θ S T sS sT BS BT g Q) := by
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ) := hb.1
  have hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ) := hb.2.1
  unfold pureTensorO pureTensorL aPlusAll
  exact constr_opPow_X_mul
    (fun k : FVar D T.rank S.rank => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (IsThetaFunO ψ S T)
    (fun f f' hf hf' => GlobalTheory.OrientedHeis.theta_add hf hf')
    (fun c f hf => GlobalTheory.OrientedHeis.theta_smul c hf)
    (fun k f hf => GlobalTheory.FockSubst.aPlus_th (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf)
    (fun i j f hf => GlobalTheory.FockSubst.aPlus_comm (hψ := hψ) (hθ := hθ) (τ := i.1) (z := _) (hS := hS) (hT := hT)
      (τ' := j.1) (z' := _) hf)
    (fun k f f' hf hf' => GlobalTheory.FockSubst.aPlus_add (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf hf')
    (fun k c f hf => GlobalTheory.FockSubst.aPlus_smul (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) c hf)
    hg y Q

theorem isPure_aPlus (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (y : Place D → WO S T → ℂ) (τ : D.what₂.Tau) (a g : WO S T → ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (h : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (Function.update y (.inr τ) a) g) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
      (Function.update y (.inr τ) (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z a))
      (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z g) := by
  have hlin := GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hML : IsMultiLin (IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀) := hlin.1
  have hd : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Function.update y (.inr τ) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w a))
        (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w g) := by
    intro w
    refine hlin.2 _ _ g τ w h (fun p hp => ?_) ?_
    · simp [hp]
    · simp
  have h4 := hML.upd_smul ((fockScale D τ : ℂ)⁻¹) (hML.upd (-Complex.I) (hd (J z)) (hd z))
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq,
    add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z a), add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g)]
  exact h4

end Theta

theorem fockPure : ∀ D : D7, FockPure D := by
  intro D
  unfold FockPure
  intro ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 BS BT pS pT hb hμ _ _ x f hx hx0 P hP
  have hth0 : IsThetaFunO ψ S T f₀ := base_theta hb
  have hthf : IsThetaFunO ψ S T f := hx.2.1
  have hlin := GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hone : ∀ g : WO S T → ℂ, pureTensorO ψ θ S T sS sT BS BT g 1 = g := by
    intro g
    have e1 : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]
      rfl
    unfold pureTensorO pureTensorL
    rw [e1, Module.Basis.constr_basis]
    unfold opPow
    simp
  have hX : ∀ τ, ∀ y ∈ (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) τ,
      ∀ x' R Q, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) (pureTensorO ψ θ S T sS sT BS BT f R) →
        IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ (MvPolynomial.X y * Q)))
          (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.X y * R)) := by
    intro τ y hy x' R Q h
    have hy' : y.1 = τ := hy
    subst hy'
    rw [pureTensorO_X_mul hb BS BT hth0 Q y, pureTensorO_X_mul hb BS BT hthf R y]
    exact isPure_aPlus hb hμ x' y.1 _ _ (cplxO (sS y.1) (sT y.1)) (unitMap (BS y.1) (BT y.1) y.2.1 y.2.2) h
  have key := prod_step hlin.1 (pureTensorO ψ θ S T sS sT BS BT f) (pureTensorO ψ θ S T sS sT BS BT f₀)
    (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) hX hP (x := x)
    (by rw [hone]; exact hx) (fun τ => by rw [hone]; exact hx0 τ) Finset.univ
  simpa using key

end GlobalTheory.FockPureTensor
