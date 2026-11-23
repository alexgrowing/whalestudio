import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

def Ses {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃) : Prop :=
  ∃ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃), (∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) ∧ (∀ x v, g (ρ₂ x v) = ρ₃ x (g v)) ∧
    Function.Injective f ∧ Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def iterN (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → MRep k (n + j) → MRep k n
  | 0, τ => τ
  | j + 1, τ => iterN ψ j (phiN ψ τ)

def dN (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) (τ : MRep k (n + j)) : GRep k n := psiN (iterN ψ j τ)

noncomputable def dG (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → GRep k (n + j) → GRep k n
  | 0, _, σ => σ
  | j + 1, _, σ => dN ψ j (gres σ)

inductive Chain {n : ℕ} (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) : ℕ → ℕ → GRep k n → Prop
  | nil (a : ℕ) (X : GRep k n) : Subsingleton X.V → Chain R Z a a X
  | step {a b : ℕ} {X Y A : GRep k n} : R a A → Ses Y.ρ X.ρ A.ρ → Chain R Z (a + 1) b Y → Chain R Z a b X
  | skip {a b : ℕ} {X Y : GRep k n} : Z a → GIso Y X → Chain R Z (a + 1) b Y → Chain R Z a b X

def RF (ψ : AddChar k Circle) {r t n : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) (ℓ a : ℕ) (A : GRep k n) : Prop :=
  ∃ (c r' t' : ℕ) (_ : a + c = ℓ) (h₁ : r = r' + a) (h₂ : t = t' + c) (hs : r' + t' = n),
    GIso A (((dG ψ a (π₁.cast h₁)).prod (dG ψ c (π₂.cast h₂))).cast hs)

def RP (ψ : AddChar k Circle) {i t n : ℕ} (τ : MRep k i) (σ : GRep k t) (j a : ℕ) (A : GRep k n) : Prop :=
  ∃ (b c i' t' : ℕ) (_ : a = b + 1) (_ : b + c = j) (hi : i = i' + b) (ht : t = t' + c) (hs : i' + t' = n),
    GIso A (((dN ψ b (mcast hi τ)).prod (dG ψ c (σ.cast ht))).cast hs)

def ZP (i t j a : ℕ) : Prop := ¬ (a ≤ i + 1 ∧ j + 1 - a ≤ t)

def ZF (r t ℓ a : ℕ) : Prop := ¬ (a ≤ r ∧ ℓ - a ≤ t)

section basic
variable {G M V₁ V₂ V₃ : Type} [Group G] [Group M] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃]

theorem ses_twist {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃} (χ : G →* ℂˣ)
    (h : Ses ρ₁ ρ₂ ρ₃) : Ses (twist ρ₁ χ) (twist ρ₂ χ) (twist ρ₃ χ) := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨f, g, fun x v => ?_, fun x v => ?_, hi, hs, he⟩
  · simp [GlobalTheory.SmGL.twist_apply, hf]
  · simp [GlobalTheory.SmGL.twist_apply, hg]

theorem ses_twAct {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v))
    (hsurj : Function.Surjective g)
    (h0 : LinearMap.ker (twMap ρ₁ ρ₂ N θ f hf) = ⊥)
    (h1 : LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg)) :
    Ses (twAct ρ₁ N θ s hs) (twAct ρ₂ N θ s hs) (twAct ρ₃ N θ s hs) := by
  refine ⟨twMap ρ₁ ρ₂ N θ f hf, twMap ρ₂ ρ₃ N θ g hg, fun x v => ?_, fun x v => ?_, LinearMap.ker_eq_bot.1 h0, ?_, h1⟩
  · induction v using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (hf (s x) v)
  · induction v using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (hg (s x) v)
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨v, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk v, rfl⟩

end basic

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_punit {G : Type} [Group G] [TopologicalSpace G] : IsSmooth (Representation.trivial ℂ G PUnit) := by
  intro v
  have : {g : G | Representation.trivial ℂ G PUnit g v = v} = Set.univ := by ext g; simp
  rw [this]; exact isOpen_univ

theorem ses_phiN (ψ : AddChar k Circle) (hc : Continuous ψ) {n : ℕ} {A B C : MRep k (n + 1)} (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (hC : IsSmooth C.ρ) (h : Ses A.ρ B.ρ C.ρ) : Ses (phiN ψ A).ρ (phiN ψ B).ρ (phiN ψ C).ρ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ses_twist _ (ses_twAct (MirUin k (n + 1)) (mirChar k ψ n) _ (levi_stab ψ n) f g hf hg hs ?_ (GlobalTheory.T.mirabolic_phi_minus_exact k ψ hc n _ _ _ _ _ _ hA hB hC f g hf hg he))
  have h0 := GlobalTheory.T.mirabolic_phi_minus_exact k ψ hc n PUnit _ _ (Representation.trivial ℂ _ PUnit) A.ρ B.ρ isSmooth_punit hA hB 0 f
    (fun _ _ => by simp) hf (by rw [LinearMap.range_zero, LinearMap.ker_eq_bot.2 hi])
  rw [← h0, LinearMap.range_eq_bot]
  ext x
  simp [twMap]

theorem ses_psiN {n : ℕ} {A B C : MRep k n} (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (hC : IsSmooth C.ρ) (h : Ses A.ρ B.ρ C.ρ) : Ses (psiN A).ρ (psiN B).ρ (psiN C).ρ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ses_twist _ (ses_twAct (MirUin k n) 1 (levi k n) (levi_normalises n) f g hf hg hs ?_ (GlobalTheory.T.mirabolic_psi_minus_exact k n _ _ _ _ _ _ hA hB hC f g hf hg he))
  have h0 := GlobalTheory.T.mirabolic_psi_minus_exact k n PUnit _ _ (Representation.trivial ℂ _ PUnit) A.ρ B.ρ isSmooth_punit hA hB 0 f
    (fun _ _ => by simp) hf (by rw [LinearMap.range_zero, LinearMap.ker_eq_bot.2 hi])
  rw [← h0, LinearMap.range_eq_bot]
  ext x
  simp [twMap]

theorem isSmooth_phiN (ψ : AddChar k Circle) {n : ℕ} {A : MRep k (n + 1)} (hA : IsSmooth A.ρ) : IsSmooth (phiN ψ A).ρ :=
  isSmooth_twist (GlobalTheory.T.smooth_phi_minus k ψ n _ A.ρ hA)
    (IsSmoothChar.comp (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _)) _ continuous_subtype_val)

theorem isSmooth_psiN {n : ℕ} {A : MRep k n} (hA : IsSmooth A.ρ) : IsSmooth (psiN A).ρ :=
  isSmooth_twist (GlobalTheory.T.smooth_psi_minus k n _ A.ρ hA) (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))

theorem isSmooth_prodGPn {m j : ℕ} (ρ : GRep k m) (τ : MRep k j) : IsSmooth (prodGPn ρ τ).ρ :=
  GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _

theorem isSmooth_prodPGn {i t : ℕ} (τ : MRep k i) (σ : GRep k t) : IsSmooth (prodPGn τ σ).ρ :=
  GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _

theorem isSmooth_mcast {a b : ℕ} (h : a = b) {τ : MRep k a} (hτ : IsSmooth τ.ρ) : IsSmooth (mcast h τ).ρ := by
  subst h; exact hτ

theorem isSmooth_gres {n : ℕ} {π : GRep k (n + 1)} (h : IsSmooth π.ρ) : IsSmooth (gres π).ρ :=
  isSmooth_comp h _ continuous_subtype_val

end

section iso
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}

theorem eint {V W : Type} {G : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (x : G) (v : V) : e (ρ x v) = σ x (e v) :=
  e.toIntertwiningMap.isIntertwining _ _ x v
theorem giso_refl (A : GRep k n) : GIso A A := ⟨Representation.Equiv.refl _⟩
theorem giso_symm {A B : GRep k n} (h : GIso A B) : GIso B A := h.map (·.symm)
theorem giso_trans {A B C : GRep k n} (h : GIso A B) (h' : GIso B C) : GIso A C := by
  obtain ⟨e⟩ := h; obtain ⟨e'⟩ := h'; exact ⟨e.trans e'⟩
theorem miso_refl (A : MRep k n) : MIso A A := ⟨Representation.Equiv.refl _⟩
theorem miso_symm {A B : MRep k n} (h : MIso A B) : MIso B A := h.map (·.symm)
theorem miso_trans {A B C : MRep k n} (h : MIso A B) (h' : MIso B C) : MIso A C := by
  obtain ⟨e⟩ := h; obtain ⟨e'⟩ := h'; exact ⟨e.trans e'⟩
theorem giso_tw {A B : GRep k n} (s : ℝ) (h : GIso A B) : GIso (A.tw s) (B.tw s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpow n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpow n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩
theorem miso_mcast {a b : ℕ} (h : a = b) {A B : MRep k a} (e : MIso A B) : MIso (mcast h A) (mcast h B) := by
  subst h; exact e
theorem giso_cast {a b : ℕ} (h : a = b) {A B : GRep k a} (e : GIso A B) : GIso (A.cast h) (B.cast h) := by
  subst h; exact e
theorem tw_cast {a b : ℕ} (h : a = b) (A : GRep k a) (s : ℝ) : GIso ((A.cast h).tw s) ((A.tw s).cast h) := by
  subst h; exact giso_refl _
theorem giso_prod {r t : ℕ} {A A' : GRep k r} {B B' : GRep k t} (e : GIso A A') (e' : GIso B B') :
    GIso (A.prod B) (A'.prod B') := by
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := e'
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ (fun x => match x with
    | false => e
    | true => e')⟩
end iso

section ses
variable {G V₀ V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
  {ρ₀ : Representation ℂ G V₀} {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}

theorem ses_mid (e : ρ₂.Equiv ρ₀) (h : Ses ρ₁ ρ₂ ρ₃) : Ses ρ₁ ρ₀ ρ₃ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨e.toLinearEquiv.toLinearMap ∘ₗ f, g ∘ₗ e.symm.toLinearEquiv.toLinearMap, fun x v => ?_, fun x v => ?_,
    e.toLinearEquiv.injective.comp hi, hs.comp e.symm.toLinearEquiv.surjective, ?_⟩
  · show e (f (ρ₁ x v)) = ρ₀ x (e (f v))
    rw [hf]; exact eint e x _
  · show g (e.symm (ρ₀ x v)) = ρ₃ x (g (e.symm v))
    rw [← hg]
    exact congrArg g (eint e.symm x v)
  · ext y
    constructor
    · rintro ⟨v, rfl⟩
      have : f v ∈ LinearMap.ker g := he ▸ LinearMap.mem_range_self f v
      simpa [LinearMap.mem_ker, Representation.Equiv.symm_apply_apply] using this
    · intro hy
      have : e.symm y ∈ LinearMap.range f := he ▸ hy
      obtain ⟨v, hv⟩ := this
      exact ⟨v, by simp [hv]⟩

theorem ses_right (e : ρ₃.Equiv ρ₀) (h : Ses ρ₁ ρ₂ ρ₃) : Ses ρ₁ ρ₂ ρ₀ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨f, e.toLinearEquiv.toLinearMap ∘ₗ g, hf, fun x v => ?_, hi, e.toLinearEquiv.surjective.comp hs, ?_⟩
  · show e (g (ρ₂ x v)) = ρ₀ x (e (g v))
    rw [hg]
    exact eint e x _
  · rw [he]
    ext y
    simp

theorem ses_zero_left (e : ρ₂.Equiv ρ₃) [Subsingleton V₁] : Ses ρ₁ ρ₂ ρ₃ := by
  refine ⟨0, e.toLinearEquiv.toLinearMap, fun x v => by simp, fun x v => eint e x v,
    Function.injective_of_subsingleton _, e.toLinearEquiv.surjective, ?_⟩
  rw [LinearMap.range_zero]
  exact (LinearEquiv.ker e.toLinearEquiv).symm

theorem equiv_of_ses_zero (h : Ses ρ₁ ρ₂ ρ₃) [Subsingleton V₃] : Nonempty (ρ₁.Equiv ρ₂) := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  have hsurj : Function.Surjective f := by
    intro y
    have : y ∈ LinearMap.range f := by rw [he]; exact Subsingleton.elim (g y) 0
    exact this
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f ⟨hi, hsurj⟩) fun x => by
    ext v; exact hf x v⟩

end ses

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R R' : ℕ → GRep k n → Prop} {Z Z' : ℕ → Prop}

def zeroG (n : ℕ) : GRep k n := ⟨PUnit, Representation.trivial ℂ _ PUnit⟩

instance (n : ℕ) : Subsingleton (zeroG (k := k) n).V := inferInstanceAs (Subsingleton PUnit)

theorem subsingleton_of_giso {A B : GRep k n} (h : GIso A B) [Subsingleton A.V] : Subsingleton B.V := by
  obtain ⟨e⟩ := h
  exact e.symm.toLinearEquiv.injective.subsingleton

theorem Chain.iso {a b : ℕ} {X X' : GRep k n} (h : Chain R Z a b X) (e : GIso X X') : Chain R Z a b X' := by
  cases h with
  | nil a X hs => exact Chain.nil _ _ (subsingleton_of_giso e)
  | step hR hs hc => obtain ⟨e⟩ := e; exact Chain.step hR (ses_mid e hs) hc
  | skip hZ he hc => exact Chain.skip hZ (giso_trans he e) hc

theorem Chain.mono {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) (hR : ∀ c A, R c A → R' c A) (hZ : ∀ c, Z c → Z' c) :
    Chain R' Z' a b X := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step (hR _ _ h) hs ih
  | skip h he _ ih => exact Chain.skip (hZ _ h) he ih

theorem Chain.shift {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) (hR : ∀ c A, R c A → R' (c + 1) A)
    (hZ : ∀ c, Z c → Z' (c + 1)) : Chain R' Z' (a + 1) (b + 1) X := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step (hR _ _ h) hs ih
  | skip h he _ ih => exact Chain.skip (hZ _ h) he ih

theorem chain_zero {X : GRep k n} (hX : Subsingleton X.V) : ∀ (d a : ℕ), (∀ c, a ≤ c → c < a + d → Z c) →
    Chain R Z a (a + d) X := by
  intro d
  induction d with
  | zero => intro a _; exact Chain.nil _ _ hX
  | succ d ih =>
    intro a h
    refine Chain.skip (h a le_rfl (by omega)) (giso_refl X) ?_
    have := ih (a + 1) (fun c h1 h2 => h c (by omega) (by omega))
    rwa [show a + 1 + d = a + (d + 1) by omega] at this

def Top (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a : ℕ) (C : GRep k n) : Prop :=
  (∃ A, R a A ∧ GIso C A) ∨ (Z a ∧ Subsingleton C.V)

theorem chain_top {a b : ℕ} {X Y C : GRep k n} (hs : Ses Y.ρ X.ρ C.ρ) (ht : Top R Z a C)
    (hc : Chain R Z (a + 1) b Y) : Chain R Z a b X := by
  rcases ht with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, h0⟩
  · exact Chain.step hR (ses_right e hs) hc
  · exact Chain.skip hZ (equiv_of_ses_zero hs) hc

theorem chain_top' {a : ℕ} {X : GRep k n} (ht : Top R Z a X) (d : ℕ) (hZ : ∀ c, a + 1 ≤ c → c < a + 1 + d → Z c) :
    Chain R Z a (a + 1 + d) X := by
  obtain ⟨e⟩ : Nonempty (X.ρ.Equiv X.ρ) := ⟨Representation.Equiv.refl _⟩
  exact chain_top (Y := zeroG n) (ses_zero_left e) ht (chain_zero inferInstance d _ hZ)

theorem Chain.tw {a b : ℕ} {X : GRep k n} (s : ℝ) (h : Chain R Z a b X) :
    Chain (fun c A' => ∃ A, R c A ∧ GIso A' (A.tw s)) Z a b (X.tw s) := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step ⟨_, h, giso_refl _⟩ (ses_twist _ hs) ih
  | skip h he _ ih => exact Chain.skip h (giso_tw s he) ih

end chain

end GlobalTheory.CompanionTheory.LeibOrd

end
