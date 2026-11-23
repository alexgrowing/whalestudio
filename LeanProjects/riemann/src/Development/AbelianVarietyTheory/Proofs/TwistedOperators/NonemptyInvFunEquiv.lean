import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary

noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct

namespace GlobalTheory.OneFunctional

section General

variable {G H K V W X : Type} [Monoid G] [Monoid H] [Monoid K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def Iso (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g x, e (ρ g x) = σ g (e x)

theorem Iso.refl (ρ : Representation ℂ G V) : Iso ρ ρ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Iso.symm {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun g x => e.injective (by rw [he]; simp)⟩

theorem Iso.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X} (h : Iso ρ σ)
    (h' : Iso σ τ) : Iso ρ τ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem Iso.comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (f : H →* G) :
    Iso (ρ.comp f : Representation ℂ H V) (σ.comp f) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun g x => he (f g) x⟩

theorem Iso.twist {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (χ : G →* ℂˣ) :
    Iso (twist χ ρ) (twist χ σ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g x => ?_⟩
  change e ((χ g : ℂ) • ρ g x) = (χ g : ℂ) • σ g (e x)
  rw [map_smul, he]

theorem Iso.tprod {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (h : Iso ρ σ) (h' : Iso ρ' σ') : Iso (ρ.tprod ρ') (σ.tprod σ') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨TensorProduct.congr e e', fun g x => ?_⟩
  induction x with
  | zero => simp
  | tmul a b => simp [he, he']
  | add a b ha hb => simp only [map_add, ha, hb]

theorem Iso.tprod_comm (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Iso (ρ.tprod σ) (σ.tprod ρ) := by
  refine ⟨TensorProduct.comm ℂ V W, fun g x => ?_⟩
  induction x with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem Iso.dual {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Iso ρ.dual σ.dual := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap, fun g x => ?_⟩
  ext w
  simp [Module.Dual.transpose_apply, he]

theorem Iso.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Iso ρ σ :=
  ⟨e.toLinearEquiv, fun g x => e.toIntertwiningMap.isIntertwining _ _ g x⟩

theorem mem_invFun {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} : l ∈ invFun ρ ↔ ∀ g x, l (ρ g x) = l x := Iff.rfl

theorem Iso.nonempty_invFun_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Nonempty (invFun ρ ≃ₗ[ℂ] invFun σ) := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap.ofSubmodules _ _ (le_antisymm ?_ fun l hl => ⟨e.symm.dualMap l, fun g x => ?_, ?_⟩)⟩
  · rintro _ ⟨l, hl, rfl⟩ g x
    change l (e (σ g x)) = l (e x)
    rw [he, hl]
  · obtain ⟨x, rfl⟩ := e.surjective x
    change l (e.symm _) = l (e.symm _)
    rw [← he, e.symm_apply_apply, e.symm_apply_apply, hl]
  · ext x
    simp

theorem Iso.finrank_invFun {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  exact e.finrank_eq

theorem Iso.invFun_eq_bot {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (h0 : invFun σ = ⊥) :
    invFun ρ = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  rw [← Submodule.subsingleton_iff_eq_bot] at h0 ⊢
  exact e.toEquiv.subsingleton

def Contracts {F : Type} [AddCommGroup F] [Module ℂ F] (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V)
    (σ' : Representation ℂ G W) : Prop :=
  ∃ π : F ⊗[ℂ] V →ₗ[ℂ] W, Function.Surjective π ∧
    (∀ h g f v, π (φ (h, g) f ⊗ₜ σ h v) = σ' g (π (f ⊗ₜ v))) ∧
    ∀ l : Module.Dual ℂ (F ⊗[ℂ] V), (∀ h f v, l (φ (h, 1) f ⊗ₜ σ h v) = l (f ⊗ₜ v)) → ∀ x, π x = 0 → l x = 0

theorem Contracts.congr {F F' V' W' : Type} [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {φ : Representation ℂ (H × G) F} {σ : Representation ℂ H V} {τ : Representation ℂ G W}
    {φ' : Representation ℂ (H × G) F'} {σ' : Representation ℂ H V'} {τ' : Representation ℂ G W'}
    (h : Contracts φ σ τ) (h1 : Iso φ φ') (h2 : Iso σ σ') (h3 : Iso τ τ') : Contracts φ' σ' τ' := by
  obtain ⟨π, hs, he, hk⟩ := h
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  obtain ⟨e3, he3⟩ := h3
  refine ⟨e3.toLinearMap ∘ₗ π ∘ₗ (TensorProduct.congr e1 e2).symm.toLinearMap,
    e3.surjective.comp (hs.comp (TensorProduct.congr e1 e2).symm.surjective), fun h g f v => ?_, fun l hl x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := e1.surjective f
    obtain ⟨v, rfl⟩ := e2.surjective v
    simp [← he1, ← he2, he, he3]
  · obtain ⟨x, rfl⟩ := (TensorProduct.congr e1 e2).surjective x
    refine hk (l ∘ₗ (TensorProduct.congr e1 e2).toLinearMap) (fun h f v => ?_) x ?_
    · simp [he1, he2, hl]
    · simpa using hx

end General

section Outer

variable {ι G H : Type} [Monoid G] [Monoid H] {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

def outer (ρ : ∀ τ, Representation ℂ G (V τ)) : Representation ℂ (ι → G) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp (Pi.evalMonoidHom (fun _ : ι => G) τ)

def outer₂ (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) : Representation ℂ ((ι → H) × (ι → G)) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp ((Pi.evalMonoidHom (fun _ : ι => H) τ).prodMap (Pi.evalMonoidHom (fun _ : ι => G) τ))

theorem piTprod_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun τ => ρ τ g := rfl

theorem outer_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : ι → G) :
    outer ρ g = PiTensorProduct.map fun τ => ρ τ (g τ) := rfl

theorem outer₂_apply (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) (h : ι → H) (g : ι → G) :
    outer₂ ρ (h, g) = PiTensorProduct.map fun τ => ρ τ (h τ, g τ) := rfl

theorem Iso.outer {ρ : ∀ τ, Representation ℂ G (V τ)} {σ : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Iso (ρ τ) (σ τ)) :
    Iso (outer ρ) (outer σ) := by
  choose e he using h
  refine ⟨PiTensorProduct.congr e, fun g x => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [outer_apply, he]
  | add a b ha hb => simp only [map_add, ha, hb]

end Outer

abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def conjU (n : ℕ) : U n →* U n where
  toFun g := ⟨(star g.1)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2
    have e : star (star g.1)ᵀ = (g.1)ᵀ := by ext i j; simp
    rw [e, ← Matrix.transpose_mul, mul_eq_one_comm.1 h, Matrix.transpose_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [star_mul, Matrix.transpose_mul])

@[simp] theorem conjU_coe (n : ℕ) (g : U n) : (conjU n g).1 = (star g.1)ᵀ := rfl

abbrev irr (n : ℕ) (lam : DomWeight n) : Representation ℂ (U n) (nablaSq ℂ n lam) := smallRep (unitaryIncl n) lam

def fockOne (a b : ℕ) (α β : ℤ) : Representation ℂ (U a × U b) (MvPolynomial (Fin b × Fin a) ℂ) :=
  twist ((detU a ^ α).comp (MonoidHom.fst _ _) * (detU b ^ β).comp (MonoidHom.snd _ _))
    (GlobalTheory.GLDuality.polyRep ((unitaryIncl a).comp (conjU a)) (unitaryIncl b))

def StepW {a b : ℕ} (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b) : Prop :=
  ∀ i : Fin b, lam'.w i = if h : i.1 < a then lam.w ⟨i.1, h⟩ + α + β else β

end GlobalTheory.OneFunctional
