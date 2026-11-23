import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix

namespace GlobalTheory.RealBessel

variable {n m r : ℕ}

structure IsFrame (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  herm : Jᴴ = J
  unit : IsUnit J
  unit₀ : IsUnit J₀
  codim : m + 2 * r + 1 = n
  gram : Fᴴ * J * F = J₀
  e_indep : LinearIndependent ℂ eᵀ
  e_iso : eᴴ * J * e = 0
  e_perp : Fᴴ * J * e = 0
  z_perpF : (Fᴴ * J) *ᵥ z = 0
  z_perpE : (eᴴ * J) *ᵥ z = 0
  z_ne : Formalism.QuantumDeterminants.herm J z z ≠ 0

def unipRad (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {u | u ∈ UH J ∧
    (∀ i : Fin r, ∃ a : Fin r → ℂ, (∀ j, i ≤ j → a j = 0) ∧ (u - 1) *ᵥ (fun k => e k i) = e *ᵥ a) ∧
    ∀ x : Fin n → ℂ, (eᴴ * J) *ᵥ x = 0 → ∃ a : Fin r → ℂ, (u - 1) *ᵥ x = e *ᵥ a}

def flagVec (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  Fin.snoc (α := fun _ => Fin n → ℂ) (fun i k => e k i) z

def IsCharWith (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (c : Fin r → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ u ∈ unipRad J e, ∀ a : Fin r → Fin r → ℂ, (∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j) →
    χ u = Complex.exp (Complex.I * ((∑ j, c j * a j j).re : ℂ))

def IsGeneric (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ c : Fin r → ℂ, (∀ j, c j ≠ 0) ∧ IsCharWith J e z c χ

def IsEmb (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin m) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  g * F = F * h ∧ ∀ x : Fin n → ℂ, (Fᴴ * J) *ᵥ x = 0 → g *ᵥ x = x

section Forms

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [AddCommGroup W] [Module ℂ W]

def IsContIrred (G : Set (Matrix (Fin m) (Fin m) ℂ)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W) : Prop :=
  IsRepOn G π₀ ∧ (∀ (w : W) (l : Module.Dual ℂ W), ContinuousOn (fun h => l (π₀ h w)) G) ∧
    ∀ U : Submodule ℂ W, (∀ h ∈ G, ∀ w ∈ U, π₀ h w ∈ U) → U = ⊥ ∨ U = ⊤

structure IsBesselForm (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) (β : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  cont : ∀ w : W, ∃ l : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG J) σ l ∧ ∀ x : V, l x = β w x
  inv : ∀ h ∈ UH J₀, ∀ g ∈ UH J, IsEmb J F g h → ∀ (w : W) (x y : V), (y : H) = σ g x → β (π₀ h w) y = β w x
  equiv : ∀ u ∈ unipRad J e, ∀ (w : W) (x y : V), (y : H) = σ u x → β w y = χ u * β w x

def besselForms (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) : Submodule ℂ (W →ₗ[ℂ] V →ₗ[ℂ] ℂ) where
  carrier := {β | IsBesselForm J J₀ F e χ σ π₀ V β}
  zero_mem' := ⟨fun _ => ⟨0, ⟨[], 0, by simp, by simp⟩, fun _ => rfl⟩, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => by simp⟩
  add_mem' := fun {β β'} hβ hβ' =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      obtain ⟨l', h1', h2'⟩ := hβ'.cont w
      exact ⟨l + l', GlobalTheory.MultMem.sobCont_add h1 h1', fun x => by simp [h2, h2']⟩,
    fun h hh g hg hE w x y hy => by
      simp only [LinearMap.add_apply, hβ.inv h hh g hg hE w x y hy, hβ'.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.add_apply, hβ.equiv u hu w x y hy, hβ'.equiv u hu w x y hy, mul_add]⟩
  smul_mem' := fun c β hβ =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      exact ⟨c • l, GlobalTheory.MultMem.sobCont_smul c h1, fun x => by simp [h2]⟩,
    fun h hh g hg hE w x y hy => by simp only [LinearMap.smul_apply, hβ.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.smul_apply, hβ.equiv u hu w x y hy, smul_eq_mul, mul_left_comm]⟩

end Forms

variable {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ}
  {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ}

theorem IsFrame.exists_emb (hf : IsFrame J J₀ F e z) {h : Matrix (Fin m) (Fin m) ℂ} (hh : h ∈ UH J₀) :
    ∃ g ∈ UH J, IsEmb J F g h := by
  have hd := (Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀
  have hh' : hᴴ * J₀ * h = J₀ := hh
  have h0 : J₀ᴴ = J₀ := by
    rw [← hf.gram]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, hf.herm, Matrix.mul_assoc]
  obtain ⟨P, hP⟩ : ∃ P, P = J₀⁻¹ * (Fᴴ * J) := ⟨_, rfl⟩
  have h1 : Fᴴ * J = J₀ * P := by rw [hP, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
  have h2 : J * F = Pᴴ * J₀ := by
    have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hf.herm, h0] at this
  have h3 : P * F = 1 := by rw [hP, Matrix.mul_assoc, hf.gram, nonsing_inv_mul _ hd]
  refine ⟨1 + F * (h - 1) * P, ?_, ?_, fun x hx => ?_⟩
  · show _ * J * _ = J
    have e1 : (1 + F * (h - 1) * P)ᴴ * J * (1 + F * (h - 1) * P) =
        J + (J * F) * (h - 1) * P + Pᴴ * (hᴴ - 1) * (Fᴴ * J) + Pᴴ * (hᴴ - 1) * (Fᴴ * J * F) * (h - 1) * P := by
      simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, Matrix.add_mul,
        Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    have e2 : J₀ * (h - 1) + (hᴴ - 1) * J₀ + (hᴴ - 1) * J₀ * (h - 1) = 0 := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hh']
      abel
    have e3 : Pᴴ * (J₀ * (h - 1) + (hᴴ - 1) * J₀ + (hᴴ - 1) * J₀ * (h - 1)) * P = 0 := by rw [e2]; simp
    rw [e1, hf.gram, h2, h1, add_assoc, add_assoc, add_eq_left, ← e3]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  · rw [Matrix.add_mul, Matrix.mul_assoc, h3, Matrix.mul_sub]; simp
  · rw [add_mulVec, ← mulVec_mulVec, hP, ← mulVec_mulVec x J₀⁻¹, hx]; simp

theorem IsFrame.exists_coords (hf : IsFrame J J₀ F e z) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad J e) :
    ∃ a : Fin r → Fin r → ℂ, ∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j := by
  have : ∀ i : Fin (r + 1), ∃ a, (u - 1) *ᵥ flagVec e z i = e *ᵥ a := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [flagVec] using hu.2.2 z hf.z_perpE
    · obtain ⟨a, -, ha⟩ := hu.2.1 j
      exact ⟨a, by simpa [flagVec] using ha⟩
  exact ⟨fun j => (this j.succ).choose, fun j => (this j.succ).choose_spec⟩

end GlobalTheory.RealBessel

namespace GlobalTheory.Published

open GlobalTheory.RealBessel

def BesselUniquenessReal : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ → IsIrredOn (UH J) σ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Mult in

theorem BesselUniquenessReal.model (hB : BesselUniquenessReal) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) {m r : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin V.rank) (Fin m) ℂ}
    {e : Matrix (Fin V.rank) (Fin r) ℂ} {z : Fin V.rank → ℂ} (hf : IsFrame (gramAt D V τ) J₀ F e z)
    {χ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ} (hχ : IsGeneric (gramAt D V τ) e z χ)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (UH J₀) π₀) :
    Module.rank ℂ (besselForms (gramAt D V τ) J₀ F e χ (M.rep τ) π₀ (M.sm τ)) ≤ 1 := by
  obtain ⟨hc, -, hU, hI, -⟩ := M.ds τ
  rw [sm_eq M τ]
  exact hB _ _ _ _ _ _ _ _ hf χ hχ _ _ (isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hU)
    (isIrredOn_trRep (M.fr_unit τ) (M.fr_gram τ) hI) W π₀ hπ

end GlobalTheory.Published

end
