import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GoodLat
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv

section Heis

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def brk (H : Sesq V) (y t : V) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H t y : ℂ))

def hatS (H : Sesq V) (vol : ℝ) (SA : Finset V) (Φ : V → ℂ) (y : V) : ℂ :=
  ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ) * ∑ t ∈ SA, Φ t * (brk H y t)⁻¹)

def xiS (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SA SB : Finset V) (Φ : V → ℂ) (e : V → ℂ) : V → ℂ :=
  sumU H (fun y => hatS H vol SA Φ y * α y) SB e

def xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) (e : V → ℂ) : V → ℂ :=
  fun z => ∑ x ∈ SX, α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) e) z

open Classical in

def indL (M : AddSubgroup V) (t : V) : ℂ := if t ∈ M then 1 else 0

def xiInd (H : Sesq V) (α : V → ℂ) (vol : ℝ) (M : AddSubgroup V) (SA SB : Finset V) (e : V → ℂ) (s : V) : V → ℂ :=
  fun z => α s * opU H (-s) (xiS H α vol SA SB (indL M) e) z

def xiU (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (θ : V → ℂ) : Sch (cU H A B) (Λ.addSubgroupOf A) →ₗ[ℂ] (V → ℂ) :=
  Classical.epsilon fun Xi => IsXi (cU H A B) (wA H α A) (wB H α B) (Λ.addSubgroupOf A) θ Xi

def xiT (H : Sesq V) (α : V → ℂ) (vol : ℝ) (A B Λ : AddSubgroup V) (θ : V → ℂ) : Sch (cU H A B) (Λ.addSubgroupOf A) →ₗ[ℂ] (V → ℂ) :=
  ((Real.sqrt vol : ℝ) : ℂ) • xiU H α A B Λ θ

def resA (A : AddSubgroup V) (Φ : V → ℂ) : A → ℂ := fun t => Φ (t : V)

def SplitHyp (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) : Prop :=
  IsHerm H ∧ IsSemiChar H A α ∧ IsSemiChar H B α ∧ IsSelfDual H A ∧ IsSelfDual H B ∧ GoodLat H α A B Λ

def InvOn (A B : AddSubgroup V) (Φ : V → ℂ) : Prop := ∀ t ∈ A, ∀ m ∈ A, m ∈ B → Φ (t + m) = Φ t

def repsOf (Λ₁ Λ₂ : AddSubgroup V) : Finset V := Classical.epsilon fun S => IsReps Λ₁ Λ₂ S

end Heis

def XiLinear : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (a : ℂ) (Φ Φ' e e' : V → ℂ) (z : V),
    xiS H α vol SA SB (fun t => a * Φ t + Φ' t) e z = a * xiS H α vol SA SB Φ e z + xiS H α vol SA SB Φ' e z ∧
    xiS H α vol SA SB Φ (fun v => a * e v + e' v) z = a * xiS H α vol SA SB Φ e z + xiS H α vol SA SB Φ e' z ∧
    xiL H α vol SX SA SB (fun t => a * Φ t + Φ' t) e z = a * xiL H α vol SX SA SB Φ e z + xiL H α vol SX SA SB Φ' e z ∧
    xiL H α vol SX SA SB Φ (fun v => a * e v + e' v) z = a * xiL H α vol SX SA SB Φ e z + xiL H α vol SX SA SB Φ e' z

def BrkComm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H →
    (∀ (y t : V) (F : V → ℂ) (z : V), opU H t (opU H y F) z = brk H y t * opU H y (opU H t F) z) ∧
    ∀ (A B : AddSubgroup V) (y : B) (t : A), cU H A B y t = brk H (y : V) (t : V)

def XiUIs : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ θ ∈ fixedBy H α Λ, IsXi (cU H A B) (wA H α A) (wB H α B) (Λ.addSubgroupOf A) θ (xiU H α A B Λ θ)

def XiTieS : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, 0 < vol → ∀ θ ∈ fixedBy H α Λ,
    ∀ Φ : V → ℂ, InvOn A B Φ → (∀ t ∈ A, t ∉ Λ → Φ t = 0) →
      ∃ h : resA A Φ ∈ Sch (cU H A B) (Λ.addSubgroupOf A), xiT H α vol A B Λ θ ⟨resA A Φ, h⟩ = xiS H α vol SA SB Φ θ

def XiTieL : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SX SA SB : Finset V, IsReps Λ A SX → IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, 0 < vol → ∀ θ ∈ fixedBy H α Λ,
    ∀ Φ : V → ℂ, InvOn A B Φ →
      ∃ h : resA A Φ ∈ Sch (cU H A B) (Λ.addSubgroupOf A), xiT H α vol A B Λ θ ⟨resA A Φ, h⟩ = xiL H α vol SX SA SB Φ θ

def XiTieInd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, 0 < vol → ∀ θ ∈ fixedBy H α Λ, ∀ s ∈ A,
      ∃ h : resA A (fun t => indL B (t - s)) ∈ Sch (cU H A B) (Λ.addSubgroupOf A),
        xiT H α vol A B Λ θ ⟨resA A (fun t => indL B (t - s)), h⟩ = xiInd H α vol B SA SB θ s

def XiVacuum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, 0 < vol → ∀ θ ∈ fixedBy H α Λ, ∀ z,
      xiS H α vol SA SB (fun _ => ((Real.sqrt vol : ℝ) : ℂ)⁻¹) θ z = θ z

def XiTranslate : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SX SA SB : Finset V, IsReps Λ A SX → IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ,
    ∀ Φ : V → ℂ, InvOn A B Φ → ∀ x ∈ A, ∀ z,
      xiL H α vol SX SA SB (fun t => Φ (t + x)) θ z = α x * opU H x (xiL H α vol SX SA SB Φ θ) z

def XiModulate : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SX SA SB : Finset V, IsReps Λ A SX → IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ,
    ∀ Φ : V → ℂ, InvOn A B Φ → ∀ y ∈ B, ∀ z,
      xiL H α vol SX SA SB (fun t => brk H y t * Φ t) θ z = α y * opU H y (xiL H α vol SX SA SB Φ θ) z

def XiIndZero : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ (vol : ℝ) (θ : V → ℂ) (z : V),
      xiS H α vol SA SB (indL B) θ z = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * sumU H α SB θ z

def XiExpandS : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ, ∀ (Φ : V → ℂ) (z : V),
      xiS H α vol SA SB Φ θ z = ∑ s ∈ SA, Φ s * xiInd H α vol B SA SB θ s z

def XiExpandL : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ S SX SA SB : Finset V, IsReps B A S → IsReps Λ A SX → IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ,
    ∀ Φ : V → ℂ, InvOn A B Φ → ∀ z,
      xiL H α vol SX SA SB Φ θ z = ∑ s ∈ S, Φ s * xiInd H α vol B SA SB θ s z

def XiIndClass : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ, ∀ s ∈ A, ∀ m ∈ A, m ∈ B → ∀ z,
      xiInd H α vol B SA SB θ (s + m) z = xiInd H α vol B SA SB θ s z

def XiReps : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SX SA SB SX' SA' SB' : Finset V, IsReps Λ A SX → IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → IsReps Λ A SX' → IsReps B (Λ ⊓ A) SA' →
    IsReps Λ B SB' → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ, ∀ Φ : V → ℂ, InvOn A B Φ → ∀ z,
      xiL H α vol SX' SA' SB' Φ θ z = xiL H α vol SX SA SB Φ θ z

def XiProject : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, ∀ θ ∈ fixedBy H α Λ, ∀ Φ : V → ℂ, ∀ y ∈ SB, ∀ z,
      ∑ x ∈ SA, (brk H y x)⁻¹ * (α x * opU H x (xiS H α vol SA SB Φ θ) z)
        = (SA.card : ℂ) * (hatS H vol SA Φ y * α y * opU H y θ z)

def XiInjective : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ →
    ∀ SA SB : Finset V, IsReps B (Λ ⊓ A) SA → IsReps Λ B SB → ∀ vol : ℝ, 0 < vol → ∀ θ ∈ fixedBy H α Λ, θ ≠ 0 →
    ∀ Φ : V → ℂ, InvOn A B Φ → (∀ z, xiS H α vol SA SB Φ θ z = 0) → ∀ t ∈ Λ ⊓ A, Φ t = 0

section Conc

open Formalism.L2.Col Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

abbrev VV (ι : Type) (a b : ℕ) : Type := ι → Fin b → Fin a → ℂ

def embH (emb : ι → E →+* ℂ) (δ : ℂ) : HomE E a b →+ VV ι a b where
  toFun x := fun τ i j => δ * emb τ (x (Pi.single j 1) i)
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def HV (sc : ℝ) : Sesq (VV ι a b) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j))
    (by intro x y w; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (by intro c x w; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (by intro x y w; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (by intro c x w; simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def alV (d : ℕ) (sc : ℝ) : VV ι a b → ℂ := alphaQ (Real.sqrt d / 2) (HV sc)

def homO (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {x | ∀ y ∈ N, x y ∈ N'}
  add_mem' := fun hx hx' y hy => add_mem (hx y hy) (hx' y hy)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r _ hx y hy => Submodule.smul_mem _ r (hx y hy)

def perO (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) :=
  Submodule.span (𝓞 E) {z | ∃ r ∈ AA0, ∃ x ∈ homO N N', z = r • x}

open Classical in

def expS (SS : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) : ℤ :=
  if Q ∈ SS then 1 else if conjPrime₂ Q ∈ SS then -1 else 0

def twist₂ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (c : ℕ)
    (e : HeightOneSpectrum (𝓞 E) → ℤ) : Submodule (𝓞 E) W :=
  ⨅ Q : HeightOneSpectrum (𝓞 E), (localization₂ Q.asIdeal M).comap ((((c : E) ^ e Q)⁻¹ • (LinearMap.id : W →ₗ[E] W)).restrictScalars (𝓞 E))

def laV (emb : ι → E →+* ℂ) (δ : ℂ) (M : Submodule (𝓞 E) (HomE E a b)) : AddSubgroup (VV ι a b) :=
  M.toAddSubgroup.map (embH emb δ)

def halfAO (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (c : ℕ) : Submodule (𝓞 E) (HomE E a b) :=
  twist₂ M c fun Q => -expS SS Q

def halfBO (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (c : ℕ) : Submodule (𝓞 E) (HomE E a b) :=
  twist₂ M c (expS SS)

def IsLiftS (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (c : ℕ) (x s : HomE E a b) : Prop :=
  s ∈ halfAO SS M c ∧ ∀ P ∈ SS, ((c : E)⁻¹ • (s - x)) ∈ localization₂ P.asIdeal M

def liftS (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) (c : ℕ) (x : HomE E a b) : HomE E a b :=
  Classical.epsilon fun s => IsLiftS SS M c x s

def volS (SS : Finset (HeightOneSpectrum (𝓞 E))) (M₀ M : Submodule (𝓞 E) (HomE E a b)) : ℝ :=
  ∏ P ∈ SS, (((localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup : ℕ) : ℝ) /
    (((localization₂ P.asIdeal M).toAddSubgroup.relIndex (localization₂ P.asIdeal M₀).toAddSubgroup : ℕ) : ℝ)

def absP (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℝ := NumberField.HeightOneSpectrum.adicAbv E P x

def movedS (SS : Finset (HeightOneSpectrum (𝓞 E))) (g : SS → Sp E a ≃ₗ[E] Sp E a) (g' : SS → Sp E b ≃ₗ[E] Sp E b)
    (Φ : SS → HomE E a b → ℂ) (t : HomE E a b) : ℂ :=
  ∏ P : SS, (((absP P.1 (LinearEquiv.det (g P) : Eˣ) ^ ((b : ℝ) / 2) * absP P.1 (LinearEquiv.det (g' P) : Eˣ) ^ (-((a : ℝ) / 2)) : ℝ) : ℂ) *
    Φ P (inFr (g P) (g' P) t))

def onV (emb : ι → E →+* ℂ) (δ : ℂ) (Ξ : HomE E a b → ℂ) (v : VV ι a b) : ℂ := by
  classical exact if h : ∃ x, embH emb δ x = v then Ξ h.choose else 0

variable (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
  (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)

def LamC : AddSubgroup (VV ι a b) := laV emb δ (perO AA0 N N')

def AC : AddSubgroup (VV ι a b) := laV emb δ (halfAO SS (perO AA0 N N') c)

def BC : AddSubgroup (VV ι a b) := laV emb δ (halfBO SS (perO AA0 N N') c)

def volC : ℝ := volS SS (perO AA0 (stdLat E a) (stdLat E b)) (perO AA0 N N')

def xiV (vol : ℝ) (Ξ : HomE E a b → ℂ) (θ : VV ι a b → ℂ) : VV ι a b → ℂ :=
  xiL (HV sc) (alV d sc) vol
    (repsOf (LamC emb δ AA0 N N') (AC emb δ AA0 SS N N' c))
    (repsOf (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c))
    (repsOf (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c)) (onV emb δ Ξ) θ

def xiIndV (vol : ℝ) (θ : VV ι a b → ℂ) (x : HomE E a b) : VV ι a b → ℂ :=
  xiInd (HV sc) (alV d sc) vol (BC emb δ AA0 SS N N' c)
    (repsOf (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c))
    (repsOf (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c)) θ (embH emb δ (liftS SS (perO AA0 N N') c x))

def xiC (Ξ : HomE E a b → ℂ) (θ : VV ι a b → ℂ) : VV ι a b → ℂ := xiV emb δ d sc AA0 SS N N' c (volC AA0 SS N N') Ξ θ

def xiIndC (θ : VV ι a b → ℂ) (x : HomE E a b) : VV ι a b → ℂ := xiIndV emb δ d sc AA0 SS N N' c (volC AA0 SS N N') θ x

def thC (Ξ : HomE E a b → ℂ) (θ : VV ι a b → ℂ) : VV ι a b → ℂ := xiV emb δ d sc AA0 SS N N' c 1 Ξ θ

def thIndC (θ : VV ι a b → ℂ) (x : HomE E a b) : VV ι a b → ℂ := xiIndV emb δ d sc AA0 SS N N' c 1 θ x

def LaFacts : Prop := IsSelfDual (HV sc) (LamC emb δ AA0 N N') ∧ IsSemiChar (HV sc) (LamC emb δ AA0 N N') (alV d sc)

end Conc

def MovedVol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b))
    (g : SS → Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : SS → Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b),
    (∀ P ∈ SS, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal AA0 = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) →
    (∀ (P : SS) (x : Formalism.L2.Col.Sp E a), g P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N ↔ x ∈ Formalism.L2.Col.stdAt E a P.1) →
    (∀ (P : SS) (x : Formalism.L2.Col.Sp E b), g' P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N' ↔ x ∈ Formalism.L2.Col.stdAt E b P.1) →
    ∏ P : SS, (absP P.1 (LinearEquiv.det (g P) : Eˣ) ^ ((b : ℝ) / 2) * absP P.1 (LinearEquiv.det (g' P) : Eˣ) ^ (-((a : ℝ) / 2)))
      = (Real.sqrt (volC AA0 SS N N'))⁻¹

def TwHom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E)
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ),
    N.FG → 0 < c → twist₂ (perO AA0 N N') c e = perO AA0 N (twist₂ N' c e)

def HalvesC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ),
    δ ≠ 0 → 0 < c → (∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) →
    IsSelfDual (HV sc) (LamC emb δ AA0 N N') → IsSelfDual (HV sc) (AC emb δ AA0 SS N N' c) → IsSelfDual (HV sc) (BC emb δ AA0 SS N N' c) →
    IsSemiChar (HV sc) (LamC emb δ AA0 N N') (alV d sc) → IsSemiChar (HV sc) (AC emb δ AA0 SS N N' c) (alV d sc) →
    IsSemiChar (HV sc) (BC emb δ AA0 SS N N' c) (alV d sc) →
      SplitHyp (HV sc) (alV d sc) (AC emb δ AA0 SS N N' c) (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N')

def LiftExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ), 0 < c → (∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) →
    (∀ x : Formalism.L2.Col.HomE E a b, ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ M) →
    ∀ x : Formalism.L2.Col.HomE E a b, (∀ P ∈ SS, (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) → IsLiftS SS M c x (liftS SS M c x)

def XiIndCClass : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ),
    SplitHyp (HV sc) (alV d sc) (AC emb δ AA0 SS N N' c) (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N') →
    relIdx (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c) ≠ 0 →
    relIdx (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c) ≠ 0 →
    ∀ θ ∈ fixedBy (HV sc) (alV d sc) (LamC emb δ AA0 N N'), ∀ x x' : Formalism.L2.Col.HomE E a b,
    IsLiftS SS (perO AA0 N N') c x (liftS SS (perO AA0 N N') c x) → IsLiftS SS (perO AA0 N N') c x' (liftS SS (perO AA0 N N') c x') →
    (∀ P ∈ SS, ((c : E)⁻¹ • (x - x')) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO AA0 N N')) →
    ∀ vol : ℝ, xiIndV emb δ d sc AA0 SS N N' c vol θ x = xiIndV emb δ d sc AA0 SS N N' c vol θ x'

def HalvesOfLa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ),
    δ ≠ 0 → 0 < c → (∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) → N.FG →
    LaFacts emb δ d sc AA0 N N' → LaFacts emb δ d sc AA0 N (twist₂ N' c (expS SS)) → LaFacts emb δ d sc AA0 N (twist₂ N' c fun Q => -expS SS Q) →
      SplitHyp (HV sc) (alV d sc) (AC emb δ AA0 SS N N' c) (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N')

def TwSelfDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (b : ℕ) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ)
    (e : HeightOneSpectrum (𝓞 E) → ℤ), N'.FG → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) →
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd E b) N' → Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd E b) (twist₂ N' c e)

def ExpSConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (SS : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) →
    ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q

def VolCPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)),
    N.FG → N'.FG → Submodule.span E (N : Set (Formalism.L2.Col.Sp E a)) = ⊤ → Submodule.span E (N' : Set (Formalism.L2.Col.Sp E b)) = ⊤ → AA0.FG → AA0 ≠ ⊥ →
      0 < volC AA0 SS N N'

def ThCMoved : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)
    (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ), 0 < volC AA0 SS N N' →
    ∀ (θ : VV ι a b → ℂ),
    (∀ Ξ : Formalism.L2.Col.HomE E a b → ℂ, thC emb δ d sc AA0 SS N N' c Ξ θ =
      xiC emb δ d sc AA0 SS N N' c (fun x => ((Real.sqrt (volC AA0 SS N N') : ℝ) : ℂ)⁻¹ * Ξ x) θ) ∧
    ∀ (x : Formalism.L2.Col.HomE E a b) (z : VV ι a b), thIndC emb δ d sc AA0 SS N N' c θ x z =
      ((Real.sqrt (volC AA0 SS N N') : ℝ) : ℂ)⁻¹ * xiIndC emb δ d sc AA0 SS N N' c θ x z

section Entries

open Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {ι : Type} [Fintype ι] (emb : ι → X.E →+* ℂ) (σ : X.K →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 X.E) X.E)

def levC (u : Pr.Word) : ℕ := cAof sel mu cst * cBof sel mu cst u

def thEntry {u : Pr.Word} (i : ℕ) (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (θ : VV ι (R.N i) (R.N (i + 1)) → ℂ) : VV ι (R.N i) (R.N (i + 1)) → ℂ :=
  thC emb δ d sc AA0 (Sall sel mu u) p.deco.1.N p'.deco.1.N (levC sel mu cst u)
    (fun x => σ (XiEntry Ch sel mu cst L i al be p p' x)) θ

def thCpl1 {u : Pr.Word} (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (θ : VV ι (R.N m2) (R.N (m2 + 1)) → ℂ) : VV ι (R.N m2) (R.N (m2 + 1)) → ℂ :=
  thC emb δ d sc AA0 (Sall sel mu u) p₀.deco.1.N p.deco.1.N (levC sel mu cst u)
    (fun x => σ (XiCpl1 Ch sel mu cst L m2 al p₀ p Y x)) θ

def thCpl2 {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu)
    (θ : VV ι (R.N (m2 + 1)) (R.N R.m) → ℂ) : VV ι (R.N (m2 + 1)) (R.N R.m) → ℂ :=
  thC emb δ d sc AA0 (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N (levC sel mu cst u)
    (fun x => σ (XiCpl2 Ch sel mu cst m2 p Y dd x)) θ

end Entries

end Formalism.L2.Ker
