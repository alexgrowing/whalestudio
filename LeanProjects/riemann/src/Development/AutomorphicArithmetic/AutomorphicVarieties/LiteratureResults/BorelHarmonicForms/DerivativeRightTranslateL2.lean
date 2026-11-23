import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct ComplexOrder

namespace UpperTheory.V.Lit.Bor

section Lie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def ell : Lie E a →ₗ[ℝ] ℝ where
  toFun X := (∑ w : InfinitePlace E, ∑ i, (X i i w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E))
  map_add' X Y := by simp [Finset.sum_add_distrib, add_div]
  map_smul' c X := by simp [← Finset.mul_sum, mul_div_assoc]

def trF (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∑ w : InfinitePlace E, ((X * Y).trace w).re

def IsFrame {n : ℕ} (e : Fin n → Herm E a) : Prop := ∀ X : Herm E a, X = ∑ j, trF (e j).1 X.1 • e j

def shift {A : Type} [Ring A] [Module ℝ A] (L : Lie E a →ₗ[ℝ] A) (r : ℝ) : Lie E a →ₗ[ℝ] A :=
  L + (r • ell E a).smulRight 1

theorem shift_apply {A : Type} [Ring A] [Module ℝ A] (L : Lie E a →ₗ[ℝ] A) (r : ℝ) (X : Lie E a) :
    shift L r X = L X + (r * ell E a X) • (1 : A) := rfl

omit [NumberField E] in

def cas {A : Type} [Ring A] [Module ℝ A] (L : Lie E a →ₗ[ℝ] A) {n : ℕ} (e : Fin n → Herm E a) : A :=
  ∑ j, (L (toL (e j).1) * L (toL (e j).1) - L (toL (Complex.I • (e j).1)) * L (toL (Complex.I • (e j).1)))

omit [NumberField E] in

def IsBasic {M : Type} [AddCommGroup M] [Module ℝ M] {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → ω X = 0

end Lie

section Form

variable {W : Type} [AddCommGroup W] [Module ℂ W]

structure IsPos (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (N : Submodule ℂ W) : Prop where
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  nonneg : ∀ x ∈ N, 0 ≤ (H x x).re
  definite : ∀ x ∈ N, H x x = 0 → x = 0

def cmp {d : ℕ} (i : Fin d) : W ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W (LinearMap.proj i)

@[simp] theorem cmp_tmul {d : ℕ} (i : Fin d) (φ : W) (v : Fin d → ℂ) : cmp i (φ ⊗ₜ[ℂ] v) = v i • φ := by simp [cmp]

theorem sum_cmp {d : ℕ} (m : W ⊗[ℂ] (Fin d → ℂ)) : ∑ i, cmp i m ⊗ₜ[ℂ] (Pi.single i 1 : Fin d → ℂ) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul φ v =>
    simp only [cmp_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    congr 1
    ext j
    simp [Pi.single_apply]

def tens (d : ℕ) (N : Submodule ℂ W) : Submodule ℂ (W ⊗[ℂ] (Fin d → ℂ)) := ⨅ i, N.comap (cmp i)

theorem mem_tens {d : ℕ} {N : Submodule ℂ W} {m : W ⊗[ℂ] (Fin d → ℂ)} : m ∈ tens d N ↔ ∀ i, cmp i m ∈ N := by
  simp [tens]

theorem mem_span_of_cmp {d : ℕ} {P : W → Prop} {m : W ⊗[ℂ] (Fin d → ℂ)} (h : ∀ i, P (cmp i m)) :
    m ∈ Submodule.span ℂ {x : W ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} := by
  rw [← sum_cmp m]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, _, h i, rfl⟩

theorem span_le_tens {d : ℕ} {P : W → Prop} {N : Submodule ℂ W} (h : ∀ φ, P φ → φ ∈ N) :
    Submodule.span ℂ {x : W ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} ≤ tens d N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ, v, hφ, rfl⟩
  exact mem_tens.2 fun i => by rw [cmp_tmul]; exact N.smul_mem _ (h φ hφ)

def tform {d : ℕ} (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (G : Matrix (Fin d) (Fin d) ℂ) :
    W ⊗[ℂ] (Fin d → ℂ) →ₗ⋆[ℂ] W ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, ∑ j, G i j • (H ∘ₛₗ cmp i).compl₂ (cmp j)

theorem tform_apply {d : ℕ} (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (G : Matrix (Fin d) (Fin d) ℂ) (x y : W ⊗[ℂ] (Fin d → ℂ)) :
    tform H G x y = ∑ i, ∑ j, G i j * H (cmp i x) (cmp j y) := by
  simp [tform, LinearMap.sum_apply]

end Form

section Complex

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (L : Lie E a →ₗ[ℝ] Module.End ℂ M) {n : ℕ} (e : Fin n → Herm E a)

def del {q : ℕ} (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) : Herm E a [⋀^Fin q]→ₗ[ℝ] M :=
  ∑ j, ((L (toL (e j).1)).restrictScalars ℝ).compAlternatingMap (ω.curryLeft (e j))

theorem del_apply {q : ℕ} (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) (X : Fin q → Herm E a) :
    del L e ω X = ∑ j, L (toL (e j).1) (ω (Matrix.vecCons (e j) X)) := by
  have h : ∀ (s : Finset (Fin n)) (f : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] M), (∑ j ∈ s, f j) X = ∑ j ∈ s, f j X := fun s f => by
    induction s using Finset.cons_induction with
    | empty => rfl
    | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, AlternatingMap.add_apply, ih]
  rw [del, h]
  rfl

def Coclosed : {q : ℕ} → (Herm E a [⋀^Fin q]→ₗ[ℝ] M) → Prop
  | 0, _ => True
  | _ + 1, ω => del L e ω = 0

def ip (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) {q : ℕ} (ω η : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : ℂ :=
  ∑ I : Fin q → Fin n, H (ω fun i => e (I i)) (η fun i => e (I i))

def adj [NumberField E] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M) (r : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ M := shift B (-r) - shift A r

theorem adj_apply [NumberField E] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M) (r : ℝ) (X : Lie E a) (m : M) :
    adj A B r X m = B X m - A X m - (2 * r * ell E a X) • m := by
  simp only [adj, LinearMap.sub_apply, shift_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  module

theorem shift_add_shift [NumberField E] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M) (r : ℝ) : shift A r + shift B (-r) = A + B := by
  refine LinearMap.ext fun X => LinearMap.ext fun m => ?_
  simp only [shift_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  module

end Complex

section Sm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smA (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lie E a X).rTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add]
  map_smul' c X := by
    rw [map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lie E a X),
      ← algebraMap_smul ℂ c (LinearMap.rTensor _ _ : Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), LinearMap.rTensor_smul]

def smB (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) := smLie Ξ - smA Ξ

theorem smA_apply (Ξ : AlgRep E a) (X : Lie E a) : smA Ξ X = (lie E a X).rTensor _ := rfl

theorem smB_apply (Ξ : AlgRep E a) (X : Lie E a) : smB Ξ X = (Matrix.toLin' (Ξ.dmat X)).lTensor _ :=
  add_sub_cancel_left _ _

def smAdj (Ξ : AlgRep E a) (r : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) := adj (smA Ξ) (smB Ξ) r

def piAdj (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  adj (M := π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (lieA π Ξ) (lieB π Ξ) r

def incl (π : CuspSub E a) (Ξ : AlgRep E a) : (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) →ₗ[ℂ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) := π.V.subtype.rTensor _

def inclCo (π : CuspSub E a) (Ξ : AlgRep E a) {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) :
    Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) := ((incl π Ξ).restrictScalars ℝ).compAlternatingMap ω

theorem inclCo_apply (π : CuspSub E a) (Ξ : AlgRep E a) {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (X : Fin q → Herm E a) :
    inclCo π Ξ ω X = incl π Ξ (ω X) := rfl

structure IsSq (r : ℝ) (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}
  one : lie E a (oneL E a) φ = -(r : ℂ) • φ
  sq : ∀ l : List (Lie E a), IsSqIntMod ((l.map (lie E a)).prod φ)

variable (E a) in

def sqSub (r : ℝ) : Submodule ℂ (Sm E a) := Submodule.span ℂ {φ | IsSq r φ}

structure IsPet (r : ℝ) (H : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ) : Prop where
  pos : IsPos H (sqSub E a r)
  skew : ∀ (X : Lie E a), ∀ φ ∈ sqSub E a r, ∀ ψ ∈ sqSub E a r,
    H (lie E a X φ) ψ + H φ (lie E a X ψ) = -((2 * r * ell E a X : ℝ) : ℂ) * H φ ψ

omit [IsTotallyComplex E] in

structure IsAdm (Ξ : AlgRep E a) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) : Prop where
  pos : G.PosDef
  adj : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), (Ξ.dmat (toL X))ᴴ * G = G * Ξ.dmat (toL (star X))

omit [IsTotallyComplex E] in

def HasOne (Ξ : AlgRep E a) (r : ℝ) : Prop := Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsTw (r : ℝ) (χ : HChar E) : Prop :=
  (∃ s : ℝ, χ.IsAbsPow s) ∧ ∀ (X : Lie E a) (φ : Sm E a),
    lie E a X (mulChi a χ φ) = mulChi a χ (lie E a X φ + ((r * ell E a X : ℝ) : ℂ) • φ)

structure IsHarm (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (r : ℝ) {n : ℕ} (e : Fin n → Herm E a) {q : ℕ}
    (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) : Prop where
  rel : IsRelCochain Ξ (IsCuspFn U Ξ) ω
  closed : dCo (smLie Ξ) ω = 0
  coclosed : Coclosed (smAdj Ξ r) e ω

omit [IsTotallyComplex E] in

def UnitsTriv [IsTotallyComplex E] (Ξ : AlgRep E a) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ u : (𝓞 E)ˣ,
    ratC Ξ (GeneralLinearGroup.scalar (Fin a) (Units.map (algebraMap (𝓞 E) E).toMonoidHom (u ^ N))) = 1

omit [NumberField E] [IsTotallyComplex E] in
variable (E) in

def emb : Cinf E →+* ((E →+* ℂ) → ℂ) := Pi.ringHom fun τ => coord τ

end Sm

structure IsHolRep {T : Type} {a d : ℕ} (R : GL (Fin a) (T → ℂ) →* Matrix (Fin d) (Fin d) ℂ)
    (D : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop where
  cont : ∀ i j, Continuous fun g => R g i j
  der : ∀ (c : ℝ → GL (Fin a) (T → ℂ)) (Z : Matrix (Fin a) (Fin a) (T → ℂ)), c 0 = 1 →
    (∀ i j t, HasDerivAt (fun s => (c s).val i j t) (Z i j t) 0) → ∀ i j, HasDerivAt (fun s => R (c s) i j) (D Z i j) 0

def EllFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (1 ≤ a → ell E a (oneL E a) = 1) ∧
    (∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), ell E a (toL (X * Y - Y * X)) = 0) ∧
    (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), ell E a (toL (k.1 * X * star k.1)) = ell E a (toL X)) ∧
    ∀ (A : Type) [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (L : Lie E a →ₗ[ℝ] A) (r : ℝ), IsLieHom L → IsLieHom (shift L r)

def FrameEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (n : ℕ) (e : Fin n → Herm E a), IsFrame e

def FrameAd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (N : Type) [AddCommGroup N] [Module ℝ N]
    (β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] N) (k : Kinf E a), ∑ j, β (adHerm k (e j)) (adHerm k (e j)) = ∑ j, β (e j) (e j)

def FrameBr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (N : Type) [AddCommGroup N] [Module ℝ N],
    (∀ (β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] N) (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z),
      ∑ j, β (brH Z hZ (e j)) (e j) + ∑ j, β (e j) (brH Z hZ (e j)) = 0) ∧
    ∀ (β : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Herm E a →ₗ[ℝ] N) (X : Herm E a)
      (h : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1)),
      ∑ j, β (X.1 * (e j).1 - (e j).1 * X.1) (e j) = -∑ j, β (Complex.I • (e j).1) (brH _ (h j) X)

def CasComm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (A : Type) [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (L : Lie E a →ₗ[ℝ] A), IsLieHom L → ∀ X, Commute (cas L e) (L X)

def CasPi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (π : CuspSub E a) (r : ℝ), ∃ c : ℂ, ∀ φ ∈ π.V, cas (shift (lie E a) r) e φ = c • φ

def CasXi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (Ξ : AlgRep E a) (r : ℝ), ∃ c : ℂ, cas (shift Ξ.dmat r) e = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def CasTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), ∃ c : ℂ, ∀ m,
    (cas (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (shift (lieB π Ξ) (-r)) e - cas (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (shift (lieA π Ξ) r) e) m = c • m

def KugaZero : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M), (∀ X Y, Commute (A X) (B Y)) →
    ∀ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, InfEq (A + B) ω → ∀ X, del (B - A) e (dCo (A + B) ω) X = (cas B e - cas A e) (ω X)

def KugaSucc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M), IsLieHom A → IsLieHom B →
    (∀ X Y, Commute (A X) (B Y)) → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), InfEq (A + B) ω → ∀ X,
      dCo (A + B) (del (B - A) e ω) X + del (B - A) e (dCo (A + B) ω) X = (cas B e - cas A e) (ω X)

def DelCochain : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
    (∀ (k : Kinf E a) (X : Herm E a), κ k * L (toL X.1) = L (toL (adHerm k X).1) * κ k) →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), IsCochain κ ω → IsCochain κ (del L e ω)

def IpAdj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L L' : Lie E a →ₗ[ℝ] Module.End ℂ M) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (N : Submodule ℂ M),
    (∀ X : Herm E a, ∀ x ∈ N, ∀ y ∈ N, H x (L (toL X.1) y) = H (L' (toL X.1) x) y) →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) (η : Herm E a [⋀^Fin q]→ₗ[ℝ] M), (∀ X, ω X ∈ N) → (∀ X, η X ∈ N) →
      ip e H ω (dCo L η) = ((q : ℂ) + 1) * ip e H (del L' e ω) η

def IpDef : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (N : Submodule ℂ M), IsPos H N → ∀ q : ℕ,
    (∀ ω η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, ip e H η ω = starRingEnd ℂ (ip e H ω η)) ∧
    ∀ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M, (∀ X, ω X ∈ N) → 0 ≤ (ip e H ω ω).re ∧ (ip e H ω ω = 0 → ω = 0)

def CasZero : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (A B : Lie E a →ₗ[ℝ] Module.End ℂ M),
    IsLieHom A → IsLieHom B → (∀ X Y, Commute (A X) (B Y)) →
    (∀ (k : Kinf E a) (X : Herm E a), κ k * (B - A) (toL X.1) = (B - A) (toL (adHerm k X).1) * κ k) →
    (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq (A + B) ω) →
    ∀ c : ℂ, (∀ m, (cas B e - cas A e) m = c • m) → HasCohomology κ (A + B) → c = 0

def AbsHarm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (A B : Lie E a →ₗ[ℝ] Module.End ℂ M),
    IsLieHom A → IsLieHom B → (∀ X Y, Commute (A X) (B Y)) → cas B e = cas A e →
    ∀ H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsPos H ⊤ → (∀ (X : Herm E a) x y, H x ((A + B) (toL X.1) y) = H ((B - A) (toL X.1) x) y) →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), InfEq (A + B) ω → dCo (A + B) ω = 0 ∧ Coclosed (B - A) e ω

def HolExt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (f : GL (Fin a) (Cinf E) → ℂ), f ∈ regFun E a → ∃ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ,
    DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} ∧ ∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = f y

def ExpGenPi : Prop :=
  ∀ (T : Type) [Fintype T] (a : ℕ) (H : Submonoid (GL (Fin a) (T → ℂ))),
    (∀ (X : Matrix (Fin a) (Fin a) (T → ℂ)) (y : GL (Fin a) (T → ℂ)), y.val = NormedSpace.exp X → y ∈ H) → ∀ y, y ∈ H

def HolIdExp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ), DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
    (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) →
    ∀ X : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ), Φ (fun i j => NormedSpace.exp X i j) = 0

def HolId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ), DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
    (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) →
    ∀ g : GL (Fin a) ((E →+* ℂ) → ℂ), Φ (fun i j => g.val i j) = 0

def CxGrp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), ∃ (R : GL (Fin a) ((E →+* ℂ) → ℂ) →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)
    (Φ : Fin Ξ.d → Fin Ξ.d → (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ),
    (∀ k l, DifferentiableOn ℂ (Φ k l) {x | IsUnit (Matrix.of x)}) ∧ (∀ g k l, R g k l = Φ k l (fun i j => g.val i j)) ∧
    ∀ y, R (GeneralLinearGroup.map (emb E) y) = Ξ.mat y

def CxExt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), ∃ (R : GL (Fin a) ((E →+* ℂ) → ℂ) →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)
    (D : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ) →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsHolRep R D ∧
    ∀ X : Matrix (Fin a) (Fin a) (Cinf E), D (X.map (emb E)) = Ξ.dmat (toL X)

def AvgPos : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (d : ℕ)
    (ρ : K →* Matrix (Fin d) (Fin d) ℂ), (∀ i j, Continuous fun k => ρ k i j) →
    ∃ G : Matrix (Fin d) (Fin d) ℂ, G.PosDef ∧ ∀ k, (ρ k)ᴴ * G * ρ k = G

def AdmAbs : Prop :=
  ∀ (T : Type) [Fintype T] (a d : ℕ) (R : GL (Fin a) (T → ℂ) →* Matrix (Fin d) (Fin d) ℂ)
    (D : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ), IsHolRep R D →
    ∃ G : Matrix (Fin d) (Fin d) ℂ, G.PosDef ∧ ∀ Z, (D Z)ᴴ * G = G * D (star Z)

def AdmEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), ∃ G, IsAdm Ξ G

def XiSchur : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), IsLieHom Ξ.dmat ∧
    ∀ P : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ, (∀ X, Commute P (Ξ.dmat X)) → ∃ c : ℂ, P = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def OneReal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), ∃ r, HasOne Ξ r

def AInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) g,
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g

def TwEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ r : ℝ, ∃ χ : HChar E, IsTw (a := a) r χ

def SqUniq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (r : ℝ) (χ : HChar E), IsTw (a := a) r χ → ∀ φ : Sm E a, lie E a (oneL E a) φ = -(r : ℂ) • φ →
    IsSqIntMod φ → GlobalTheory.UnitaryBC.IsSqInt (mulChi a χ φ).1

def SqLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : ℝ), (∀ (X : Lie E a) (φ : Sm E a), IsSq r φ → IsSq r (lie E a X φ)) ∧
  ∀ (X : Lie E a), ∀ φ ∈ sqSub E a r, lie E a X φ ∈ sqSub E a r

def DerivativeRightTranslateL2 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ)
    (hφ : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ φ) (hψ : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous ψ → Continuous c → c 0 = 1 →
    (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) →
    HasDerivAt (fun s => GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s) hφ.toL2) hψ.toL2 0

def OneParam : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Lie E a), ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
    Continuous (fun t => infGL E a (c t)) ∧ HasDerivAt (fun t => toL (c t).val) X 0 ∧
    ∀ t : ℝ, (c t).val = NormedSpace.exp (t • Matrix.of X)

open scoped GlobalTheory.CuspRep.CuspidalL2GL in

def SkewLieActionL2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (X : Lie E a) (φ ψ : Sm E a),
    IsOpen {k | act (.fin k) φ = φ} → IsOpen {k | act (.fin k) ψ = ψ} →
    ∀ (h1 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (h2 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
      (h3 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
      (h4 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1),
      inner ℂ h3.toL2 h2.toL2 + inner ℂ h1.toL2 h4.toL2 = 0

open scoped GlobalTheory.CuspRep.CuspidalL2GL in

def SqMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (r : ℝ) (χ : HChar E), IsTw (a := a) r χ →
    ∀ φ ∈ sqSub E a r, IsOpen {k | act (.fin k) (mulChi a χ φ) = mulChi a χ φ} ∧
      GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (mulChi a χ φ).1

def PetEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ r : ℝ, ∃ H, IsPet (E := E) (a := a) r H

def CuspSq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (r : ℝ), (∀ φ ∈ π.V, lie E a (oneL E a) φ = -(r : ℂ) • φ) → ∀ φ ∈ π.V, IsSq r φ

def TformPos : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (d : ℕ) (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (N : Submodule ℂ W)
    (G : Matrix (Fin d) (Fin d) ℂ), IsPos H N → G.PosDef → IsPos (tform H G) (tens d N)

def TformAdj : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (d : ℕ) (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (N : Submodule ℂ W)
    (G P Q : Matrix (Fin d) (Fin d) ℂ) (S T : Module.End ℂ W),
    (Pᴴ * G = G * Q → ∀ x y, tform H G x ((Matrix.toLin' Q).lTensor W y) = tform H G ((Matrix.toLin' P).lTensor W x) y) ∧
    ((∀ φ ∈ N, ∀ ψ ∈ N, H φ (S ψ) = H (T φ) ψ) → ∀ x ∈ tens d N, ∀ y ∈ tens d N,
      tform H G x (S.rTensor _ y) = tform H G (T.rTensor _ x) y)

def SmForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (H : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsPet r H → IsAdm Ξ G →
    ∀ X : Herm E a, ∀ x ∈ tens Ξ.d (sqSub E a r), ∀ y ∈ tens Ξ.d (sqSub E a r),
      tform H G x (smLie Ξ (toL X.1) y) = tform H G (smAdj Ξ r (toL X.1) x) y

def OneEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → IsCohFor π Ξ →
    ∀ φ ∈ π.V, lie E a (oneL E a) φ = -(r : ℂ) • φ

def InclFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), Function.Injective (incl π Ξ) ∧
    (∀ i m, cmp i (incl π Ξ m) = (cmp i m).1) ∧ (∀ k m, incl π Ξ (tensorK π Ξ k m) = smK Ξ k (incl π Ξ m)) ∧
    (∀ X m, incl π Ξ (tensorLie π Ξ X m) = smLie Ξ X (incl π Ξ m)) ∧
    ∀ X m, incl π Ξ (piAdj π Ξ r X m) = smAdj Ξ r X (incl π Ξ m)

def PiForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), (∀ φ ∈ π.V, lie E a (oneL E a) φ = -(r : ℂ) • φ) →
    ∃ H : (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) →ₗ⋆[ℂ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) →ₗ[ℂ] ℂ, IsPos H ⊤ ∧
      ∀ (X : Herm E a) x y, H x (tensorLie π Ξ (toL X.1) y) = H (piAdj π Ξ r (toL X.1) x) y

def PiHarm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → IsCohFor π Ξ →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), IsCochain (tensorK π Ξ) ω →
      dCo (tensorLie π Ξ) ω = 0 ∧ Coclosed (piAdj π Ξ r) e ω

def BasicEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M), HasCohomology κ L →
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), ω ≠ 0 ∧ IsCochain κ ω ∧ IsBasic ω

def AvgProj : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (U : Subgroup G), IsCompact (U : Set G) → (∀ v, IsOpen {g | ρ g v = v}) →
    ∃ p : Module.End ℂ V, (∀ v, ∀ u ∈ U, ρ u (p v) = p v) ∧ (∀ v, (∀ u ∈ U, ρ u v = v) → p v = v) ∧
      ∀ T : Module.End ℂ V, (∀ u ∈ U, Commute T (ρ u)) → Commute T p

def LevelOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ π : CuspSub E a, HasFixed π.finPart U →
    ∀ φ : π.V, φ ≠ 0 → ∃ T : Module.End ℂ π.V, T φ ≠ 0 ∧ (∀ k, Commute T (π.op (.cpt k))) ∧
      ∀ ψ, ∀ u ∈ U, π.op (.fin u) (T ψ) = T ψ

def LevelCo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (π : CuspSub E a) (Ξ : AlgRep E a), IsCohFor π Ξ → HasFixed π.finPart U →
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), ω ≠ 0 ∧ IsCochain (tensorK π Ξ) ω ∧ IsBasic ω ∧
      ∀ X i, ∀ u ∈ U, π.op (.fin u) (cmp i (ω X)) = cmp i (ω X)

def HarmEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → IsCohFor π Ξ → HasFixed π.finPart U →
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d π.V

def CentreLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
    (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → dCo L ω = 0 ∧ InfEq L ω) →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → ∀ (z : Cinf E) X, L (toL (Matrix.scalar (Fin a) z)) (ω X) = 0

def Flow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (m : (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)),
    y.val = NormedSpace.exp X → smLie Ξ (toL X) m = 0 → ∀ g,
      Ξ.mat y *ᵥ (fun i => (cmp i m).1 (g * infGL E a y)) = fun i => (cmp i m).1 g

def UnitPow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ N : ℕ, 0 < N ∧ ∀ u : (𝓞 E)ˣ, GeneralLinearGroup.map (algebraMap E (Af E))
      (GeneralLinearGroup.scalar (Fin a) (Units.map (algebraMap (𝓞 E) E).toMonoidHom (u ^ N))) ∈ U

def UnitAbs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (m : (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), m ≠ 0 →
    (∀ i γ g, (cmp i m).1 (ratGL E a γ * g) = (cmp i m).1 g) → (∀ i, ∀ u ∈ U, act (.fin u) (cmp i m) = cmp i m) →
    (∀ z : Cinf E, smLie Ξ (toL (Matrix.scalar (Fin a) z)) m = 0) → UnitsTriv Ξ

def UnitTriv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (π : CuspSub E a) (Ξ : AlgRep E a), IsCohFor π Ξ → HasFixed π.finPart U →
    UnitsTriv Ξ

def SmallLev : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∃ U' ≤ U, IsOpen (U' : Set (GL (Fin a) (Af E))) ∧
      IsCompact (U' : Set (GL (Fin a) (Af E))) ∧ ∀ (γ : GL (Fin a) E) (g : GL (Fin a) (Af E)),
        g⁻¹ * GeneralLinearGroup.map (algebraMap E (Af E)) γ * g ∈ U' → IsOfFinOrder γ → γ = 1

def Orth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → ∀ (q : ℕ) (η : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))),
      IsRelCochain Ξ (IsCuspFn U Ξ) η → IsHarm U Ξ r e (dCo (smLie Ξ) η) → dCo (smLie Ξ) η = 0

def HarmLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (r : ℝ) (q : ℕ),
    (∀ (s : ℕ) (ω : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (c : Fin s → ℂ), (∀ i, IsHarm U Ξ r e (ω i)) →
      IsHarm U Ξ r e (∑ i, c i • ω i)) ∧
    ∀ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), (IsHarm U Ξ r e ω → IsRelCochain Ξ (IsLevelFn U Ξ) ω) ∧
      ∀ U' ≤ U, (IsHarm U Ξ r e ω → IsHarm U' Ξ r e ω) ∧
        (IsRelCochain Ξ (IsLevelFn U Ξ) ω → IsRelCochain Ξ (IsLevelFn U' Ξ) ω)

def NoExact : Prop :=
  BorelC → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → UnitsTriv Ξ →
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), IsHarm U Ξ r e ω → IsRelExact U Ξ ω → ω = 0

def IndepAbs : Prop :=
  ∀ (O W : Type) [AddCommGroup W] [Module ℂ W] (A : O → Module.End ℂ W) (s : ℕ) (V : Fin s → Submodule ℂ W)
    (h : ∀ i o, ∀ x ∈ V i, A o x ∈ V i), (∀ i, ∀ N ≤ V i, (∀ o, ∀ x ∈ N, A o x ∈ N) → N = ⊥ ∨ N = V i) →
    (∀ i j, i ≠ j → ¬ ∃ T : V i ≃ₗ[ℂ] V j, ∀ o x, T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x)) →
    iSupIndep V

def Indep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (d q s : ℕ) (π : Fin s → CuspSub E a), (∀ i j, (π i).Iso (π j) → i = j) →
    ∀ ω : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ)), (∀ i, ω i ≠ 0) → (∀ i X, ω i X ∈ tens d (π i).V) →
      ∀ c : Fin s → ℂ, ∑ i, c i • ω i = 0 → c = 0

def Count : Prop :=
  ∀ (X : Type) (S : Finset X) (deg : X → ℕ) (κ : ℕ → Cardinal.{0}),
    (∀ (q s : ℕ) (f : Fin s → X), Function.Injective f → (∀ i, f i ∈ S ∧ deg (f i) = q) → (s : Cardinal) ≤ κ q) →
    (S.card : Cardinal) ≤ Cardinal.sum κ

theorem borelInjC_of_steps (hD : DeRhamInj) (h1 : FrameEx) (h2 : OneReal) (h3 : HarmEx) (h4 : UnitTriv) (h5 : HarmLin)
    (h6 : NoExact) (h7 : Indep) (h8 : Count) (hB : BorelC) : UpperTheory.V.Published.BorelInjC := by
  intro E _ _ _ a ha U hUo hUc Ξ S hS hC
  classical
  obtain ⟨n, e, he⟩ := h1 E a
  obtain ⟨r, hr⟩ := h2 E a Ξ
  have hex : ∀ π : CuspSub E a, ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))),
      π ∈ S → ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d π.V := fun π => by
    by_cases h : π ∈ S
    · obtain ⟨q, ω, hω⟩ := h3 E a ha n e he U hUc π Ξ r hr (hC π h).1 (hC π h).2
      exact ⟨q, ω, fun _ => hω⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose deg w hw using hex
  refine h8 _ S deg _ fun q s f hf hq => ?_
  have hex2 : ∀ i, ∃ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)),
      ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d (f i).V := fun i => by
    obtain ⟨hi, rfl⟩ := hq i
    exact ⟨w _, hw _ hi⟩
  choose ω h0 hH hV using hex2
  refine hD E a ha U hUo hUc Ξ q s ω (fun i => ⟨((h5 E a n e U Ξ r q).2 _).1 (hH i), (hH i).closed⟩) fun c hc => ?_
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Subsingleton.elim _ _
  have hi := (hq ⟨0, hs⟩).1
  exact h7 E a Ξ.d q s f (fun i j h => hf (hS _ (hq i).1 _ (hq j).1 h)) ω h0 hV c
    (h6 hB E a ha n e he U hUo hUc Ξ r hr (h4 E a ha U hUo hUc _ Ξ (hC _ hi).1 (hC _ hi).2) q _
      ((h5 E a n e U Ξ r q).1 s ω c hH) hc)

end UpperTheory.V.Lit.Bor
