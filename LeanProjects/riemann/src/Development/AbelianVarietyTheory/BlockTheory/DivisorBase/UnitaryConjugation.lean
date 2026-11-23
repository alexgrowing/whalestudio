import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.WeilM
open GlobalTheory.Mem.Th (IsCuspForm)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def flatDet (ξ : (AE D)ˣ →* Circle) (V : HSp D) (g : GA D V) : ℂ := ξ (GlobalTheory.RecDict.exists_isDetRoot D V g).choose

abbrev UB {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) : Type := WeilTensorModels.UA D.sp.cm.sig J

abbrev incM {m n : Type} (J : Matrix m n D.host.E) : Matrix m n (AE D) := WeilTensorModels.incM D.host.F J

theorem mt_gram (V : HSp D) (g : GA D V) : ((mt V g).map (cA D))ᵀ * incM V.gram * mt V g = incM V.gram := g.2

theorem incM_smul {m n : Type} (c : D.host.E) (J : Matrix m n D.host.E) : incM (c • J) = incA D c • incM J := by
  ext a b
  simp only [incM, WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

def conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) (g : GA D V) :
    UB J :=
  ⟨GeneralLinearGroup.map (cA D) (matHom V g), by
    have e : ((mt V g).map (cA D)).map (cA D) = mt V g := Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
    show ((mt V g).map (cA D))ᵀ * incM J * ((mt V g).map (cA D)).map (cA D) = incM J
    rw [e, h, incM_smul, Matrix.mul_smul, Matrix.smul_mul, mt_gram]⟩

theorem continuous_conj (D : D7) : Continuous (cA D) := by
  let f : AE D →ₗ[AF D.host.F] AE D :=
    TensorProduct.AlgebraTensorModule.map LinearMap.id D.sp.cm.sig.toLinearMap
  have hf : ⇑(cA D) = ⇑f := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [cA, sigR, f]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hf]
  exact IsModuleTopology.continuous_of_linearMap f

theorem continuous_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    Continuous (conjU V c h) := by
  unfold conjU
  refine Continuous.subtype_mk ?_ _
  have hv : Continuous fun g : GA D V =>
      ((matHom V g : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V =>
      (((matHom V g)⁻¹ : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  rw [Units.continuous_iff]
  exact ⟨hv.matrix_map (continuous_conj D), hi.matrix_map (continuous_conj D)⟩

def blk {R : Type} [Zero R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : Matrix (Fin d) (Fin d) R := reindex e e (fromBlocks A 0 0 B)

theorem blk_mul {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A A' : Matrix (Fin p) (Fin p) R)
    (B B' : Matrix (Fin q) (Fin q) R) : blk e A B * blk e A' B' = blk e (A * A') (B * B') := by
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]

theorem blk_one {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) :
    blk e (1 : Matrix (Fin p) (Fin p) R) 1 = 1 := by
  simp only [blk, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem blk_map {R R' : Type} [Zero R] [Zero R'] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) {f : R → R'} (h : f 0 = 0) : (blk e A B).map f = blk e (A.map f) (B.map f) := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [Matrix.map_zero _ h]

theorem blk_transpose {R : Type} [Zero R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : (blk e A B)ᵀ = blk e Aᵀ Bᵀ := by
  simp only [blk, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero]

def skewGram (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) : Matrix (Fin d) (Fin d) D.host.E :=
  D.host.xi0 • blk e A.gramᵀ B.gramᵀ

def blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (x : GA D A × GA D B) : UB J :=
  ⟨⟨blk e (mt A x.1) (mt B x.2), blk e (mt A x.1⁻¹) (mt B x.2⁻¹),
    by simp only [Formalism.L2.Theta.mt, blk_mul, map_inv, Units.mul_inv, blk_one],
    by simp only [Formalism.L2.Theta.mt, blk_mul, map_inv, Units.inv_mul, blk_one]⟩, by
    have k : ∀ (V : HSp D) (g : GA D V), (mt V g)ᵀ * incM V.gramᵀ * (mt V g).map (cA D) = incM V.gramᵀ := fun V g => by
      have := congrArg transpose (mt_gram V g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have e1 : incM (blk e A.gramᵀ B.gramᵀ) = blk e (incM A.gramᵀ) (incM B.gramᵀ) := blk_map _ _ _ (map_zero _)
    show (blk e (mt A x.1) (mt B x.2))ᵀ * incM J * (blk e (mt A x.1) (mt B x.2)).map (cA D) = incM J
    rw [h, skewGram, incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1, blk_map _ _ _ (map_zero _), blk_transpose, blk_mul,
      blk_mul, k, k]⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def routeA (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.down t (i + 1) j) (.one (.right i (j + 1)))

def routeB (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.right i j) (.one (.down t i j))

variable (W : G.Weil) (M : Vol G)

def alg (a : Arrow T) : Submodule ℂ (Sch G a) :=
  Submodule.span ℂ {φ | ∃ f P, IsThetaFunO W.ψ (G.pS a.pair) (G.pT a.pair) f ∧
    (∀ τ, IsFockVacAt (heisO W.ψ (G.pS a.pair) (G.pT a.pair)) W.θ τ
      (cplxO (G.cartS W.cart a.pair τ) (G.onT W.cart a.pair τ)) f) ∧ φ = W.fock a.pair f P}

def IsAlg {X Y : Node} {p : Path T X Y} (τ : TotT G p) : Prop :=
  ∀ d ∈ τ.support, Path.Fam.All (fun a f => f ∈ alg W a) d

variable (t : T) (i j : ℕ)

variable (G) in

abbrev spV : HSp D := G.V (.grid i (j + 1))

variable (G) in

abbrev spW : HSp D := G.V (.grid (i + 1) (j + 1))

variable (G) in

abbrev spW₁ : HSp D := G.V (.grid i j)

variable (G) in

abbrev spV₁ : HSp D := G.V (.grid (i + 1) j)

variable (G) in

def eps : ℕ := (spW₁ G i j).rank % 2

variable (G) in

def alpha : (AE D)ˣ →* Circle := L.mu t (j + 1) * L.eta ^ eps G i j

variable (G) in

def beta : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - i) * L.eta ^ eps G i j

variable (G) in

def xiV (g : GA D (spV G i j)) : ℂ := flatDet (L.eta ^ (2 * eps G i j))⁻¹ _ g

variable (G) in

def xiV₁ (g : GA D (spV₁ G i j)) : ℂ := flatDet (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ _ g

structure LiftsCusp (F : Fn G (.grid i (j + 1))) : Prop where

  x : ∀ f ∈ alg W (.right i (j + 1)), IsCuspForm W.θ (spW G i j) (liftA W M (.right i (j + 1)) f F)

  th : ∀ f ∈ alg W (.down t i j), IsCuspForm W.θ (spW₁ G i j) (liftA W M (.down t i j) f F)

  thx : ∀ f ∈ alg W (.right i (j + 1)), ∀ f' ∈ alg W (.down t (i + 1) j),
    IsCuspForm W.θ (spV₁ G i j) (liftA W M (.down t (i + 1) j) f' (liftA W M (.right i (j + 1)) f F))

  xth : ∀ f ∈ alg W (.down t i j), ∀ f' ∈ alg W (.right i j),
    IsCuspForm W.θ (spV₁ G i j) (liftA W M (.right i j) f' (liftA W M (.down t i j) f F))

variable (G) in

abbrev Num : Type := Fin (spV G i j).rank ⊕ Fin (spV₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)

variable (G) in

abbrev Geo : Type := WeilTensorModels.Geo D.sp.cm.sig (spW G i j).rank (spW₁ G i j).rank

structure IsTripleOf (e : Num G i j) (B : WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : B.ψ = W.ψ

  JW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram

  JWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e

  cart : ∀ w, ∃ τ, (∀ x, (B.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
    Γ.V'.θ w = -W.cart (.grid i j) τ ∧
    Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj

  α : X.α = alpha G t i j

  β : X.β = beta G i j

  μW : Γ.M.μ = (M.ν (.grid (i + 1) (j + 1))).map (conjU _ 1 JW)

  μW₁ : Γ.M'.μ = (M.ν (.grid i j)).map (conjU _ (-1) JW₁)

variable {i j}

def mulG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : Matrix (Fin n) (Fin S.rank) (AE D) :=
  HMul.hMul x (incM S.gram)

def colV {n : ℕ} (e : Num G i j) (u : Matrix (Fin n) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin n) (Fin (spV G i j).rank) (AE D) := u.submatrix id fun k => e (.inl k)

def adjV₁ {n : ℕ} (e : Num G i j) (u : Matrix (Fin n) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin n) (Fin (spV₁ G i j).rank) (AE D) :=
  -mulG (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))

variable {t}

def boxA (e : Num G i j) (d : PureT G (routeA t i j))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : ℂ :=
  (d.1.2 : Sch G (.right i (j + 1))) (mulG (negSp (spW G i j)) (colV e u)ᵀ) *
    (d.2 : Sch G (.down t (i + 1) j)) (adjV₁ e u)

def boxB (e : Num G i j) (d : PureT G (routeB t i j))
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : ℂ :=
  (d.1.2 : Sch G (.down t i j)) (mulG (spW₁ G i j) (colV e u)ᵀ) * (d.2 : Sch G (.right i j)) (adjV₁ e u)

def IsDatumA (e : Num G i j) (Γ : Geo G i j) (τ : TotT G (routeA t i j))
    (Φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → AF D.host.F) → ℂ) : Prop :=
  Φ ∈ schA D.host.F _ ∧ ∀ u, thetaSum D.host.F (Γ.M.co.rho W.ψ u Φ) = τ.sum fun d c => c * boxA e d u

def IsDatumB (e : Num G i j) (Γ : Geo G i j) (τ : TotT G (routeB t i j))
    (Φ : (Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → AF D.host.F) → ℂ) : Prop :=
  Φ ∈ schA D.host.F _ ∧ ∀ u, thetaSum D.host.F (Γ.M'.co.rho W.ψ u Φ) = τ.sum fun d c => c * boxB e d u

variable (i j) in

def quotMeas : Measure (GA D (spV G i j) × GA D (spV₁ G i j)) :=
  ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) j)).restrict (M.fd (.grid (i + 1) j)))

variable (t) in

def ppInt (F : Fn G (.grid i (j + 1))) (F₁ : Fn G (.grid (i + 1) j)) (f : GA D (spV G i j) × GA D (spV₁ G i j) → ℂ)
    (x : GA D (spV G i j) × GA D (spV₁ G i j)) : ℂ :=
  f x * (xiV G i j x.1 * F x.1) * conj (conj (xiV₁ G t i j x.2) * F₁ x.2)

variable (t) in

def PairEq (F : Fn G (.grid i (j + 1))) (F₁ φ : Fn G (.grid (i + 1) j)) (f : GA D (spV G i j) × GA D (spV₁ G i j) → ℂ) :
    Prop :=
  IntegrableOn (fun g => φ g * conj (F₁ g)) (M.fd (.grid (i + 1) j)) (M.ν (.grid (i + 1) j)) ∧
    Integrable (ppInt t F F₁ f) (quotMeas M i j) ∧
    ∫ g in M.fd (.grid (i + 1) j), φ g * conj (F₁ g) ∂M.ν (.grid (i + 1) j) = ∫ x, ppInt t F F₁ f x ∂quotMeas M i j

def SquareFubini : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T) (sc : Consts) (G : GridData L sc) (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ),
    L.Is μ0 → M.Is t → i + 1 ≤ D.R.m → j + 1 ≤ D.R.m →
    ∀ (e : Num G i j) B (Γ : Geo G i j) X om om', ∀ h : IsTripleOf W M t i j e B Γ X, WeilTensorModels.IsTriple B Γ X om om' →
    ∀ F F₁, IsCuspForm W.θ (spV G i j) F → IsCuspForm W.θ (spV₁ G i j) F₁ →
      (∀ τ Φ, IsAlg W τ → IsDatumA W e Γ τ Φ → TotConv W M (routeA t i j) τ F ∧ Γ.M.Conv om Φ ∧
        PairEq M t F F₁ (liftT W M (routeA t i j) τ F) fun x => Γ.M.I om Φ (blkU _ _ e h.JWW x)) ∧
      ∀ τ Φ, IsAlg W τ → IsDatumB W e Γ τ Φ → Φ ∈ Γ.M'.So B.ψ B.τ₁ →
        (τ.support.card ≤ 1 → TotConv W M (routeB t i j) τ F) ∧ Γ.M'.Conv om' Φ ∧
        (TotConv W M (routeB t i j) τ F →
          PairEq M t F F₁ (liftT W M (routeB t i j) τ F) fun x => Γ.M'.I om' Φ (blkU _ _ e h.JWW x))

def SquareCommutes : Prop :=
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T) (sc : Consts) (G : GridData L sc) (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ),
    L.Is μ0 → M.Is t → i + 1 ≤ D.R.m → j + 1 ≤ D.R.m →
    ∀ (e : Num G i j) B (Γ : Geo G i j) X om om' R Rf, IsTripleOf W M t i j e B Γ X → WeilTensorModels.IsMatched B Γ X om om' R Rf →
    ∀ c, WeilTensorModels.IsConst B Γ X om om' R Rf c →
    ∀ τA τB ΦA ΦB, IsAlg W τA → IsAlg W τB → IsDatumA W e Γ τA ΦA → IsDatumB W e Γ τB ΦB →
      WeilTensorModels.PolMatch B Γ X R Rf ΦA ΦB →
    ∀ F, IsCuspForm W.θ (spV G i j) F → LiftsCusp W M t i j F →
      TotConv W M (routeA t i j) τA F ∧ TotConv W M (routeB t i j) τB F ∧
        liftT W M (routeA t i j) τA F = c • liftT W M (routeB t i j) τB F

def TwoRoutes : Prop := SquareFubini ∧ SquareCommutes

example (f : Sch G (.right i (j + 1))) (f' : Sch G (.down t (i + 1) j)) (F : Fn G (.grid i (j + 1))) :
    liftP W M (routeA t i j) (((), f), f') F = liftA W M (.down t (i + 1) j) f' (liftA W M (.right i (j + 1)) f F) := rfl

theorem nonempty_num {μ0 : T} (hL : L.Is μ0) (hi : i + 1 ≤ D.R.m) (hj : j + 1 ≤ D.R.m) : Nonempty (Num G i j) := by
  have hr : ∀ X : Node, X.InRange D.R.m → (G.V X).rank = X.rank D := fun X hX => (node_isV G hL hX).rank
  have h1 := hr (.grid i (j + 1)) (by simp only [Node.InRange]; constructor <;> omega)
  have h2 := hr (.grid (i + 1) j) (by simp only [Node.InRange]; constructor <;> omega)
  have h3 := hr (.grid (i + 1) (j + 1)) (by simp only [Node.InRange]; constructor <;> omega)
  have h4 := hr (.grid i j) (by simp only [Node.InRange]; constructor <;> omega)
  have key : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    rw [show (spV G i j).rank = _ from h1, show (spV₁ G i j).rank = _ from h2,
      show (spW G i j).rank = _ from h3, show (spW₁ G i j).rank = _ from h4]
    simp only [Node.rank, rankV]
    ring
  exact ⟨finSumFinEquiv.trans (finCongr key)⟩

example : alpha G t i j / beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

end
