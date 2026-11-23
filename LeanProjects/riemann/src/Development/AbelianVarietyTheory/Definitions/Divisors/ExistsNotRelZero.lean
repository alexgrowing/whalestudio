import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

abbrev routeBig (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.down t (i + 1) j) (Path.one (.right i (j + 1)))

abbrev routeSmall (t : T) (i j : ℕ) : Path T (.grid i (j + 1)) (.grid (i + 1) j) :=
  .snoc (.right i j) (Path.one (.down t i j))

section Kernels

variable (W : G.Weil) {t : T} {i j : ℕ}

def kerBig (τ : TotT G (routeBig t i j)) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    Fn G (.grid (i + 1) (j + 1)) := fun u =>
  τ.sum fun d c => c * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁)

def kerSmall (τ : TotT G (routeSmall t i j)) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    Fn G (.grid i j) := fun u =>
  τ.sum fun d c => c * (W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁)

end Kernels

def translates {H : Type} [Mul H] (z : H →₀ ℂ) (φ : H → ℂ) : H → ℂ := fun u => z.sum fun k c => c * φ (u * k)

def zdeg {H : Type} (z : H →₀ ℂ) : ℂ := z.sum fun _ c => c

theorem translates_one {H : Type} [MulOneClass H] (φ : H → ℂ) :
    translates (Finsupp.single 1 1) φ = φ ∧ zdeg (Finsupp.single (1 : H) 1) = 1 :=
  ⟨funext fun u => by simp [translates], by simp [zdeg]⟩

variable (G) in

abbrev PolRoute (X M Y : Node) : Type := PolF D (G.V X).rank (G.V M).rank ⊗[ℂ] PolF D (G.V M).rank (G.V Y).rank

def toTens {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] :
    ((Unit × P) × Q →₀ ℂ) →ₗ[ℂ] P ⊗[ℂ] Q := Finsupp.linearCombination ℂ fun d => d.1.2 ⊗ₜ d.2

theorem toTens_surjective {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] :
    Function.Surjective (toTens (P := P) (Q := Q)) := fun x => by
  induction x with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q => exact ⟨Finsupp.single (((), p), q) 1, by simp [toTens]⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

structure RealMatch (W : G.Weil) where

  vX : ∀ i j, Sch G (.right i j)

  vT : ∀ i j, WO (G.V (.grid i j)) (G.V (.grid i (j + 1))) → ℂ

  vX_is : ∀ i j, i < D.R.m → j ≤ D.R.m → W.IsVac (.chi i j) (vX i j)

  vT_is : ∀ t i j, i ≤ D.R.m → j < D.R.m → W.IsVac (.mu t i j) (vT i j)

  vX_row : ∀ i, vX i 0 = W.vac i

  rel : ∀ i j, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))

  onto_big : ∀ i j a, ∃ b, (a, b) ∈ rel i j

  onto_small : ∀ i j b, ∃ a, (a, b) ∈ rel i j

  proper : ∀ i j, rel i j ≠ ⊤

namespace RealMatch

variable {W : G.Weil} (ρ : RealMatch W)

def Matched {t : T} {i j : ℕ} (a : PolT G (routeBig t i j) →₀ ℂ) (b : PolT G (routeSmall t i j) →₀ ℂ) : Prop :=
  (toTens a, toTens b) ∈ ρ.rel i j

theorem exists_matched (i j : ℕ) (b : (Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid i j)).rank) ×
    PolF D (G.V (.grid i j)).rank (G.V (.grid (i + 1) j)).rank →₀ ℂ) :
    ∃ a : (Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) ×
      PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank →₀ ℂ, ∀ t : T, ρ.Matched (t := t) (i := i) (j := j) a b := by
  obtain ⟨x, hx⟩ := ρ.onto_small i j (toTens b)
  obtain ⟨a, rfl⟩ := toTens_surjective x
  exact ⟨a, fun _ => hx⟩

theorem exists_not_rel_zero (i j : ℕ) : ∃ a, (a, 0) ∉ ρ.rel i j := by
  by_contra! h
  refine ρ.proper i j (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨a, ha⟩ := ρ.onto_small i j x.2
  simpa using add_mem ha (h (x.1 - a))

end RealMatch

def RealMatch.Over {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    {G : GridData R.toLevCh sc} {W : G.Weil} (ρ : RealMatch W) : Prop :=
  (∀ k, k + 1 < D.R.m → HEq (ρ.vT 0 k) (R.vac k)) ∧ ∀ k, k + 1 = D.R.m → HEq (ρ.vT 0 k) R.vacX

theorem exists_isVac (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) {p : Pair T} (hp : p.InRange D.R.m) : ∃ f, W.IsVac p f := by
  have a := node_isV G hL hp
  have b := node_isV G hL hp.small
  have ca := W.cart_is _ hp
  have cb := W.cart_is _ hp.small
  cases p
  all_goals first
    | exact GlobalTheory.VacuumO.vacExists D _ _ W.ψ_std W.θ_is _ _ _ _ b.sigOK a.sigOK cb ca _ _ b.sd a.sd
    | exact GlobalTheory.VacuumO.vacExists D _ _ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg a.sigOK) b.sigOK
        (fun τ => isCartanInv_neg (ca τ)) cb _ _ (isSelfDualC_neg a.sd) b.sd

theorem exists_rel (X M M' Y : Node) : ∃ R : Submodule ℂ (PolRoute G X M Y × PolRoute G X M' Y),
    (∀ a, ∃ b, (a, b) ∈ R) ∧ (∀ b, ∃ a, (a, b) ∈ R) ∧ R ≠ ⊤ := by
  have H : ∀ M, ∃ (f : PolRoute G X M Y →ₗ[ℂ] ℂ) (x : PolRoute G X M Y), f x = 1 := fun M =>
    ⟨LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map (MvPolynomial.lcoeff ℂ 0) (MvPolynomial.lcoeff ℂ 0), 1 ⊗ₜ 1, by simp⟩
  obtain ⟨f, x, hx⟩ := H M
  obtain ⟨g, y, hy⟩ := H M'
  refine ⟨LinearMap.eqLocus (f ∘ₗ LinearMap.fst _ _ _) (g ∘ₗ LinearMap.snd _ _ _), fun a => ⟨f a • y, by simp [hy]⟩,
    fun b => ⟨g b • x, by simp [hx]⟩, fun h => ?_⟩
  simpa [hx] using h.ge (Submodule.mem_top (x := (x, 0)))

theorem nonempty_realMatch (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) : Nonempty (RealMatch W) := by
  have h1 : ∀ i j, ∃ f : Sch G (.right i j), (i < D.R.m → j ≤ D.R.m → W.IsVac (.chi i j) f) ∧
      ∀ h : j = 0, f = (by subst h; exact W.vac i) := fun i j => by
    rcases j with _ | j
    · exact ⟨W.vac i, fun hi _ => W.vac_is i hi, fun _ => rfl⟩
    · by_cases h : i < D.R.m ∧ j + 1 ≤ D.R.m
      · obtain ⟨f, hf⟩ := exists_isVac W hL (p := .chi i (j + 1)) h
        exact ⟨f, fun _ _ => hf, fun h => by omega⟩
      · exact ⟨0, fun a b => absurd ⟨a, b⟩ h, fun h => by omega⟩
  have h2 : ∀ i j, ∃ f : Sch G (.down μ₀ i j), i ≤ D.R.m → j < D.R.m → W.IsVac (.mu μ₀ i j) f := fun i j => by
    by_cases h : i ≤ D.R.m ∧ j < D.R.m
    · obtain ⟨f, hf⟩ := exists_isVac W hL (p := .mu μ₀ i j) h
      exact ⟨f, fun _ _ => hf⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
  choose vX h1 using h1
  choose vT h2 using h2
  choose rel h3 using fun i j : ℕ => exists_rel (G := G) (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid i j) (.grid (i + 1) j)
  exact ⟨⟨vX, vT, fun i j => (h1 i j).1, fun _ => h2, fun i => (h1 i 0).2 rfl, rel, fun i j => (h3 i j).1,
    fun i j => (h3 i j).2.1, fun i j => (h3 i j).2.2⟩⟩

section Finite

variable (W : G.Weil) (B : Frames G) (t : T)

def IsLocVec (p : Pair T) (e : AE D) (f₀ φ f : WO (G.pS p) (G.pT p) → ℂ) : Prop :=
  IsSBHalf e (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) φ ∧
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ φ f

def HasLocal (e : AE D) {X M Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hM : M.1 ≤ D.R.m ∧ M.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (P₁ : (φ f : Mx D (G.V (.grid X.1 X.2)).rank (G.V (.grid M.1 M.2)).rank → ℂ) → Prop)
    (P₂ : (φ f : Mx D (G.V (.grid M.1 M.2)).rank (G.V (.grid Y.1 Y.2)).rank → ℂ) → Prop)
    (τ : (Unit × (Mx D (G.V (.grid X.1 X.2)).rank (G.V (.grid M.1 M.2)).rank → ℂ)) ×
      (Mx D (G.V (.grid M.1 M.2)).rank (G.V (.grid Y.1 Y.2)).rank → ℂ) →₀ ℂ)
    (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank M)) (Fin ((locGrid G t w).rank X) ⊕ Fin ((locGrid G t w).rank Y)) (Kw w) → ℂ) :
    Prop :=
  ∃ (φ₁ : _ → _) (φ₂ : _ → _), (∀ d ∈ τ.support, P₁ (φ₁ d) d.1.2 ∧ P₂ (φ₂ d) d.2) ∧
    ∀ x₁ x₂, IsHalf e x₁ → IsHalf e x₂ → (τ.sum fun d c => c * (φ₁ d x₁ * φ₂ d x₂)) =
      ∏ w ∈ locPl G t, Φ w (fromCols (B.coord t w hX hM (x₁.map fun a => cpt w (toEAf D a)))
        (B.coord t w hM hY (x₂.map fun a => cpt w (toEAf D a)))ᵀ)

def flipAt (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  squareFlip (haarVol ((givenLevel G t w (i, j)).map invT)) (stdSplit ((locGrid G t w).rank_square i j)) (psiAt W w)
    ((locGrid G t w).nu i j) (unifAt w) n (Assignment.one.block _ _) Φ

theorem flipTensor_eq (i j : ℕ) (w : Pl D.host.E) (n : ℕ) (S : (locGrid G t w).Args → ℂ) (x : (locGrid G t w).Args) :
    (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) n i j (givenLevel G t w) S x =
      flipAt W t i j w n ((locGrid G t w).sliceB i j S x) ((locGrid G t w).joinA i j x) := rfl

variable {W} (ρ : RealMatch W) (i j : Fin D.R.m)

def HasFlip (n : Pl D.host.E → ℕ)
    (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧
    HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ' Φ ∧
    HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ
      fun w => flipAt W t i j w (n w) (Φ w)

def IsMatched (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) : Prop :=
  ∃ a b τ τ' n Φ, ρ.Matched a b ∧ (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧
    HasFlip B t ρ i j n Φ τ τ' ∧ Θ = tensT W a τ ∧ Θ' = tensT W b τ'

end Finite

variable (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)

variable {t} in

def SquareConv {i j : ℕ} (M : Vol G) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (z : GA D (G.V (.grid i j)) →₀ ℂ) (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) : Prop :=
  IntegrableOn (kerBig W Θ g g₁) (M.fd _) (M.ν _) ∧ IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _)

def IsSquareConst (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ z g g₁, SquareConv W M Θ Θ' z g g₁ →
    zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _

def SquareNonzero : Prop :=
  ∃ M : Vol G, M.Is t ∧ ∃ Θ Θ', IsMatched B t ρ i j Θ Θ' ∧ ∃ z g g₁, SquareConv W M Θ Θ' z g g₁ ∧
    ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ ≠ 0

def CommutesWith (c : ℂ) : Prop :=
  ∀ M : Vol G, M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ F : Fn G (.grid i (j + 1)),
    IsAutFunSm W.θ _ F → IsCuspFun _ F → G.IsListed W.θ _ F → TotConv W M _ Θ F → TotConv W M _ Θ' F →
      liftT W M (routeBig t i j) Θ F = c • liftT W M (routeSmall t i j) Θ' F

variable {W B ρ t i j}

theorem IsSquareConst.unique (h : SquareNonzero W B ρ t i j) {c c' : ℂ} (hc : IsSquareConst W B ρ t i j c)
    (hc' : IsSquareConst W B ρ t i j c') : c = c' := by
  obtain ⟨M, hM, Θ, Θ', hΘ, z, g, g₁, hz, h0⟩ := h
  exact mul_right_cancel₀ h0 ((hc M hM Θ Θ' hΘ z g g₁ hz).symm.trans (hc' M hM Θ Θ' hΘ z g g₁ hz))

theorem IsSquareConst.of_integrable {c : ℂ} (hc : IsSquareConst W B ρ t i j c) {M : Vol G} (hM : M.Is t) {Θ Θ'}
    (hΘ : IsMatched B t ρ i j Θ Θ') {g g₁} (h : IntegrableOn (kerBig W Θ g g₁) (M.fd _) (M.ν _))
    (h' : IntegrableOn (kerSmall W Θ' g g₁) (M.fd _) (M.ν _)) :
    ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, kerSmall W Θ' g g₁ u ∂M.ν _ := by
  have := hc M hM Θ Θ' hΘ (Finsupp.single 1 1) g g₁ ⟨h, by rwa [(translates_one _).1]⟩
  rwa [(translates_one _).1, (translates_one (fun _ => 0)).2, one_mul] at this

example (t : T) : (routeSmall t 0 0).arrows = [.down t 0 0, .right 0 0] ∧
    (routeBig t 0 0).arrows = [.right 0 1, .down t 1 0] := ⟨rfl, rfl⟩

example (M : Vol G) (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M _ (Finsupp.single d 1) F g₁ =
      ∫ u in M.fd _, ∫ g in M.fd _, kerSmall W (Finsupp.single d 1) g g₁ u * F g ∂M.ν _ ∂M.ν _ := by
  rw [liftT_single, one_smul]
  refine integral_congr_ae (.of_forall fun u => ?_)
  have e : ∀ g, kerSmall W (Finsupp.single d 1) g g₁ u * F g =
      W.kerA (.right i j) d.2 u g₁ * (W.kerA (.down t i j) d.1.2 g u * F g) := fun g => by
    rw [kerSmall, Finsupp.sum_single_index (zero_mul _)]; ring
  simp only [e, integral_const_mul]
  rfl

example {H : Type} (u v : H) : zdeg (Finsupp.single u 1 - Finsupp.single v 1) = 0 := by
  rw [zdeg, Finsupp.sum_sub_index (fun _ _ _ => rfl)]; simp

end GlobalTheory.FunObj

end
