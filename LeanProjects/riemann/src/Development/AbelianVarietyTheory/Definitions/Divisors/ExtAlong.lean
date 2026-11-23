import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (Λ : Submodule (𝓞 K) (Fin g → K)) (k : K) : Prop :=
  (∀ c : Matrix (Fin g) (Fin g) K, (∀ i, c i ∈ Λ) → IsIntegral ℤ (k * c.det ^ 4)) ∧
  (1 : K) ∈ Submodule.span (𝓞 K) {z | ∃ c : Matrix (Fin g) (Fin g) K, (∀ i, c i ∈ Λ) ∧ z = k * c.det ^ 4}

def Frame (κ : Rule) {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K'']
    [Algebra K K''] (x : KeyIn K'') (hg : x.P.g = F.P₀.g) (ψ : x.P.A.left ⟶ F.P₀.A.left) {AA : Over (Sp (𝓞 K''))} [GrpObj AA]
    (φ : x.P.A.left ⟶ AA.left) : Prop :=
  IsOver F ψ φ ∧ IsSemiAbelian AA ∧ IsGrpPullback x.P.A AA (spMap (algebraMap (𝓞 K'') K'')) φ ∧
  (∀ k, IsVecOver (algebraMap K K'') ψ (F.v k) (x.v (k.cast hg.symm))) ∧ KeyUnit (latBC K'' F.lieLat) (κ K'' x : K'')

def TrFull {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : K →+* Ω) (z : Over.mk (spMap f) ⟶ P.A), z ^ N = 1 →
    ∃ U : ThetaGrp P.A P.L (N : ℤ) (baseOver (Sp K)), FinOrdT P U ∧ spMap f ≫ U.pt.left = z.left

def IsTrAt {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ) (z : Sp R ⟶ x.P.A.left) (s : (lbPow x.P.L (m ^ 2)).Sec) : Prop :=
  ∃ th U t, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧ FinOrdT x.P U ∧ Tr x.P x.rig m th U t ∧
    OnT x.P (baseOver (Sp R)) (m ^ 2) s t ∧ U.pt.left = z

def Val0 {K : Type} [Field K] (x : KeyIn K) (n : ℕ) (s : (lbPow x.P.L n).Sec) (β : K) : Prop :=
  ∀ i : x.P.L.ι, ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i →
    valR (X := x.P.A.left) (eSec x.P.A) _ (s.f fun _ => i) = β * valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val ^ n

structure PB {K K' : Type} [Field K] [Field K'] (x : KeyIn K) (f : K →+* K') where

  x' : KeyIn K'
  hg : x'.P.g = x.P.g

  ψ : x'.P.A.left ⟶ x.P.A.left
  key : KeyPB x' x f
  fib : IsPolFibre f x.P x'.P ψ
  vec : ∀ i, IsVecOver f ψ (x.v (i.cast hg)) (x'.v i)

  w : ∀ n, LB.Iso ((lbPow x.P.L n).pull ψ) (lbPow x'.P.L n)
  gen : ∀ n, (w n).IsGen
  rig : ∀ (n : ℕ) (i : x.P.L.ι) (i' : x'.P.L.ι), ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (eSec x'.P.A) ⁻¹ᵁ x'.P.L.U i' →
    valR (X := x'.P.A.left) (eSec x'.P.A) _ ((w n).s (fun _ => i', fun _ _ => i)).val *
      f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val) ^ n =
      valR (X := Sp K') (𝟙 _) _ (x'.rig.s fun _ => i').val ^ n
  tr : ∀ (m : ℕ) z s, IsTrAt x m z s → ∃ z' s', z' ≫ ψ = spMap f ≫ z ∧ IsTrAt x' m z' s' ∧ SecMaps (w (m ^ 2)) (secPull s ψ) s'

structure Cx {K : Type} [Field K] (x : KeyIn K) (σ : K →+* ℂ) extends PB x σ where

  u : HolUnif x'.P.A x'.P.L x'.P.g

  Hm : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  χ : u.Λ → ℂ

  W : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  θ : (Fin x'.P.g → ℂ) → ℂ

  Fd : Set (Fin x'.P.g → ℂ)

  Ef : LinearMap.BilinForm ℤ u.Λ
  ah : u.IsAH Hm χ
  isRig : u.IsRig x'.rig
  fn : u.IsFn x'.th θ
  theta : u.IsThetaFn Hm χ 1 θ
  diff : ∀ i, u.IsDiff (W i) (x'.v i)
  fd : IsAddFundamentalDomain u.Λ Fd volume
  ef : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im
  efb : Function.Bijective Ef
  secs : ∀ (n : ℕ) s, ∃! Θ, u.IsThetaFn Hm χ n Θ ∧ u.IsFnPow n s Θ

def nrmAt {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (Θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℝ :=
  ‖Θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))

def meanSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (Θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) : ℝ :=
  (∫ z in Fd, nrmAt Hm n Θ z) / (volume Fd).toReal

def Cx.nth {K : Type} [Field K] {x : KeyIn K} {σ : K →+* ℂ} (c : Cx x σ) : ℝ := meanSq c.Hm 1 c.θ c.Fd

def ExtAlong {X Y Z : Scheme.{0}} {M : LB X} {φ : Y ⟶ X} {N : LB Y} (w : LB.Iso (M.pull φ) N) (s : N.Sec) (j : Z ⟶ X)
    (φ' : Y ⟶ Z) : Prop :=
  ∃ t : (M.pull j).Sec, ∀ (i : N.ι) (p : PUnit → M.ι) (V : Y.Opens) (h₁ : V ≤ N.U i ⊓ (M.pull φ).U p)
    (h₂ : V ≤ φ' ⁻¹ᵁ (M.pull j).U p),
    resG Y (h₁.trans inf_le_left) (s.f i) =
      resG Y h₁ (@id (Γ(Y, N.U i ⊓ (M.pull φ).U p)ˣ) (w.s (i, p)) : Γ(Y, N.U i ⊓ (M.pull φ).U p)) *
        (φ'.appLE _ V h₂).hom (t.f p)

end GlobalTheory.MBLow

end
