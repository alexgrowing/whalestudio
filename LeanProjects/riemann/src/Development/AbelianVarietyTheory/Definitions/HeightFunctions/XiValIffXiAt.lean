import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def WeberIn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (F : IntermediateField ℚ ℂ) (n : ℕ) : Prop :=
  ∀ L : PeriodPair, (∀ x, x ∈ L.lattice ↔ ∃ s, x = GlobalTheory.CompRat.wC H s) →
    L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∈ F ∧
      ∀ s, GlobalTheory.CompRat.wC H s / n ∉ L.lattice →
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (GlobalTheory.CompRat.wC H s / n) ∈ F

def CoverOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (p : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  d.pd = p ∧ d.I = I ∧ d.IsLev ∧ d.l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂

def RootOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  (∃ m : ℕ, 0 < m ∧ d.cδ ^ m = 1) ∧
    ∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F,
      evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a

def DeltaOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (p : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  CoverOK d p I ∧ RootOK d ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ)

structure FieldOK (D : D7) (p : ℕ) : Prop where
  own : p = D.host.pde ∨ p = D.host.pde'
  full : OFull D
  zetaM : OZeta D
  zetaP : zeta p ∈ FO D
  curve : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) (D.host.g 0 * D.host.g 1 * p)
  kpsi : OKPsi D
  vol : VolTieG D
  bad : 0 ∉ D.host.levelPrimes
  split : D.host.cls p = PrimeClass.splitK

variable {D : D7}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def barF (D : D7) : AfE D →ₐ[D.host.F] AfE D :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) (GlobalTheory.Member.cF D : D.host.E →ₐ[D.host.F] D.host.E)

def NormOne (x : (AfE D)ˣ) : Prop := (x : AfE D) * barF D (x : AfE D) = 1

def CongOne (N : ℕ) (x : (AfE D)ˣ) : Prop := ∃ w ∈ intAE D, (x : AfE D) - 1 = N • w

structure XiOK (D : D7) (p : ℕ) (xi : (AfE D)ˣ →* ℂˣ) : Prop where
  rat : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1
  tame : ∀ x, NormOne x → CongOne (D.host.g 0 * D.host.g 1 * p) x → xi x = 1
  ram : ∃ x, NormOne x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ xi x ≠ 1
  fin : ∃ m : ℕ, 0 < m ∧ ∀ x, NormOne x → xi x ^ m = 1
  val : ∀ x, NormOne x → ((xi x : ℂˣ) : ℂ) ∈ FO D

def XiAt (J : CoreJ D) (j : ℕ) {n : ℕ} (d : DeltaDat (J.Q.Xo j) J.Q.c n) (xi : (AfE D)ˣ →* ℂˣ) : Prop :=
  ∃ (hr : (J.V j J.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (J.V j J.σ₀) hr J.σ₀ (Tup := Unit) (fun _ => d) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ J.iota j) (J.x₀ j J.σ₀) fun _ => xi

theorem xiVal_iff_xiAt (T : Full D) (j n : ℕ) : T.XiVal j n ↔ XiAt T.J j (T.dδ j n) T.xi := Iff.rfl

def ChiOK (D : D7) (chi₀ : ℕ → (AE D)ˣ →* Circle) : Prop :=
  ∀ j, InR D j → IsHeckeChar D (chi₀ j) ∧ (∀ a, chi₀ j (idF D a) = 1) ∧
    ∀ x, FinUnit x → ((chi₀ j x : Circle) : ℂ) ∈ FO D

theorem chiOK_one (D : D7) : ChiOK D (fun _ => 1) := fun _ _ =>
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ => rfl, fun _ _ => by simpa using (FO D).one_mem⟩

end GlobalTheory.FinalJoin
