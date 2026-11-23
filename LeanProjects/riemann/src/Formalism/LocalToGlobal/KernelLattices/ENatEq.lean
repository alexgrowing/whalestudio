import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThEquiv
import Formalism.LocalToGlobal.KernelLattices.ColumnData

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section Fam

variable {D : D7}

def Base.ekFac (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : ℂ :=
  letI := D.host.cmStar
  Base.chiFac χ N N' (SDLat.smulLat γ L) (SDLat.smulLat γ' L') * (Base.chiFac χ N N' L L')⁻¹

def ekDet (D : D7) (N N' : ℕ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) : ℂ :=
  (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ γ.det) ^ (-((N' / 2 : ℕ) : ℤ)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ γ'.det) ^ (((N / 2 : ℕ) : ℤ))

def EkDetP (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      Base.ekFac χ N N' L.1 L'.1 (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) =
        ekDet D N N' (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def ChiDetSmul (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : SDLat D.host.E N), Even N → ∀ γ : Matrix.unitaryGroup (Fin N) D.host.E,
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L.1)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def Base.ThMovedEq (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L.1 L'.1) =
        fun z => Base.ekFac χ N N' L.1 L'.1 (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) *
          B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1) z

def Base.ThetaTransformUnitaryScalar : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L.1 L'.1) =
        fun z => ekDet D N N' (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) *
          B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1) z

def Base.ThMovedGL : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (g : GL (Fin N) D.host.E) (g' : GL (Fin N') D.host.E), g.1 ∈ Matrix.unitaryGroup (Fin N) D.host.E →
      g'.1 ∈ Matrix.unitaryGroup (Fin N') D.host.E → ∀ z : TaylorLogMetric.VC D N N',
      B.thMoved N N' (SDLat.smulLat g.1 L.1) (SDLat.smulLat g'.1 L'.1) z =
        (ekDet D N N' g.1 g'.1)⁻¹ * B.thMoved N N' L.1 L'.1 fun τ =>
          (((g'⁻¹).1.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (g.1.map (TaylorLogMetric.embT D τ)) : Matrix (Fin N') (Fin N) ℂ)

def Base.ENatGL (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (g : GL (Fin N) D.host.E) (g' : GL (Fin N') D.host.E), g.1 ∈ Matrix.unitaryGroup (Fin N) D.host.E →
      g'.1 ∈ Matrix.unitaryGroup (Fin N') D.host.E → ∀ z : TaylorLogMetric.VC D N N',
      B.eNat χ N N' (SDLat.smulLat g.1 L.1) (SDLat.smulLat g'.1 L'.1) z =
        B.eNat χ N N' L.1 L'.1 fun τ =>
          (((g'⁻¹).1.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (g.1.map (TaylorLogMetric.embT D τ)) : Matrix (Fin N') (Fin N) ℂ)

end Fam

section OnAmb

variable {X : Fields} (A : Amb X) (a b : ℕ)

def Amb.thU (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : VCx X.Tau a b → ℂ :=
  fun z => (A.chiF a b N N')⁻¹ * A.e a b N N' z

def Amb.ek (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : ℂ :=
  A.chiF a b (gmap γ.1 N) (gmap γ'.1 N') * (A.chiF a b N N')⁻¹

def Amb.ekDet (γ : UF X.E a) (γ' : UF X.E b) : ℂ :=
  (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) ^ (-((b / 2 : ℕ) : ℤ)) *
    (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E)) ^ (((a / 2 : ℕ) : ℤ))

def Amb.ChiNe : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → A.chiF a b N N' ≠ 0

def Amb.EqLawU : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ z, A.thU a b N N' (A.pullV a b γ.1 γ'.1 z) = A.ek a b γ γ' N N' * A.thU a b (gmap γ.1 N) (gmap γ'.1 N') z

def Amb.EkLaw : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.ek a b γ γ' N N' = A.ekDet a b γ γ'

def Amb.EqLawDet : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ z, A.thU a b N N' (A.pullV a b γ.1 γ'.1 z) = A.ekDet a b γ γ' * A.thU a b (gmap γ.1 N) (gmap γ'.1 N') z

def Amb.ThDatEq (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → X.K),
    IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → (∀ x, ∀ y ∈ mulLat cB (homAt Sall N N'), Ξ (x + y) = Ξ x) →
    ∀ z, A.thDat Sall cA cB (gmap γ.1 N) (gmap γ'.1 N') (fun x => Ξ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) z =
      A.thDat Sall cA cB N N' Ξ (A.pullV a b γ.1 γ'.1 z)

def Amb.ThCEq (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → X.K),
    IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → (∀ x, ∀ y ∈ mulLat cB (homAt Sall N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt Sall N N') → Ξ x = 0) →
    ∀ z, thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sall (gmap γ.1 N) (gmap γ'.1 N') (cA * cB)
        (fun x => A.σ₀ (Ξ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))) (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) z =
      thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sall N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N') (A.pullV a b γ.1 γ'.1 z)

end OnAmb

section FamC

variable {D : Car}

def Cd.Base.ekFac (χ : Cd.TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : ℂ :=
  letI := D.host.cmStar
  Cd.Base.chiFac χ N N' (SDLat.smulLat γ L) (SDLat.smulLat γ' L') * (Cd.Base.chiFac χ N N' L L')⁻¹

def Cd.ekDet (D : Car) (N N' : ℕ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) : ℂ :=
  (∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ γ.det) ^ (-((N' / 2 : ℕ) : ℤ)) * (∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ γ'.det) ^ (((N / 2 : ℕ) : ℤ))

def Cd.EkDetP (D : Car) (χ : Cd.TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      Cd.Base.ekFac χ N N' L.1 L'.1 (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) =
        Cd.ekDet D N N' (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def Cd.ChiDetSmul (D : Car) (χ : Cd.TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : SDLat D.host.E N), Even N → ∀ γ : Matrix.unitaryGroup (Fin N) D.host.E,
    χ (Cd.TaylorLogMetric.detId D (Cd.StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)) =
      (∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ * χ (Cd.TaylorLogMetric.detId D (Cd.StandardLatticesGL3.stdL D N) L.1)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

def Cd.Base.ThMovedEq (χ : Cd.TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      Cd.TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L.1 L'.1) =
        fun z => Cd.Base.ekFac χ N N' L.1 L'.1 (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) *
          B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1) z

def Cd.Base.ThetaTransformUnitaryScalar : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      Cd.TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L.1 L'.1) =
        fun z => Cd.ekDet D N N' (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) *
          B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1) z

def Cd.Base.ThMovedGL : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (g : GL (Fin N) D.host.E) (g' : GL (Fin N') D.host.E), g.1 ∈ Matrix.unitaryGroup (Fin N) D.host.E →
      g'.1 ∈ Matrix.unitaryGroup (Fin N') D.host.E → ∀ z : Cd.TaylorLogMetric.VC D N N',
      B.thMoved N N' (SDLat.smulLat g.1 L.1) (SDLat.smulLat g'.1 L'.1) z =
        (Cd.ekDet D N N' g.1 g'.1)⁻¹ * B.thMoved N N' L.1 L'.1 fun τ =>
          (((g'⁻¹).1.map (Cd.TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (g.1.map (Cd.TaylorLogMetric.embT D τ)) : Matrix (Fin N') (Fin N) ℂ)

def Cd.Base.ENatGL (χ : Cd.TaylorLogMetric.IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (g : GL (Fin N) D.host.E) (g' : GL (Fin N') D.host.E), g.1 ∈ Matrix.unitaryGroup (Fin N) D.host.E →
      g'.1 ∈ Matrix.unitaryGroup (Fin N') D.host.E → ∀ z : Cd.TaylorLogMetric.VC D N N',
      B.eNat χ N N' (SDLat.smulLat g.1 L.1) (SDLat.smulLat g'.1 L'.1) z =
        B.eNat χ N N' L.1 L'.1 fun τ =>
          (((g'⁻¹).1.map (Cd.TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (g.1.map (Cd.TaylorLogMetric.embT D τ)) : Matrix (Fin N') (Fin N) ℂ)

end FamC

end Formalism.L2.Ker
