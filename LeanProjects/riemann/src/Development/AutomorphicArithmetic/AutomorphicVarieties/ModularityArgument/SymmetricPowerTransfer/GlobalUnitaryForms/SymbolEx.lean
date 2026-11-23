import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Defs

variable {K : Type} [Field K]

def jstd (τ : K) : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1) τ)

def Cu (O : Type) [CommRing O] [Algebra O K] (τ : K) : Subgroup (Etau K τ)ˣ :=
  (Units.map ((integralClosure O (Etau K τ)).val : integralClosure O (Etau K τ) →* Etau K τ)).range

def scalE (τ : K) : Subgroup (Etau K τ)ˣ := (Units.map (algebraMap K (Etau K τ) : K →* Etau K τ)).range

open Classical in

def toUnit {R : Type} [Monoid R] (x : R) : Rˣ := if h : IsUnit x then h.unit else 1

variable {F : Type} [Field F] [NumberField F]

abbrev TA (τ : F) : Type := RP (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)

def IsDiagT (τ : F) (φ : (Etau F τ)ˣ →* TA τ) : Prop := ∀ z v, ((φ z).1 v : Etau (Kv v) (cv v τ)) = emap (cv v) τ z

open Classical in

def ms (τ : F) : ℂ :=
  if h : ∃ φ, IsDiagT τ φ then mass h.choose (scalE τ) ((rpg _ _).box fun v => Cint (Ov v) (cv v τ)) else 0

variable {Δ : F} (D : Dat Δ)

def Dat.Good (t : Dat.Par F) (τ : F) : Prop := (∀ σ : F →+* ℝ, σ (τ ^ 2 - 4) < 0) ∧ ∀ v ∈ D.Sg, Ind (D.S v).H (cv v τ) (t v)

def Dat.nS (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) 1 (toUnit QuadraticAlgebra.omega)

def Dat.nK (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + QuadraticAlgebra.omega))

def Dat.sumS (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nS τ)

def Dat.sumK (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nK τ)

def Dat.Off (x : DA Δ) : Prop := ∀ v ∈ D.Sg, x.1 v = 1

end Defs

def BaseG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (U3 Δ) V) (Θ : V →ₗ[ℂ] V) (ch : F → ℂ), (∀ γ v, Θ (W γ v) = W (theta Δ γ) (Θ v)) →
    (∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (W δ ∘ₗ Θ) = ch τ) →
    ∃ (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s ∧ B.W = W ∧ s.Θ = Θ

def BaseS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (SU Δ) V) (ch : F → ℂ), (∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (W γ) = ch τ) →
    ∀ x : DA Δ, ∃ B : Base (SU Δ) (SA Δ) V, D.IsBS ch x B ∧ B.W = W

def BaseK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (DX Δ) V) (ch : F → ℂ),
    (∀ z s, IsScal z s → ∀ v, W s v = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ • v) →
    (∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) → LinearMap.trace ℂ V (W g) = ch τ) →
    ∃ B : Base (DX Δ) (DA Δ) V, D.IsBK ch B ∧ B.W = W

def FinG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s → B.Fin ∧ ∀ t, D.Cone t → s.IsTest (D.FG t)

def FinS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), D.IsBS ch x B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FSx t x)

def FinK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (DX Δ) (DA Δ) V), D.IsBK ch B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FK t)

def SideG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c e : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw),
    D.IsBG ch B s → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms (s.R (D.FG t)) = c * (D.sumS ch t + e * D.sumK ch t)

def SideS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ (n : ℕ) (x : Fin (n + 1) → DA Δ) (c : ℝ), x 0 = 1 ∧
    (∀ i, D.Off (x i)) ∧ 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Fin (n + 1) → Base (SU Δ) (SA Δ) V),
    (∀ i, D.IsBS ch (x i) (B i)) → ∀ t, D.Cone t →
    ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R (D.FSx t (x i))) = c * D.sumS ch t

def SideK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V),
    D.IsBK ch B → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms ((Base.Tw.one B).R (D.FK t)) = c * D.sumK ch t

def TFId : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ (n : ℕ) (x : Fin (n + 1) → DA Δ) (a b : ℝ), x 0 = 1 ∧
    (∀ i, D.Off (x i)) ∧ 0 < a ∧
    ∀ (VG VS VK : Type) [AddCommGroup VG] [Module ℂ VG] [FiniteDimensional ℂ VG] [AddCommGroup VS] [Module ℂ VS]
      [FiniteDimensional ℂ VS] [AddCommGroup VK] [Module ℂ VK] [FiniteDimensional ℂ VK] (ch : F → ℂ)
      (BG : Base (U3 Δ) (GA Δ) VG) (s : BG.Tw) (BS : Fin (n + 1) → Base (SU Δ) (SA Δ) VS) (BK : Base (DX Δ) (DA Δ) VK),
    D.IsBG ch BG s → (∀ i, D.IsBS ch (x i) (BS i)) → D.IsBK ch BK → ∀ t, D.Cone t →
    LinearMap.trace ℂ BG.Forms (s.R (D.FG t)) =
      a * ∑ i, LinearMap.trace ℂ (BS i).Forms ((Base.Tw.one (BS i)).R (D.FSx t (x i))) +
      b * LinearMap.trace ℂ BK.Forms ((Base.Tw.one BK).R (D.FK t))

def Recip : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 →
    {v : Pl F | hs (cv v d) (cv v x) ≠ 1}.Finite ∧ (∏ᶠ v : Pl F, hs (cv v d) (cv v x)) = ∏ σ : F →+* ℝ, hs (σ d) (σ x)

def SymbolEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F), d ≠ 0 → ∀ y : ∀ v : Pl F, (Kv v)ˣ, {v | hs (cv v d) (y v : Kv v) ≠ 1}.Finite →
    (∏ᶠ v : Pl F, hs (cv v d) (y v : Kv v)) = 1 →
    ∃ x : F, x ≠ 0 ∧ (∀ σ : F →+* ℝ, 0 < σ x) ∧ ∀ v, hs (cv v d) (cv v x) = hs (cv v d) (y v : Kv v)

def HsMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (d x y : Kv v), d ≠ 0 → x ≠ 0 → y ≠ 0 → hs d (x * y) = hs d x * hs d y

def HsHasse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, hs (σ d) (σ x) = 1) →
    (∀ v : Pl F, hs (cv v d) (cv v x) = 1) → hs d x = 1

end UpperTheory.V.Z.Sym.Glob
