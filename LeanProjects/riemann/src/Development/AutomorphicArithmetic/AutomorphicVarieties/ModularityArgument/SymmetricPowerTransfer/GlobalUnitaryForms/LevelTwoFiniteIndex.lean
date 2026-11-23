import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Polynomial Loc

section Field

variable {K K' : Type} [Field K] [Field K']

def qmap (f : K →+* K') (a b : K) : QuadraticAlgebra K a b →+* QuadraticAlgebra K' (f a) (f b) where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def lmap (f : K →+* K') (Δ : K) : Lsq K Δ →+* Lsq K' (f Δ) where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def emap (f : K →+* K') (τ : K) : Etau K τ →+* Etau K' (f τ) where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

variable (Δ : K)

def wJ : GL (Fin 2) (Lsq K Δ) :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

def DX : Subgroup (GL (Fin 2) (Lsq K Δ)) :=
  (GeneralLinearGroup.map (starRingEnd (Lsq K Δ))).eqLocus (MulAut.conj (wJ Δ)⁻¹).toMonoidHom

def SU : Subgroup (DX Δ) := (GeneralLinearGroup.det.comp (DX Δ).subtype).ker

variable {Δ}

abbrev mt (g : DX Δ) : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := (g : GL (Fin 2) (Lsq K Δ))

def IsScal (z : Kˣ) (g : DX Δ) : Prop := mt g = scalar (Fin 2) (algebraMap K (Lsq K Δ) z)

variable (Δ) in

def ZD : Subgroup (DX Δ) :=
  ((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))).range.subgroupOf (DX Δ)

def IsEmb (τ : K) (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ) : Prop :=
  ∀ z, mt (j z) = (z : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + (z : Etau K τ).im • mt γ

def HasTau (δ : U3 Δ) (τ : K) : Prop :=
  ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).charpoly = (X - 1) * (X ^ 2 - C (algebraMap K _ τ) * X + 1)

def HasTr (γ : DX Δ) (τ : K) : Prop := (mt γ).det = 1 ∧ (mt γ).trace = algebraMap K _ τ

def Ind (H : Subgroup Kˣ) (τ : K) (t : Kˣ) : Prop := ∃ h ∈ H, τ = (t * h : Kˣ) + ((t * h)⁻¹ : Kˣ)

open Classical in

def one (p : Prop) : ℂ := if p then 1 else 0

variable (O : Type) [CommRing O] [Algebra O K]

variable (Δ) in

def KD : Subgroup (DX Δ) :=
  (GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range.subgroupOf (DX Δ)

open Classical in

def fZD (χ : Kˣ →* ℂˣ) (g : DX Δ) : ℂ :=
  if h : ∃ z : Kˣ, ∃ s : DX Δ, IsScal z s ∧ s⁻¹ * g ∈ KD Δ O then ((χ h.choose)⁻¹ : ℂˣ) else 0

def IsChi (Δ : K) [IsLocalRing O] (χ : Kˣ →* ℂˣ) : Prop :=
  Unr O χ ∧ ∀ (ϖ : O) (x : Kˣ), Irreducible ϖ → (x : K) = algebraMap O K ϖ →
    (χ x : ℂ) = hs Δ (x : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ)

variable (Δ) in

structure SigData where
  P : Set Kˣ
  H : Subgroup Kˣ
  J : Subgroup (U3 Δ)
  J2 : Subgroup (DX Δ)
  fG : Kˣ → U3 Δ → ℂ
  fS : Kˣ → DX Δ → ℂ
  fK : Kˣ → DX Δ → ℂ
  cG : ℝ
  cS : ℝ
  cK : ℝ

structure SigOk (χ : Kˣ →* ℂˣ) (S : SigData Δ) : Prop where
  cG : 0 < S.cG
  cS : 0 < S.cS
  cK : 0 < S.cK
  J_le : S.J ≤ KU O Δ
  J_fin : S.J.relIndex (KU O Δ) ≠ 0
  levelTwoLeIntegral : S.J2 ≤ KD Δ O
  levelTwoFiniteIndex : S.J2.relIndex (KD Δ O) ≠ 0
  reg : ∀ t ∈ S.P, ∀ τ, Ind S.H τ t → IsSquare (τ ^ 2 - 4) ∧ ¬ IsIntegral O τ
  G_inv : ∀ t ∈ S.P, ∀ u ∈ S.J, ∀ y, S.fG t (u * y) = S.fG t y ∧ S.fG t (y * theta Δ u) = S.fG t y
  G_fin : ∀ t ∈ S.P, {x : U3 Δ ⧸ S.J | S.fG t (theta Δ x.out) ≠ 0}.Finite
  G_supp : ∀ t ∈ S.P, ∀ δ τ, HasTau δ τ → S.fG t δ ≠ 0 → Ind S.H τ t
  G_orb : ∀ t ∈ S.P, ∀ (τ c : K) (d m : EL Δ τ) δ ι Q, IsDat c d m → Models c d m δ ι Q →
    FinOrb ι (theta Δ) S.J (S.fG t) δ ∧ orb ι (Cint O τ) (theta Δ) S.J (S.fG t) δ = S.cG * one (Ind S.H τ t) ∧
    (Ind S.H τ t → ∀ y : U3 Δ ⧸ S.J, ((MulAction.stabilizer (U3 Δ) y).comap ι).relIndex (Cint O τ) ≠ 0)
  S_inv : ∀ t ∈ S.P, ∀ u ∈ S.J2, ∀ y, S.fS t (u * y) = S.fS t y ∧ S.fS t (y * u) = S.fS t y
  S_fin : ∀ t ∈ S.P, {x : SU Δ ⧸ S.J2.subgroupOf (SU Δ) | S.fS t x.out ≠ 0}.Finite
  S_supp : ∀ t ∈ S.P, ∀ γ τ, HasTr γ τ → S.fS t γ ≠ 0 → Ind S.H τ t
  K_inv : ∀ t ∈ S.P, (∀ u ∈ S.J2, ∀ y, S.fK t (u * y) = S.fK t y ∧ S.fK t (y * u) = S.fK t y) ∧
    ∀ z s, IsScal z s → ∀ y, S.fK t (s * y) = ((χ z)⁻¹ : ℂˣ) * S.fK t y
  K_fin : ∀ t ∈ S.P, {x : DX Δ ⧸ (ZD Δ ⊔ S.J2) | S.fK t x.out ≠ 0}.Finite
  K_supp : ∀ t ∈ S.P, ∀ g, S.fK t g ≠ 0 → ∃ τ, Ind S.H τ t ∧ (mt g).trace ^ 2 = algebraMap K _ (2 + τ) * (mt g).det
  D_orb : ∀ t ∈ S.P, ∀ τ γ j, τ ^ 2 - 4 ≠ 0 → HasTr γ τ → IsEmb τ γ j → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega →
    FinOrb j (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fS t) γ ∧ FinOrb j (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fK t) (j z) ∧
    orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fS t) γ = S.cS * one (Ind S.H τ t) ∧
    orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fK t) (j z) = S.cK * one (Ind S.H τ t) ∧
    (Ind S.H τ t → ∀ y : DX Δ ⧸ (ZD Δ ⊔ S.J2), ((MulAction.stabilizer (DX Δ) y).comap j).relIndex (Cint O τ) ≠ 0)

end Field

def RP {I : Type} (Gv : I → Type) [∀ v, Group (Gv v)] (K : ∀ v, Subgroup (Gv v)) : Subgroup (∀ v, Gv v) where
  carrier := {x | ∀ᶠ v in Filter.cofinite, x v ∈ K v}
  one_mem' := show ∀ᶠ v in Filter.cofinite, (1 : Gv v) ∈ K v from Filter.Eventually.of_forall fun _ => one_mem _
  mul_mem' {a b} ha hb := show ∀ᶠ v in Filter.cofinite, a v * b v ∈ K v from
    (Filter.Eventually.and (show ∀ᶠ v in Filter.cofinite, a v ∈ K v from ha) (show ∀ᶠ v in Filter.cofinite, b v ∈ K v from hb)).mono
      fun _ h => mul_mem h.1 h.2
  inv_mem' {a} ha := show ∀ᶠ v in Filter.cofinite, (a v)⁻¹ ∈ K v from
    (show ∀ᶠ v in Filter.cofinite, a v ∈ K v from ha).mono fun _ h => inv_mem h

def rpg {I : Type} (Gv : I → Type) [∀ v, Group (Gv v)] (K : ∀ v, Subgroup (Gv v)) : RPG (RP Gv K) Gv K where
  p v := (Pi.evalMonoidHom Gv v).comp (RP Gv K).subtype
  inj _ h := Subtype.ext (funext h)
  ae g := g.2
  surj x hx := ⟨⟨x, hx⟩, fun _ => rfl⟩

section Global

variable {F : Type} [Field F] [NumberField F]

abbrev Pl (F : Type) [Field F] : Type := HeightOneSpectrum (𝓞 F)

abbrev Kv (v : Pl F) : Type := v.adicCompletion F

abbrev Ov (v : Pl F) : Type := v.adicCompletionIntegers F

abbrev cv (v : Pl F) : F →+* Kv v := algebraMap F (Kv v)

variable (Δ : F)

abbrev GA : Type := RP (fun v : Pl F => U3 (cv v Δ)) fun v => KU (Ov v) (cv v Δ)

abbrev DA : Type := RP (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)

def SA : Subgroup (DA Δ) := ⨅ v, (SU (cv v Δ)).comap ((rpg _ _).p v)

structure Dat where
  Sg : Finset (Pl F)
  S : ∀ v : Pl F, SigData (cv v Δ)
  χ : ∀ v : Pl F, (Kv v)ˣ →* ℂˣ

variable {Δ} (D : Dat Δ)

structure Dat.Ok : Prop where
  real : IsTotallyReal F
  neg : ∀ σ : F →+* ℝ, σ Δ < 0
  ne : D.Sg.Nonempty
  off : ∀ v ∉ D.Sg, IsLoc (Ov v) (cv v Δ)
  split : ∀ v ∈ D.Sg, IsSquare (cv v Δ)
  chi : ∀ v, IsChi (Ov v) (cv v Δ) (D.χ v)
  sig : ∀ v ∈ D.Sg, SigOk (Ov v) (D.χ v) (D.S v)

namespace Dat

open Classical in

def Jv (v : Pl F) : Subgroup (U3 (cv v Δ)) := if v ∈ D.Sg then (D.S v).J else KU (Ov v) _

open Classical in

def J2v (v : Pl F) : Subgroup (DX (cv v Δ)) := if v ∈ D.Sg then (D.S v).J2 else KD _ (Ov v)

def UG : Subgroup (GA Δ) := (rpg _ _).box D.Jv

def U2 : Subgroup (DA Δ) := (rpg _ _).box D.J2v

def UZ : Subgroup (DA Δ) := (rpg _ _).box fun v => ZD _ ⊔ D.J2v v

abbrev Par (F : Type) [Field F] [NumberField F] : Type := ∀ v : Pl F, (Kv v)ˣ

def Cone (t : Par F) : Prop := ∀ v ∈ D.Sg, t v ∈ (D.S v).P

open Classical in

def fGv (t : Par F) (v : Pl F) (g : U3 (cv v Δ)) : ℂ := if v ∈ D.Sg then (D.S v).fG (t v) g else one (g ∈ KU (Ov v) _)

open Classical in

def fSv (t : Par F) (v : Pl F) (g : DX (cv v Δ)) : ℂ := if v ∈ D.Sg then (D.S v).fS (t v) g else one (g ∈ KD _ (Ov v))

open Classical in

def fKv (t : Par F) (v : Pl F) (g : DX (cv v Δ)) : ℂ := if v ∈ D.Sg then (D.S v).fK (t v) g else fZD (Ov v) (D.χ v) g

def FG (t : Par F) (g : GA Δ) : ℂ := ∏ᶠ v, D.fGv t v (g.1 v)

def FS (t : Par F) (g : DA Δ) : ℂ := ∏ᶠ v, D.fSv t v (g.1 v)

def FSx (t : Par F) (x : DA Δ) (g : SA Δ) : ℂ := D.FS t (x⁻¹ * g * x)

def FK (t : Par F) (g : DA Δ) : ℂ := ∏ᶠ v, D.fKv t v (g.1 v)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure IsBG (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw) : Prop where
  ι : ∀ γ v, (((B.ι γ).1 v : U3 (cv v Δ)) : Matrix (Fin 3) (Fin 3) _) = (γ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map (lmap (cv v) Δ)
  U : B.U = D.UG
  ω : B.ω = 1
  Γ₀ : B.Γ₀ = ⊥
  θΓ : ∀ γ, s.θΓ γ = theta Δ γ
  θ : ∀ g v, (s.θ g).1 v = theta _ (g.1 v)
  tr : ∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) = ch τ

structure IsBS (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V) : Prop where
  ι : ∀ γ v, mt ((B.ι γ : DA Δ).1 v) = (mt (γ : DX Δ)).map (lmap (cv v) Δ)
  U : ∀ g : SA Δ, g ∈ B.U ↔ x⁻¹ * g * x ∈ D.U2
  ω : B.ω = 1
  Γ₀ : B.Γ₀ = ⊥
  tr : ∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (B.W γ) = ch τ

structure IsBK (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V) : Prop where
  ι : ∀ γ v, mt ((B.ι γ).1 v) = (mt γ).map (lmap (cv v) Δ)
  U : B.U = D.UZ
  ω : ∀ (u : B.U) (z : Par F) (s : ∀ v : Pl F, DX (cv v Δ)), (∀ v, IsScal (z v) (s v) ∧ (s v)⁻¹ * u.1.1 v ∈ D.J2v v) →
    (B.ω u : ℂ) = ∏ᶠ v, (D.χ v (z v) : ℂ)
  Γ₀ : B.Γ₀ = ZD Δ
  tr : ∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) →
    LinearMap.trace ℂ V (B.W g) = ch τ

end Dat

end Global

example : SigData (K := ℚ) (-1) := ⟨∅, ⊤, ⊤, ⊤, 0, 0, 0, 1, 1, 1⟩

end UpperTheory.V.Z.Sym.Glob
