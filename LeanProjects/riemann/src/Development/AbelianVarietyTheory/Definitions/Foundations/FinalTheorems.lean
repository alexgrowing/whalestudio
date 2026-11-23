import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

abbrev Pl : Type := HeightOneSpectrum (𝓞 ℚ)

abbrev R2 (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Type := G ℚ Ω →* GL (Fin 2) (Qbar l)

abbrev mat (W : R2 Ω l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (Qbar l) := (W s : Matrix (Fin 2) (Fin 2) (Qbar l))

abbrev eps (l : ℕ) [Fact l.Prime] (s : G ℚ Ω) : Qbar l := (cycBar ℚ Ω l s : Qbar l)

def dt (W : R2 Ω l) : G ℚ Ω →* (Qbar l)ˣ := Matrix.GeneralLinearGroup.det.comp W

def dual1 (W : R2 Ω l) : R2 Ω l := tw W (cycBar ℚ Ω l * (dt W)⁻¹)

def om (x y : Fin 2 → Qbar l) : Qbar l := x 0 * y 1 - x 1 * y 0

def H0g (W : R2 Ω l) : Subgroup (G ℚ Ω) := (cycBar ℚ Ω l).ker ⊓ (dt W).ker

def N0g (W : R2 Ω l) : Subgroup (G ℚ Ω) := (cycBar ℚ Ω l).ker ⊓ W.ker

def IsConj (s : G ℚ Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (s x) = starRingEnd ℂ (j x)

def OverL (l : ℕ) (A : ValuationSubring Ω) : Prop := ∃ v : Pl, IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal

structure admitted (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) : Prop where
  cont : Continuous W
  det2 : dt W ^ 2 = 1
  odd : ∀ s, IsConj s → dt W s = -1
  irr : IsIrr (W.comp (H0g W).subtype)
  away : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M W
  modular : ∃ (f : Newform (2 * e + 1)) (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M ∧ KillsMu M φ ∧
    f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * φ))
  flag : ∃ (A : ValuationSubring Ω) (χ : G ℚ Ω →* (Qbar l)ˣ) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    OverL l A ∧ KillsMu l χ ∧ IsFlagOn W (Dec (F := ℚ) A) κ ∧ Ine (F := ℚ) A ≤ (dt W).ker ∧
    ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) * χ s ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ)) * χ s

def VanishOrd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : R2 Ω l, admitted ι e W → BlochKatoSelmerVanishes l (Loc.colRep W)

structure Nf (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) : Prop where
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  cont : Continuous W
  int : ∃ c : Coef l, ∀ s i j, mat W s i j ∈ c.O
  above : ContainsAbove S l
  unr : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker
  det2 : dt W ^ 2 = 1
  odd : ∀ s, IsConj s → dt W s = -1
  irr : IsIrr (W.comp (H0g W).subtype)
  atL : OverL l A
  upper : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0
  wt : ∃ m : ℕ, 1 ≤ m ∧ ∀ s ∈ Ine (F := ℚ) A, mat W s 0 0 ^ m = eps l s ^ (e * m)
  ne : ∃ s ∈ Dec (F := ℚ) A, mat W s 0 0 ≠ eps l s

def Unr (W : R2 Ω l) (c : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧
    ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, c s = mat W s *ᵥ x - x

def Gr (W : R2 Ω l) (A : ValuationSubring Ω) (c : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, c s 1 = mat W s 1 1 * x - x

def Triv (W : R2 Ω l) (A : ValuationSubring Ω) (c : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∃ x : Fin 2 → Qbar l, ∀ s ∈ Dec (F := ℚ) A, c s = mat W s *ᵥ x - x

def GrZero (W : R2 Ω l) (A : ValuationSubring Ω) : Prop :=
  ∀ c ∈ Z1 (Loc.colRep W), Unr W c → Gr W A c → c ∈ ReciprocityTheory.Gal.B1 (Loc.colRep W)

def StrZero (W : R2 Ω l) (A : ValuationSubring Ω) : Prop :=
  ∀ c ∈ Z1 (Loc.colRep W), Unr W c → Triv W A c → c ∈ ReciprocityTheory.Gal.B1 (Loc.colRep W)

def Cg (n : ℕ) (a b : Qbar l) : Prop := ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

def Cv (n : ℕ) (a b : Fin 2 → Qbar l) : Prop := ∀ i, Cg n (a i) (b i)

def Tame (c : Coef l) (W : R2 Ω l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl)
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) : Prop :=
  ∃ (Y : G ℚ Ω → ZMod (l ^ n) → Fin 2 → Qbar l) (P u : Qbar l) (b : Fin 2 → Qbar l),
    Continuous Y ∧ (∀ s x i, Y s x i ∈ c.O) ∧ P ∈ c.O ∧ ‖u‖ = 1 ∧ (∀ i, b i ∈ c.O) ∧
    (∀ s t x, Y (s * t) x = Y s x + mat W s *ᵥ Y t (x - (ψ s).toAdd)) ∧
    (∀ s, ∑ᶠ x, Y s x = P • y s + (mat W s *ᵥ b - b)) ∧
    (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det)) ∧
    ∀ q : Pl, q ≠ w → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧
      ∃ t : ZMod (l ^ n) → Fin 2 → Qbar l, (∀ x i, t x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ x, Y s x = mat W s *ᵥ t x - t x

def ES (W : R2 Ω l) (A : ValuationSubring Ω) : Prop :=
  ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), (∀ s i j, mat W s i j ∈ c.O) ∧ y ∈ Z1 (Loc.colRep W) ∧
    (∀ s i, y s i ∈ c.O) ∧ Unr W y ∧ ¬ Gr W A y ∧
    ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ

def FinalTheorems (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (g : Newform (2 * e + 1)) : Prop :=
  ¬ l ∣ g.M ∧ ‖ι.symm (g.a l)‖ = 1 ∧ ∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ))

structure Coc2 (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) : Prop where
  cont : Continuous fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2
  int : ∀ s t, ξ s t ∈ c.O
  coc : ∀ r s t, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)
  unr : ∀ s t, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cg n (ξ (s * a) (t * b)) (ξ s t)

def Cob2 (c : Coef l) (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) : Prop :=
  ∃ u : G ℚ Ω → Qbar l, ContinuousOn u H ∧ (∀ s, u s ∈ c.O) ∧
    ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ s t) (eps l s * u t - u (s * t) + u s)

def Coc1 (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ContinuousOn a H ∧ (∀ s i, a s i ∈ c.O) ∧ ∀ s ∈ H, ∀ t ∈ H, Cv n (a (s * t)) (a s + mat W s *ᵥ a t)

def Cob1 (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ H, Cv n (a s) (mat W s *ᵥ x - x)

def cup (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l) (s t : G ℚ Ω) : Qbar l := om (a s) (mat (dual1 W) s *ᵥ b t)

def ht (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (s : G ℚ Ω) : Qbar l :=
  (mat W s - 1).det * u s - om ((mat W s - 1).adjugate *ᵥ y s) (z s)

structure Inp0 : Prop extends U3.CohInp where
  lemM : Alg.LemmaM
  lemM' : Alg.LemmaM'
  lemP : Alg.LemmaP
  adK : Af.AdVanishK
  adQ : Af.AdVanishQ
  newAut : Af.NewformAut
  number : Af.CongruenceNumberRankThree

end GlobalTheory.Ord2

end
