import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratV {n : ℕ} (x : Fin n → D.host.E) : Fin n → AE D := fun i => incA D (x i)

def subOne (B : HSp D) (g : GA D B) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  ((matHom B g).1 : Matrix (Fin B.rank) (Fin B.rank) (AE D)) - 1

def NFlag (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) : Subgroup (GA D B) :=
  Subgroup.closure {g |
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne B g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
    ∀ x : Fin B.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).mulVec x = 0 →
      ∃ a : Fin ρ → AE D, (subOne B g).mulVec (ratV x) = (e.map (incA D)).mulVec a}

def NFlagQ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) : Subgroup (NFlag B e) :=
  (GQ B).subgroupOf (NFlag B e)

structure BesDat (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  ρ : ℕ
  codim : A.rank + 2 * ρ + 1 = B.rank

  e : Matrix (Fin B.rank) (Fin ρ) D.host.E
  e_iso : IsIsoSub B e
  e_perp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * e = 0

  z : Fin B.rank → D.host.E
  z_perpA : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).mulVec z = 0
  z_perpE : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram).mulVec z = 0
  z_ne : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram z z ≠ 0

  c : Fin ρ → D.host.E
  c_ne : ∀ i, c i ≠ 0

  y : GfC B

def IsBesVal (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B)
    (v : ℂ) : Prop :=
  ∃ (a : Fin d.ρ → Fin d.ρ → AE D) (b : Fin d.ρ → AE D),
    (∀ i, (subOne B n).mulVec (ratV fun k => d.e k i) = (d.e.map (incA D)).mulVec (a i)) ∧
    (subOne B n).mulVec (ratV d.z) = (d.e.map (incA D)).mulVec b ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D)
      ((∑ i : Fin d.ρ, ∑ j : Fin d.ρ, if j.1 = i.1 + 1 then incA D (d.c i) * a j i else 0) +
        ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then incA D (d.c i) * b i else 0))

open Classical in

def besChar (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ℂ :=
  if h : ∃ v, IsBesVal ψ d n v then h.choose else 1

def IsAniso (A : HSp D) : Prop := ∀ (r : ℕ) (C : Matrix (Fin A.rank) (Fin r) D.host.E), ¬ IsIsoFrame A C

structure BesselTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) where

  dat : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), Odd (B.rank - A.rank) → X.Pos A B ι → BesDat A B ι

  dat_y : ∀ A B ι h p, ((dat A B ι h p).y : GA D B) = 1

  besC : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), X.Pos A B ι → ℝ
  besC_pos : ∀ A B ι p, 0 < besC A B ι p

  bper : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ho : Odd (B.rank - A.rank)), A.rank ≤ B.rank → A.SigOK →
    HSpace.IsIsomEmb A B ι → ∀ (p : X.Pos A B ι), (∃ u, HEq p (X.posSym u)) → ∀ (sF : X.FJd A B ι),
    ∀ μ 𝓕, IsVolPair D A μ 𝓕 →
    ∀ (μN : Measure (NFlag B (dat A B ι ho p).e)) (𝓕N : Set (NFlag B (dat A B ι ho p).e)), μN.IsHaarMeasure →
      IsFundamentalDomain (NFlagQ B (dat A B ι ho p).e) 𝓕N μN → μN 𝓕N = 1 →
    ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
    ∀ (φ : X.AF A) (F : X.cusp B), IsAniso A ∨ φ ∈ X.cusp A →
      X.Bper A B ι p sF φ F = ((besC A B ι p * T.petC A : ℝ) : ℂ) *
        ∫ h in 𝓕, ∫ n in 𝓕N, star (T.ev A φ h) *
          T.ev B (F : X.AF B) ((n : GA D B) * s h * ((dat A B ι ho p).y : GA D B)) *
          star (besChar Wl.ψ (dat A B ι ho p) (n : GA D B)) ∂μN ∂μ

  besC_one : ∀ A B ι p, besC A B ι p = 1

end Formalism.L2.Theta

end
