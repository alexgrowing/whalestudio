import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

def comb (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (z : X) (q : N.ι)
    (j : Fin mB) : X.presheaf.stalk z :=
  ∑ i, gs p z ⊤ (c i j) * gs φ z (N.U q) ((a i).f q)

def Generates (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q, φ z ∈ N.U q → ∃ j, IsUnit (comb a φ p c z q j)

def Proport (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (Ψ : X ⟶ B₀)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q k, φ z ∈ N.U q → Ψ z ∈ H.U k → ∀ j j',
    gs Ψ z (H.U k) ((b j).f k) * comb a φ p c z q j' = gs Ψ z (H.U k) ((b j').f k) * comb a φ p c z q j

def gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (z : X) : R →+* X.presheaf.stalk z :=
  (X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def Kills {R : Type} [CommRing R] (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (F : MvPolynomial (Fin mB) R) : Prop :=
  ∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0

def FormsOK {R : Type} [CommRing R] (a : Fin mA → LB.Sec N) (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀)
    (p : X ⟶ T) (t : T ⟶ Sp R) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin mB) R), F.IsHomogeneous d → Kills fB b F →
    ∀ z q, φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0

def IsVal {S : Scheme.{0}} (e : S ⟶ A₀) (u : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ) (s : LB.Sec N) (α : Γ(S, ⊤)) :
    Prop :=
  ∀ z q, e z ∈ N.U q → gs e z (N.U q) (s.f q) = gs (𝟙 S) z ⊤ α * (u z q).val

def Normal {S : Scheme.{0}} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤)) (α : Fin mA → Γ(S, ⊤)) (β : Fin mB → Γ(S, ⊤)) :
    Prop :=
  ∀ j, t.appTop (β j) = ∑ i, c i j * t.appTop (α i)

def θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A.left ⟶ (topS Rg ⊗ A).left :=
  (lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)).left

theorem θ_snd {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ (snd (topS Rg) A).left = 𝟙 A.left := by
  rw [θ, ← Over.comp_left, lift_snd]; rfl

abbrev fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : (topS Rg ⊗ A).left ⟶ Sp Rg := (topS Rg ⊗ A).hom

theorem coord_comp {Rg : Type} [CommRing Rg] {X' : Scheme.{0}} {n : ℕ} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin n) Rg)) (i : Fin n) : coord (h ≫ g) i = h.appTop (coord g i) := by
  rfl

def uFr {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (z : (𝟙_ (Over (Sp Rg))).left) (q : (LPow A L (k : ℤ) (topS Rg)).ι) :
    ((𝟙_ (Over (Sp Rg))).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 _) z _ (eA.s fun _ => q 0)) ^ k

end GlobalTheory.HomFixUniv
