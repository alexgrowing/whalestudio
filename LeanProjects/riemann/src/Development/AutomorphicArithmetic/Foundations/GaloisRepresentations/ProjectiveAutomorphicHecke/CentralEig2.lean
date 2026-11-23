import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CompLocOfApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev GLw (n : ℕ) (w : Plc E) : Type := GL (Fin n) (w.adicCompletion E)

abbrev diagF (E : Type) [Field E] [NumberField E] : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom

abbrev sgl (w : Plc E) : (w.adicCompletion E)ˣ →* (Af E)ˣ := Units.map (Neutral.B1.finiteSingle E w)

def HasType (U : Submodule ℂ (UA E n → ℂ)) (w : Plc E) (J : Subgroup (GLw n w)) (χ : J →* ℂˣ) : Prop :=
  ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU n w, ∀ h : cLoc w x ∈ J, RU E n x φ = ((χ ⟨cLoc w x, h⟩ : ℂˣ) : ℂ) • φ

structure Shape (Up : Plc E → Prop) (w₀ : Plc E) (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : Prop where
  mem : w₀ ∈ S
  opn : ∀ w ∈ S, IsOpen (Kw w : Set (GLw n w))
  cpt : ∀ w ∈ S, IsCompact (Kw w : Set (GLw n w))
  le : ∀ w ∈ S, w ≠ w₀ → Kw w ≤ KGL w n
  up : ∀ w ∈ S, IsSplitAt w → Up w ∧ cj w ∉ S

structure IsZeta (x : E) (ζ : (Af E)ˣ →* GUf E n) : Prop where
  cont : Continuous ζ
  central : ∀ y g, ζ y * g = g * ζ y
  onRat : ∀ k : Eˣ, ∃ (γ : Gam0 E n) (t : Eˣ), ζ (diagF E k) = rat γ ∧ γ.1.1.val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) ∧
    (∀ φ : E →+* ℂ, φ t = ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = -φ x), φ' k) ∧
    ((γ.1.2 : ℚ) : ℂ) = ∏ φ' : E →+* ℂ, φ' k
  off : ∀ (w : Plc E) y u, ¬ SameK x (cj u) w → comp u (ζ (sgl w y)) = 1
  unit : ∀ (w : Plc E) y, IsUnitAt w y → ∀ u, comp u (ζ (sgl w y)) ∈ KGL u n
  unif : ∀ (w : Plc E) y, IsUnifAt w y → ¬ SameK x (cj w) w → ∀ u, SameK x (cj u) w → ∃ t : u.adicCompletion E,
    (comp u (ζ (sgl w y))).val = t • (1 : Matrix (Fin n) (Fin n) _) ∧
      Valued.v t = Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E)

structure IsForm (U : Submodule ℂ (UA E n → ℂ)) (W : Wt E n) (j : ℤ) (w₀ : Plc E) (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ)
    (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) : Prop where
  ne : Φ ≠ 0
  left : ∀ γ g, Φ (rat γ * g) = xi0 W j γ (Φ g)
  right : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ J, ∀ g, Φ (g * k) = ((χ ⟨comp w₀ k, h⟩ : ℂˣ) : ℂ) • Φ g
  sat : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU U w B →
    IsSatVecGL w ((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)) Φ B

structure IsKap (x : E) (W : Wt E n) (j : ℤ) (S : Finset (Plc E)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E) : Prop where
  alg : IsAlgPos κ (mOf x W j)
  unr : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → κ.UnrAt w
  cen : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → ¬ SameK x (cj w) w → ∀ z, IsCen x w z →
    ∀ g, Φ (g * z) = ((κ.val w : ℂˣ) : ℂ)⁻¹ • Φ g

end Defs

def SeedGU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (π : AutSub E n) (W : Wt E n), π.finPart W ≠ ⊥ → ∀ (j : ℤ) (Up : Plc E → Prop), (∀ w, IsSplitAt w → Up w ∨ Up (cj w)) →
  ∀ w₀ : Plc E, IsSplitAt w₀ → Up w₀ → ∀ (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ), IsOpen (J : Set (GLw n w₀)) →
    IsCompact (J : Set (GLw n w₀)) → HasType π.V w₀ J χ →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E),
    Shape Up w₀ S Kw ∧ Kw w₀ = J ∧ IsOpen {k : J | χ k = 1} ∧ IsOpen (lev S Kw : Set (GUf E n)) ∧ IsCompact (lev S Kw : Set (GUf E n)) ∧
    (∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU π.V w B) → w ∉ S ∧ cj w ∉ S) ∧
    IsForm π.V W j w₀ J χ S Kw Φ ∧ IsKap x W j S Φ κ

def CentralEig2 : Prop := ∀ (Γ H Z V : Type) [Group Γ] [Group H] [Group Z] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H)
  (K : Subgroup H) (ξ : Representation ℂ Γ V) (ζ : Z →* H), (∀ z g, ζ z * g = g * ζ z) →
  ∀ M : Submodule ℂ (H → V), FiniteDimensional ℂ M → M ≤ forms ι K ξ → M ≠ ⊥ → (∀ Φ ∈ M, ∀ z, (fun g => Φ (g * ζ z)) ∈ M) →
  ∃ Φ ∈ M, Φ ≠ 0 ∧ ∃ ψ : Z →* ℂˣ, CentralChar ι K ξ ζ ψ Φ

def ExtEig2 : Prop := ∀ (Γ H A Z V : Type) [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H)
  (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (ζ : Z →* H), (∀ z g, ζ z * g = g * ζ z) →
  (∃ s : Finset Z, ∀ z, ∃ t ∈ s, ∃ z₀ z₁, z = t * z₀ * z₁ ∧ ζ z₀ ∈ K ∧ ∃ (γ : Γ) (a : ℂ), ζ z₁ = ι γ ∧ ∀ v, ξ γ v = a • v) →
  ∀ φ : H → V, KerForm ι K ξ c φ → (∃ u, c u = 1 ∧ φ u ≠ 0) →
  ∀ (J : Type) (r : J → H →₀ ℂ) (θ : J → ℂ), (∀ j, ∀ u ∈ (r j).support, c u = 1) →
    (∀ j, ∀ Φ ∈ forms ι K ξ, rop (r j) Φ ∈ forms ι K ξ) → (∀ j u, c u = 1 → rop (r j) φ u = θ j • φ u) →
  ∃ Φ ∈ forms ι K ξ, Φ ≠ 0 ∧ (∀ j, rop (r j) Φ = θ j • Φ) ∧ ∃ ψ : Z →* ℂˣ, CentralChar ι K ξ ζ ψ Φ

def LocAdj : Prop := ∀ (G V X : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
  (ρ : Representation ℂ G V) (π : Submodule ℂ V), (∀ g, ∀ φ ∈ π, ρ g φ ∈ π) →
  (∀ N ≤ π, (∀ g, ∀ φ ∈ N, ρ g φ ∈ N) → N = ⊥ ∨ N = π) → ∀ H C : Subgroup G, C ≤ H →
  (∀ g, ∃ h ∈ H, ∃ c, (∀ y ∈ H, c * y = y * c) ∧ g = h * c) →
  (∀ φ ∈ π, ∃ N : Subgroup C, N.FiniteIndex ∧ ∀ k ∈ N, ρ (k : G) φ = φ) →
  ∀ χ : C →* ℂˣ, (∃ φ ∈ π, φ ≠ 0 ∧ ∀ k : C, ρ (k : G) φ = (χ k : ℂ) • φ) →
  ∀ f : X →ₗ[ℂ] V, f ≠ 0 → (∀ v, f v ∈ π) →
  ∃ r : G →₀ ℂ, (∀ g ∈ r.support, g ∈ H) ∧ (∃ v, (r.sum fun g a => a • ρ g (f v)) ≠ 0) ∧
    ∀ (k : C) v, ρ (k : G) (r.sum fun g a => a • ρ g (f v)) = (χ k : ℂ) • r.sum fun g a => a • ρ g (f v)

def RootsAlg : Prop := ∀ (q n : ℕ), 0 < q → ∀ (B : Multiset ℂˣ), B.card = n → ∀ (a c : ℂ) (ϑ : ℕ → ℂ),
  (∀ i ≤ n, ϑ i = a * satEig q n B i * c ^ i) →
  ϑ 0 = a ∧ crystallineComparison.heckePol q n ϑ = Polynomial.C a * crystallineComparison.rootPol ((UpperTheory.V.Af.algSat n q B).map (· * c))

def FinToHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] (ψ : (Af E)ˣ →* ℂˣ) (m : (E →+* ℂ) → ℤ), IsOpen (ψ.ker : Set (Af E)ˣ) →
  (∀ k : Eˣ, (ψ (diagF E k) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ m φ)⁻¹) →
  ∃ κ : HChar E, IsAlgPos κ m ∧ ∀ (w : Plc E) y, κ.loc w y = ψ (sgl w y)

def ClassFin : Prop := ∀ (E : Type) [Field E] [NumberField E] (O : Subgroup (Af E)ˣ), IsOpen (O : Set (Af E)ˣ) →
  ∃ s : Finset (Af E)ˣ, ∀ y, ∃ t ∈ s, ∃ o ∈ O, ∃ k : Eˣ, y = t * o * diagF E k

def ZetaEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∃ ζ : (Af E)ˣ →* GUf E n, IsZeta x ζ

def XiScalar : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (j : ℤ) (y : GL (Fin n) E) (s : ℚˣ) (t : Eˣ),
  y.val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) → ∀ v, xi W j (y, s) v =
    (((s : ℚ) : ℂ) ^ j * ∏ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i)) • v

def XiZeta : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (j : ℤ) (x : E) (ζ : (Af E)ˣ →* GUf E n),
  IsZeta x ζ → ∀ k : Eˣ, ∃ γ : Gam0 E n, ζ (diagF E k) = rat γ ∧ ∀ v, xi0 W j γ v = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ) • v

def IntConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (k : GUf E n) (w : Plc E),
  sim k ∈ ZU → comp w k ∈ KGL w n → comp (cj w) k ∈ KGL (cj w) n

def IntSim : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ k : GUf E n,
  (∀ w, comp w k ∈ KGL w n) → sim k ∈ ZU

def OfUBij : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  Function.Injective (ofU : finU E n → GUf E n) ∧ ∀ g : GUf E n, sim g = 1 → ∃ u, ofU u = g

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w),
  (∀ k : GUf E n, comp w k = 1 → ∀ y, k * loc hw y = loc hw y * k) ∧ (∀ u, Apart u w ↔ u ≠ w ∧ u ≠ cj w) ∧
    cj w ≠ w ∧ IsSplitAt (cj w) ∧ cj (cj w) = w ∧ locU (E := E) n (cj w) = locU n w

def LocMem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Finset (Plc E))
  (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (w : Plc E) (hw : IsSplitAt w), cj w ∉ S → ∀ y : GLw n w,
  (w ∈ S → y ∈ Kw w → loc hw y ∈ lev S Kw) ∧ (w ∉ S → y ∈ KGL w n → loc hw y ∈ lev S Kw)

def LevOpen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Finset (Plc E))
  (Kw : ∀ w : Plc E, Subgroup (GLw n w)), (∀ w ∈ S, IsOpen (Kw w : Set (GLw n w))) → IsOpen (lev S Kw : Set (GUf E n))

def IntCompact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  IsCompact (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))

def LevCompact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Up : Plc E → Prop) (w₀ : Plc E), IsSplitAt w₀ →
  ∀ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), Shape Up w₀ S Kw → IsCompact (lev S Kw : Set (GUf E n))

def Nbhd2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (O : Subgroup (finU E n)), IsOpen (O : Set (finU E n)) →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ KGL w n) ∧
    ∀ u : finU E n, (∀ w, cLoc w u.1 ∈ KGL w n) → (∀ w ∈ S, cLoc w u.1 ∈ Kw w) → u ∈ O

def NbhdU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (O : Subgroup (finU E n)), IsOpen (O : Set (finU E n)) →
  ∀ Up : Plc E → Prop, (∀ w, IsSplitAt w → Up w ∨ Up (cj w)) → ∀ w₀ : Plc E, IsSplitAt w₀ → Up w₀ →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), Shape Up w₀ S Kw ∧ ∀ u : finU E n, ofU u ∈ lev S Kw → u ∈ O

def SphType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : Plc E), IsSplitAt w →
  ((∃ B, SatU π.V w B) → HasType π.V w (KGL w n) 1 ∧ HasType π.V (cj w) (KGL (cj w) n) 1) ∧
  ∀ (J : Subgroup (GLw n w)) (χ : J →* ℂˣ), HasType π.V w J χ → IsOpen {k : J | χ k = 1}

def StepAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (f : algForms W),
  f ∈ π.finPart W → f ≠ 0 → ∀ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (w : Plc E), IsSplitAt w → w ∈ S → cj w ∉ S →
  (∀ u : finU E n, ofU u ∈ lev S Kw → algRep W u f = f) →
  ∀ (J : Subgroup (GLw n w)) (χ : J →* ℂˣ), IsCompact (J : Set (GLw n w)) → HasType π.V w J χ →
  ∃ f' ∈ π.finPart W, f' ≠ 0 ∧ ∀ u : finU E n, ofU u ∈ lev S (Function.update Kw w J) → ∀ h : cLoc w u.1 ∈ J,
    algRep W u f' = ((χ ⟨cLoc w u.1, h⟩ : ℂˣ) : ℂ) • f'

def VecU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n), π.finPart W ≠ ⊥ →
  ∀ Up : Plc E → Prop, (∀ w, IsSplitAt w → Up w ∨ Up (cj w)) → ∀ w₀ : Plc E, IsSplitAt w₀ → Up w₀ →
  ∀ (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ), IsOpen (J : Set (GLw n w₀)) → IsCompact (J : Set (GLw n w₀)) → HasType π.V w₀ J χ →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), Shape Up w₀ S Kw ∧ Kw w₀ = J ∧
    (∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU π.V w B) → w ∉ S ∧ cj w ∉ S) ∧
    ∃ f ∈ π.finPart W, f ≠ 0 ∧ ∀ u : finU E n, ofU u ∈ lev S Kw → ∀ h : cLoc w₀ u.1 ∈ J,
      algRep W u f = ((χ ⟨cLoc w₀ u.1, h⟩ : ℂˣ) : ℂ) • f

def SatVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (f : algForms W),
  f ∈ π.finPart W → f ≠ 0 → ∀ (w : Plc E) (hw : IsSplitAt w), (∀ k ∈ KGL w n, algRep W (locF hw k) f = f) →
  ∀ B, SatU π.V w B → IsSatVecGL w ((algRep W).comp (locF hw)) f B

def KerFormU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (j : ℤ) (f : algForms W), f ≠ 0 →
  ∀ K : Subgroup (GUf E n), (∀ k ∈ K, sim k ∈ ZU) → (∀ u : finU E n, ofU u ∈ K → algRep W u f = f) →
  ∃ φ : GUf E n → Module.Dual ℂ W.Sp, KerForm rat K (xi0 W j) sim φ ∧ (∀ u : finU E n, φ (ofU u) = algForms.val f u.1) ∧
    ∃ g, sim g = 1 ∧ φ g ≠ 0

def HeckePres : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ i : ℕ, ∃ R : Finset (GLw n w),
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
    heckeVec ρ (KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ i) v = ∑ g ∈ R, ρ g v) ∧
  ∀ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), w ∉ S → cj w ∉ S →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (Gam0 E n) V), ∀ Φ ∈ forms rat (lev S Kw) ξ,
      (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ

def FormGU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : E) (ζ : (Af E)ˣ →* GUf E n), IsZeta x ζ →
  ∀ (π : AutSub E n) (W : Wt E n) (j : ℤ) (Up : Plc E → Prop) (w₀ : Plc E), IsSplitAt w₀ →
  ∀ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), Shape Up w₀ S Kw → ∀ χ : Kw w₀ →* ℂˣ, IsOpen {k : Kw w₀ | χ k = 1} →
  ∀ f ∈ π.finPart W, f ≠ 0 → (∀ u : finU E n, ofU u ∈ lev S Kw → ∀ h : cLoc w₀ u.1 ∈ Kw w₀,
      algRep W u f = ((χ ⟨cLoc w₀ u.1, h⟩ : ℂˣ) : ℂ) • f) →
  ∃ (Φ : GUf E n → Module.Dual ℂ W.Sp) (ψ : (Af E)ˣ →* ℂˣ), IsForm π.V W j w₀ (Kw w₀) χ S Kw Φ ∧
    ∀ y g, Φ (g * ζ y) = (ψ y : ℂ) • Φ g

def KapOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (x : E) (ζ : (Af E)ˣ →* GUf E n), IsZeta x ζ →
  ∀ (U : Submodule ℂ (UA E n → ℂ)) (W : Wt E n) (j : ℤ) (Up : Plc E → Prop) (w₀ : Plc E)
    (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)), Shape Up w₀ S Kw → ∀ χ : Kw w₀ →* ℂˣ, IsOpen {k : Kw w₀ | χ k = 1} →
  ∀ (Φ : GUf E n → Module.Dual ℂ W.Sp) (ψ : (Af E)ˣ →* ℂˣ), IsForm U W j w₀ (Kw w₀) χ S Kw Φ →
    (∀ y g, Φ (g * ζ y) = (ψ y : ℂ) • Φ g) → ∃ κ : HChar E, IsKap x W j S Φ κ

theorem seedGU_of (h1 : ZetaEx) (h2 : VecU) (h3 : SphType) (h4 : FormGU) (h5 : KapOf) (h6 : LevOpen) (h7 : LevCompact) : SeedGU := by
  intro E _ _ _ n hn d x hd hx π W hW j Up hUp w₀ hw₀ hu J χ hJo hJc hT
  obtain ⟨ζ, hζ⟩ := h1 E n d x hd hx
  obtain ⟨S, Kw, hS, rfl, hsph, f, hf, hf0, hfix⟩ := h2 E n π W hW Up hUp w₀ hw₀ hu J χ hJo hJc hT
  have hχ := (h3 E n π w₀ hw₀).2 _ χ hT
  obtain ⟨Φ, ψ, hΦ, hψ⟩ := h4 E n x ζ hζ π W j Up w₀ hw₀ S Kw hS χ hχ f hf hf0 hfix
  obtain ⟨κ, hκ⟩ := h5 E n hn x ζ hζ π.V W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ
  exact ⟨S, Kw, Φ, κ, hS, rfl, hχ, h6 E n S Kw hS.opn, h7 E n Up w₀ hw₀ S Kw hS, hsph, hΦ, hκ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
