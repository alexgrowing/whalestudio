import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

instance {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalRing ↥c.O := c.dvr.toIsLocalRing

instance {l : ℕ} [Fact l.Prime] (c : Coef l) : IsNoetherianRing ↥c.O :=
  @PrincipalIdealRing.isNoetherianRing _ _ c.dvr.toIsPrincipalIdealRing

instance {l : ℕ} [Fact l.Prime] (c : Coef l) : IsAdicComplete (IsLocalRing.maximalIdeal ↥c.O) ↥c.O := by
  have h := dvrFacts l c.O
  obtain ⟨-, -, -, h, -⟩ := h
  exact h

section Comp

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι]
  {rbar : Γ →* Matrix ι ι (ResidueField O)}

def OnComp (P : Cond O rbar) (ρ₀ : Γ →* Matrix ι ι O) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : Lift O rbar R) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (_ : IsDomain B) (ρ : Lift O rbar B),
    P B ρ ∧ (∃ x : B →ₐ[O] O, ∀ g a b, x (ρ.hom g a b) = ρ₀ g a b) ∧ ∃ y : B →ₐ[O] R, ρ.map y = r

end Comp

structure Raw (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) where
  S : Finset ℕ
  e : ℕ
  ψ : G ℚ Ω →* c.Oˣ
  ξ : G ℚ Ω →* c.Oˣ

  om : G ℚ Ω →* c.Oˣ

  cc : G ℚ Ω

  pl : ℕ → ValuationSubring Ω

  sg : ℕ → G ℚ Ω

  ph : G ℚ Ω
  g0 : G ℚ Ω

  s0 : Dec (F := ℚ) (pl l)

namespace Raw

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

def Psi : G ℚ Ω →* c.Oˣ := Chr.Psi l D.e D.ψ

def al : G ℚ Ω →* c.Oˣ := chiO ℚ Ω l c.O * D.om⁻¹ * D.ξ

def be : G ℚ Ω →* c.Oˣ := D.Psi * D.al⁻¹

def th : G ℚ Ω →* c.Oˣ := D.al * D.Psi

def ps : Fin 4 → G ℚ Ω →* c.Oˣ := ![D.th, D.Psi, D.al, 1]

def wts4 : Fin 4 → ℕ := ![D.e + 1, D.e, 1, 0]

def r0 : G ℚ Ω →* M4 c.O := diagRep D.ps

def rbar : G ℚ Ω →* M4 (ResidueField c.O) := mapRep (residue c.O) D.r0

abbrev Gp (p : ℕ) : Subgroup (G ℚ Ω) := Dec (F := ℚ) (D.pl p)

abbrev Ip (p : ℕ) : Subgroup (G ℚ Ω) := Ine (F := ℚ) (D.pl p)

open Classical in

def Sb : Finset ℕ := D.S.filter fun p => p ≠ l ∧ l ∣ Nat.card ((D.Ip p).map D.ψ)

def T : Finset ℕ := insert l D.Sb

def Away (U : Finset ℕ) (A : ValuationSubring Ω) : Prop := ∀ p ∈ U, ¬ A.valuation (p : Ω) < 1

abbrev bar (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) : ResidueField c.O := residue c.O (γ g : c.O)

def UnrT {M : Type} (f : G ℚ Ω → M) (a : M) : Prop :=
  ∀ A : ValuationSubring Ω, Away D.T A → ∀ g ∈ Ine (F := ℚ) A, D.rbar g = 1 → f g = a

def XVan (γ : G ℚ Ω →* c.Oˣ) : Prop :=
  ∀ z : G ℚ Ω → ResidueField c.O, IsLocallyConstant z → (∀ g h, z (g * h) = z g + bar γ g * z h) → D.UnrT z 0 →
    (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = bar γ g * m - m) → ∃ m, ∀ g, z g = bar γ g * m - m

structure Good : Prop where
  l_odd : l ≠ 2
  S_prime : ∀ p ∈ D.S, p.Prime
  two_mem : 2 ∈ D.S
  l_mem : l ∈ D.S
  two_le : 2 ≤ D.e
  pl_over : ∀ p : ℕ, p.Prime → (D.pl p).valuation (p : Ω) < 1
  isCC : IsCC D.cc
  psi_open : IsOpen (D.ψ.ker : Set (G ℚ Ω))
  psi_unr : ∀ A, Away D.S A → Ine (F := ℚ) A ≤ D.ψ.ker
  Psi_even : D.Psi D.cc = 1
  om_pow : D.om ^ (l - 1) = 1
  om_bar : ∀ g, bar D.om g = bar (chiO ℚ Ω l c.O) g
  xi_open : IsOpen (D.ξ.ker : Set (G ℚ Ω))
  xi_ord : ∃ m : ℕ, l.Coprime m ∧ D.ξ ^ m = 1
  xi_unr : ∀ A, Away D.S A → Ine (F := ℚ) A ≤ D.ξ.ker
  xi_unrT : ∀ v ∈ D.T, D.Ip v ≤ D.ξ.ker
  xi_odd : D.ξ D.cc = -1
  sg_frob : ∀ v ∈ D.T, IsFrob (D.pl v) v (D.sg v)
  sg_cyc : cycZ ℚ Ω l (D.sg l) = 1
  condD : ∀ v ∈ D.T, ∀ i : ℤ, bar (D.ξ * D.Psi ^ i) (D.sg v) ≠ 1
  xvan : ∀ γ ∈ [D.al, D.be, D.th], D.XVan γ ∧ D.XVan γ⁻¹
  ph_lim : Filter.Tendsto (fun n : ℕ => D.sg l ^ l ^ n.factorial) Filter.atTop (nhds D.ph)
  genElt_alpha : bar D.al D.g0 ≠ 1
  genElt_Psi : bar D.Psi D.g0 ≠ 1
  decompSigma_mem : (D.s0 : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker
  decompSigma_ord : ¬ IsOfFinOrder (cycZ ℚ Ω l D.s0)

abbrev rbarAt (v : ℕ) : D.Gp v →* M4 (ResidueField c.O) := D.rbar.comp (D.Gp v).subtype

abbrev r0At (v : ℕ) : D.Gp v →* M4 c.O := D.r0.comp (D.Gp v).subtype

def condL : Cond c.O (D.rbarAt l) := fun R _ _ _ ρ =>
  (∀ g : D.Gp l, IsGSp (algebraMap c.O R (D.th g)) (ρ.hom g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 ρ.hom

def condP (p : ℕ) : Cond c.O (D.rbarAt p) := fun R _ _ _ ρ =>
  (∀ g : D.Gp p, IsGSp (algebraMap c.O R (D.th g)) (ρ.hom g)) ∧
    ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → ρ.hom g = 1

section Ring

variable {R : Type} [CommRing R] [Algebra c.O R]

def hEl (r : G ℚ Ω →* M4 R) : M4 R := r D.g0 + algebraMap c.O R (D.th D.g0) • r D.g0⁻¹

def Nrm (r : G ℚ Ω →* M4 R) : Prop := IsBlock (r D.ph) ∧ D.hEl r 0 2 = 0 ∧ D.hEl r 2 0 = 0

def Mult (r : G ℚ Ω →* M4 R) : Prop := ∀ g, IsGSp (algebraMap c.O R (D.th g)) (r g)

variable [IsCO c.O R]

abbrev loc (r : Lift c.O D.rbar R) (v : ℕ) : Lift c.O (D.rbarAt v) R := r.comap (D.Gp v).subtype continuous_subtype_val

structure IsEq (r : Lift c.O D.rbar R) : Prop where
  mult : D.Mult r.hom
  unr : D.UnrT r.hom 1
  nrm : D.Nrm r.hom
  atL : D.condL R (D.loc r l)
  atP : ∀ p ∈ D.Sb, D.condP p R (D.loc r p)

structure IsPt (r : Lift c.O D.rbar R) : Prop where
  mult : D.Mult r.hom
  unr : D.UnrT r.hom 1
  nrm : D.Nrm r.hom
  atL : OnComp D.condL (D.r0At l) (D.loc r l)
  atP : ∀ p ∈ D.Sb, OnComp (D.condP p) (D.r0At p) (D.loc r p)

end Ring

def PtIn (K : Type) [CommRing K] [Algebra c.O K] (r : G ℚ Ω →* M4 K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R) (y : R →ₐ[c.O] K),
    D.IsPt ρ ∧ r = mapRep (y : R →+* K) ρ.hom

abbrev EPt (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := D.PtIn (PadicAlgCl l) r

def r0E : G ℚ Ω →* M4 (PadicAlgCl l) := mapRep (algebraMap c.O (PadicAlgCl l)) D.r0

def Fin0 : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), D.IsPt ρ →
    Module.Finite c.O (Algebra.adjoin c.O (mono ρ.hom 0))

def NoEnd : Prop :=
  ∀ r, D.EPt r → (∀ g, IsBlock (r g)) →
    Submodule.span (PadicAlgCl l) (Set.range fun g => (r g).submatrix ixA ixA) ≠ ⊤

def AllIrr (P : (G ℚ Ω →* M4 (PadicAlgCl l)) → Prop) : Prop := ∀ r, D.EPt r → Irr r → P r

def RigidAt (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop :=
  ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) →
    ∃ X ∈ sp4 (PadicAlgCl l), ∀ g i j, (r' g i j).snd = (X * r g - r g * X) i j

def aVal (g : G ℚ Ω) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : PadicAlgCl l := (r g).trace - (D.r0E g).trace

def sha : ℕ∞ := Chr.VS l (∏ p ∈ D.S, p) D.e D.ψ

def Ineq (g : G ℚ Ω) : Prop :=
  D.sha ≠ ⊤ ∧ ∃ Xi : Finset (G ℚ Ω →* M4 (PadicAlgCl l)), (∀ r ∈ Xi, D.EPt r ∧ Irr r) ∧
    (∀ r ∈ Xi, ∀ r' ∈ Xi, IsConj4 r r' → r = r') ∧
      Chr.nrm l c.O D.sha * Real.log l ≤ 2 * ∑ r ∈ Xi, -Real.log ‖D.aVal g r‖

end Raw

end UpperTheory.V.GradeZeroInterpolatingElement

end
