import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def w4 (i : Fin 4) : ℤ × ℤ := (lamW i, muW i)

theorem w4_sub_w4_eq_wt (i j : Fin 4) : w4 i - w4 j = wt i j := rfl

def J4 (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

def form (O : Type) [CommRing O] : FormData O w4 where
  J := J4 O
  unit := IsUnit.of_mul_eq_one (-J4 O) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_apply, Fin.sum_univ_four])
  sym := Or.inr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4])
  κ := Unit
  blk _ := ()
  σ := id
  invol _ := rfl
  hblk _ _ _ := rfl
  c := (1, 1)
  hw a b h := by
    fin_cases a <;> fin_cases b <;> simp [J4] at h <;> decide

namespace Raw

variable (D : Raw Ω c)

theorem residueChar_mem_levelPrimes : l ∈ D.T := Finset.mem_insert_self _ _

theorem mem_T {p : ℕ} (hp : p ∈ D.Sb) : p ∈ D.T := Finset.mem_insert_of_mem hp

def LocEqs {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R) : Prop :=
  D.eqL (ρ ⟨l, D.residueChar_mem_levelPrimes⟩).hom ∧ ∀ p (hp : p ∈ D.Sb), D.eqP p (ρ ⟨p, D.mem_T hp⟩).hom

def SP : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | ∃ p ∈ D.S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}

abbrev Gam : Type := GS Ω D.SP

def frame : Frame D.Gam where
  T := D.T
  v0 := ⟨l, D.residueChar_mem_levelPrimes⟩
  Gv v := D.Gp v
  φ v := locHom D.SP (D.pl v)
  hφ v := continuous_locHom D.SP (D.pl v)
  Q := (D.S \ D.T : Finset ℕ)
  Gq q := D.Gp q
  ψ q := locHom D.SP (D.pl q)
  hψ q := continuous_locHom D.SP (D.pl q)
  N q := (D.Ip q ⊓ D.rbar.ker).subgroupOf (D.Gp q)

def Nums : Prop :=
  ∀ (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ),
    Module.Finite (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) ∧
    Module.finrank (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) =
      Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) +
        (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) = 0)

end Raw

structure LocBase (D : Raw Ω c) where
  B : Type
  [cB : CommRing B]
  [aB : Algebra c.O B]
  [coB : IsCO c.O B]
  W : WPres c.O (ℤ × ℤ) B
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) B
  eqs : D.LocEqs ρ
  univ : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ' : ∀ v : D.T, Lift c.O (D.rbarAt v) R), D.LocEqs ρ' →
    ∃! f : B →ₐ[c.O] R, ∀ v, (ρ v).map f = ρ' v
  hom : ∀ (v : D.T) g i j, (ρ v).hom g i j ∈ W.part (wt i j)
  at0 : ∀ (v : D.T) (g : D.Gp v) i j, W.origin org ((ρ v).hom g i j) = D.r0 g i j
  smooth : SmoothPt W.gr ((W.origin org).comp W.A.val) fun j => dimL j + D.Sb.card * dimP j

attribute [instance] LocBase.cB LocBase.aB LocBase.coB

end UpperTheory.V.GradeZeroInterpolatingElement

end
