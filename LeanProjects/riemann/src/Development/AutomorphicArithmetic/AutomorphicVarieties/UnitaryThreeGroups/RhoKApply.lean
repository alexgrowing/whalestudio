import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg
open IsLocalRing Matrix Formalism.MainNotions.N GlobalTheory.GalOfCusp

namespace UpperTheory.V.U3

abbrev CharCont {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ) : Prop :=
  ∀ n : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ n : Oˣ) : O)

structure Dat (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) where
  gd : GD Ω K l e ψ
  η : G ℚ Ω →* ℤˣ
  η_ker : η.ker = galOf ℚ K Ω
  cc : G ℚ Ω
  conj : ∃ φ : Ω →+* ℂ, ∀ x, φ (cc x) = starRingEnd ℂ (φ x)
  j : Ω →+* Om l
  ι : GQ l →* G ℚ Ω
  ι_cont : Continuous ι
  ι_spec : ∀ σ x, σ (j x) = j (ι σ x)
  Kv : FinExt l
  Kv_spec : ∀ g, η (ι g) = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Loc.Iq l, η (ι g) = 1
  τ_open : IsOpen (((Chr.dirG ℚ Ω (comp l ψ)).comp ι).ker : Set (GQ l))
  Ψ_cont : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ))
  Ψ_I : ∀ g ∈ Loc.Iq l, Chr.Psi l e (Chr.dirG ℚ Ω ψ) (ι g) =
    Loc.cycA l l c.O g ^ e * Chr.dirG ℚ Ω (comp l ψ) (ι g)

namespace Dat

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)

abbrev Ψ (_ : Dat Ω K c e ψ) : G ℚ Ω →* c.Oˣ := Chr.Psi l e (Chr.dirG ℚ Ω ψ)

def ΨQ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp D.Ψ

abbrev loc : Loc.Dat3 l c.O where
  η := D.η.comp D.ι
  Ψ := D.Ψ.comp D.ι
  τ := (Chr.dirG ℚ Ω (comp l ψ)).comp D.ι
  e := e
  Kv := D.Kv
  odd := D.gd.l_odd
  e_pos := D.gd.e_pos
  η_ker := D.Kv_spec
  η_unr := D.η_unr
  τ_open := D.τ_open
  Ψ_cont n := by
    have h := (D.Ψ_cont 1 n).comp_continuous D.ι_cont
    simp only [zpow_one] at h
    exact h
  Ψ_I := D.Ψ_I

def Kill : Set (G ℚ Ω) :=
  {g | ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧ rbar c.O D.η D.Ψ g = 1}

abbrev ULoc : Type 1 := Univ (GCond.noCondition c.O (D.η.comp D.ι) (D.Ψ.comp D.ι))

abbrev Ring (U : D.ULoc) (g₁ : G ℚ Ω) : Type 1 := SRing D.Kill D.ι_cont U (D.loc.It U) D.cc g₁

abbrev Marked (g₁ : G ℚ Ω) : Prop := Marks D.η D.Ψ D.cc g₁

def rhoK {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG 3 κ) (hr : HasMult D.η r) : G K Ω →* GL (Fin 3) κ :=
  (glPart D.η r hr).comp ((galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s)

theorem rhoK_apply {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG 3 κ) (hr : HasMult D.η r) (s : G K Ω) :
    D.rhoK r hr s = (r (galEmb ℚ K Ω s)).left := rfl

structure IsPt (U : D.ULoc) (g₁ : G ℚ Ω) (r : G ℚ Ω →* GG 3 (PadicAlgCl l)) : Prop where
  mult : HasMult D.η r
  cont : Continuous (mats r)
  int : ∀ g a b, ‖(r g).mat a b‖ ≤ 1
  red : ∀ g a b, ‖(r g).mat a b - (r0 D.η D.ΨQ g).mat a b‖ < 1
  norm : Normalised D.cc g₁ r
  kill : ∀ g ∈ D.Kill, r g = 1
  loc : ∃ f : U.R →ₐ[c.O] PadicAlgCl l, IsLocPt f ∧ D.loc.It U ≤ RingHom.ker f ∧ push f U.r.hom = r.comp D.ι

def IsExt {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG 3 κ) (W : G ℚ Ω →* GL (Fin 2) κ) : Prop :=
  (∀ g ∈ D.η.ker, (W g : Matrix (Fin 2) (Fin 2) κ) = corner (r g).mat) ∧ (W D.cc : Matrix (Fin 2) (Fin 2) κ).trace = 0

def IsAutI [IsCMField K] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GG 3 (PadicAlgCl l)) (hr : HasMult D.η r) : Prop :=
  Af.IsAutCsd ι (Af.tw (D.rhoK r hr) (cycBar K Ω l)⁻¹)

def IsModular (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))

end Dat

end UpperTheory.V.U3

end
