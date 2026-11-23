import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

def tDims (r r' m : ℕ) (j : ℤ × ℤ) : ℕ :=
  if j = wAl ∨ j = wBe ∨ j = wTh then 1 else if j = wPs then r' else if j = -wPs then r else if j = 0 then m else 0

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

namespace Raw

variable (D : Raw Ω c)

structure ShaCoc (a : c.O) (z : G ℚ Ω → c.O ⧸ Ideal.span {a}) : Prop where
  lc : IsLocallyConstant z
  coc : ∀ g h, z (g * h) = z g + Ideal.Quotient.mk _ ((D.Psi⁻¹ g : c.Oˣ) : c.O) * z h
  unr : D.UnrT z 0
  g0 : z D.g0 = 0
  loc : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = Ideal.Quotient.mk _ ((D.Psi⁻¹ g : c.Oˣ) : c.O) * m - m

end Raw

structure Model (D : Raw Ω c) where
  R : Type
  [cR : CommRing R]
  [aR : Algebra c.O R]
  [coR : IsCO c.O R]
  [dR : IsDomain R]
  W : WPres c.O (ℤ × ℤ) R
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  r : ℕ
  r' : ℕ
  m : ℕ
  one_le : 1 ≤ r
  smooth : SmoothPt W.gr ((W.origin org).comp W.A.val) (tDims r r' m)
  F : Fin (r + 1) → R
  E : Fin r' → R
  Z : Fin m → R
  hF : ∀ i, F i ∈ W.part (-wPs)
  hE : ∀ i, E i ∈ W.part wPs
  hZ : ∀ i, Z i ∈ W.part 0 ∧ W.origin org (Z i) = 0
  S : Type
  [cS : CommRing S]
  [aS : Algebra c.O S]
  [coS : IsCO c.O S]
  π : R →ₐ[c.O] S
  surj : Function.Surjective π
  ker : RingHom.ker π = Ideal.span (Set.range F ∪ Set.range E ∪ Set.range Z)
  ru : Lift c.O D.rbar S
  pt : D.IsPt ru
  gen : ru.Generates
  hom : ∀ g i j, ∃ f ∈ W.part (wt i j), π f = ru.hom g i j
  at0 : ∀ g i j f, π f = ru.hom g i j → W.origin org f = D.r0 g i j
  der : ∀ (a : c.O) (z : G ℚ Ω → c.O ⧸ Ideal.span {a}), a ≠ 0 → D.ShaCoc a z →
    ∃ δ ∈ PtDer (W.origin org) c.O, HasWt W.part (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = ru.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (D.th g : c.O) * z g) ∧
        (π f = ru.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (D.Psi g : c.O) * z g)

attribute [instance] Model.cR Model.aR Model.coR Model.dR Model.cS Model.aS Model.coS

namespace Model

variable {D : Raw Ω c} (M : Model D)

def sPart (j : ℤ × ℤ) : Submodule c.O M.S := (M.W.part j).map M.π.toLinearMap

instance : SetLike.GradedMonoid M.sPart where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one M.π⟩
  mul_mem := by
    rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, SetLike.GradedMul.mul_mem hf hg, map_mul M.π f g⟩

def SS : Subalgebra c.O M.S := gradedSub M.sPart

theorem entry_mem (g : G ℚ Ω) (i j : Fin 4) : M.ru.hom g i j ∈ M.sPart (wt i j) := M.hom g i j

theorem sPart_le {j : ℤ × ℤ} {x : M.S} (hx : x ∈ M.sPart j) : x ∈ M.SS := le_iSup M.sPart j hx

def ent (g : G ℚ Ω) (i j : Fin 4) : M.SS := ⟨M.ru.hom g i j, M.sPart_le (M.entry_mem g i j)⟩

def rS : G ℚ Ω →* M4 M.SS where
  toFun g := Matrix.of (M.ent g)
  map_one' := by
    ext i j
    show M.ru.hom 1 i j = _
    rw [map_one]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' a b := by
    ext i j
    show M.ru.hom (a * b) i j = _
    rw [map_mul]
    simp [Matrix.mul_apply, ent]

def rep {K : Type} [CommRing K] [Algebra c.O K] (ξ : M.SS →ₐ[c.O] K) : G ℚ Ω →* M4 K := mapRep (ξ : M.SS →+* K) M.rS

def aPart (n : ℤ) : Submodule c.O M.R := M.W.part (0, n)

instance : SetLike.GradedMonoid M.aPart where
  one_mem := (SetLike.GradedOne.one_mem : (1 : M.R) ∈ M.W.part 0)
  mul_mem i j a b ha hb := by
    have h : a * b ∈ M.W.part ((0, i) + (0, j)) := SetLike.GradedMul.mul_mem ha hb
    simpa [aPart] using h

def A : Subalgebra c.O M.R := gradedSub M.aPart

def gr (n : ℤ) : Submodule c.O M.A := (M.aPart n).comap M.A.val.toLinearMap

instance : SetLike.GradedMonoid M.gr where
  one_mem := (SetLike.GradedOne.one_mem : (1 : M.R) ∈ M.aPart 0)
  mul_mem _ _ _ _ ha hb := (SetLike.GradedMul.mul_mem ha hb : _ ∈ M.aPart _)

theorem aPart_le {n : ℤ} {x : M.R} (hx : x ∈ M.aPart n) : x ∈ M.A := le_iSup M.aPart n hx

def x0 : M.A →ₐ[c.O] c.O := (M.W.origin M.org).comp M.A.val

def eqns : Eqns M.gr M.x0 M.r 0 M.r' 0 M.m where
  F i := ⟨M.F i, M.aPart_le (n := -1) (M.hF i)⟩
  G := Fin.elim0
  E i := ⟨M.E i, M.aPart_le (n := 1) (M.hE i)⟩
  E' := Fin.elim0
  Z i := ⟨M.Z i, M.aPart_le (n := 0) (M.hZ i).1⟩
  hF i := M.hF i
  hG i := i.elim0
  hE i := M.hE i
  hE' i := i.elim0
  hZ i := M.hZ i

theorem π_mem (f : M.A) : M.π f ∈ M.SS := by
  obtain ⟨f, hf⟩ := f
  refine Submodule.iSup_induction M.aPart (motive := fun f => M.π f ∈ M.SS) hf (fun n a ha => ?_) (by simp)
    (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
  exact M.sPart_le (j := (0, n)) ⟨a, ha, rfl⟩

def toSS : M.A →ₐ[c.O] M.SS := (M.π.comp M.A.val).codRestrict M.SS M.π_mem

end Model

variable (Ω l) in

def SoV : Prop :=
  ∀ ψ : G ℚ Ω →* (PadicAlgCl l)ˣ, IsOpen (ψ.ker : Set (G ℚ Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ θ : G ℚ Ω → PadicAlgCl l,
    (∀ g, θ g * (ψ g : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1) →
    ∀ z : G ℚ Ω → PadicAlgCl l, Continuous z → (∀ g h, z (g * h) = z g + θ g * z h) →
    (∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := ℚ) A, z g = θ g * m - m) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := ℚ) A, z g = θ g * m - m) →
    ∃ m, ∀ g, z g = θ g * m - m

variable (Ω l) in

def SoFin : Prop :=
  ∀ (c : Coef l) (ψ : G ℚ Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G ℚ Ω)) → ∀ e : ℕ, 1 ≤ e → Chr.V l e ψ ≠ ⊤

structure CohomologyHyp : Prop where
  loc : Loc.LocalPublishedTheorems
  pt : GlobalTheory.Published.PoitouTateNormalised
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  uo : UnramifiedOrthogonality
  gw : GreenbergWiles

end UpperTheory.V.GradeZeroInterpolatingElement

end
