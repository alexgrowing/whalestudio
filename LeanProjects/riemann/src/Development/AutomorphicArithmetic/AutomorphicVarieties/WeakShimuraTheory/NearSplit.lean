import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CuspidalRankFourRegularAlgebraic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

structure Amb (l : ℕ) [Fact l.Prime] where
  K : Type
  [fK : Field K]
  [ac : IsAlgClosed K]
  V : ValuationSubring K
  a : ∀ c : Coef l, c.O →+* V
  compat : ∀ (c c' : Coef l) (h : c.O ≤ c'.O) (x : c.O), a c' (Subalgebra.inclusion h x) = a c x
  loc : ∀ c, IsLocalHom (a c)
  alg : ∀ x : V, ∃ (c : Coef l) (y : c.O), x - a c y ∈ maximalIdeal V

attribute [instance] Amb.fK Amb.ac Amb.loc

abbrev inc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : c.O →+* c'.O := (Subalgebra.inclusion h : c.O →ₐ[ℤ_[l]] c'.O)

namespace Amb

variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)

abbrev k : Type := ResidueField 𝔞.V

abbrev red (c : Coef l) : c.O →+* 𝔞.k := (residue 𝔞.V).comp (𝔞.a c)

def j (c : Coef l) : ResidueField c.O →+* 𝔞.k := ResidueField.map (𝔞.a c)

abbrev toK : 𝔞.V →+* 𝔞.K := 𝔞.V.subtype

def IsZero (e : 𝔞.K ≃+* PadicAlgCl l) : Prop := (∀ c x, e (𝔞.a c x) = x) ∧ ∀ x, x ∈ 𝔞.V ↔ ‖e x‖ ≤ 1

structure IsDvr {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V) : Prop where
  inj : Function.Injective f
  loc : IsLocalHom f
  complete : IsAdicComplete (maximalIdeal A) A
  fin : Finite (ResidueField A)
  alg : ∀ x : 𝔞.K, ∃ p : A[X], p ≠ 0 ∧ p.eval₂ (𝔞.toK.comp f) x = 0

def Small {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (P : PD ι Γ 𝔞.V) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (P₁ : PD ι Γ A),
    𝔞.IsDvr f ∧ P₁.Cont (maximalIdeal A) ∧ P₁.map f = P

end Amb

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def Ctx2 (D : Raw Ω c) : Prop :=
  D.Good ∧ ∃ (h : Host) (t e : ℕ) (ψ : DirichletCharacter c.O h.N), h.Big t ∧ 0 < e ∧ e < t ∧ ψ ∈ h.X c e ∧
    h.CaseII l e ψ ∧ Aut.OfChar D e ψ (h.nII l ψ) 1 1

def Ctx3 (D : Raw Ω c) : Prop :=
  D.Good ∧ ∃ (h : Host) (t e : ℕ) (ψ : DirichletCharacter c.O h.N), h.Big t ∧ 0 < e ∧ e < t ∧ ψ ∈ h.X c e ∧
    h.CaseIII l e ψ ∧ Aut.OfChar D e ψ (h.nIII l ψ) (pOne h.chi) (orderOf ψ)

structure KPair (D : Raw Ω c) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) (u : M4 𝔞.V) : Prop where
  small : 𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _)
  red : ∀ g i j, r g i j - 𝔞.a c (D.r0 g i j) ∈ maximalIdeal 𝔞.V
  mult : ∀ g, IsGSp (𝔞.a c (D.th g)) (r g)
  unr : D.UnrT r 1
  atP : ∀ p ∈ D.Sb, ∀ g ∈ D.Ip p ⊓ D.ψ.ker, r g = 1
  sp : IsGSp 1 u
  flag : ∀ s ∈ D.Gp l, IsUp (adj u * r s * u)
  char : ∀ s ∈ D.Gp l, ∀ i, (adj u * r s * u) i i - 𝔞.a c (D.ps i s) ∈ maximalIdeal 𝔞.V
  inert : ∀ s ∈ D.Ip l, ∀ i, (adj u * r s * u) i i = 𝔞.a c (D.ps i s)

def Pure (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop :=
  ∃ (H : Subgroup (G ℚ Ω)) (M : ℕ), IsOpen (H : Set (G ℚ Ω)) ∧ M ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ M →
    ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (f : ℕ) (σ : G ℚ Ω), 0 < f → σ ∈ H → IsFrob A (p ^ f) σ →
      ∀ x ∈ (r σ).charpoly.roots, ∀ y ∈ (r σ).charpoly.roots, ‖ι x‖ = ‖ι y‖

def Con (D : Raw Ω c) : Prop :=
  ∀ 𝔞 : Amb l, CharP 𝔞.K l → ∀ r u, KPair D 𝔞 r u → ¬ Star (mapRep 𝔞.toK r)

def Pur (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
    Pure ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)

def Autm (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Irr (mapRep 𝔞.toK r) →
    Aut.IsAut4 ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)

def VPt (D : Raw Ω c) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  𝔞.Small (⟨r, fun _ => 1⟩ : PD Unit _ _) ∧
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R) (y : R →+* 𝔞.V),
      D.IsPt ρ ∧ y.comp (algebraMap c.O R) = 𝔞.a c ∧ (∀ x ∈ maximalIdeal R, y x ∈ maximalIdeal 𝔞.V) ∧ r = mapRep y ρ.hom

abbrev resQ (F : IntermediateField ℚ Ω) : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

def resLe {F L : IntermediateField ℚ Ω} (h : F ≤ L) : G L Ω →* G F Ω where
  toFun g := { g.toRingEquiv with commutes' := fun x => g.commutes ⟨x.1, h x.2⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

def lab (pr : Bool) : Fin 4 → Fin 4 := if pr then ![2, 3, 0, 1] else id

def chi (D : Raw Ω c) (pr : Bool) (i : Fin 4) : G ℚ Ω →* c.Oˣ := D.ps (lab pr i)

def LabOk (D : Raw Ω c) (pr : Bool) : Prop := pr = true → ∀ s ∈ D.Gp l, Raw.bar D.Psi s = 1

def frQ (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) : Fr c.O (G ℚ Ω) where
  ι := Unit
  Gv _ := D.Gp l
  Iv _ := D.Ip l
  Mu _ := ∅
  N := {g | (∃ A, Raw.Away D.T A ∧ g ∈ Ine (F := ℚ) A ∧ D.rbar g = 1) ∨ ∃ p ∈ D.Sb, g ∈ D.Ip p ⊓ D.ψ.ker}
  χ := chi D pr
  ν := D.th
  g0 := g0

structure QPair (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V) : Prop where
  small : 𝔞.Small P
  pair : (frQ D pr g0).IsPair (𝔞.a c) P
  inert : ∀ s ∈ D.Ip l, ∀ i, P.ψ () i s = 𝔞.a c (D.ps i s)

structure NearSplit (D : Raw Ω c) (pr : Bool) (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V) : Prop where
  red : ∀ g i j, P.r g i j - 𝔞.a c (diagRep (chi D pr) g i j) ∈ maximalIdeal 𝔞.V
  flag : ∀ i j, i ≠ j → wt i j ≠ -wPs → P.n () i j ∈ maximalIdeal 𝔞.V
  char : ∀ s ∈ D.Gp l, ∀ i, P.ψ () i s - 𝔞.a c (chi D pr i s) ∈ maximalIdeal 𝔞.V

structure LatShape (D : Raw Ω c) (pr : Bool) (g0 : G ℚ Ω) {k : Type} [Field k] (a : c.O →+* k)
    (P : PD Unit (G ℚ Ω) k) : Prop where
  res : (frQ D pr g0).IsRes a P
  supp : Supp nP P.r
  flag : SuppM qQ (P.n ())
  be : Ent P.r wBe
  ps : Ent P.r (-wPs) ∨ (Supp vV P.r ∧ P.n () 2 0 ≠ 0 ∧ (∀ s ∈ D.Gp l, Raw.bar D.Psi s = 1) ∧
    ¬ ∃ m : k, ∀ s ∈ D.Gp l, P.r s 1 2 = m * (a (chi D pr 2 s) - a (chi D pr 1 s)))

def Over {F F' : Type} [Field F] [Field F'] [Algebra F Ω] [Algebra F' Ω] (φ : G F' Ω →* G F Ω) {ι ι' R : Type} [CommRing R]
    (pl : ι → ValuationSubring Ω) (pl' : ι' → ValuationSubring Ω) (P : PD ι (G F Ω) R) (P' : PD ι' (G F' Ω) R) : Prop :=
  P'.r = P.r.comp φ ∧ ∀ v', ∃ (v : ι) (g : G F Ω), (∀ x, g x ∈ pl' v' ↔ x ∈ pl v) ∧ IsUp (adj (P'.n v') * P.r g * P.n v)

structure Tower (D : Raw Ω c) where
  pr : Bool
  K : IntermediateField ℚ Ω
  F : IntermediateField ℚ Ω
  L : IntermediateField ℚ Ω
  [nK : NumberField K]
  [nF : NumberField F]
  [nL : NumberField L]
  [cmK : IsCMField K]
  [realF : IsTotallyReal F]
  [cmL : IsCMField L]
  [abF : IsAbelianGalois ℚ F]
  degK : Module.finrank ℚ K = 2
  hL : L = F ⊔ K
  g0 : G F Ω
  ι : Type
  [fin : Finite ι]
  pl : ι → ValuationSubring Ω
  ovl : ∀ v, (pl v).valuation (l : Ω) < 1
  cover : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃! v, ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ pl v
  one : ∀ v, ∀ x ∈ K, x ∈ pl v ↔ x ∈ D.pl l

attribute [instance] Tower.nK Tower.nF Tower.nL Tower.cmK Tower.realF Tower.cmL Tower.abF Tower.fin

def TameL (l : ℕ) (F : IntermediateField ℚ Ω) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, ∃ m : ℕ, l.Coprime m ∧ g ^ m ∈ F.fixingSubgroup

variable (l) in

def IsLayer (m : ℕ) (F F' : IntermediateField ℚ Ω) : Prop :=
  ∀ g : G ℚ Ω, g ∈ F'.fixingSubgroup ↔ g ∈ F.fixingSubgroup ∧ cycZ ℚ Ω l g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (m + 1)

variable (l) in

def Dies (w : ℕ) (F : IntermediateField ℚ Ω) : Prop :=
  ∀ θ : G ℚ Ω →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (G ℚ Ω)) →
    (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) → F.fixingSubgroup ≤ θ.ker

namespace Tower

variable {D : Raw Ω c} (T : Tower D)

theorem F_le : T.F ≤ T.L := T.hL ▸ le_sup_left

abbrev d : ℕ := Module.finrank ℚ T.F

def GalL : Subgroup (G T.F Ω) := T.K.fixingSubgroup.comap (resQ T.F)

def G' : Subgroup (G T.F Ω) := T.GalL ⊓ (cycZ T.F Ω l).ker

def fr (W : Finset ℕ) : Fr c.O (G T.F Ω) where
  ι := T.ι
  Gv v := Dec (F := T.F) (T.pl v)
  Iv v := Ine (F := T.F) (T.pl v)
  Mu v := muOf l (Dec (F := T.F) (T.pl v))
  N := {g | ∃ A, Raw.Away (insert l W) A ∧ g ∈ Ine (F := T.F) A ∧ D.rbar (resQ T.F g) = 1}
  χ i := (chi D T.pr i).comp (resQ T.F)
  ν := D.th.comp (resQ T.F)
  g0 := T.g0

abbrev rb (w : ℤ × ℤ) (g : G T.F Ω) : ResidueField c.O := residue c.O ((T.fr ∅).rt w g : c.O)

def U1 (v : T.ι) : Set (G T.F Ω) :=
  {s | s ∈ Ine (F := T.F) (T.pl v) ∧ cycZ T.F Ω l s = 1 ∧ D.rbar (resQ T.F s) = 1}

def Splits (w : ℕ) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ T.F.fixingSubgroup ⊓ D.rbar.ker ⊓ D.om.ker

structure Ok : Prop where
  lab : LabOk D T.pr
  even : Even T.d
  unr : ∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL
  split : ∀ p ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ T.K.fixingSubgroup
  g2 : ∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)
  g3 : ∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1
  g3' : ∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) →
    (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1
  ord : ∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1
  kb : ∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1
  kc : ∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1
  ineL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1
  dist : ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)
  locL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1

structure Two : Prop where
  sq : ∀ g : G T.F Ω, T.rb wPs g ^ 2 = 1
  unr : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.F) A, T.rb wPs g = 1
  atL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := T.F) A, T.rb wPs g = 1
  quad : ∃ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 ∧ IsTotallyReal k₀ ∧
    (∀ p ∈ [2, l], ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ k₀.fixingSubgroup) ∧
    ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ resQ T.F g ∈ k₀.fixingSubgroup
  ord : ∃ n : ℕ, D.ξ ^ 2 ^ n = 1
  xi : ∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker
  bigL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := T.F) A, T.rb wAl g ^ 4 ≠ 1
  big2 : ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → ∃ g ∈ Ine (F := T.F) A, T.rb wAl g ^ 4 ≠ 1

structure Three : Prop where
  five : 5 ≤ l
  sb : D.Sb = ∅
  psi : ∃ m : ℕ, l.Coprime m ∧ D.ψ ^ m = 1
  sq : ∀ g : G T.F Ω, T.rb wPs g = T.rb wAl g ^ 2

structure Three0 (T : Tower D) : Prop where
  five : 5 ≤ l
  sb : D.Sb = ∅
  psi : ∃ m : ℕ, l.Coprime m ∧ D.ψ ^ m = 1

def Fit : Prop := T.Ok ∧ ((Ctx2 D ∧ T.Two) ∨ (Ctx3 D ∧ T.Three0))

def Deep : Prop := ∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, D.ψ (resQ T.F g) ^ m = 1

structure Le (T' : Tower D) : Prop where
  pr : T'.pr = T.pr
  K : T'.K = T.K
  le : T.F ≤ T'.F
  pow : ∃ j : ℕ, ∀ g ∈ T.F.fixingSubgroup, g ^ l ^ j ∈ T'.F.fixingSubgroup
  g0 : ∃ j : ℕ, resQ T'.F T'.g0 = resQ T.F T.g0 ^ l ^ j

abbrev OverQ {R : Type} [CommRing R] (P : PD Unit (G ℚ Ω) R) (P' : PD T.ι (G T.F Ω) R) : Prop :=
  Over (resQ T.F) (fun _ => D.pl l) T.pl P P'

abbrev OverT {T' : Tower D} (h : T.Le T') {R : Type} [CommRing R] (P : PD T.ι (G T.F Ω) R) (P' : PD T'.ι (G T'.F Ω) R) : Prop :=
  Over (resLe h.le) T.pl T'.pl P P'

def Wts (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

structure IsSeed (ι : PadicAlgCl l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop where
  irr : Irr (P.r.comp T.G'.subtype)
  aut : ∃ (h : Fin 4 → ℤ) (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ),
    (∀ i : Fin 3, ∃ n : ℤ, 2 ≤ n ∧ h i.castSucc = h i.succ + 2 * n) ∧ T.Wts h P ∧ Continuous κ ∧ 0 < k ∧ Even (a + h 0) ∧
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) ∧
    CuspidalRankFourRegularAlgebraic π ∧ Af.AttC ι (Af.tw (P.r.comp (resLe T.F_le)).toHomUnits κ) π

structure SeedPair (ι : PadicAlgCl l ≃+* ℂ) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O) : Prop where
  pair : (T.fr ∅).IsPair (inc h) Q
  cont : Q.Cont (maximalIdeal c₁.O)
  res : (T.fr ∅).Res ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O))
  seed : T.IsSeed ι (Q.map (algebraMap c₁.O (PadicAlgCl l)))

structure PM (ι : PadicAlgCl l ≃+* ℂ) {c' : Coef l} {h : c.O ≤ c'.O} (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) : Prop where
  fin : ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
    Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1}
  p1 : ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
    (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
    (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
    Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
    X.LocZero J (y : X.A →+* PowerSeries k)
  seed : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeed ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
    X.LocZero J (y : X.A →+* PadicAlgCl l)
  pur : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Pure ι r
  aut : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
      Irr (r.comp T.L.fixingSubgroup.subtype) → Aut.IsAut4 ι r

end Tower

def SeedII : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    Ctx2 D → T.Ok → T.Two → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ,
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))

def SeedIII : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → T₀.Three → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧
      Supp nM s.r ∧ Ent s.r (-wAl) ∧ Ent s.r (-wBe) ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → T.Three → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁))

def PMEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    T.Fit → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ, ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∀ X : Space (T.fr ∅) (inc h), ∃ J, T.PM ι X J

def ProMod (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  ∃ (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V)
    (r₁ : G ℚ Ω →* M4 𝔞.V), T.Fit ∧ T.Deep ∧ T.PM ι X J ∧ y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧
    (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧ (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧
    IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK r₁) ∧ (∀ g, IsGSp (𝔞.a c (D.th g)) (r₁ g)) ∧
    r₁.comp (resQ T.F) = (X.P.map y).r ∧
    ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s))

end UpperTheory.V.Ws

end
