import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

def muOf (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) : Set Γ :=
  {s | s ∈ H ∧ ∃ a : ℕ, s ^ l ^ a ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure}

structure Fr (O Γ : Type) [CommRing O] [Group Γ] where
  ι : Type
  [fin : Finite ι]
  Gv : ι → Subgroup Γ
  Iv : ι → Subgroup Γ
  Mu : ι → Set Γ
  N : Set Γ
  χ : Fin 4 → Γ →* Oˣ
  ν : Γ →* Oˣ
  g0 : Γ

attribute [instance] Fr.fin

@[ext] structure PD (ι Γ R : Type) [Group Γ] [CommRing R] where
  r : Γ →* M4 R
  n : ι → M4 R

def roots : Finset (ℤ × ℤ) := oddRoots ∪ {wPs, -wPs}

def nP : Finset (ℤ × ℤ) := {wBe, -wAl, -wTh, -wPs}

def nM : Finset (ℤ × ℤ) := {-wAl, -wBe, -wPs, -wTh}

def vV : Finset (ℤ × ℤ) := {wBe, -wAl, -wTh}

def qQ : Finset (ℤ × ℤ) := {-wAl, -wPs, -wTh}

def redTypes : List (Finset (ℤ × ℤ)) :=
  [{wBe, -wBe, -wAl, -wTh, -wPs}, {wBe, -wBe, wAl, wTh, wPs}, {wTh, -wTh, wPs, wBe, -wAl}, {wTh, -wTh, -wPs, -wBe, wAl},
   {wAl, -wAl, -wTh, -wPs, -wBe}, {wAl, -wAl, wTh, wPs, wBe}, {wPs, -wPs, wBe, -wAl, -wTh}, {wPs, -wPs, -wBe, wAl, wTh},
   {wBe, -wBe, wTh, -wTh}]

section Mat

variable {R : Type} [CommRing R]

def SuppM (S : Finset (ℤ × ℤ)) (X : M4 R) : Prop := ∀ i j, i ≠ j → wt i j ∉ S → X i j = 0

def IsUp (X : M4 R) : Prop := ∀ i j, j < i → X i j = 0

def IsLow (X : M4 R) : Prop := IsGSp 1 X ∧ (∀ i, X i i = 1) ∧ ∀ i j, i < j → X i j = 0

variable {Γ : Type} [Group Γ]

def Supp (S : Finset (ℤ × ℤ)) (r : Γ →* M4 R) : Prop := ∀ g, SuppM S (r g)

def Ent (r : Γ →* M4 R) (w : ℤ × ℤ) : Prop := ∃ g i j, wt i j = w ∧ r g i j ≠ 0

def StarE (r : Γ →* M4 R) : Prop := Ent r wPs ∧ Ent r (-wPs) ∧ (Ent r wBe ∨ Ent r (-wAl) ∨ Ent r (-wTh))

def ixB : Fin 2 → Fin 4 := ![1, 3]

def BlockExt (r : Γ →* M4 R) : Prop :=
  (∀ g i j, lamW j < lamW i → r g i j = 0) ∧
    Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) = ⊤ ∧
    ¬ ∃ Y : M4 R, (∀ i j, ¬ lamW i < lamW j → Y i j = 0) ∧ ∀ g, IsBlock ((1 - Y) * r g * (1 + Y))

def Star (r : Γ →* M4 R) : Prop := Irr r ∨ BlockExt r

end Mat

namespace PD

variable {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R']

def map (P : PD ι Γ R) (f : R →+* R') : PD ι Γ R' := ⟨mapRep f P.r, fun v => (P.n v).map f⟩

def ψ (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) : R := (adj (P.n v) * P.r s * P.n v) i i

def Cont [TopologicalSpace Γ] (P : PD ι Γ R) (I : Ideal R) : Prop := ∀ i j, AdicCont I fun g => P.r g i j

end PD

namespace Fr

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)

def rt (w : ℤ × ℤ) : Γ →* Oˣ where
  toFun g := (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ w.1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ w.2
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_inv, mul_zpow, inv_zpow]; ac_rfl

structure IsPair (P : PD Φ.ι Γ R) : Prop where
  mult : ∀ g, IsGSp (a (Φ.ν g)) (P.r g)
  kill : ∀ g ∈ Φ.N, P.r g = 1
  nrm : (P.r Φ.g0).IsDiag
  low : ∀ v, IsLow (P.n v)
  flag : ∀ v, ∀ s ∈ Φ.Gv v, IsUp (adj (P.n v) * P.r s * P.n v)
  mu : ∀ v, ∀ s ∈ Φ.Mu v, ∀ i, P.ψ v i s = 1

structure Res (P : PD Φ.ι Γ R) : Prop where
  diag : ∀ g i, P.r g i i = a (Φ.χ i g)
  char : ∀ v, ∀ s ∈ Φ.Gv v, ∀ i, P.ψ v i s = a (Φ.χ i s)
  shape : (Supp nP P.r ∧ ∀ v, SuppM qQ (P.n v)) ∨ Supp nM P.r

variable {Φ} in

def InV (P : PD Φ.ι Γ R) : Prop := Supp vV P.r ∧ ∀ v, SuppM qQ (P.n v) ∧ P.n v 2 0 ≠ 0

def Good (P : PD Φ.ι Γ R) : Prop :=
  (Ent P.r (-wPs) ∧ (Ent P.r wBe ∨ Ent P.r (-wAl))) ∨ (Ent P.r (-wAl) ∧ Ent P.r (-wBe)) ∨
    (InV P ∧ Ent P.r (-wAl)) ∨
    (InV P ∧ Ent P.r wBe ∧ Ent P.r (-wTh) ∧ ∀ v, ∃ s ∈ Φ.Gv v, a (Φ.rt wAl s) ≠ 1)

variable [TopologicalSpace Γ]

structure IsRes (P : PD Φ.ι Γ R) : Prop where
  pair : Φ.IsPair a P
  res : Φ.Res a P
  cont : P.Cont ⊥

def Linked (c c' : PD Φ.ι Γ R) : Prop :=
  ∃ P : PD Φ.ι Γ R[X], Φ.IsRes (C.comp a) P ∧ P.map (evalRingHom 0) = c ∧ P.map (evalRingHom 1) = c'

def Chain (c c' : PD Φ.ι Γ R) : Prop :=
  Φ.Good a c ∧ Relation.ReflTransGen (fun x y => Φ.Good a y ∧ Φ.Linked a x y) c c'

def Zloc (H : Subgroup Γ) (w : ℤ × ℤ) : Submodule R (H → R) where
  carrier := {z | IsLocallyConstant z ∧ ∀ g h : H, z (g * h) = z g + a (Φ.rt w g) * z h}
  add_mem' := by
    rintro x y ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨a1.add b1, fun g h => by simp only [Pi.add_apply, a2, b2]; ring⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp⟩
  smul_mem' := by
    rintro c x ⟨a1, a2⟩
    exact ⟨a1.comp (c • ·), fun g h => by simp only [Pi.smul_apply, a2, smul_eq_mul]; ring⟩

def Zgl (w : ℤ × ℤ) : Submodule R (Γ → R) where
  carrier := {z | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + a (Φ.rt w g) * z h) ∧ (∀ g ∈ Φ.N, z g = 0) ∧
    (w ≠ 0 → z Φ.g0 = 0)}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    exact ⟨a1.add b1, fun g h => by simp only [Pi.add_apply, a2, b2]; ring, fun g h => by simp [a3 g h, b3 g h],
      fun h => by simp [a4 h, b4 h]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    exact ⟨a1.comp (c • ·), fun g h => by simp only [Pi.smul_apply, a2, smul_eq_mul]; ring,
      fun g h => by simp [a3 g h], fun h => by simp [a4 h]⟩

def LocTriv (w : ℤ × ℤ) (z : Γ → R) (n : Φ.ι → R) : Prop := ∀ v, ∀ s ∈ Φ.Gv v, z s = n v - a (Φ.rt w s) * n v

def Str (w : ℤ × ℤ) : Submodule R (Γ → R) :=
  Φ.Zgl a w ⊓
    { carrier := {z | ∃ n, Φ.LocTriv a w z n}
      add_mem' := by
        rintro x y ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨n + m, fun v s hs => by simp only [Pi.add_apply, hn v s hs, hm v s hs]; ring⟩
      zero_mem' := ⟨0, fun v s _ => by simp⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        exact ⟨c • n, fun v s hs => by simp only [Pi.smul_apply, hn v s hs, smul_eq_mul]; ring⟩ }

structure Bounds (d C : ℕ) : Prop where
  card : Nat.card Φ.ι ≤ C
  str : ∀ w ∈ roots, Module.rank R (Φ.Str a w) ≤ C
  even : ∀ w ∈ [0, wPs, -wPs], Module.rank R (Φ.Zgl a w) ≤ C
  odd : ∀ w ∈ oddRoots, Module.rank R (Φ.Zgl a w) ≤ d + C
  loc : ∀ w ∈ oddRoots, Module.rank R (∀ v, Φ.Zloc a (Φ.Gv v) w) ≤ d + C

structure Ok : Prop where
  mul : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g
  kill : ∀ g ∈ Φ.N, ∀ i, a (Φ.χ i g) = 1
  dist : ∀ i j, i ≠ j → IsUnit (a (Φ.χ i Φ.g0) - a (Φ.χ j Φ.g0))
  two : IsUnit (2 : R)
  lc : ∀ i, IsLocallyConstant fun g => a (Φ.χ i g)

def Tan (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Set ((Γ → M4 R) × (Φ.ι → M4 R)) :=
  {x | IsLocallyConstant x.1 ∧ (∀ g, x.1 g ∈ sp4 R) ∧ (∀ g h, x.1 (g * h) = x.1 g + c.r g * x.1 h * c.r g⁻¹) ∧
    (∀ g ∈ Φ.N, x.1 g = 0) ∧ (x.1 Φ.g0).IsDiag ∧ (∀ g, SuppM S (x.1 g * c.r g)) ∧
    (∀ v, x.2 v ∈ sp4 R ∧ ∀ i j, i ≤ j → (adj (c.n v) * x.2 v * c.n v) i j = 0) ∧
    ∀ v, ∀ s ∈ Φ.Gv v, IsUp (adj (c.n v) * (x.1 s + c.r s * x.2 v * c.r s⁻¹ - x.2 v) * c.n v)}

end Fr

section Def

variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  (a : O →+* Λ)

structure Fr.Lifts (c : PD Φ.ι Γ (ResidueField Λ)) {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) : Prop where
  pair : Φ.IsPair ((algebraMap Λ R).comp a) P
  cont : P.Cont (maximalIdeal R)
  red : P.map (res Λ R : R →+* ResidueField Λ) = c

def Fr.IsDef (c : PD Φ.ι Γ (ResidueField Λ)) {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) : Prop :=
  Φ.Lifts a c P ∧ ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.Lifts a c P' →
    ∃! f : R →ₐ[Λ] R', P.map (f : R →+* R') = P'

structure Space where
  A : Type
  [cA : CommRing A]
  [aA : Algebra Λ A]
  B : Type
  [cB : CommRing B]
  [aB : Algebra Λ B]
  [coB : IsCO Λ B]
  [aBA : Algebra B A]
  [tower : IsScalarTower Λ B A]
  inj : Function.Injective (algebraMap B A)
  ft : Algebra.FiniteType B A
  P : PD Φ.ι Γ A
  pair : Φ.IsPair ((algebraMap Λ A).comp a) P
  cont : P.Cont ((maximalIdeal B).map (algebraMap B A))
  gen : Algebra.adjoin B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
    Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) = ⊤
  cp : Γ → B[X]
  cp_map : ∀ g, (cp g).map (algebraMap B A) = (P.r g).charpoly
  cp_cont : ∀ n, AdicCont (maximalIdeal B) fun g => (cp g).coeff n
  cp_red : ∀ g, (cp g).map (res Λ B : B →+* ResidueField Λ) = ∏ i, (X - C (residue Λ (a (Φ.χ i g))))
  ψ : Φ.ι → Fin 4 → Γ → B
  ψ_map : ∀ v i, ∀ s ∈ Φ.Gv v, algebraMap B A (ψ v i s) = P.ψ v i s
  ψ_cont : ∀ v i, AdicCont (maximalIdeal B) fun s : Φ.Gv v => ψ v i s
  ψ_red : ∀ v i, ∀ s ∈ Φ.Gv v, res Λ B (ψ v i s) = residue Λ (a (Φ.χ i s))
  genB : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : B →ₐ[Λ] R),
    (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → (∀ v i, ∀ s ∈ Φ.Gv v, f (ψ v i s) = f' (ψ v i s)) → f = f'
  univ : ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (c : PD Φ.ι Γ (ResidueField Λ)) (Q : PD Φ.ι Γ R),
    Φ.IsRes ((residue Λ).comp a) c → Φ.Lifts a c Q → ∃ f : A →ₐ[Λ] R, P.map (f : A →+* R) = Q
  line : ∀ Q : PD Φ.ι Γ (ResidueField Λ)[X], Φ.IsRes (C.comp ((residue Λ).comp a)) Q →
    ∃ f : A →ₐ[Λ] (ResidueField Λ)[X], P.map (f : A →+* (ResidueField Λ)[X]) = Q ∧
      ∀ b ∈ maximalIdeal B, f (algebraMap B A b) = 0

attribute [instance] Space.cA Space.aA Space.cB Space.aB Space.coB Space.aBA Space.tower

variable {Φ a}

def Space.SomeIn (X : Space Φ a) (J : Ideal X.B) (p : Ideal X.A) : Prop :=
  ∃ q ∈ minimalPrimes X.A, q ≤ p ∧ J.map (algebraMap X.B X.A) ≤ q

def Space.AllIn (X : Space Φ a) (J : Ideal X.B) (p : Ideal X.A) : Prop :=
  ∀ q ∈ minimalPrimes X.A, q ≤ p → J.map (algebraMap X.B X.A) ≤ q

def Space.LocZero (X : Space Φ a) (J : Ideal X.B) {K : Type} [CommRing K] (y : X.A →+* K) : Prop :=
  ∀ q : Ideal X.B, q.IsPrime → (∀ s ∈ q, y (algebraMap X.B X.A s) = 0) → J ≤ q

end Def

structure Fr.Std {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Φ : Fr O Γ) (l : ℕ)
    {Λ : Type} [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ) : Prop where
  ok : Φ.Ok ((residue Λ).comp a)
  char : CharP (ResidueField Λ) l
  cont : ∀ i, AdicCont (maximalIdeal Λ) fun g => a (Φ.χ i g)
  phi : ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → Subgroup.normalClosure Φ.N ≤ H → Finite {φ : H →* Multiplicative (ZMod l) //
    IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ (Subgroup.normalClosure Φ.N).topologicalClosure → φ g = 1}
  closed : ∀ v, IsClosed (Φ.Gv v : Set Γ)
  phiv : ∀ v, PhiCond (Φ.Gv v) l
  mu : ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, residue Λ (a (Φ.χ i s)) = 1

def redIdeal {Γ R : Type} [Group Γ] [CommRing R] (S : Finset (ℤ × ℤ)) (r : Γ →* M4 R) : Ideal R :=
  Ideal.span {x | ∃ g i j, i ≠ j ∧ wt i j ∉ S ∧ x = r g i j}

def PD.SamePs {ι Γ R : Type} [Group Γ] [CommRing R] (P P' : PD ι Γ R) : Prop :=
  (∀ g, P.r g 2 0 = P'.r g 2 0) ∧ ∀ v, P.n v 2 0 = P'.n v 2 0

def PD.SameAl {ι Γ R : Type} [Group Γ] [CommRing R] (P P' : PD ι Γ R) : Prop :=
  (∀ g, P.r g 1 0 = P'.r g 1 0) ∧ ∀ v, P.n v 1 0 = P'.n v 1 0

def PD.In {ι Γ R : Type} [Group Γ] [CommRing R] (S : Finset (ℤ × ℤ)) (P : PD ι Γ R) : Prop :=
  Supp S P.r ∧ ∀ v, SuppM qQ (P.n v)

def Fr.split {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) : PD Φ.ι Γ R :=
  ⟨mapRep a (diagRep Φ.χ), fun _ => 1⟩

end UpperTheory.V.Ws

end
