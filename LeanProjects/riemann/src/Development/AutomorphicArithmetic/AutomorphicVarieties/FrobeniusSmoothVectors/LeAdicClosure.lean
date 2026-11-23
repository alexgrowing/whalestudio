import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def w (n : ℕ) (i : Fin n) : ℤ := if n = 3 then 1 - (i : ℕ) else (n : ℤ) - 1 - 2 * (i : ℕ)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (n : ℕ)

def ordProd {H K : Type} [CommRing K] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    Matrix (Fin n) (Fin n) K := (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) K)).prod

theorem ordProd_map {H K K' : Type} [CommRing K] [CommRing K'] {n : ℕ} (f : K →+* K')
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => f.mapMatrix (r s)) (fun i s => f (ψ i s)) g = f.mapMatrix (ordProd r ψ g) := by
  simp only [ordProd, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, map_sub]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

@[ext] structure NRep (K : Type) [CommRing K] where
  r : F.G0 →* Matrix (Fin n) (Fin n) K
  ψ : ∀ v, Fin n → F.Gv v →* Kˣ
  pol : ∀ g, r (F.star g) = Jmat K n * (r g)ᵀ * Jmat K n
  diag : ∀ i j, i ≠ j → (r F.g0 - r (F.star F.g0)) i j = 0
  ord : ∀ v g, ordProd (fun s => r (F.loc0 v s)) (fun i s => (ψ v i s : K)) g = 0

namespace NRep

variable {F n} {K K' : Type} [CommRing K] [CommRing K']

def map (f : K →+* K') (ρ : NRep F n K) : NRep F n K' where
  r := (f.mapMatrix : Matrix (Fin n) (Fin n) K →+* _).toMonoidHom.comp ρ.r
  ψ v i := (Units.map f.toMonoidHom).comp (ρ.ψ v i)
  pol g := by
    show f.mapMatrix (ρ.r (F.star g)) = Jmat K' n * (f.mapMatrix (ρ.r g))ᵀ * Jmat K' n
    rw [ρ.pol, map_mul, map_mul]
    simp only [RingHom.mapMatrix_apply, Jmat_map, Matrix.transpose_map]
  diag i j h := by
    show f (ρ.r F.g0 i j) - f (ρ.r (F.star F.g0) i j) = 0
    rw [← map_sub]
    exact (congrArg f (ρ.diag i j h)).trans (map_zero f)
  ord v g := (ordProd_map f _ _ g).trans (by rw [ρ.ord, map_zero])

@[simp] theorem map_r (f : K →+* K') (ρ : NRep F n K) (g : F.G0) (i j : Fin n) :
    (ρ.map f).r g i j = f (ρ.r g i j) := rfl

@[simp] theorem map_ψ (f : K →+* K') (ρ : NRep F n K) (v : F.V) (i : Fin n) (g : F.Gv v) :
    ((ρ.map f).ψ v i g : K') = f (ρ.ψ v i g) := rfl

theorem map_map {K'' : Type} [CommRing K''] (f : K →+* K') (f' : K' →+* K'') (ρ : NRep F n K) :
    (ρ.map f).map f' = ρ.map (f'.comp f) := rfl

def restrict {O : Type} [CommRing O] [Algebra O K] (ρ : NRep F n K) (A : Subalgebra O K)
    (h1 : ∀ g i j, ρ.r g i j ∈ A) (h2 : ∀ v i g, (ρ.ψ v i g : K) ∈ A) : NRep F n A where
  r :=
    { toFun := fun g => Matrix.of fun i j => ⟨ρ.r g i j, h1 g i j⟩
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [h, Matrix.one_apply]
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  ψ v i :=
    { toFun := fun g => ⟨⟨ρ.ψ v i g, h2 v i g⟩, ⟨ρ.ψ v i g⁻¹, h2 v i g⁻¹⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  pol g := by
    refine Matrix.map_injective (f := (A.val : A →+* K)) Subtype.val_injective ?_
    show _ = (A.val : A →+* K).mapMatrix _
    rw [map_mul, map_mul]
    simp only [RingHom.mapMatrix_apply, Jmat_map]
    exact ρ.pol g
  diag i j h := Subtype.ext (ρ.diag i j h)
  ord v g := by
    refine Matrix.map_injective (f := (A.val : A →+* K)) Subtype.val_injective ?_
    show (A.val : A →+* K).mapMatrix _ = (A.val : A →+* K).mapMatrix _
    rw [← ordProd_map, map_zero]
    exact ρ.ord v g

def Cont (I : Ideal K) (ρ : NRep F n K) : Prop :=
  (∀ i j, AdicCont I fun g => ρ.r g i j) ∧ ∀ v i, AdicCont I fun g => (ρ.ψ v i g : K)

def IsBar (f : k →+* K) (ρ : NRep F n K) : Prop :=
  (∀ g i, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) ∧ ∀ v i g, (ρ.ψ v i g : K) = f ((F.Ψ (F.loc v g) ^ w n i : kˣ) : k)

def IsDiag (ρ : NRep F n K) : Prop := ∀ g i j, i ≠ j → ρ.r g i j = 0

def triP (ρ : NRep F n K) : Ideal K := Ideal.span {x | ∃ g i j, j < i ∧ x = ρ.r g i j}

def triM (ρ : NRep F n K) : Ideal K := Ideal.span {x | ∃ g i j, i < j ∧ x = ρ.r g i j}

def ee (ρ : NRep F n K) : Ideal K := Ideal.span {x | ∃ g i j, Odd (w n i - w n j) ∧ x = ρ.r g i j}

def OffTri (ρ : NRep F n K) (p : Ideal K) : Prop := ¬ ρ.triP ≤ p ∧ ¬ ρ.triM ≤ p

def TI (ρ : NRep F n K) (p : Ideal K) : Prop := ρ.OffTri p ∧ (n = 3 → ¬ ρ.ee ≤ p)

def TE (ρ : NRep F n K) (p : Ideal K) : Prop := ρ.OffTri p ∧ n = 3 ∧ ρ.ee ≤ p

def Coin (ρ : NRep F n K) (p : Ideal K) (v : F.V) (i j : Fin n) : Prop :=
  ∀ g ∈ F.Nv v, (ρ.ψ v i g : K) - ρ.ψ v j g ∈ p

def mon (ρ : NRep F n K) (j : ℤ) : Set K :=
  {x | ∃ L : List (F.G0 × Fin n × Fin n), (L.map fun s => w n s.2.1 - w n s.2.2).sum = j ∧
    x = (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod}

end NRep

def Irr {H K : Type} [Field K] {ι : Type} [Fintype ι] (r : H → Matrix ι ι K) : Prop :=
  ∀ U : Submodule K (ι → K), (∀ g, ∀ u ∈ U, r g *ᵥ u ∈ U) → U = ⊥ ∨ U = ⊤

def adicClosure {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (S : Subalgebra O R) :
    Subalgebra O R where
  carrier := {x | ∀ N : ℕ, ∃ y ∈ S, x - y ∈ maximalIdeal R ^ N}
  mul_mem' {a b} ha hb N := by
    obtain ⟨x, hx, h1⟩ := ha N
    obtain ⟨y, hy, h2⟩ := hb N
    refine ⟨x * y, mul_mem hx hy, ?_⟩
    have : a * b - x * y = (a - x) * b + x * (b - y) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
  add_mem' {a b} ha hb N := by
    obtain ⟨x, hx, h1⟩ := ha N
    obtain ⟨y, hy, h2⟩ := hb N
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem h1 h2
  algebraMap_mem' c N := ⟨_, S.algebraMap_mem c, by simp⟩

theorem le_adicClosure {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (S : Subalgebra O R) :
    S ≤ adicClosure S := fun x hx _ => ⟨x, hx, by simp⟩

class IsCoef (l : outParam ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop where
  complete : IsAdicComplete (maximalIdeal O) O
  fin : Finite (ResidueField O)
  char : CharP (ResidueField O) l

attribute [instance] IsCoef.complete IsCoef.fin IsCoef.char

section Space

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] (F : Frame l (ResidueField O)) (n : ℕ)

variable {F n} in

def IsLift {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) : Prop :=
  ρ.Cont (maximalIdeal R) ∧ (ρ.map (res O R : R →+* ResidueField O)).IsBar (RingHom.id _) ∧
    (ρ.map (res O R : R →+* ResidueField O)).IsDiag

structure Space : Type 1 where
  R : Type
  [cr : CommRing R]
  [al : Algebra O R]
  [co : IsCO O R]
  ρ : NRep F n R
  lift : IsLift O ρ
  univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (ρ' : NRep F n C), IsLift O ρ' →
    ∃! f : R →ₐ[O] C, ρ.map (f : R →+* C) = ρ'

attribute [instance] Space.cr Space.al Space.co

namespace Space

variable {O F n} (S : Space O F n)

def B : Subalgebra O S.R :=
  adicClosure (Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}))

def A : Subalgebra O S.R := Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})

theorem B_le_A : S.B ≤ S.A := fun _ hx => Algebra.subset_adjoin (Or.inl hx)

theorem ψ_mem (v : F.V) (i : Fin n) (g : F.Gv v) : (S.ρ.ψ v i g : S.R) ∈ S.B :=
  le_adicClosure _ (Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩))

theorem mon_mem {x : S.R} (hx : x ∈ S.ρ.mon 0) : x ∈ S.B := le_adicClosure _ (Algebra.subset_adjoin (Or.inl hx))

theorem r_mem (g : F.G0) (i j : Fin n) : S.ρ.r g i j ∈ S.A := Algebra.subset_adjoin (Or.inr ⟨g, i, j, rfl⟩)

def inc : S.B →ₐ[O] S.A := Subalgebra.inclusion S.B_le_A

instance : Algebra S.B S.A := (S.inc : S.B →+* S.A).toAlgebra

instance : IsScalarTower O S.B S.A := IsScalarTower.of_algebraMap_eq fun _ => rfl

def u : NRep F n S.A := S.ρ.restrict S.A S.r_mem fun v i g => S.B_le_A (S.ψ_mem v i g)

def ψB (v : F.V) (i : Fin n) (g : F.Gv v) : S.B := ⟨S.ρ.ψ v i g, S.ψ_mem v i g⟩

def aB (g : F.G0) (i : Fin n) : S.B := ⟨S.ρ.r g i i, S.mon_mem ⟨[(g, i, i)], by simp, by simp⟩⟩

def trB (g : F.G0) : S.B := ∑ i, S.aB g i

def mB : Ideal S.B := (maximalIdeal S.R).comap (S.B.val : S.B →+* S.R)

def π (p : Ideal S.A) : Ideal S.B := p.comap (S.inc : S.B →+* S.A)

def gr (j : ℤ) : Submodule S.B S.A := Submodule.span S.B (S.u.mon j)

def IsHom (I : Ideal S.A) : Prop := I = Ideal.span {x | x ∈ I ∧ ∃ j, x ∈ S.gr j}

def lamId : Ideal S.B :=
  (maximalIdeal O).map (algebraMap O S.B) ⊔
    Ideal.span {x | ∃ v i g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ x = S.ψB v i g - 1}

def FinLam (I : Ideal S.B) : Prop := S.mB ≤ (I ⊔ S.lamId).radical

def BB : Set (PrimeSpectrum S.A) := {p | S.mB ≤ S.π p.asIdeal ∧ ¬ S.u.triP ≤ p.asIdeal}

structure Loc (x : Ideal S.A) : Type 1 where
  O' : Type
  [cO : CommRing O']
  [dO : IsDomain O']
  [vO : IsDiscreteValuationRing O']
  [coef : IsCoef l O']
  [aO : Algebra O O']
  [fO : Module.Finite O O']
  unr : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O'
  R : Type
  [cr : CommRing R]
  [al' : Algebra O' R]
  [co : IsCO O' R]
  [al : Algebra O R]
  [tw : IsScalarTower O O' R]
  ι : S.A →ₐ[O] R
  lies : (maximalIdeal R).comap (ι : S.A →+* R) = x
  univ : ∀ (C : Type) [CommRing C] [Algebra O' C] [IsCO O' C] [Algebra O C] [IsScalarTower O O' C]
    (f : S.A →ₐ[O] C), (∀ a, res O' C (f a) = res O' R (ι a)) → ∃! g : R →ₐ[O'] C, ∀ a, g (ι a) = f a

attribute [instance] Loc.cO Loc.dO Loc.vO Loc.coef Loc.aO Loc.fO Loc.cr Loc.al' Loc.co Loc.al Loc.tw

namespace Loc

variable {S} {x : Ideal S.A} (L : S.Loc x)

def ρ : NRep F n L.R := S.u.map (L.ι : S.A →+* L.R)

def im (P : Ideal L.R) : Ideal S.A := P.comap (L.ι : S.A →+* L.R)

def π (P : Ideal L.R) : Ideal S.B := S.π (L.im P)

end Loc

end Space

end Space

structure IsThickMod {F : Frame l k} {Q : Type} [CommRing Q] (ρ : NRep F 3 Q) (r : F.G0 →* Matrix (Fin 3) (Fin 3) Q) :
    Prop where
  even : ∀ g i j, ¬ Odd (w 3 i - w 3 j) → r g i j = ρ.r g i j
  sub : ∀ g, r g 1 0 = 0 ∧ r g 1 2 = 0
  ord : ∀ v g, ordProd (fun s => r (F.loc0 v s)) (fun i s => (ρ.ψ v i s : Q)) g = 0
  ord_star : ∀ v g, ordProd (fun s => r (F.star (F.loc0 v s))) (fun i s => (ρ.ψ v i.rev s : Q)) g = 0
  nonsplit : ∀ (K : Type) [Field K] (f : Q →+* K), Function.Injective f →
    ¬ ∃ y : Fin 3 → K, y 1 = 1 ∧ ∀ g, (r g).map f *ᵥ y = f (r g 1 1) • y

def Thick {F : Frame l k} {R : Type} [CommRing R] [IsLocalRing R] (ρ : NRep F 3 R) (P : Ideal R) : Prop :=
  ρ.TE P ∧ ∃ r : F.G0 →* Matrix (Fin 3) (Fin 3) (R ⧸ P),
    (∀ i j, AdicCont ((maximalIdeal R).map (Ideal.Quotient.mk P)) fun g => r g i j) ∧
      IsThickMod (ρ.map (Ideal.Quotient.mk P)) r

end UpperTheory.V.Fr
