import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def UpT {C : Type} [Zero C] {n : ℕ} (M : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, j < i → M i j = 0

def bor {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | UpT ((g : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
  add_mem' {X Y} hX hY i j h := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

def lieT (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((w n i : ℤ) : K)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

@[ext] structure Box (F : Frame l k) (n : ℕ) (C : Type) [CommRing C] where
  r : F.Γ →* GG n C
  nu : ∀ s, (r s).right = F.del s
  g : F.V → GL (Fin n) C
  tri : ∀ v s, UpT ((g v : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
    (((g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))

variable {F : Frame l k} {n : ℕ}

namespace Box

variable {C C' : Type} [CommRing C] [CommRing C']

def map (f : C →+* C') (B : Box F n C) : Box F n C' where
  r := (GG.map f).comp B.r
  nu := B.nu
  g v := GeneralLinearGroup.map f (B.g v)
  tri v s i j h := by
    have e : ((GeneralLinearGroup.map f (B.g v) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
        (((GG.map f).comp B.r) (F.loc v s)).mat *
        (((GeneralLinearGroup.map f (B.g v))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul, ← map_inv]
      rfl
    rw [e]
    exact (congrArg f (B.tri v s i j h)).trans (map_zero f)

theorem map_map {C'' : Type} [CommRing C''] (f : C →+* C') (f' : C' →+* C'') (B : Box F n C) :
    (B.map f).map f' = B.map (f'.comp f) := rfl

def Cont (I : Ideal C) (B : Box F n C) : Prop := ∀ i j, AdicCont I fun s => (B.r s).mat i j

structure Of (B : Box F n C) (ρ : NRep F n C) : Prop where
  atc : (B.r F.c).mat = 1
  res : ∀ s : F.G0, (B.r s).mat = ρ.r s
  psi : ∀ v i s, ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i = ρ.ψ v i s

theorem Of.map {B : Box F n C} {ρ : NRep F n C} (h : B.Of ρ) (f : C →+* C') : (B.map f).Of (ρ.map f) where
  atc := by
    show ((B.r F.c).mat).map f = 1
    rw [h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  res s := by
    show ((B.r s).mat).map f = _
    rw [h.res]
    rfl
  psi v i s := by
    have e : (((B.map f).g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') * (ρ.map f).r (F.loc0 v s) *
        ((((B.map f).g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul]
      rfl
    rw [e]
    exact congrArg f (h.psi v i s)

def ad (B : Box F n C) : Representation C F.Γ (Matrix (Fin n) (Fin n) C) := adRep B.r

def b (B : Box F n C) (v : F.V) : Submodule C (Matrix (Fin n) (Fin n) C) := bor (B.g v)

end Box

structure NRep.Good {K : Type} [Field K] (ρ : NRep F n K) : Prop where
  two : (2 : K) ≠ 0
  zd : ∀ i j, i ≠ j → (ρ.r F.g0 - ρ.r (F.star F.g0)) i i ≠ (ρ.r F.g0 - ρ.r (F.star F.g0)) j j
  ψd : ∀ v, ∃ s, ∀ i j, i ≠ j → ρ.ψ v i s ≠ ρ.ψ v j s

section CO

variable (O : Type) [CommRing O] [IsLocalRing O]

abbrev NRep.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (ρ : NRep F n C) : NRep F n (ResidueField O) :=
  ρ.map (res O C : C →+* ResidueField O)

abbrev Box.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (B : Box F n C) : Box F n (ResidueField O) :=
  B.map (res O C : C →+* ResidueField O)

structure NRep.Univ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) : Prop where
  cont : ρ.Cont (maximalIdeal R)
  univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (ρ' : NRep F n C), ρ'.Cont (maximalIdeal C) →
    ρ'.bar O = ρ.bar O → ∃! g : R →ₐ[O] C, ρ.map (g : R →+* C) = ρ'

abbrev Tan (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O)

def Box.tanCo {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R) :
    (R →ₗ[O] ResidueField O) →ₗ[ResidueField O] (F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun D s := (B.r s).mat.map D *
    ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
  map_add' D D' := funext fun s => by
    rw [Pi.add_apply, ← Matrix.add_mul]
    rfl
  map_smul' c D := funext fun s => by
    rw [Pi.smul_apply, RingHom.id_apply, ← Matrix.smul_mul]
    rfl

structure IsSq {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (μ : ResidueField O →+ C) : Prop where
  mul : ∀ a c, μ (res O C a * c) = a * μ c
  mem : ∀ c, μ c ∈ maximalIdeal C

variable {O}

open Classical in

def evK {C : Type} [CommRing C] [Algebra O C] (K : Ideal C) (u : K →ₗ[O] ResidueField O) (x : C) : ResidueField O :=
  if h : x ∈ K then u ⟨x, h⟩ else 0

theorem evK_of_mem {C : Type} [CommRing C] [Algebra O C] {K : Ideal C} (u : K →ₗ[O] ResidueField O) {x : C}
    (h : x ∈ K) : evK K u x = u ⟨x, h⟩ := dif_pos h

variable {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C] [Algebra O C]

structure SetLift (p : C' →ₐ[O] C) (B : Box F n C) where
  r : F.Γ → GL (Fin n) C'
  r_cont : ∀ i j, AdicCont (maximalIdeal C') fun s => r s i j
  r_map : ∀ s, GeneralLinearGroup.map (p : C' →+* C) (r s) = (B.r s).left
  g : F.V → GL (Fin n) C'
  g_map : ∀ v, GeneralLinearGroup.map (p : C' →+* C) (g v) = B.g v
  t : ∀ v, F.Gv v → GL (Fin n) C'
  t_cont : ∀ v i j, AdicCont (maximalIdeal C') fun s => t v s i j
  t_tri : ∀ v s, UpT (t v s : Matrix (Fin n) (Fin n) C')
  t_map : ∀ v s, GeneralLinearGroup.map (p : C' →+* C) (t v s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹

namespace SetLift

variable {p : C' →ₐ[O] C} {B : Box F n C} (D : SetLift p B)

def om (x : F.Γ × F.Γ) : Matrix (Fin n) (Fin n) C' :=
  ((D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def a (v : F.V) (s : F.Gv v) : Matrix (Fin n) (Fin n) C' :=
  ((D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def co : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O]
    (F.Γ × F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) × (∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun u := (fun x => (D.om x).map (evK _ u), fun v s => (D.a v s).map (evK _ u))
  map_add' u u' := by
    have e : ∀ x, evK _ (u + u') x = evK _ u x + evK _ u' x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]
  map_smul' c u := by
    have e : ∀ x, evK _ (c • u) x = c * evK _ u x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]

end SetLift

variable (O) in

def HasObs (R : Type) [CommRing R] [Algebra O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ →
    ∃ ob : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

def IsMinPres {σ R : Type} [CommRing R] [Algebra O R] (p : MvPowerSeries σ O →ₐ[O] R) : Prop :=
  Function.Surjective p ∧ ∀ f ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) f ∈ maximalIdeal O

end CO

end UpperTheory.V.Fr
