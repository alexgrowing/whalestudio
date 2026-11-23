import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ContinuousContractNth

noncomputable section

namespace UpperTheory.V.AlgebraTools.Cx

variable {A : Type} [CommRing A]

structure Sel (A : Type) [CommRing A] (ι : Type) : Type 1 where
  G : Cx A
  L : ι → Cx A
  P : ι → Cx A
  res : ∀ i, Hom G (L i)
  inc : ∀ i, Hom (P i) (L i)

namespace Sel

variable {ι : Type} (S : Sel A ι)

def dif : Hom (prod S.G (pi S.P)) (pi S.L) where
  f n := LinearMap.pi fun i => ((S.res i).f n).comp (LinearMap.fst A (S.G.X n) (∀ i, (S.P i).X n)) -
    ((S.inc i).f n).comp ((LinearMap.proj i).comp (LinearMap.snd A (S.G.X n) (∀ i, (S.P i).X n)))
  comm n x := funext fun i => by
    show (S.res i).f (n + 1) (S.G.d n x.1) - (S.inc i).f (n + 1) ((S.P i).d n (x.2 i)) =
      (S.L i).d n ((S.res i).f n x.1 - (S.inc i).f n (x.2 i))
    rw [map_sub, Hom.comm, Hom.comm]

def cx : Cx A := fib S.dif

def toG : Hom S.cx S.G :=
  Hom.comp ⟨fun n => LinearMap.fst A (S.G.X n) ((pi S.P).X n), fun _ _ => rfl⟩ (fibFst S.dif)

def toP (i : ι) : Hom S.cx (S.P i) :=
  Hom.comp ⟨fun n => (LinearMap.proj i).comp (LinearMap.snd A (S.G.X n) (∀ i, (S.P i).X n)), fun _ _ => rfl⟩
    (fibFst S.dif)

def grp (n : ℕ) : Submodule A (S.G.H n) :=
  ⨅ i, (LinearMap.range ((S.inc i).H n)).comap ((S.res i).H n)

structure Map (S T : Sel A ι) where
  g : Hom S.G T.G
  l : ∀ i, Hom (S.L i) (T.L i)
  p : ∀ i, Hom (S.P i) (T.P i)
  res : ∀ i n x, (T.res i).f n (g.f n x) = (l i).f n ((S.res i).f n x)
  inc : ∀ i n x, (T.inc i).f n ((p i).f n x) = (l i).f n ((S.inc i).f n x)

end Sel

def Hom.prodMap {K L K' L' : Cx A} (φ : Hom K K') (ψ : Hom L L') : Hom (prod K L) (prod K' L') :=
  ⟨fun n => (φ.f n).prodMap (ψ.f n), fun n x => Prod.ext (φ.comm n x.1) (ψ.comm n x.2)⟩

def Hom.piMap {ι : Type} {K L : ι → Cx A} (φ : ∀ i, Hom (K i) (L i)) : Hom (pi K) (pi L) :=
  ⟨fun n => LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i), fun n x => funext fun i => (φ i).comm n (x i)⟩

def Sel.Map.cx {ι : Type} {S T : Sel A ι} (m : Sel.Map S T) : Hom S.cx T.cx :=
  fibMap (m.g.prodMap (Hom.piMap m.p)) (Hom.piMap m.l) fun n x => funext fun i => by
    show (T.res i).f n (m.g.f n x.1) - (T.inc i).f n ((m.p i).f n (x.2 i)) =
      (m.l i).f n ((S.res i).f n x.1 - (S.inc i).f n (x.2 i))
    rw [map_sub, m.res, m.inc]

def Sel.Map.mul {ι : Type} (S : Sel A ι) (a : A) : Sel.Map S S where
  g := (Hom.id _).smul a
  l _ := (Hom.id _).smul a
  p _ := (Hom.id _).smul a
  res _ _ _ := map_smul _ _ _
  inc _ _ _ := map_smul _ _ _

section Two

variable (P Q : Type) [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

def twoX : ℕ → Type
  | 0 => P
  | 1 => Q
  | _ + 2 => PUnit

instance twoGrp : ∀ n, AddCommGroup (twoX P Q n)
  | 0 => inferInstanceAs (AddCommGroup P)
  | 1 => inferInstanceAs (AddCommGroup Q)
  | _ + 2 => inferInstanceAs (AddCommGroup PUnit)

instance twoMod : ∀ n, Module A (twoX P Q n)
  | 0 => inferInstanceAs (Module A P)
  | 1 => inferInstanceAs (Module A Q)
  | _ + 2 => inferInstanceAs (Module A PUnit)

variable {P Q}

def twoD (f : P →ₗ[A] Q) : ∀ n, twoX P Q n →ₗ[A] twoX P Q (n + 1)
  | 0 => f
  | _ + 1 => 0

def two (f : P →ₗ[A] Q) : Cx A where
  X := twoX P Q
  d := twoD f
  dd _ _ := rfl

def Hom.ofTwo (f : P →ₗ[A] Q) (L : Cx A) (u : P →ₗ[A] L.X 0) (v : Q →ₗ[A] L.X 1) (h : ∀ x, v (f x) = L.d 0 (u x))
    (h' : ∀ y, L.d 1 (v y) = 0) : Hom (two f) L where
  f
    | 0 => u
    | 1 => v
    | _ + 2 => 0
  comm
    | 0, x => h x
    | 1, y => (h' y).symm
    | _ + 2, _ => (map_zero _).symm

end Two

def FinUpTo (K : Cx A) (N : ℕ) : Prop := (∀ n, Module.length A (K.H n) ≠ ⊤) ∧ ∀ n, N ≤ n → Subsingleton (K.H n)

def chi (K : Cx A) (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, (-1) ^ n * ((Module.length A (K.H n)).toNat : ℤ)

abbrev IsRed {K N : Cx A} (a : A) (p : Hom K N) : Prop := SES ((Hom.id K).smul a) p

instance (ι : Type) : Inhabited (Sel A ι) :=
  ⟨⟨default, fun _ => default, fun _ => default, fun _ => Hom.id _, fun _ => Hom.id _⟩⟩

end UpperTheory.V.AlgebraTools.Cx

end
