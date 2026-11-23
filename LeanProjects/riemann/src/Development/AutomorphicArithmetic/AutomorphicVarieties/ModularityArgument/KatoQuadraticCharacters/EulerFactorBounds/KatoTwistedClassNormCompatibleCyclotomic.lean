import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftsWith

noncomputable section

open scoped MatrixGroups Matrix Classical
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

structure Lev (l n N M₀ M : ℕ) (g : SL(2, ℤ)) : Prop where
  eq : M = N * M₀
  dN : N ∣ M₀
  dl : l ^ n ∣ M₀
  pos : 1 ≤ n
  cop : Nat.Coprime l N
  g0 : (N : ℤ) ∣ en g 1 0

def Bas (l N : ℕ) {M : ℕ} (x y : Row M) : Prop :=
  Nat.Coprime l N ∧ ((x 0).val : ZMod l) * ((y 1).val : ZMod l) - ((x 1).val : ZMod l) * ((y 0).val : ZMod l) ≠ 0

def tp (p M : ℕ) (t : Fin 2 → ZMod p) : Row (p * M) := fun i => ((M * (t i).val : ℕ) : ZMod (p * M))

def pushB (X : Tower Ω ε) (p M : ℕ) [Fact p.Prime] (a : Fam X (p * M)) : Fam X M := fun x y =>
  ∏ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0),
    a (up p M x + tp p M tt.1) (up p M y + tp p M tt.2)

def lin (p N : ℕ) : Option (Fin p) → Fin 2 → ZMod p
  | none => ![0, 1]
  | some j => ![1, ((N * (j : ℕ) : ℕ) : ZMod p)]

def pushL (X : Tower Ω ε) (p N M : ℕ) [Fact p.Prime] (a : Fam X (p * M)) : Fam X M := fun x y =>
  ∏ o : Option (Fin p), ∏ i : ZMod p, ∏ j : ZMod p, a (up p M x + tp p M (i • lin p N o)) (up p M y + tp p M (j • lin p N o))

def hP (l p N : ℕ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![en (sgD N l p) 0 0 * p, N * en (sgD N l p) 0 1; en (sgD N l p) 1 0 / N * p, en (sgD N l p) 1 1]
  | some j => !![1, N * ((j : ℕ) : ℤ); 0, p]

def heF (X : Tower Ω ε) (l p N M : ℕ) (a : Fam X M) : Fam X M := fun x y =>
  ∏ o : Option (Fin p), slU X (toGQ (hP l p N o))
    (a (x ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M))) (y ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M))))

end

instance primeNeZero (p : ℕ) [h : Fact p.Prime] : NeZero p := ⟨h.out.ne_zero⟩

def SApi : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ), Equivalence (CgF X l n) ∧ (∀ a b a' b', CgF X l n a b → CgF X l n a' b' → CgF X l n (a + a') (b + b') ∧ CgF X l n (a - a') (b - b')) ∧
    (∀ (k : ℤ_[l]) a b, CgF X l n a b → CgF X l n (k • a) (k • b)) ∧
    (∀ (ι : Type) (S : Finset ι) (a b : ι → X.Fn l), (∀ i ∈ S, CgF X l n (a i) (b i)) → CgF X l n (∑ i ∈ S, a i) (∑ i ∈ S, b i)) ∧
    (∀ (k k' : ℤ_[l]) (a : X.Khat l), (l : ℤ_[l]) ^ n ∣ k - k' → AdicCompletion.eval (idl l) (X.Kl l) n (k • a - k' • a) = 0) ∧
    (∀ m a b, CgF X l n a b → CgF X l n (X.act l m a) (X.act l m b)) ∧
    (∀ s a b, CgF X l n a b → CgF X l n (X.galB l s a) (X.galB l s b)) ∧
    (∀ a b, CgF X l (n + 1) a b → CgF X l n a b) ∧ (∀ a b, CgF X l 0 a b) ∧
    (∀ s t a, X.galB l (s * t) a = X.galB l s (X.galB l t a)) ∧ ∀ a, X.galB l 1 a = a

def SCls : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ), (∀ f : X.Kˣ, Rep X l n f (clsK X l n (f : X.K))) ∧
    (∀ f f' a a', Rep X l n f a → Rep X l n f' a' → Rep X l n (f * f') (a + a') ∧ Rep X l n (f / f') (a - a')) ∧
    (∀ f a (k : ℕ), Rep X l n f a → Rep X l n (f ^ k) ((k : ℤ_[l]) • a)) ∧
    (∀ f f' a a', Rep X l n f a → Rep X l n f' a' → Cgr (l ^ n) f f' → AdicCompletion.eval (idl l) (X.Kl l) n (a - a') = 0) ∧
    (∀ (φ : X.K ≃+* X.K) f a, Rep X l n f a → Rep X l n (Units.map (φ : X.K →* X.K) f) (X.kmap l φ a)) ∧
    (∀ f a, Rep X l (n + 1) f a → Rep X l n f a) ∧
    ∀ (f : X.Kˣ) (k : ℤ_[l]) a, Rep X l n f a → ∃ j : ℕ, Rep X l n (f ^ j) (k • a)

def SInvApi : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ), InvM X l N w n 0 ∧ (∀ a b, InvM X l N w n a → InvM X l N w n b → InvM X l N w n (a + b) ∧ InvM X l N w n (a - b)) ∧
    (∀ (k : ℤ_[l]) a, InvM X l N w n a → InvM X l N w n (k • a)) ∧ (∀ a b, CgF X l n a b → InvM X l N w n b → InvM X l N w n a) ∧
    (∀ (ι : Type) (S : Finset ι) (a : ι → X.Fn l), (∀ i ∈ S, InvM X l N w n (a i)) → InvM X l N w n (∑ i ∈ S, a i)) ∧
    (∀ a, InvM X l N w (n + 1) a → InvM X l N w n a) ∧ (∀ a, InvM X l N w 0 a) ∧
    ∀ (m : (Matrix (Fin 2) (Fin 2) ℤ)) t, 0 < m.det → PolMod X l w n t → PolMod X l w n (X.act l m t)

def SGalAct : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ), 0 < N → ∀ (s : Ω ≃ₐ[ℚ] Ω) a, InvM X l N w n a → InvM X l N w n (X.galB l s a) ∧
    ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l,
      InvM X l N w n (X.act l (δ : (Matrix (Fin 2) (Fin 2) ℤ)) a) ∧ CgF X l n (X.galB l s (X.act l (δ : (Matrix (Fin 2) (Fin 2) ℤ)) a)) (X.act l (δ : (Matrix (Fin 2) (Fin 2) ℤ)) (X.galB l s a))

def SHeckeInv : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n p : ℕ), 0 < N → p.Prime → Nat.Coprime p (l * N) → ∀ a, InvM X l N w n a → InvM X l N w n (X.heckeT N l p a)

def SHeckeGal : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n p : ℕ), 0 < N → p.Prime → Nat.Coprime p (l * N) → ∀ (s : Ω ≃ₐ[ℚ] Ω) a, InvM X l N w n a →
    CgF X l n (X.galB l s (X.heckeT N l p a)) (X.heckeT N l p (X.galB l s a))

def SCdFacts : Prop :=
  ∀ (N M₀ M : ℕ) [NeZero N] [NeZero M₀] [NeZero M], M = N * M₀ →
    (∀ m m' : Matrix (Fin 2) (Fin 2) (ZMod M), ((m 1 0).val : ZMod N) = 0 → ((m' 1 0).val : ZMod N) = 0 →
      cD N M₀ (m * m') = cD N M₀ m * cD N M₀ m') ∧ cD N M₀ (1 : Matrix (Fin 2) (Fin 2) (ZMod M)) = 1 ∧
    (∀ m : GL (Fin 2) (ZMod M), (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0 → ∀ x y : Row M₀, Ok x y →
      Ok (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))) ∧
    ∀ h h' : (Matrix (Fin 2) (Fin 2) ℤ), !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1] →
      cD N M₀ (h.map (Int.castRingHom (ZMod M))) = h'.map (Int.castRingHom (ZMod M₀))

def SSlD : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ), 0 < N →
    (∀ s f, X.gal s (slD X N f) = slD X N (X.gal s f)) ∧
    (∀ h h' : (Matrix (Fin 2) (Fin 2) ℤ), 0 < h.det → !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1] → ∀ f,
      X.sl (toGQ h) (slD X N f) = slD X N (X.sl (toGQ h') f)) ∧
    (∀ γ : SL(2, ℤ), toGQ (γ : (Matrix (Fin 2) (Fin 2) ℤ)) = ofSL γ) ∧
    (∀ h h' : (Matrix (Fin 2) (Fin 2) ℤ), 0 < h.det → 0 < h'.det → toGQ (h * h') = toGQ h * toGQ h') ∧
    (∀ m (q : GQ), ∀ f ∈ X.Un m, slU X q f ∈ X.Un m) ∧ (∀ m s, ∀ f ∈ X.Un m, galU X s f ∈ X.Un m) ∧
    (∀ m, 1 ∈ X.Un m ∧ ∀ f ∈ X.Un m, ∀ f' ∈ X.Un m, f * f' ∈ X.Un m ∧ f⁻¹ ∈ X.Un m) ∧
    ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω), cyc M s = (cycM M s : ZMod M) ∧ (∀ t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t) ∧
      (∀ y, cycM M (repM M y : Ω ≃ₐ[ℚ] Ω) = y) ∧ (s ∈ fixMu Ω M ↔ cycM M s = 1) ∧
      ∀ (M' : ℕ) [NeZero M'] (h : M' ∣ M), Units.map (ZMod.castHom h (ZMod M')).toMonoidHom (cycM M s) = cycM M' s

def SCycZ : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (s : Ω ≃ₐ[ℚ] Ω),
    cycMod (F := ℚ) (Ω := Ω) l r s = cycM (l ^ r) s ∧
      (l : ℤ_[l]) ^ r ∣ (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - ((cycM (l ^ r) s : ZMod (l ^ r)).val : ℤ_[l])

def SXiMul : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (x y : Row M₀), Ok x y → ∀ (P : (ZMod M)ˣ → Prop),
    (∀ a a' b b' : Fam X M₀, (∀ x y, Ok x y → Cgr (l ^ n) (a x y) (a' x y * b x y / b' x y)) →
      CgF X l n (Xi X l n N M₀ M w g x y P a)
        (Xi X l n N M₀ M w g x y P a' + (Xi X l n N M₀ M w g x y P b - Xi X l n N M₀ M w g x y P b'))) ∧
    (∀ (a : Fam X M₀) (k : ℕ), CgF X l n (Xi X l n N M₀ M w g x y P fun x y => a x y ^ k) ((k : ℤ_[l]) • Xi X l n N M₀ M w g x y P a)) ∧
    (∀ a : Fam X M₀, CgF X l n (Xi X l (n + 1) N M₀ M w g x y P a) (Xi X l n N M₀ M w g x y P a)) ∧
    ∀ (a : Fam X M₀) (A : Type) (π : (ZMod M)ˣ → A) (t : A) [DecidableEq A],
      Xi X l n N M₀ M w g x y (fun z => π z = t) a =
        ∑ z ∈ Finset.univ.filter (fun z => π z = t), Xi X l n N M₀ M w g x y (fun z' => z' = z) a

def SXiTw : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (x y : Row M₀) (P : (ZMod M)ˣ → Prop) (a : Fam X M₀) (s : Ω ≃ₐ[ℚ] Ω),
    CgF X l n (Xi X l n N M₀ M w g x y P (tw X (l ^ n) M₀ s a)) (X.galB l s (Xi X l n N M₀ M w g x y (fun z => P (z * cycM M s)) a))

def SXiAct : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (x y : Row M₀), Ok x y → ∀ (P : (ZMod M)ˣ → Prop) (a : Fam X M₀), Eqv X (l ^ n) M₀ a →
    ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ ν : (ZMod M)ˣ,
      ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N) → ((ν : ZMod M).val : ZMod (l ^ n)) = 1 → (∀ z, P (z * ν ^ 2) ↔ P z) →
      CgF X l n (X.act l (δ : (Matrix (Fin 2) (Fin 2) ℤ)) (Xi X l n N M₀ M w g x y P a))
        (Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y) P a)

def SXiInv : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ (x y : Row M₀), Ok x y → ∀ (P : (ZMod M)ˣ → Prop) (a : Fam X M₀), Eqv X (l ^ n) M₀ a →
    InvM X l N w n (Xi X l n N M₀ M w g x y P a)

def SXiScal : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (x y : Row M₀) (P : (ZMod M)ˣ → Prop) (a : Fam X M₀) (ν : (ZMod M)ˣ), ((ν : ZMod M).val : ZMod N) = 1 →
    CgF X l n (((ν : ZMod M).val : ℤ_[l]) ^ w • Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y) P a)
      (((ν : ZMod M).val : ℤ_[l]) ^ 2 • Xi X l n N M₀ M w g x y (fun z => P (z * ν⁻¹ ^ 2)) a)

def SXiCoh : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ (x y : Row M₀), Ok x y → ∀ (A : Type) [Group A] (π : (ZMod M)ˣ →* A) (u u' : (Ω ≃ₐ[ℚ] Ω) → Fam X M₀),
    Coh X (l ^ n) M₀ u u' → CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t) (u s)) fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t) (u' s)

def SXiOne : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (x y : Row M₀), Ok x y → ∀ (a : Fam X M₀), Eqv X (l ^ n) M₀ a →
    CgF X l n (trM X l N M w g (clsK X l n (slD X N (a x y : X.K)))) (Xi X l n N M₀ M w g x y (fun z => z = 1) a)

def STrM : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ a : X.Kˣ, a ∈ X.Un (l ^ n) → InvMod X M (l ^ n) a → InvM X l N w n (trM X l N M w g (clsK X l n (a : X.K))) ∧
    ∀ σ ∈ fixMu Ω M, CgF X l n (X.galB l σ (trM X l N M w g (clsK X l n (a : X.K)))) (trM X l N M w g (clsK X l n (X.gal σ a)))

def STopRel : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ (c d : ℕ) ws, Laws X l c d ws → Lv c d M₀ → ∀ (x y : Row M₀), Ok x y → ∀ x' y' : Fin 2 → ℚ,
    (∀ i, ∃ j : ℤ, x' i = toQ M₀ x i + j) → (∀ i, ∃ j : ℤ, y' i = toQ M₀ y i + j) →
    ∃ β, InvM X l N w n β ∧ ∀ σ ∈ fixMu Ω M, CgF X l n (clsG X l n N M w c d g x' y' σ)
      (Xi X l n N M₀ M w g x y (fun z => z = 1) (ws n M₀ σ) + (X.galB l σ β - β))

def STopCocG : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ (x y : Row M₀), Ok x y → ∀ u, IsCoc X (l ^ n) M₀ u → ∀ z β, InvM X l N w n β →
    (∀ σ ∈ fixMu Ω M, CgF X l n (z σ) (Xi X l n N M₀ M w g x y (fun z => z = 1) (u σ) + (X.galB l σ β - β))) → TopCoc X l N w n M z

def SBridge : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → LiftsWith X l N w (cL X l N w) →  ∀ (x y : Row M₀), Ok x y → ∀ u, IsCoc X (l ^ n) M₀ u → ∀ z β, InvM X l N w n β →
    (∀ σ ∈ fixMu Ω M, CgF X l n (z σ) (Xi X l n N M₀ M w g x y (fun z => z = 1) (u σ) + (X.galB l σ β - β))) →
    ∀ (A : Type) [Group A] [DecidableEq A] (π : (ZMod M)ˣ →* A), CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (GlobalTheory.KA.push π (shB X l M z)) fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t) (u s)

def SCohApi : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ), 0 < N → ∀ (A : Type) [CommGroup A] (κ : (Ω ≃ₐ[ℚ] Ω) → A), Equivalence (CohB X l N w n κ) ∧
    (∀ z z', (∀ s y, CgF X l n (z s y) (z' s y)) → CohB X l N w n κ z z') ∧
    (∀ z z' v v', CohB X l N w n κ z z' → CohB X l N w n κ v v' → CohB X l N w n κ (z + v) (z' + v') ∧ CohB X l N w n κ (z - v) (z' - v')) ∧
    (∀ (k : ℤ_[l]) (t : A) z z', CohB X l N w n κ z z' → CohB X l N w n κ (fun s y => k • z s (y * t)) fun s y => k • z' s (y * t)) ∧
    (∀ z z', CohB X l N w (n + 1) κ z z' → CohB X l N w n κ z z') ∧ (∀ z z', CohB X l N w 0 κ z z') ∧
    (∀ (A' : Type) [CommGroup A'] [Fintype A] [DecidableEq A'] (π : A →* A') z z', CohB X l N w n κ z z' →
      CohB X l N w n (fun s => π (κ s)) (GlobalTheory.KA.push π z) (GlobalTheory.KA.push π z')) ∧
    ∀ p : ℕ, p.Prime → Nat.Coprime p (l * N) → ∀ z z', CohB X l N w n κ z z' →
      CohB X l N w n κ (fun s y => X.heckeT N l p (z s y)) (fun s y => X.heckeT N l p (z' s y)) ∧
      CohB X l N w n κ (fun s y => X.diam N l p (z s y)) fun s y => X.diam N l p (z' s y)

def SXiDist : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (M' : ℕ) [NeZero M'] [NeZero (l * M₀)] (h : M ∣ M'), M' = N * (l * M₀) → ∀ x y : Row (l * M₀), Bas l N x y →
    ∀ (P : (ZMod M)ˣ → Prop) (a : Fam X (l * M₀)),
      CgF X l n (Xi X l n N (l * M₀) M' w g x y (fun z => P (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z)) a)
        (Xi X l n N M₀ M w g (dn l M₀ x) (dn l M₀ y) P (pushD X l M₀ a))

def SXiTame : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (p M' : ℕ) [Fact p.Prime] [NeZero M'] [NeZero (p * M₀)] (h : M ∣ M'), M' = N * (p * M₀) → Nat.Coprime p M →
    ∀ (x y : Row M₀) (t t' : Fin 2 → ZMod p), t 0 * t' 1 - t 1 * t' 0 ≠ 0 → ∀ (P : (ZMod M)ˣ → Prop) (a : Fam X (p * M₀)),
      CgF X l n (Xi X l n N (p * M₀) M' w g (up p M₀ x + tp p M₀ t) (up p M₀ y + tp p M₀ t')
          (fun z => P (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z)) a)
        (Xi X l n N M₀ M w g x y P (pushB X p M₀ a))

def SPairs : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (p N M₀ : ℕ) [Fact p.Prime] [NeZero M₀], Nat.Coprime p (N * M₀) →
    ∀ (a : Fam X (p * M₀)) (x y : Row M₀), pushB X p M₀ a x y * pushL X p N M₀ a x y =
      pushD X p M₀ a ((p : ZMod M₀) • x) ((p : ZMod M₀) • y) * a (up p M₀ x) (up p M₀ y) ^ p

def SLineCoh : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ p c d : ℕ) [Fact p.Prime] [NeZero N] [NeZero M₀], Nat.Coprime p (l * N * M₀) → ∀ ws, Laws X l c d ws → Lv c d (p * M₀) →
    Coh X (l ^ n) M₀ (fun s => pushL X p N M₀ (ws n (p * M₀) s)) fun s => heF X l p N M₀ (ws n M₀ s)

def SXiHecke : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)), Lev l n N M₀ M g → ∀ (p : ℕ) [Fact p.Prime] (q : (ZMod M)ˣ), (q : ZMod M) = p → ∀ (x y : Row M₀) (P : (ZMod M)ˣ → Prop) (a : Fam X M₀),
    CgF X l n (X.heckeT N l p (Xi X l n N M₀ M w g ((p : ZMod M₀) • x) ((p : ZMod M₀) • y) (fun z => P (z * q)) a))
      ((p : ℤ_[l]) • Xi X l n N M₀ M w g x y P (heF X l p N M₀ a))

def STop0 : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, TopCoc X l N w n (topM l n r (N * N)) (cls0 X l n r N x c d w g)

def STopT : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → p.Prime → Nat.Coprime p (l * N * c * d) → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, TopCoc X l N w n (lvT l n r N p) (clsT X l n r N p x c d w g)

def KatoClassNormCompatibleCyclotomic : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, CohB X l N w n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (GlobalTheory.KA.push (redL l r) (Y0 X l n (r + 1) N x c d w g)) (Y0 X l n r N x c d w g)

def KatoClassCompatibleModPowers : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, CohB X l N w n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y0 X l (n + 1) r N x c d w g) (Y0 X l n r N x c d w g)

def KatoTwistedClassNormCompatibleCyclotomic : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → p.Prime → Nat.Coprime p (l * N * c * d) → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, CohB X l N w n (kT l r p)
    (GlobalTheory.KA.push (Prod.map id (redL l r)) (YT X l n (r + 1) N p x c d w g)) (YT X l n r N p x c d w g)

def KatoTwistedClassCompatibleModPowers : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → p.Prime → Nat.Coprime p (l * N * c * d) → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, CohB X l N w n (kT l r p) (YT X l (n + 1) r N p x c d w g) (YT X l n r N p x c d w g)

def KatoClassHeckeEulerFactorRelation : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)), Hyp l N c d g → p.Prime → Nat.Coprime p (l * N * c * d) → (∃ ws, Laws X l c d ws) → LiftsWith X l N w (cL X l N w) →  ∀ n r : ℕ, CohB X l N w n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)
    (fun s y => (p : ℤ_[l]) • ∑ a, YT X l n r N p x c d w g s (a, y))
    fun s y => (p : ℤ_[l]) • Y0 X l n r N x c d w g s y - X.heckeT N l p (Y0 X l n r N x c d w g s (y * inv1 (l ^ r) p)) +
      (p : ℤ_[l]) ^ w • X.diam N l p (Y0 X l n r N x c d w g s (y * inv1 (l ^ r) p ^ 2))

def SBStab : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), 0 < N → ∀ b ∈ X.B N l w, (∀ s, X.galB l s b ∈ X.B N l w) ∧
    (∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w) ∧
    ∀ p : ℕ, p.Prime → Nat.Coprime p (l * N) → X.heckeT N l p b ∈ X.B N l w

def SLiftOk : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) [NeZero N],
    l ≠ 2 → Nat.Coprime l N → Odd w → LiftsWith X l N w (cL X l N w)

end UpperTheory.V.Z.Kato.Nb

end
