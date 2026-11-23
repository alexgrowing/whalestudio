import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobeniusCompatInclusion

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

def FixedIntegersIsUnitOfNotMemPrimeSpan : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : R0 A, x ∉ Ideal.span {(l : R0 A)} → IsUnit x

def FixedIntegersMonicHasRootModPrime : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ P : Polynomial (R0 A), P.Monic → 0 < P.natDegree → ∃ x : R0 A, P.eval x ∈ Ideal.span {(l : R0 A)}

def SFrobEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → (∃ fr ∈ Dec (F := ℚ) A, IsFrob A l fr ∧ cycBar ℚ Ω l fr = 1) ∧ (∀ σ ∈ Dec (F := ℚ) A, ∀ σ' ∈ Dec (F := ℚ) A, IsFrob A l σ → IsFrob A l σ' → σ⁻¹ * σ' ∈ Ine (F := ℚ) A) ∧ ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u

def SFixAbs : Prop :=
  ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] R] (σ : R ≃+* R), FrobLift R p σ → ∀ x : R, σ x = x → ∃ z : ℤ_[p], algebraMap ℤ_[p] R z = x

def SFrEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ j : Ω →+* Qbar l, (∀ x ∈ A, ‖j x‖ ≤ 1) → Nonempty (Fr l A j)

def SBasEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), Nonempty (Bas c) ∧ ∀ β : Bas c, (∀ i, ‖β.val i‖ ≤ 1) ∧ (∀ (n : ℕ) (x : Fin β.d → ℤ_[l]), Cg n (∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (x i)) 0 → ∀ i, (l : ℤ_[l]) ^ n ∣ x i) ∧ (∀ (n : ℕ) (x : c.O), Cg n (x : PadicAlgCl l) 0 → ∃ y : c.O, x = (l : c.O) ^ n * y) ∧ ∀ x : Qbar l, x ∈ c.O → ‖x‖ = 1 → x⁻¹ ∈ c.O

def SGenEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ (g : ℕ) (hg : ¬ l ∣ g), 2 ≤ g ∧ ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), x ∈ Subgroup.zpowers (un g hg r)

def SUniq : Prop :=
  ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h : PowerSeries R) (c m₀ : ℕ), (∀ m, m₀ ≤ m → LC p m (m - c) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) h) 0) → h = 0

def SWD : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j), ∀ ζ : ℕ → Ω, Roots l ζ → ∀ m, 1 ≤ m → ∀ P : Polynomial (R0 A), (pv P (ζ m) = 0 → ev Φ.R l m (Φ.ser P) = 0) ∧ ((pv P (ζ m) ∈ A ∧ pv P (ζ m) ≠ 0 ∧ (pv P (ζ m))⁻¹ ∈ A) → IsUnit (Φ.ser P))

def SPolyEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ ζ : ℕ → Ω, Roots l ζ → ∀ m, ∀ u ∈ A, (∀ s ∈ Hm l A m, s u = u) → ∃ P : Polynomial (R0 A), pv P (ζ m) = u

def SDlogCmp : Prop :=
  ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (m n N : ℕ), 1 ≤ m → ∀ F g w : PowerSeries R, IsUnit F → IsUnit g → IsUnit w → LC p m N F (g * w ^ p ^ n) → LC p m (min n (min (m - 1) N)) (dl F) (dl g)

def SKumTriv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ ζ : ℕ → Ω, Roots l ζ → ∀ m n, n ≤ m → ∀ u : Ω, u ≠ 0 → (∀ s ∈ Hm l A m, KumVal (l := l) n (ζ n) u s 0) → ∃ v : Ω, v ^ l ^ n = u ∧ ∀ s ∈ Hm l A m, s v = v

def SKumAlg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ ζ : ℕ → Ω, Roots l ζ → ∀ m n, n ≤ m → ∀ s ∈ Hm l A m, (∀ (u u' : Ω) (k k' : ZMod (l ^ n)), KumVal (l := l) n (ζ n) u s k → KumVal (l := l) n (ζ n) u' s k' → KumVal (l := l) n (ζ n) (u * u') s (k + k') ∧ KumVal (l := l) n (ζ n) u⁻¹ s (-k) ∧ ∀ a : ℕ, KumVal (l := l) n (ζ n) (u ^ a) s (a * k)) ∧ (∀ (u : Ω) (k : ZMod (l ^ n)) (n' : ℕ), n' ≤ n → u ≠ 0 → KumVal (l := l) n (ζ n) u s k → KumVal (l := l) n' (ζ n') u s (k.val : ZMod (l ^ n'))) ∧ ∀ (u : Ω) (k : ZMod (l ^ n)) (t : G ℚ Ω), KumVal (l := l) n (ζ n) (t⁻¹ u) s k → KumVal (l := l) n (ζ n) u (t * s * t⁻¹) (((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * k)

def SPresMono : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (Z Z' : Sy Ω l) (m n n' : ℕ) (P : Fin β.d → Polynomial (R0 A)), n' ≤ n → (∀ s ∈ Hm l A m, Cg n' (Z m s 1) (Z' m s 1)) → BPres β A ζ Z m n P → BPres β A ζ Z' m n' P

def SPresDl : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (Z : Sy Ω l) (m n : ℕ), 1 ≤ m → ∀ P P' : Fin β.d → Polynomial (R0 A), BPres β A ζ Z m n P → BPres β A ζ Z m n P' → ∀ i, (∃ Q : Polynomial (R0 A), (pv Q (ζ m) ∈ A ∧ pv Q (ζ m) ≠ 0 ∧ (pv Q (ζ m))⁻¹ ∈ A) ∧ pv (P i) (ζ m) = pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ n) ∧ LC l m (min n (m - 1)) (dl (Φ.ser (P i))) (dl (Φ.ser (P' i)))

def SRepUniq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (Z Z' : Sy Ω l) (D D' : Fin β.d → PowerSeries Φ.R), Rep Φ β ζ Z D → Rep Φ β ζ Z' D' → (∀ m, ∀ s ∈ Hm l A m, Z m s 1 = Z' m s 1) → D = D'

def SConj : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (Z : Sy Ω l), IwI c A Z → ∀ m, ∀ s ∈ Hm l A m, ∀ t ∈ Ine (F := ℚ) A, t * s * t⁻¹ ∈ Hm l A m ∧ ∀ x, Z m (t * s * t⁻¹) x = Z m s (x * (cycMod ℚ Ω l m t)⁻¹)

def SPresTr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → ∀ (b : ℕ) (hb : ¬ l ∣ b) (m n : ℕ) (P : Fin β.d → Polynomial (R0 A)), BPres β A ζ Z m n P → BPres β A ζ (fun r s x => (b : Qbar l) * tr b hb Z r s x) m n (fun i => Polynomial.expand (R0 A) b (P i))

def SNormGal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → ∀ m n, 1 ≤ n → n ≤ m → ∀ P P' : Fin β.d → Polynomial (R0 A), BPres β A ζ Z (m + 1) n P → BPres β A ζ Z m n P' → ∀ i, ∃ Q : Polynomial (R0 A), (pv Q (ζ m) ∈ A ∧ pv Q (ζ m) ≠ 0 ∧ (pv Q (ζ m))⁻¹ ∈ A) ∧ ∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv (P i) (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val) = pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ (n - 1)

def SNormLev : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j), ∀ ζ : ℕ → Ω, Roots l ζ → ∀ (m : ℕ) (hm : 1 ≤ m) (P Q : Polynomial (R0 A)), ∏ x ∈ (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1), pv P (ζ (m + 1) ^ (x : ZMod (l ^ (m + 1))).val) = pv Q (ζ m) → nrm l m hm (ev Φ.R l (m + 1) (Φ.ser P)) = ev Φ.R l m (Φ.ser Q)

def SExact : Prop :=
  ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → (∀ x : R, x ∉ Ideal.span {(p : R)} → IsUnit x) → ∀ (g : ℕ → PowerSeries R) (c m₀ : ℕ), (∀ m, m₀ ≤ m → IsUnit (g m)) → (∀ (m : ℕ) (hm : 1 ≤ m), m₀ ≤ m → ∃ w : PowerSeries R, IsUnit w ∧ nrm p m hm (ev R p (m + 1) (g (m + 1))) = ev R p m (g m * w ^ p ^ (m - c))) → ∃ f : PowerSeries R, IsUnit f ∧ ∀ m, 1 ≤ m → m₀ ≤ m → ∀ N : ℕ, ∃ w : PowerSeries R, IsUnit w ∧ LC p m N (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) f) (g m * w ^ p ^ (m - c))

def SRepEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → HasPres β A ζ Z → ∃ D, Rep Φ β ζ Z D

def SRepAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → (∀ (Z Z' : Sy Ω l) (D D' : Fin β.d → PowerSeries Φ.R), Rep Φ β ζ Z D → Rep Φ β ζ Z' D' → Rep Φ β ζ (fun r s x => Z r s x + Z' r s x) (D + D')) ∧ ∀ Z : Sy Ω l, (∀ m, ∀ s ∈ Hm l A m, Z m s 1 = 0) → Rep Φ β ζ Z 0

def SRepSmul : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (Z : Sy Ω l) (D : Fin β.d → PowerSeries Φ.R) (b : c.O), Rep Φ β ζ Z D → Rep Φ β ζ (fun r s x => (b : PadicAlgCl l) * Z r s x) (Φ.act (β.mat b) D)

def SRepTr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → ∀ (b : ℕ) (hb : ¬ l ∣ b) (D : Fin β.d → PowerSeries Φ.R), Rep Φ β ζ Z D → Rep Φ β ζ (tr b hb Z) (fun i => sb b (D i))

def SRepFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (Z : Sy Ω l) (D : Fin β.d → PowerSeries Φ.R) (a : c.O), Rep Φ β ζ Z D → (∀ m, ∀ s ∈ Hm l A m, Z m (Φ.fr * s * Φ.fr⁻¹) 1 = (a : PadicAlgCl l) * Z m s 1) → ∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a) D i

def SLangR : Prop :=
  ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → (∀ x : R, x ∉ Ideal.span {(p : R)} → IsUnit x) → (∀ P : Polynomial R, P.Monic → 0 < P.natDegree → ∃ x : R, P.eval x ∈ Ideal.span {(p : R)}) → ∀ (d : ℕ) (N : Matrix (Fin d) (Fin d) R), IsUnit N.det → ∃ V : Matrix (Fin d) (Fin d) R, IsUnit V.det ∧ V.map σ = N * V

def SPeriod : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j), ∀ (c : Coef l) (β : Bas c) (a : c.O), IsUnit a → ∃ v : ℂ_[l], ‖v‖ = 1 ∧ ∀ x : Fin β.d → Φ.R, (∀ i, Φ.σ.symm (x i) = ∑ k, algebraMap ℤ_[l] Φ.R (β.mat a i k) * x k) → ∃ o : c.O, Φ.lam β x = v * algebraMap (PadicAlgCl l) ℂ_[l] (o : PadicAlgCl l)

def SContOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → HasPres β A ζ Z → Cont A Z

def SKumEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ Z : Sy Ω l, IwI c A Z → Cont A Z → ∀ (b : ℕ) (hb : ¬ l ∣ b), HasPres β A ζ (sharp b hb Z)

def SIwOps : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (Z : Sy Ω l), IwI c A Z → ∀ (b : ℕ) (hb : ¬ l ∣ b), IwI c A (tr b hb Z) ∧ IwI c A (sharp b hb Z)

def SCob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (Z : Sy Ω l), IwI c A Z → ∀ (φ : DirichletCharacter (Qbar l) l) (k : ℕ), 1 ≤ k → SpZero A φ k Z → ∃ (c₂ : ℕ) (w : Qbar l), w ∈ c.O ∧ ∀ s ∈ Ine (F := ℚ) A, ∀ n : ℕ, ∃ r₀, ∀ r, r₀ ≤ r → Cg n ((l : Qbar l) ^ c₂ * sp (eta φ k r) (Z r) s) ((eta φ k r (cycMod ℚ Ω l r s) - 1) * w)

def SDivAlg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (g : ℕ) (hg : ¬ l ∣ g), 2 ≤ g → (∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), x ∈ Subgroup.zpowers (un g hg r)) → ∀ (φ : DirichletCharacter (Qbar l) l) (k : ℕ), 1 ≤ k → (∀ r : ℕ, ∃ c₃ : ℕ, ∀ (q : (ZMod (l ^ r))ˣ → Qbar l) (n : ℕ), (∀ x, Cg (n + c₃) (q (x * un g hg r) - φ (g : ZMod l) * (g : Qbar l) ^ k * q x) 0) → ∀ x, Cg n (q x) 0) ∧ ∀ μ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l, (∀ r x, μ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ r))ˣ), μ r x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ => red l r x' = x), μ (r + 1) x') → (∀ n : ℕ, ∃ r₀, ∀ r, r₀ ≤ r → Cg n (∑ x, eta φ k r x * μ r x) 0) → ∀ r, ∃ q : (ZMod (l ^ r))ˣ → Qbar l, (∀ x, q x ∈ c.O) ∧ ∀ x, μ r x = q (x * un g hg r) - φ (g : ZMod l) * (g : Qbar l) ^ k * q x

def SDiv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (Z : Sy Ω l), IwI c A Z → Cont A Z → ∀ (φ : DirichletCharacter (Qbar l) l) (k : ℕ), 1 ≤ k → SpZero A φ k Z → ∃ (g : ℕ) (hg : ¬ l ∣ g) (c₂ : ℕ) (Z' : Sy Ω l), IwI c A Z' ∧ Cont A Z' ∧ ∀ m, ∀ s ∈ Hm l A m, ∀ x, (l : Qbar l) ^ c₂ * Z m s x = tr g hg Z' m s x - φ (g : ZMod l) * (g : Qbar l) ^ k * Z' m s x

def SEvHom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j), ∀ m, 1 ≤ m → ∀ z : ℂ_[l], IsPrimitiveRoot z (l ^ m) → ∃ ε : lev Φ.R l m →+* ℂ_[l], (∀ y, ‖ε y‖ ≤ 1) ∧ (∀ x, ε (ev Φ.R l m (PowerSeries.C x)) = Φ.jh x) ∧ ε (ev Φ.R l m (1 + PowerSeries.X)) = z ∧ ∀ h : PowerSeries Φ.R, ‖ε (ev Φ.R l m h) - ∑ i ∈ Finset.range (l ^ (3 * m)), Φ.jh (h.coeff i) * (z - 1) ^ i‖ ≤ ‖(l : ℂ_[l]) ^ m‖

def SToBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → ∀ (j : Ω →+* Qbar l), (∀ x ∈ A, ‖j x‖ ≤ 1) → ∀ (Z : Sy Ω l) (m n : ℕ) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l), 1 ≤ m → (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → (∀ i, o i ∈ c.O) → KumPres A n m (ζ n) (Z m) (fun i => (P i).eval (ζ m)) o → ∃ P' : Fin β.d → Polynomial (R0 A), BPres β A ζ Z m n P' ∧ ∀ b : (ZMod (l ^ m))ˣ, Cg n (htv j (ζ m) P o (b : ZMod (l ^ m)).val) (htv j (ζ m) (fun i => (P' i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val)

def SClause1 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j) (c : Coef l) (β : Bas c) (ζ : ℕ → Ω), Roots l ζ → (∀ x ∈ A, ‖j x‖ ≤ 1) → ∀ Z : Sy Ω l, IwI c A Z → ∀ (d₀ : ℕ) (hd : ¬ l ∣ d₀) (D : Fin β.d → PowerSeries Φ.R) (a : c.O) (Gs : PowerSeries (Qbar l)) (v : ℂ_[l]) (vm : ℕ → Qbar l), Rep Φ β ζ (sharp d₀ hd Z) D → (∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a) D i) → (∀ n, ‖Gs.coeff n‖ ≤ 1) → (∀ n, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (Gs.coeff n)) → (∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ ≤ ‖(l : ℂ_[l]) ^ m‖) → ∀ e₀ : ℕ, ∃ c₁ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ P : Fin β.d → Polynomial (R0 A), BPres β A ζ Z m (m - e₀) P → ∀ b : (ZMod (l ^ m))ˣ, Cg (m - c₁) (htv j (ζ m) (fun i => (P i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val - (d₀ : Qbar l) * htv j (ζ m) (fun i => (P i).map (R0 A).subtype) β.val ((b * un d₀ hd m : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val) (vm m * (a : PadicAlgCl l) ^ m * tval Gs (l ^ (3 * m)) (j (ζ m) ^ (b : ZMod (l ^ m)).val))

def SIntShift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : PowerSeries (Qbar l)), (∀ n, ‖H.coeff n‖ ≤ 1) → ∀ (g : ℕ), ¬ l ∣ g → ∀ (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) (ξ : Qbar l), 1 ≤ r → IsPrimitiveRoot ξ (l ^ r) → Cg (2 * r) (intg φ k (sb g H) r ξ) (φ (g : ZMod l) * (g : Qbar l) ^ k * intg φ k H r ξ)

def SClause2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (j : Ω →+* Qbar l) (Φ : Fr l A j), (∀ x ∈ A, ‖j x‖ ≤ 1) → ∀ (c : Coef l) (β : Bas c) (D D' : Fin β.d → PowerSeries Φ.R) (Gs : PowerSeries (Qbar l)) (v : ℂ_[l]) (g c₂ k : ℕ) (φ : DirichletCharacter (Qbar l) l) (θ : c.O), ¬ l ∣ g → (θ : PadicAlgCl l) = φ (g : ZMod l) * (g : Qbar l) ^ k → ‖v‖ = 1 → (∀ n, ‖Gs.coeff n‖ ≤ 1) → (∀ n, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (Gs.coeff n)) → (∀ i, Φ.act (β.mat ((l : c.O) ^ c₂)) D i = sb g (D' i) - Φ.act (β.mat θ) D' i) → IntZero φ k Gs

def SCore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (c : Coef l) (Z : Sy Ω l) (a : Qbar l) (j : Ω →+* Qbar l) (d₀ e₀ m₀ : ℕ) (ζ : ℕ → Ω), IwI c A Z → ‖a‖ = 1 → (∀ σ ∈ Dec (F := ℚ) A, IsFrob A l σ → cycBar ℚ Ω l σ = 1 → ∀ m, ∀ s ∈ Hm l A m, Z m (σ * s * σ⁻¹) 1 = a * Z m s 1) → (∀ x ∈ A, ‖j x‖ ≤ 1) → ¬ l ∣ d₀ → Roots l ζ → (∀ m, m₀ ≤ m → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧ KumPres A (m - e₀) m (ζ (m - e₀)) (Z m) (fun i => (P i).eval (ζ m)) o) → ∃ (Gs : PowerSeries (Qbar l)) (v : ℕ → Qbar l) (c₁ m₁ : ℕ), (∀ n, Gs.coeff n ∈ c.O) ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ (∀ m, m₁ ≤ m → ∀ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → (∀ i, o i ∈ c.O) → KumPres A (m - e₀) m (ζ (m - e₀)) (Z m) (fun i => (P i).eval (ζ m)) o → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), Cg (m - c₁) ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j (ζ m) P o (b : ZMod (l ^ m)).val) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (j (ζ m) ^ (b : ZMod (l ^ m)).val))) ∧ ∀ (φ : DirichletCharacter (Qbar l) l) (k : ℕ), 1 ≤ k → SpZero A φ k Z → IntZero φ k Gs

end UpperTheory.Kd.C7
