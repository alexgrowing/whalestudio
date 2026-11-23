import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GenDataEmpty
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

def Combine : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (J : Type) (θ : J → k) (S T : Set (J → k)) (Q : MvPolynomial J ℤ),
    PolyApprox θ S → (∀ η ∈ S, MvPolynomial.aeval η Q ≠ 0 ∧ PolyApprox η T) →
    PolyApprox θ {η | η ∈ T ∧ MvPolynomial.aeval η Q ≠ 0}

def Restrict : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (J J' : Type) (i : J → J') (θ : J' → k) (S : Set (J' → k)),
    PolyApprox θ S → PolyApprox (θ ∘ i) ((· ∘ i) '' S)

def AlgC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (H : Type) [Group H] [Fintype H], IsPGroup l H →
    ∀ P : Submodule ℂ (H → ℂ), (∀ c ∈ P, ∀ g, (fun h => c (h * g)) ∈ P) → Fintype.card H ≤ 2 * Module.finrank ℂ P →
    ∃ c ∈ P, ∀ h, ‖ι.symm (1 - c h)‖ ^ 2 ≤ ‖((l : ℕ) : Qbar l)‖

def LocOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ), ∃ C : ℝ, ∀ p ∈ symmetricLaurent a,
    ∃ h : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g ∈ h.support, ∀ g' ∈ h.support, g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w a → g = g') ∧
      ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (z : Fin a → ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z) →
        ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a), opOf σ.ρ h v = evalAt z p • v

def GlobOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E)),
    IsSplitAt w → HypAt K w → ∃ C : ℝ, ∀ p ∈ symmetricLaurent a,
    ∃ h : UA E a →₀ ℂ, (∀ g ∈ h.support, g ∈ locU a w) ∧ (∀ g ∈ h.support, ∀ g' ∈ h.support, g⁻¹ * g' ∈ K → g = g') ∧
      ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 ∧
      ∀ U, IsAutRepU U → ∀ z, SatAt U w z → ∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) h φ = evalAt z p • φ

def NeglAt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)) (w₀ w : HeightOneSpectrum (𝓞 E)),
    IsSplitAt w → Apart w w₀ → HypAt K w → ∀ Φ : MvPolynomial (Fin a) ℂ, Φ ≠ 0 → Negl w₀ K fun U => ¬ GenAt w Φ U

def TestOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E)),
    IsSplitAt w → HypAt K w → ∀ Φ : MvPolynomial (Fin a) ℂ, ∃ (f : UA E a →₀ ℂ) (η : Submodule ℂ (UA E a → ℂ) → ℂ),
      (∀ g ∈ f.support, g ∈ finU E a) ∧ ∀ U, IsAutRepU U →
        (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) f φ = η U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (η U ≠ 0 ↔ GenAt w Φ U))

structure IsTower {G : Type} [Group G] [TopologicalSpace G] (J : ℕ → Subgroup G) : Prop where
  isOpen : ∀ n, IsOpen (J n : Set G)
  compact : ∀ n, IsCompact (J n : Set G)
  anti : Antitone J
  normal : ∀ n, ∀ g ∈ J 0, ∀ x ∈ J n, g * x * g⁻¹ ∈ J n
  small : ∀ N ∈ nhds (1 : G), ∃ n, (J n : Set G) ⊆ N

def CongSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
    ∃ J : ℕ → Subgroup (GL (Fin a) (w.adicCompletion E)), IsTower J ∧ ∀ n, ∀ x ∈ J n, x ^ l ∈ J (n + 1)

def Tower : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
    1 ≤ a → ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∃ J : ℕ → Subgroup (GL (Fin a) (w.adicCompletion E)),
      IsTower J ∧ (J 0 : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N ∧ (∀ g ∈ J 0, IsOfFinOrder g → g = 1) ∧
      ∀ n, ∀ x ∈ J 0, x ^ l ^ n ∈ J n

structure IsLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (C : Subgroup (UA E a)) : Prop where
  fin : C ≤ finU E a
  compact : IsCompact (C : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C

def LevFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ →
    ∀ K : Subgroup (UA E a), IsLevelAway w₀ K → ∀ J : Subgroup (GL (Fin a) (w₀.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
    IsLevel (lev K w₀ J) ∧
    (∀ c, c ∈ lev K w₀ J ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J ∧ c = k * x) ∧
    (∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J) ∧ (∀ c ∈ lev K w₀ J, cLoc w₀ c = 1 → c ∈ K) ∧
    (∀ y : GL (Fin a) (w₀.adicCompletion E), ∃ x ∈ locU a w₀, cLoc w₀ x = y) ∧
    ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)), ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J' → c ∈ lev K w₀ J'

def LocComm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (x g : UA E a),
    x ∈ locU a w₀ → (∀ u, ¬ Apart u w₀ → cLoc u g = 1) → x * g = g * x

def RatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ),
    (∀ Z : Set (UA E a), IsCompact Z → (Z ∩ (ratU E a : Set (UA E a))).Finite) ∧
    ∀ (w : HeightOneSpectrum (𝓞 E)), ∀ γ ∈ ratU E a, cLoc w γ = 1 → γ = 1

def Ell : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C →
    ∀ (H : Type) [Group H] (lam : C →* H), (∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ ∀ c : C, c.1 ∈ N → lam c = 1) →
    (∀ c : C, IsOfFinOrder c → lam c = 1) → ∃ ℓ : UA E a → H, (∀ g, ∀ x ∈ infU E a, ℓ (g * x) = ℓ g) ∧
      (∀ g (c : C), ℓ (g * c) = ℓ g * lam c) ∧ ∀ φ : H → ℂ, IsAutFormU fun g => φ (ℓ g)

def EllGrp : Prop :=
  ∀ (G H : Type) [Group G] [Group H] (Γ C : Subgroup G) (lam : C →* H), (∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) →
    ∃ ℓ : G → H, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧ ∀ g (c : C), ℓ (g * c) = ℓ g * lam c

def WBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (d : ℕ) (B : Module.Basis (Fin d) ℂ W.Sp),
    ∃ M : ℝ, ∀ (x : infU E a) i j, ‖B.repr (W.rep x (B i)) j‖ ≤ M

def Covers {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (C : Subgroup (UA E a)) {X : Type} (p : X → UA E a) : Prop :=
  ∀ g : UA E a, ∃ γ ∈ ratU E a, ∃ y : X, ∃ x ∈ infU E a, ∃ c ∈ C, g = γ * p y * x * c

def Separates {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (C : Subgroup (UA E a)) {X : Type} (p : X → UA E a)
    (T : Finset (UA E a)) : Prop :=
  ∀ y : X, ∀ g ∈ T, ∀ g' ∈ T, ∀ γ ∈ ratU E a, ∀ x ∈ infU E a, ∀ c ∈ C, p y * g' = γ * (p y * g) * x * c → g = g'

def CountCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a), ∃ M : ℝ, 0 ≤ M ∧
    ∀ (C : Subgroup (UA E a)) (X : Type) [Fintype X] (p : X → UA E a), Covers C p → ∀ h : UA E a →₀ ℂ, Separates C p h.support →
    ∀ V : Submodule ℂ (algForms W), V ≤ fixedBy W C → (∀ f ∈ V, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v) →
      FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℝ) ≤ M * Fintype.card X * ∑ g ∈ h.support, ‖h g‖ ^ 2

def Cover : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ →
    ∀ K : Subgroup (UA E a), IsLevelAway w₀ K → ∀ J : ℕ → Subgroup (GL (Fin a) (w₀.adicCompletion E)), IsTower J →
    ∃ S : Finset (UA E a), ∀ n, ∃ r : (J 0 ⧸ (J n).subgroupOf (J 0)) → UA E a, (∀ q, r q ∈ locU a w₀ ∧ cLoc w₀ (r q) ∈ J 0) ∧
      Covers (lev K w₀ (J n)) fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2

def Sep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ →
    ∀ K : Subgroup (UA E a), IsLevelAway w₀ K → ∀ J : ℕ → Subgroup (GL (Fin a) (w₀.adicCompletion E)), IsTower J →
    ∀ S T : Finset (UA E a), (∀ g ∈ T, g ∈ finU E a ∧ ∀ u, ¬ Apart u w₀ → cLoc u g = 1) →
    (∀ g ∈ T, ∀ g' ∈ T, g⁻¹ * g' ∈ K → g = g') → ∃ n₀, ∀ n, n₀ ≤ n →
      Separates (lev K w₀ (J n)) (fun y : S × {j : UA E a // j ∈ locU a w₀ ∧ cLoc w₀ j ∈ J 0} => y.1.1 * y.2.1) T

def Count : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ →
    ∀ K : Subgroup (UA E a), IsLevelAway w₀ K → ∀ J : ℕ → Subgroup (GL (Fin a) (w₀.adicCompletion E)), IsTower J →
    ∀ (W : Wt E a) (B : Submodule ℂ (UA E a → ℂ) → Prop), Negl w₀ K B → ∀ ε : ℝ, 0 < ε → ∃ n₀, ∀ n, n₀ ≤ n →
      FiniteDimensional ℂ (part W (lev K w₀ (J n)) B) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) B) : ℝ) ≤ ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))

def CountGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ →
    ∀ K : Subgroup (UA E a), IsLevelAway w₀ K → ∀ J : ℕ → Subgroup (GL (Fin a) (w₀.adicCompletion E)), IsTower J →
    ∀ (W : Wt E a) (S : Finset (HeightOneSpectrum (𝓞 E))) (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ),
    GenData w₀ K S Φ → ∃ n, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ∧
      2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ≤
        Nat.card (J 0 ⧸ (J n).subgroupOf (J 0))

def PartFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (C : Subgroup (UA E a))
    (P : Submodule ℂ (UA E a → ℂ) → Prop),
    fixedBy W C ≤ part W C P ⊔ part W C (fun U => ¬ P U) ∧ part W C P ≤ fixedBy W C ∧
    (∀ K : Subgroup (UA E a), K ≤ C → part W C P ≤ part W K P) ∧
    (∀ x : finU E a, (∀ c ∈ C, x.1⁻¹ * c * x.1 ∈ C) → ∀ f ∈ part W C P, algRep W x f ∈ part W C P) ∧
    ∀ G ∈ part W C P, ∃ (I : Finset (AutSub E a)) (F : AutSub E a → algForms W),
      (∀ π ∈ I, P π.V ∧ F π ∈ π.finPart W ∧ F π ∈ fixedBy W C ∧ F π ≠ 0) ∧ G = ∑ π ∈ I, F π

def StepCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a)
    (C C' : Subgroup (UA E a)), C ≤ finU E a → ∀ (H : Type) [Group H] [Finite H], IsPGroup l H → ∀ lam : C →* H,
    Function.Surjective lam → C' ≤ C → (∀ c : C, c.1 ∈ C' ↔ lam c = 1) → ∀ ℓ : UA E a → H,
    (∀ g, ∀ x ∈ infU E a, ℓ (g * x) = ℓ g) → (∀ g (c : C), ℓ (g * c) = ℓ g * lam c) → (∀ φ : H → ℂ, IsAutFormU fun g => φ (ℓ g)) →
    ∀ P : Submodule ℂ (UA E a → ℂ) → Prop, FiniteDimensional ℂ (part W C' fun U => ¬ P U) →
    2 * Module.finrank ℂ (part W C' fun U => ¬ P U) ≤ Nat.card H → ∀ f ∈ fixedBy W C,
    ∃ G ∈ part W C' P, ∃ e : UA E a → ℂ, (∀ g, ‖ι.symm (e g)‖ ^ 2 ≤ ‖((l : ℕ) : Qbar l)‖) ∧
      ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def Step : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (W : Wt E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ), GenData w₀ K S Φ → ∀ f ∈ fixedBy W K,
    ∃ G ∈ part W K (fun U => ∀ w ∈ S, GenAt w (Φ w) U), ∃ e : UA E a → ℂ,
      (∀ g, ‖ι.symm (e g)‖ ^ 2 ≤ ‖((l : ℕ) : Qbar l)‖) ∧ ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def SmoothAt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ → ∀ (W : Wt E a)
    (f : algForms W), ∃ N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E)), ∀ x ∈ locU a w₀, cLoc w₀ x ∈ N →
      ∀ v g, f.1 v (g * x) = f.1 v g

def FrameEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a),
    ∃ (d : ℕ) (b : UA E a → Fin d → W.Sp), (∀ f : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (f.1 (b g i) g)‖ ≤ R) ∧
      (∀ f : algForms W, (∀ g i, f.1 (b g i) g = 0) → f = 0) ∧
      (∀ h ∈ finU E a, ∃ m : Fin d → Fin d → ℂ, ∀ g i, b g i = ∑ j, m i j • b (g * h) j) ∧
      ∀ h ∈ finU E a, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal → cLoc u h = 1) → ∀ g, b (g * h) = b g

def FrameOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a) (J : Type)
    (t : J → (UA E a →₀ ℂ)), (∀ j, ∀ g ∈ (t j).support, g ∈ finU E a) →
    ∃ c : J → ℕ, (∀ j, IsIntegralOp ι (t j) → c j = 0) ∧ Framed ι W fun j => ((l : ℂ) ^ c j) • t j

def ToPoly : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), K ≤ finU E a → ∀ (lam : (E →+* ℂ) → DomWeight a)
    (P : Submodule ℂ (UA E a → ℂ) → Prop), Dense ι (Wt.ofFam lam) K P → ∀ (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), Framed ι (Wt.ofFam lam) t → ActsBy K t η → ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η U' j)}

end UpperTheory.Gal.Gen

end
