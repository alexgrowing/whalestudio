import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)

def chartMono (pt : MRingOver o ι →ₐ[o] Ω) (i : (k : K) → ι k) (c : K → ℤ) : Ω :=
  ∏ k, pt (X ⟨k, i k⟩) ^ c k

def degLine (pt : MRingOver o ι →ₐ[o] Ω) (c : K → ℤ) (ω : Ω) (i : (k : K) → ι k) : Set Ω :=
  {a | ∃ r ∈ chartRing o (segreVec pt) i, a = r * chartMono pt i c * ω}

end Coordinates

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

def gradedLat {x : ((k : K) → ι k) → Ω} (B : ChartBundle o x N E) (u : Basis (Fin N) Ω E)
    (l : Fin N) (i : (k : K) → ι k) : Set Ω :=
  {a | ∃ e ∈ B.lat i, (∀ j, l < j → u.repr e j = 0) ∧ u.repr e l = a}

def IsFlagGrading (pt : MRingOver o ι →ₐ[o] Ω) (B : ChartBundle o (segreVec pt) N E)
    (u : Basis (Fin N) Ω E) (m : Fin N → K → ℤ) (ω : Fin N → Ω) : Prop :=
  (∀ l, ω l ≠ 0) ∧ ∀ i, segreVec pt i ≠ 0 → ∀ l, gradedLat B u l i = degLine pt (m l) (ω l) i

def IsTwistedForms {τ : Type*} [Fintype τ] (pt : MRingOver o ι →ₐ[o] Ω)
    (B : ChartBundle o (segreVec pt) N E) (φ : τ → E →ₗ[Ω] Ω) (c : K → ℤ) : Prop :=
  ∀ i, segreVec pt i ≠ 0 →
    (∀ t, ∀ e ∈ B.lat i, φ t e ∈ degLine pt c 1 i) ∧
    ∀ ψ : E →ₗ[Ω] Ω, (∀ e ∈ B.lat i, ψ e ∈ chartRing o (segreVec pt) i) →
      ∃ a : τ → Ω, (∀ t, a t ∈ chartRing o (segreVec pt) i) ∧
        ψ = ∑ t, (a t * (chartMono pt i c)⁻¹) • φ t

def SameGenericFibre {x : ((k : K) → ι k) → Ω} (ϖ : o) (B B' : ChartBundle o x N E) : Prop :=
  ∀ i, x i ≠ 0 → ∀ e : E,
    (∃ n : ℕ, algebraMap o Ω ϖ ^ n • e ∈ B.lat i) ↔ (∃ n : ℕ, algebraMap o Ω ϖ ^ n • e ∈ B'.lat i)

end Flags

section ProjBundle

variable {K : Type*} [Fintype K]

def extIdx (ι : K → Type w) (τ : Type w) : Option K → Type w
  | none => τ
  | some k => ι k

instance extIdx.fintype {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ] :
    (k : Option K) → Fintype (extIdx ι τ k)
  | none => inferInstanceAs (Fintype τ)
  | some k => inferInstanceAs (Fintype (ι k))

def extDeg (Y : K → ℤ) : Option K → ℤ := fun k => k.elim 0 Y

def zetaDeg (c : K → ℤ) : Option K → ℤ := fun k => k.elim 1 fun k => -c k

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

def projBundleMap (pt : MRingOver F ι →ₐ[F] Ω) (u : Basis (Fin N) Ω E) (φ : τ → E →ₗ[Ω] Ω) :
    MRingOver F (extIdx ι τ) →ₐ[F] MvPolynomial (K ⊕ Fin N) Ω :=
  aeval fun p => match p with
    | ⟨none, t⟩ => ∑ l, C (φ t (u l)) * X (Sum.inr l)
    | ⟨some k, i⟩ => C (pt (X ⟨k, i⟩)) * X (Sum.inl k)

def projBundleIdeal (pt : MRingOver F ι →ₐ[F] Ω) (u : Basis (Fin N) Ω E) (φ : τ → E →ₗ[Ω] Ω) :
    Ideal (MRingOver F (extIdx ι τ)) :=
  RingHom.ker (projBundleMap pt u φ)

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

def tupleOfList {α : Type*} [Zero α] {n : ℕ} (L : List α) : Fin n → α := fun j => L.getD j 0

variable {F : Type*} [Field F]

def polyNum (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {N : ℕ} (cls : Fin N → K → ℤ)
    (Q : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * I V n (tupleOfList ((monoList mono).map cls ++ Y))

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def vNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    (p : VPair K O ι) (L : List (K → ℤ)) : ℤ :=
  redEval (fun W => Iκ W n (tupleOfList L)) (divO P p.f p.g)

def monoPairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (ls : List (Fin r)) : ℤ :=
  ∑ k : Fin ls.length, vNum P Iκ n (pr (ls.get k))
    ((ls.take k).map (fun l => (pr l).y - (pr l).b) ++ (ls.drop (k + 1)).map fun l => (pr l).y)

def pairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * monoPairNum P Iκ n pr (monoList mono)

def flagPairs {N : ℕ} (m m' : Fin N → K → ℤ) (f g : Fin N → MRingOver O ι) : Fin N → VPair K O ι :=
  fun l => ⟨m l, m l - m' l, f l, g l⟩

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

def IsFlagPair (pt : MRingOver O ι →ₐ[O] Ω) (P : Ideal (MRingOver O ι))
    (B B' : ChartBundle O (segreVec pt) N E) (u : Basis (Fin N) Ω E) (m m' : Fin N → K → ℤ)
    (ω ω' : Fin N → Ω) (f g : Fin N → MRingOver O ι) : Prop :=
  IsFlagGrading pt B u m ω ∧ IsFlagGrading pt B' u m' ω' ∧
    ∀ l, (∃ α β : K → ℕ, IsMultiHomog (f l) α ∧ IsMultiHomog (g l) β ∧
        ∀ k, (α k : ℤ) - β k = m l k - m' l k) ∧
      g l ∉ P ∧ pt (f l) * ω l = pt (g l) * ω' l

end Pairs

def ProjectiveBundleNumbers.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
    (τ : Type w) [Fintype τ] (V : Ideal (MRingOver F ι)) (e N : ℕ) (Ω : Type u₁) [Field Ω]
    [Algebra F Ω] (pt : MRingOver F ι →ₐ[F] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
    (B : ChartBundle F (segreVec pt) N E) (u : Basis (Fin N) Ω E) (m : Fin N → K → ℤ)
    (ω : Fin N → Ω) (φ : τ → E →ₗ[Ω] Ω) (c : K → ℤ) (I : IFamily F ι)
    (I' : IFamily F (extIdx ι τ)) (j : ℕ) (Y : Fin j → K → ℤ),
    IsProjVarF V e → RingHom.ker pt = V → 1 ≤ N → IsFlagGrading pt B u m ω →
    IsTwistedForms pt B φ c → IsFieldIntersection I → IsFieldIntersection I' → j ≤ N - 1 + e →
    I' (projBundleIdeal pt u φ) (N - 1 + e)
        (tupleOfList (List.replicate (N - 1 + e - j) (zetaDeg c) ++ (List.ofFn Y).map extDeg)) =
      if j ≤ e then polyNum I V e (fun l => -m l) (hsymm (Fin N) ℤ (e - j)) (List.ofFn Y) else 0

def TwoExpansionsAgree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d N : ℕ) (Ω : Type u₁) [Field Ω] [Algebra O Ω]
      (pt : MRingOver O ι →ₐ[O] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec pt) N E) (u₁ u₂ : Basis (Fin N) Ω E)
      (m₁ m₁' m₂ m₂' : Fin N → K → ℤ) (ω₁ ω₁' ω₂ ω₂' : Fin N → Ω)
      (f₁ g₁ f₂ g₂ : Fin N → MRingOver O ι) (G : MvPolynomial (Fin N) ℤ)
      (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P d → RingHom.ker pt = P → SameGenericFibre ϖ B B' →
      IsFlagPair pt P B B' u₁ m₁ m₁' ω₁ ω₁' f₁ g₁ → IsFlagPair pt P B B' u₂ m₂ m₂' ω₂ ω₂' f₂ g₂ →
      G.IsSymmetric → G.IsHomogeneous (d + 1) → IsFieldIntersection Iκ →
      pairNum P Iκ d (flagPairs m₁ m₁' f₁ g₁) G = pairNum P Iκ d (flagPairs m₂ m₂' f₂ g₂) G

def TwoExpansionsAgree.WithPairsStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d N : ℕ) (Ω : Type u₁) [Field Ω] [Algebra O Ω]
      (pt : MRingOver O ι →ₐ[O] Ω) (E : Type u₂) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec pt) N E) (u₁ u₂ : Basis (Fin N) Ω E)
      (m₁ m₁' m₂ m₂' : Fin N → K → ℤ) (ω₁ ω₁' ω₂ ω₂' : Fin N → Ω)
      (f₁ g₁ f₂ g₂ : Fin N → MRingOver O ι) (r : ℕ) (R : Fin r → VPair K O ι)
      (G : MvPolynomial (Fin N) ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P d → RingHom.ker pt = P → SameGenericFibre ϖ B B' →
      IsFlagPair pt P B B' u₁ m₁ m₁' ω₁ ω₁' f₁ g₁ → IsFlagPair pt P B B' u₂ m₂ m₂' ω₂ ω₂' f₂ g₂ →
      (∀ j, IsVerticalDiv ϖ P (R j).b (R j).f (R j).g) → r ≤ d + 1 →
      G.IsSymmetric → G.IsHomogeneous (d + 1 - r) → IsFieldIntersection Iκ →
      pairNum P Iκ d (Fin.append (flagPairs m₁ m₁' f₁ g₁) R)
          (rename (Fin.castAdd r) G * ∏ j : Fin r, X (Fin.natAdd N j)) =
        pairNum P Iκ d (Fin.append (flagPairs m₂ m₂' f₂ g₂) R)
          (rename (Fin.castAdd r) G * ∏ j : Fin r, X (Fin.natAdd N j))

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def trivLat {ι' : Type*} (x : ι' → Ω) (N : ℕ) (i : ι') : AddSubgroup (Fin N → Ω) where
  carrier := {e | ∀ q, e q ∈ chartRing o x i}
  add_mem' ha hb q := add_mem (ha q) (hb q)
  zero_mem' _ := zero_mem _
  neg_mem' ha q := neg_mem (ha q)

def trivBundle {ι' : Type*} (x : ι' → Ω) (N : ℕ) : ChartBundle o x N (Fin N → Ω) where
  lat := trivLat o x N
  stable i a ha e he q := by
    show a * e q ∈ chartRing o x i
    exact mul_mem ha (he q)
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨Pi.basisFun Ω (Fin N), (Pi.basisFun Ω (Fin N)).linearIndependent,
      (Pi.basisFun Ω (Fin N)).span_eq, fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    constructor
    · intro he
      exact ⟨e, he, by simpa using ((Pi.basisFun Ω (Fin N)).sum_repr e).symm⟩
    · rintro ⟨a, ha, rfl⟩ q
      have : (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q = a q := by
        simp [Finset.sum_apply, Pi.single_apply]
      show (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q ∈ chartRing o x i
      rw [this]
      exact ha q
  overlap i j hi _ e he := by
    choose m hm using fun q => exists_pow_mul_mem_chartRing x i j hi (he q)
    refine ⟨∑ q, m q, fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : ((x i / x j) ^ (∑ q, m q) • e) q =
        (x i / x j) ^ (∑ q, m q - m q) * ((x i / x j) ^ m q * e q) := by
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    exact mul_mem (pow_mem (div_mem_chartRing x j i) _) (hm q)

variable {o}

theorem mem_trivBundle {ι' : Type*} {x : ι' → Ω} {N : ℕ} {i : ι'} {e : Fin N → Ω} :
    e ∈ (trivBundle o x N).lat i ↔ ∀ q, e q ∈ chartRing o x i :=
  Iff.rfl

theorem single_mem_trivBundle {ι' : Type*} {x : ι' → Ω} {N : ℕ} {i : ι'} (l : Fin N) {r : Ω}
    (hr : r ∈ chartRing o x i) : Pi.single l r ∈ (trivBundle o x N).lat i := by
  refine mem_trivBundle.2 fun q => ?_
  by_cases h : q = l
  · subst h
    simpa using hr
  · simp [h, zero_mem]

omit [∀ k, Fintype (ι k)] in
theorem chartMono_zero (pt : MRingOver o ι →ₐ[o] Ω) (i : (k : K) → ι k) : chartMono pt i 0 = 1 := by
  simp [chartMono]

omit [∀ k, Fintype (ι k)] in

theorem trivBundle_isFlagGrading (pt : MRingOver o ι →ₐ[o] Ω) (N : ℕ) :
    IsFlagGrading pt (trivBundle o (segreVec pt) N) (Pi.basisFun Ω (Fin N)) 0 1 := by
  refine ⟨fun _ => one_ne_zero, fun i _ l => ?_⟩
  ext a
  simp only [gradedLat, degLine, Pi.basisFun_repr, Pi.zero_apply, chartMono_zero, mul_one,
    Pi.one_apply, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, -, rfl⟩
    exact ⟨e l, mem_trivBundle.1 he l, rfl⟩
  · rintro ⟨r, hr, hra⟩
    refine ⟨Pi.single l r, single_mem_trivBundle l hr, fun j hj => ?_, by simp [hra]⟩
    simp [ne_of_gt hj]

omit [∀ k, Fintype (ι k)] in

theorem trivBundle_isTwistedForms (pt : MRingOver o ι →ₐ[o] Ω) (N : ℕ) :
    IsTwistedForms pt (trivBundle o (segreVec pt) N)
      (fun t : Fin N => (LinearMap.proj t : (Fin N → Ω) →ₗ[Ω] Ω)) 0 := by
  intro i _
  refine ⟨fun t e he => ⟨e t, mem_trivBundle.1 he t, by simp [chartMono_zero]⟩, fun ψ hψ => ?_⟩
  refine ⟨fun t => ψ (Pi.single t 1), fun t => hψ _ (single_mem_trivBundle t (one_mem _)), ?_⟩
  apply LinearMap.pi_ext
  intro s y
  have hs : (Pi.single s y : Fin N → Ω) = y • Pi.single s (1 : Ω) := by
    ext q
    by_cases h : q = s
    · subst h; simp
    · simp [h]
  rw [hs, map_smul]
  simp [chartMono_zero, LinearMap.sum_apply, Pi.single_apply, smul_eq_mul, mul_comm]

variable (o) in

def genPt (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MRingOver R ι →ₐ[R] FractionRing (MRingOver R ι) :=
  IsScalarTower.toAlgHom R _ _

omit [Fintype K] in
theorem ker_genPt (R : Type*) [CommRing R] [IsDomain R] :
    RingHom.ker (genPt R ι) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective _ _)

theorem isProjVarF_line (F : Type*) [Field F] :
    IsProjVarF (⊥ : Ideal (MRingOver F (fun _ : Unit => Fin 2))) 1 := by
  refine ⟨⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ⟨0, by simp [X_ne_zero]⟩⟩, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem ProjectiveBundleNumbers.hyp_inhabited (F : Type*) [Field F] :
    IsProjVarF (⊥ : Ideal (MRingOver F (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt F (fun _ : Unit => Fin 2)) = ⊥ ∧ 1 ≤ 2 ∧
      IsFlagGrading (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2) (Pi.basisFun _ (Fin 2)) 0 1 ∧
      IsTwistedForms (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2)
        (fun t : Fin 2 => (LinearMap.proj t : (Fin 2 → _) →ₗ[_] _)) 0 ∧ 1 ≤ 2 - 1 + 1 :=
  ⟨isProjVarF_line F, ker_genPt F, by norm_num, trivBundle_isFlagGrading _ 2,
    trivBundle_isTwistedForms _ 2, by norm_num⟩

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem trivBundle_isFlagPair (N : ℕ) :
    IsFlagPair (genPt O ι) ⊥ (trivBundle O (segreVec (genPt O ι)) N)
      (trivBundle O (segreVec (genPt O ι)) N) (Pi.basisFun _ (Fin N)) 0 0 1 1 1 1 := by
  refine ⟨trivBundle_isFlagGrading _ N, trivBundle_isFlagGrading _ N, fun l => ⟨?_, ?_, rfl⟩⟩
  · exact ⟨0, 0, by simpa using isMultiHomog_C (ι := ι) (1 : O),
      by simpa using isMultiHomog_C (ι := ι) (1 : O), by simp⟩
  · exact Ideal.isPrime_bot.one_notMem

def unifPair (ϖ : O) : VPair K O ι := ⟨0, 0, C ϖ, 1⟩

end DVR

theorem isHomogeneous_esymm_int (σ : Type*) [Fintype σ] (n : ℕ) :
    (esymm σ ℤ n).IsHomogeneous n := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have := IsHomogeneous.prod t (fun i => (X i : MvPolynomial σ ℤ)) (fun _ => 1)
    fun i _ => isHomogeneous_X ℤ i
  simpa [(Finset.mem_powersetCard.1 ht).2] using this

theorem TwoExpansionsAgree.hyp_inhabited :
    Irreducible ((2 : ℕ) : ℤ_[2]) ∧
      IsModelOver (⊥ : Ideal (MRingOver ℤ_[2] (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt ℤ_[2] (fun _ : Unit => Fin 2)) = ⊥ ∧
      SameGenericFibre ((2 : ℕ) : ℤ_[2])
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2) ∧
      IsFlagPair (genPt ℤ_[2] (fun _ : Unit => Fin 2)) ⊥
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (Pi.basisFun _ (Fin 2)) 0 0 1 1 1 1 ∧
      (esymm (Fin 2) ℤ 2).IsSymmetric ∧ (esymm (Fin 2) ℤ 2).IsHomogeneous (1 + 1) :=
  ⟨PadicInt.irreducible_p, isModelOver_line ℤ_[2], ker_genPt ℤ_[2],
    fun _ _ _ => Iff.rfl, trivBundle_isFlagPair 2, esymm_isSymmetric _ _ _,
    isHomogeneous_esymm_int _ 2⟩

theorem TwoExpansionsAgree.withPairs_hyp_inhabited :
    IsVerticalDiv ((2 : ℕ) : ℤ_[2]) (⊥ : Ideal (MRingOver ℤ_[2] (fun _ : Unit => Fin 2)))
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).b
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).f
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).g ∧
      1 ≤ 1 + 1 ∧ (esymm (Fin 2) ℤ 1).IsSymmetric ∧ (esymm (Fin 2) ℤ 1).IsHomogeneous (1 + 1 - 1) :=
  ⟨isVerticalDiv_unif _ Ideal.isPrime_bot, by norm_num, esymm_isSymmetric _ _ _,
    isHomogeneous_esymm_int _ 1⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
