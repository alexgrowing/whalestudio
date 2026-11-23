import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

variable (D : Formalism.BasicNotions.D7) (hV : admB2 D) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem mem_vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  have h := ((hV R ℤ n LZ S).1 P Q).1
  rw [h, WithTop.coe_add]
  exact add_le_add hP hQ

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have h := sDegs_C (R := R) LZ S (lastIdx n) c k hk
  rw [Set.mem_singleton_iff] at h
  subst h
  exact le_rfl

theorem mem_vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using mem_vg_C (R := R) (n := n) S 1
  | succ k ih =>
    have e : (((k + 1 : ℕ) : ℤ) * a : ℤ) = (k : ℤ) * a + a := by push_cast; ring
    rw [e, pow_succ]
    exact mem_vg_mul D hV S ih hP

theorem mem_vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using mem_vg_C (R := R) (n := n) S 1
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mem_vg_mul D hV S (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_X (v : ℤ × Fin n) (he : Even v.1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have hk0 : (0 : ℤ) ≤ k := by
    by_cases hS : v.1 ∈ S
    · have hv : LZ.vec v.1 = true := by simp [LZ, he]
      have h := sDegs_X_vec (R := R) LZ S (lastIdx n) v.1 v.2 hS hv k hk
      have h01 : k = 0 ∨ k = 1 := by simpa using h
      rcases h01 with h | h <;> simp [h]
    · have h := sDegs_X_out (R := R) LZ S (lastIdx n) v hS k hk
      rw [Set.mem_singleton_iff] at h
      simp [h]
  exact WithTop.coe_le_coe.mpr hk0

theorem mem_vg_monom {κ : Type} (s : Finset κ) (v : κ → ℤ × Fin n) (e : κ → ℕ) (he : ∀ i ∈ s, Even (v i).1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
  have h0 : ∀ i ∈ s, (((fun _ => (0 : ℤ)) i : ℤ) : WithTop ℤ) ≤
      valS LZ S ((X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
    intro i hi
    simpa using mem_vg_pow D hV S (mem_vg_X (R := R) S (v i) (he i hi)) (e i)
  simpa using mem_vg_prod D hV S s (fun i => (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) (fun _ => 0) h0

end Kit

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerTimesMonomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat)

omit [NeZero n'] [NeZero r] in

def memMu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ u v

def memPl (O : Type) [CommRing O] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) :
    MvPolynomial (ℤ × Fin r) O :=
  segRen X.F j O r (Psi O (plPart μ) (Ican (plPart μ)))

def memA (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin r) O :=
  X.discPowerTimesMonomial p K O j b * X.memMu O j q.2.2 * X.memPl K O j q.1

def memG (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin K) O :=
  segRen X.F j O K (Psi O (tanPart q.1) q.2.1)

def memM [NeZero K] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => if Even (segE X.F j i) then tanPart μ i.succ 0 else tanPart μ i.castSucc 0) 0

theorem famEl_eq (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    X.famEl p K O j b q = plEmb O r K (X.memA p K O j b q) * nmEmb O r K (X.memG K O j q) := by
  first
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def, plVar, tanVar]
     ring)
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def]
     ring_nf)

end Dat

def RestMemA (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      X.memA p K O j b q.1 ∈ supported O {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
      X.memG K O j q.1 ∈ supported O {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} ∧
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.memA p K O j b q.1)) ∧
        (¬ Even x → lam1S LZ {y | y < x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.memA p K O j b q.1)) ∧
        geR (valS LZ {y | y < x} (X.memA p K O j b q.1)) (X.thc p K j b x)

def RestMemB (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      ∀ mm ∈ (plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1)).support,
        ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.oc p K j x

def RestMemC (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ Pol O (r + K) b

def RestMemD (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ restrictSupport O (X.resSet p K j)

theorem restMem_of_rests (C₀ : ℝ) (hA : RestMemA C₀) (hB : RestMemB C₀) (hC : RestMemC C₀) (hD : RestMemD C₀) :
    RestMem C₀ := by
  intro p n' r K _ _ _ X O _ _ _ hS hX hCLa hCk j b hb q
  have hA' := hA p n' r K X O hS hX hCLa hCk j b hb q
  have hB' := hB p n' r K X O hS hX hCLa hCk j b hb q
  have hC' := hC p n' r K X O hS hX hCLa hCk j b hb q
  have hD' := hD p n' r K X O hS hX hCLa hCk j b hb q
  rw [X.famEl_eq p K O j b q.1]
  simp only [Dat.Mj, XX', Submodule.mem_inf]
  refine ⟨⟨⟨Submodule.subset_span ⟨X.memA p K O j b q.1, X.memG K O j q.1, X.memM K j q.1.1,
    hA'.1, hA'.2.1, hA'.2.2, rfl⟩, ?_⟩, hC'⟩, hD'⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact hB' mm hmm

end Formalism.MainNotions.SelectionLemmas.Pf
