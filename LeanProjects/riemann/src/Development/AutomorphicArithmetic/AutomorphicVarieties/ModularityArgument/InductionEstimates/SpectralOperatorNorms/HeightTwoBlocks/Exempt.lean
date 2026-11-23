import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloAt

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW
open PositivityTheory.Rg.Tf.Core

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (BW.Pl E)}

private noncomputable def bV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

private theorem bV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bV b) := b.summand.choose_spec.1

private theorem bV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bV b :=
  b.summand.choose_spec.2

private theorem sum_blo {n : ℕ} (d : Dat S n) : ∑ i, (d.blo i).1 = n := by
  induction d with
  | nil =>
    change ∑ i : Fin 0, _ = 0
    simp
  | @cons r s b d ih =>
    change ∑ i : Fin (d.len + 1), _ = r + s
    rw [Fin.sum_univ_succ]
    exact congrArg (r + ·) ih

private noncomputable def datOf {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h
  d := fun i => (d.blo i).1
  pos := fun i => (d.blo i).2.pos
  sum := sum_blo d
  μ := fun i => mu1 E (d.blo i).1
  V := fun i => bV (d.blo i).2
  summand := fun i => bV_summand _

private theorem map_split {r s : ℕ} (f : Fin (r + s) → ℂ) :
    (Finset.univ.val.map f) = (Finset.univ.val.map fun i : Fin r => f (Fin.castAdd s i)) +
      (Finset.univ.val.map fun i : Fin s => f (Fin.natAdd r i)) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

private theorem lam_ms {n : ℕ} (d : Dat S n) (τ : E →+* ℂ) : ∀ z : Fin d.len → ℂ,
    (Finset.univ.val.map fun i : Fin n => d.lam τ i + z (d.idx i)) =
      ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j) := by
  induction d with
  | nil =>
    intro z
    change _ = ∑ j : Fin 0, _
    simp
  | @cons r s b d ih =>
    intro (z : Fin (d.len + 1) → ℂ)
    change _ = ∑ j : Fin (d.len + 1), (Finset.univ.val.map (((Dat.cons b d).blo j).2.Λ τ)).map (· + z j)
    rw [map_split, Fin.sum_univ_succ]
    have h1 : (fun i : Fin r => (Dat.cons b d).lam τ (Fin.castAdd s i) + z ((Dat.cons b d).idx (Fin.castAdd s i))) =
        fun i => b.Λ τ i + z 0 := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
    have h2 : (fun i : Fin s => (Dat.cons b d).lam τ (Fin.natAdd r i) + z ((Dat.cons b d).idx (Fin.natAdd r i))) =
        fun i => d.lam τ i + z (d.idx i).succ := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)
    rw [h1, h2, ih fun j => z j.succ, Multiset.map_map]
    rfl

private theorem sat_blo {n : ℕ} (d : Dat S n) (j : Fin d.len) : d.sat j = (d.blo j).2.sat := by
  induction d with
  | nil => exact (j : Fin 0).elim0
  | @cons r s b d ih =>
    revert j
    change ∀ j : Fin (d.len + 1), _
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact ih i

private theorem pt_on {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ}
    (ho : d.On Λ t) : (datOf d h).Pt S Λ t := by
  obtain ⟨z, hΛ, ht⟩ := ho
  refine ⟨z, fun i τ => Finset.univ.val.map ((d.blo i).2.Λ τ), fun i w => ((d.blo i).2.sat w).map fun x : ℂˣ => (x : ℂ),
    fun i => UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.bloAt E S _ _ _ (bV_summand _) (bV_mem _), fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ]
    exact lam_ms d τ z
  · rw [ht w hw]
    unfold Dat.ptS
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sat_blo, Multiset.map_map]
    rfl

private theorem two_blocks {n : ℕ} (d : Dat S n) (h : d.len = 2) (hs : ∀ i, (d.blo i).1 = 2) :
    ∃ b₁ b₂ : Blo S 2, HEq d (Dat.cons b₁ (Dat.cons b₂ (Dat.nil : Dat S 0))) := by
  cases d with
  | nil => exact absurd h (by simp [Dat.len])
  | @cons r s b d =>
    cases d with
    | nil => exact absurd h (by simp [Dat.len])
    | @cons r' s' b' d =>
      cases d with
      | nil =>
        obtain rfl : r = 2 := hs (0 : Fin 2)
        obtain rfl : r' = 2 := hs (1 : Fin 2)
        exact ⟨b, b', HEq.rfl⟩
      | cons _ _ => exact absurd h (by simp [Dat.len])

private theorem form_mem {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ} {τ : Submodule ℂ (LL (mu1 E 2))}
    (b : Blo S 2) (hA : At (mu1 E 2) S (bV b) m B)
    (hs : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m B → V = τ) :
    ((cuspToL2 (mu1 E 2) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ := by
  rw [← hs _ (bV_summand b) hA]
  exact bV_mem b

private theorem fin_two_ne : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

set_option maxHeartbeats 2000000 in
private theorem core (τ₁ τ₂ : Submodule ℂ (LL (mu1 E 2))) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ) (B₁ B₂ : BW.Pl E → Multiset ℂ)
    (smo₁ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₁ B₁ → V = τ₁)
    (smo₂ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₂ B₂ → V = τ₂)
    (rigid : ∀ b : Datum E (2 + 2), b.Pt S (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w) →
      b.r = 2 ∧ (∀ i, b.d i = 2) ∧ ∃ i j, i ≠ j ∧ At (b.μ i) S (b.V i) m₁ B₁ ∧ At (b.μ j) S (b.V j) m₂ B₂)
    (d : Dat S (2 + 2)) (h : 2 ≤ d.len) (ho : d.On (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w)) :
    ∃ b₁ b₂ : Blo S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
      ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂) ∨
        (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁)) := by
  have hP := pt_on d h ho
  have key := rigid (datOf d h) hP
  have hr := key.1
  have hd := key.2.1
  obtain ⟨b₁, b₂, he⟩ := two_blocks d hr hd
  obtain ⟨i, j, hij, hi, hj⟩ := key.2.2
  have he' : d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) := eq_of_heq he
  subst he'
  refine ⟨b₁, b₂, rfl, ?_⟩
  revert i j
  change ∀ i j : Fin 2, _
  intro i j hij hi hj
  rcases fin_two_ne i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨form_mem b₁ hi smo₁, form_mem b₂ hj smo₂⟩
  · exact Or.inr ⟨form_mem b₁ hj smo₂, form_mem b₂ hi smo₁⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.exempt :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (μ : Measure (normOneGL E (2 + 2))) [μ.IsHaarMeasure] (θ : Twist μ)
      (𝔢 : Side θ 2) (𝔵 : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (d : Dat 𝔢.S (2 + 2)), 2 ≤ d.len → d.On 𝔵.Λ 𝔵.t →
      ∃ b₁ b₂ : Blo 𝔢.S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
        ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂) ∨
          (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁)) := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 d h ho
  exact core 𝔵.τ₁ 𝔵.τ₂ 𝔵.m₁ 𝔵.m₂ 𝔵.B₁ 𝔵.B₂ 𝔵.smo₁ 𝔵.smo₂ 𝔵.rigid d h ho
