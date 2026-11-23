import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.MixApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FixGen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def infPart {F : Type} [Field F] [NumberField F] (b : A F) : A F := ⟨b.1, 0⟩

private theorem cm {F : Type} [Field F] [NumberField F] (a b : G1 F) :
    ((a * b : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = a.1 * b.1 := rfl

private theorem nU_coe {F : Type} [Field F] [NumberField F] (b : A F) :
    ((nU b : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = !![1, b; 0, 1] := rfl

private theorem wW_coe (F : Type) [Field F] [NumberField F] :
    ((wW F : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = !![0, 1; -1, 0] := rfl

private theorem pi_nU {F : Type} [Field F] [NumberField F] (pi : G1 F →* G1 F)
    (h1 : ∀ g, FinOne (pi g)) (h2 : ∀ g i j, (pi g i j).1 = (g i j).1) (b : A F) :
    pi (nU b) = nU (infPart b) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Prod.ext ((h2 _ i j).trans ?_) ((h1 _ i j).trans ?_)
  · fin_cases i <;> fin_cases j <;> simp [nU, infPart]
  · fin_cases i <;> fin_cases j <;> simp [nU, infPart]

private theorem nU_inv' {F : Type} [Field F] [NumberField F] (b : A F) : (nU b)⁻¹ = nU (-b) := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  simp only [cm, nU_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem wW_inv' (F : Type) [Field F] [NumberField F] : (wW F)⁻¹ = wW F * wW F * wW F := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  simp only [cm, wW_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem prod_entries {F : Type} [Field F] [NumberField F] (e : A F) (he : e * e = e) :
    ((nU e * (wW F * nU e * (wW F * wW F * wW F)) * nU e : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) =
      !![1 - e, e; -e, 1 - e] := by
  simp only [cm, nU_coe, wW_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · rw [he]; ring
  · rw [he]; linear_combination (-1 : A F) * he
  · rw [he]; ring

private theorem pi_wW {F : Type} [Field F] [NumberField F] (pi : G1 F →* G1 F)
    (h1 : ∀ g, FinOne (pi g)) (h2 : ∀ g i j, (pi g i j).1 = (g i j).1) :
    pi (wW F) = nU (infPart 1) * (wW F * nU (infPart 1) * (wW F)⁻¹) * nU (infPart 1) := by
  have he : infPart (1 : A F) * infPart 1 = infPart 1 :=
    Prod.ext (by change ((1 : A F) * 1).1 = (1 : A F).1; rw [mul_one])
      (by change (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0; exact mul_zero _)
  have a1 : (1 - infPart 1 : A F).1 = 0 := by
    change (1 : A F).1 - (1 : A F).1 = 0
    exact sub_self _
  have a2 : (1 - infPart 1 : A F).2 = (1 : A F).2 := by
    change (1 : A F).2 - 0 = _
    exact sub_zero _
  have a3 : (-infPart 1 : A F).1 = (-1 : A F).1 := rfl
  have a4 : (-infPart 1 : A F).2 = 0 := by
    change -(0 : FiniteAdeleRing (𝓞 F) F) = 0
    exact neg_zero
  have a5 : (infPart 1 : A F).1 = (1 : A F).1 := rfl
  have a6 : (infPart 1 : A F).2 = 0 := rfl
  rw [wW_inv']
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [prod_entries _ he]
  refine Prod.ext ((h2 _ i j).trans ?_) ((h1 _ i j).trans ?_)
  · fin_cases i <;> fin_cases j <;> simp [wW, a1, a3, a5]
  · fin_cases i <;> fin_cases j <;> simp [a2, a4, a6]

private def keep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) : Submonoid (G1 F) where
  carrier := {g | ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ}
  one_mem' := fun φ h => by
    rw [map_one]
    exact h
  mul_mem' := fun {a b} ha hb φ h => by
    rw [map_mul]
    exact ha _ (hb _ h)

private theorem mem_keep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) (g : G1 F) :
    g ∈ keep W Λ ↔ ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ := Iff.rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.omFix :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (g : G1 F), FinOne g → ∀ Λ, ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W g hg Λ φ hφ
  obtain ⟨pi, pf, -, hp⟩ := proj F
  have h1 : ∀ g, FinOne (pi g) := fun g => (hp g).1
  have h2 : ∀ g i j, (pi g i j).1 = (g i j).1 := fun g => (hp g).2.2.2.1
  have hw : wW F ∈ keep W Λ := (mem_keep W Λ _).2 fun φ h => (fixGen F E D W Λ φ h).1
  have hn : ∀ b : A F, b.2 = 0 → nU b ∈ keep W Λ := fun b hb =>
    (mem_keep W Λ _).2 fun φ h => (fixGen F E D W Λ φ h).2 b hb
  have hwi : (wW F)⁻¹ ∈ keep W Λ := by
    rw [wW_inv']
    exact mul_mem (mul_mem hw hw) hw
  have hpn : ∀ b, pi (nU b) ∈ keep W Λ := fun b => by
    rw [pi_nU pi h1 h2]
    exact hn _ rfl
  have hpw : pi (wW F) ∈ keep W Λ := by
    rw [pi_wW pi h1 h2]
    exact mul_mem (mul_mem (hn _ rfl) (mul_mem (mul_mem hw (hn _ rfl)) hwi)) (hn _ rfl)
  have hpwi : pi (wW F)⁻¹ ∈ keep W Λ := by
    rw [wW_inv', map_mul, map_mul]
    exact mul_mem (mul_mem hpw hpw) hpw
  let T : Subgroup (G1 F) :=
    { carrier := {y | pi y ∈ keep W Λ ∧ pi y⁻¹ ∈ keep W Λ}
      one_mem' := ⟨by rw [map_one]; exact one_mem _, by rw [inv_one, map_one]; exact one_mem _⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨by rw [map_mul]; exact mul_mem ha.1 hb.1, by rw [_root_.mul_inv_rev, map_mul]; exact mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have hT : Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) ≤ T := by
    refine (Subgroup.closure_le T).2 ?_
    rintro _ (⟨b, rfl⟩ | rfl)
    · exact ⟨hpn b, by rw [nU_inv']; exact hpn _⟩
    · exact ⟨hpw, hpwi⟩
  have hgT : g ∈ T := hT (by rw [(gen F).1]; exact Subgroup.mem_top g)
  have hpg : pi g = g := Matrix.SpecialLinearGroup.ext _ _ fun i j =>
    Prod.ext (h2 g i j) ((h1 g i j).trans (hg i j).symm)
  have hk : g ∈ keep W Λ := by
    have := hgT.1
    rwa [hpg] at this
  exact (mem_keep W Λ g).1 hk φ hφ
