import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.TrivFlagKills
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmShift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
import Development.WeilBound.CoreStatements.IdealCycleValues.ProjIdealIndependentOfBasis
import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagZ

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.HtPt.Pflag

theorem aeval_neg_hsymm (N a : ℕ) :
    aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) =
      C ((-1 : ℝ) ^ a) * hsymm (Fin N) ℝ a := by
  have hneg : (fun i : Fin N => (-X i : MvPolynomial (Fin N) ℝ)) = fun i => C (-1) * X i := by
    funext i
    simp
  simp only [hsymm, map_sum, map_multiset_prod, Multiset.map_map, Function.comp_def, aeval_X,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hneg, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← map_pow]
  simp

section
variable (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
  [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F))

theorem swap_num {N : ℕ} (b u : Fin N → K → ℤ) (G H : MvPolynomial (Fin N) ℝ) (Q : List (K → ℤ)) :
    ∑ μ ∈ G.support, G.coeff μ * genNum F V u H (classList b μ ++ Q) =
      ∑ ν ∈ H.support, H.coeff ν * genNum F V b G (classList u ν ++ Q) := by
  simp only [genNum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
  rw [intNumL_perm_of_perm F K ι V (classList u ν ++ (classList b μ ++ Q))
    (classList b μ ++ (classList u ν ++ Q)) (List.perm_append_comm_assoc _ _ _)]
  ring

private theorem genNum_eq_sum_of_support_subset {N : ℕ} (b : Fin N → K → ℤ) (P : MvPolynomial (Fin N) ℝ)
    (Q : List (K → ℤ)) (s : Finset (Fin N →₀ ℕ)) (hs : P.support ⊆ s) :
    genNum F V b P Q = ∑ μ ∈ s, P.coeff μ * (intNumL F V (classList b μ ++ Q) : ℝ) := by
  unfold genNum
  refine Finset.sum_subset hs fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]

private theorem genNum_add {N : ℕ} (b : Fin N → K → ℤ) (P P' : MvPolynomial (Fin N) ℝ)
    (Q : List (K → ℤ)) : genNum F V b (P + P') Q = genNum F V b P Q + genNum F V b P' Q := by
  classical
  rw [genNum_eq_sum_of_support_subset F K ι V b (P + P') Q (P.support ∪ P'.support) support_add,
    genNum_eq_sum_of_support_subset F K ι V b P Q (P.support ∪ P'.support) Finset.subset_union_left,
    genNum_eq_sum_of_support_subset F K ι V b P' Q (P.support ∪ P'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_add, add_mul]

private theorem genNum_monomial {N : ℕ} (b : Fin N → K → ℤ) (m : Fin N →₀ ℕ) (c : ℝ)
    (Q : List (K → ℤ)) : genNum F V b (monomial m c) Q = c * intNumL F V (classList b m ++ Q) := by
  classical
  rw [genNum_eq_sum_of_support_subset F K ι V b (monomial m c) Q {m} support_monomial_subset]
  simp

private theorem genNum_mul {N : ℕ} (b : Fin N → K → ℤ) (G H : MvPolynomial (Fin N) ℝ)
    (Q : List (K → ℤ)) :
    genNum F V b (G * H) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V b H (classList b μ ++ Q) := by
  classical
  let L : MvPolynomial (Fin N) ℝ →+ ℝ :=
    { toFun := fun P => genNum F V b P Q
      map_zero' := by simp [genNum]
      map_add' := fun P P' => genNum_add F K ι V b P P' Q }
  have hL : ∀ P, genNum F V b P Q = L P := fun _ => rfl
  have hG : G * H = ∑ μ ∈ G.support, ∑ ν ∈ H.support,
      monomial μ (G.coeff μ) * monomial ν (H.coeff ν) := by
    conv_lhs => rw [G.as_sum, H.as_sum]
    rw [Finset.sum_mul_sum]
  rw [hG, hL, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  unfold genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hp : (classList b (μ + ν)).Perm (classList b ν ++ classList b μ) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
    simp [classList, Finsupp.toMultiset_add, add_comm]
  have e1 : L (monomial μ (G.coeff μ) * monomial ν (H.coeff ν)) =
      G.coeff μ * H.coeff ν * intNumL F V (classList b (μ + ν) ++ Q) := by
    rw [← hL, monomial_mul, genNum_monomial]
  rw [e1, intNumL_perm_of_perm F K ι V _ (classList b ν ++ (classList b μ ++ Q))
    ((hp.append_right Q).trans (List.Perm.of_eq (List.append_assoc _ _ _)))]
  ring

theorem agree_mul {N : ℕ} (e : ℕ) (b u : Fin N → K → ℤ) (G H : MvPolynomial (Fin N) ℝ) (m n : ℕ)
    (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous n)
    (aG : ∀ Q : List (K → ℤ), m + Q.length = e → genNum F V b G Q = genNum F V u G Q)
    (aH : ∀ Q : List (K → ℤ), n + Q.length = e → genNum F V b H Q = genNum F V u H Q)
    (Q : List (K → ℤ)) (hQ : m + n + Q.length = e) :
    genNum F V b (G * H) Q = genNum F V u (G * H) Q := by
  classical
  calc genNum F V b (G * H) Q
      = ∑ μ ∈ G.support, G.coeff μ * genNum F V b H (classList b μ ++ Q) :=
        genNum_mul F K ι V b G H Q
    _ = ∑ μ ∈ G.support, G.coeff μ * genNum F V u H (classList b μ ++ Q) := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [aH]
        rw [List.length_append, length_classList_of_hom b hG hμ]
        omega
    _ = ∑ ν ∈ H.support, H.coeff ν * genNum F V b G (classList u ν ++ Q) :=
        swap_num F K ι V b u G H Q
    _ = ∑ ν ∈ H.support, H.coeff ν * genNum F V u G (classList u ν ++ Q) := by
        refine Finset.sum_congr rfl fun ν hν => ?_
        rw [aG]
        rw [List.length_append, length_classList_of_hom u hH hν]
        omega
    _ = genNum F V u (G * H) Q := by
        rw [mul_comm G H, genNum_mul]

theorem agree_prod {N : ℕ} (e : ℕ) (b u : Fin N → K → ℤ)
    (ah : ∀ (a : ℕ) (Q : List (K → ℤ)), a + Q.length = e →
      genNum F V b (hsymm (Fin N) ℝ a) Q = genNum F V u (hsymm (Fin N) ℝ a) Q)
    (t : Multiset ℕ) :
    ((t.map (hsymm (Fin N) ℝ)).prod).IsHomogeneous t.sum ∧
      ∀ Q : List (K → ℤ), t.sum + Q.length = e →
        genNum F V b (t.map (hsymm (Fin N) ℝ)).prod Q =
          genNum F V u (t.map (hsymm (Fin N) ℝ)).prod Q := by
  classical
  induction t using Multiset.induction_on with
  | empty =>
    refine ⟨by simpa using isHomogeneous_one (Fin N) ℝ, fun Q _ => ?_⟩
    have h1 : (1 : MvPolynomial (Fin N) ℝ) = monomial 0 1 := by
      rw [← C_1, C_apply]
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [h1, genNum_monomial, genNum_monomial]
    simp [classList]
  | cons a t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine ⟨(isHomogeneous_hsymm_real N a).mul ih1, fun Q hQ => ?_⟩
    exact agree_mul F K ι V e b u _ _ a t.sum (isHomogeneous_hsymm_real N a) ih1
      (fun Q hQ => ah a Q hQ) ih2 Q hQ

theorem cast_num {N : ℕ} (b : Fin N → K → ℤ) (G : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) :
    ((∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList b μ ++ Y) : ℤ) : ℝ) =
      genNum F V b (MvPolynomial.map (Int.castRingHom ℝ) G) Y := by
  unfold genNum
  rw [MvPolynomial.support_map_of_injective _ (Int.castRingHom ℝ).injective_int]
  push_cast
  simp [MvPolynomial.coeff_map]

end

private theorem relDim_eq_of_ringKrullDim_quotient (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    (P : Ideal (MRing ι F)) (e : ℕ)
    (hdim : ringKrullDim (MRing ι F ⧸ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hdim]
  have h1 : (((e + Fintype.card K : ℕ) : WithBot ℕ∞)) =
      ((((e + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) := rfl
  rw [h1, WithBot.map_coe]
  have h3 : ((e + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ) = (e : ℤ) := by
    push_cast
    ring
  have h4 : WithTop.map (fun e' : ℕ => (e' : ℤ) - (Fintype.card K : ℤ))
      (((e + Fintype.card K : ℕ) : ℕ∞)) = (((e : ℤ)) : WithTop ℤ) := by
    rw [← h3]
    rfl
  rw [h4]
  rfl

private theorem shift_agree_lemma_5 (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type)
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ)
    (hP : IsMultiProjPrime (pointIdeal F y))
    (hdim : ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (N : ℕ) (hN : 0 < N) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V)
    (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ) (hw : IsFlagFrame y B w b)
    (hv : IsFlagFrame y B v u) (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω V)
    (hφ : IsTwistedDualGens y B a φ) (r : ℕ) (Y : List (K → ℤ)) (hr : r + Y.length = e) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple N r,
        intNumL F (pointIdeal F y) (rootList (fun i => a - b i) α ++ Y) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r,
        intNumL F (pointIdeal F y) (rootList (fun i => a - u i) α ++ Y) := by
  let Φ := FractionRing (MvPolynomial (Fin N) Ω)
  let t : Fin N → Φ := fun i => algebraMap (MvPolynomial (Fin N) Ω) Φ (X i)
  have ht : AlgebraicIndependent Ω t :=
    (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) Φ)
      (IsFractionRing.injective (MvPolynomial (Fin N) Ω) Φ)
  have h1 := NumericalSegre.full F Ω K ι y e hP hdim N hN V B w b hw M a φ hφ Φ t ht
    (r + (N - 1)) Y (by omega)
  have h2 := NumericalSegre.full F Ω K ι y e hP hdim N hN V B v u hv M a φ hφ Φ t ht
    (r + (N - 1)) Y (by omega)
  have heq : projIdeal F y w φ t = projIdeal F y v φ t :=
    le_antisymm (BaseChangeColon.projIdeal_le y w v φ t ht) (BaseChangeColon.projIdeal_le y v w φ t ht)
  rw [heq, h2] at h1
  have hle : N - 1 ≤ r + (N - 1) := by omega
  have hsub : r + (N - 1) - (N - 1) = r := by omega
  rw [if_pos hle, if_pos hle, hsub] at h1
  exact h1.symm

private theorem negs_agree_lemma_6 (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)) (hP : IsMultiProjPrime W) (d : ℕ)
    (hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim W = ((d : ℕ) : WithBot (WithTop ℤ)))
    (N : ℕ) (hN : 0 < N) (b u : Fin N → K → ℤ) (a : K → ℤ)
    (hS : ∀ (r : ℕ) (Y : List (K → ℤ)), r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => a - b i) α ++ Y) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => a - u i) α ++ Y)) :
    ∀ (r : ℕ) (Y : List (K → ℤ)), r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (-b) α ++ Y) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (-u) α ++ Y) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro Y hrY
  have hb := HsymmShift.proof F K ι W hP d hrel N hN (-b) a r Y hrY
  have hu := HsymmShift.proof F K ι W hP d hrel N hN (-u) a r Y hrY
  have hab : (fun i => (-b) i + a) = fun i => a - b i := by
    funext i
    simp only [Pi.neg_apply]
    abel
  have hau : (fun i => (-u) i + a) = fun i => a - u i := by
    funext i
    simp only [Pi.neg_apply]
    abel
  rw [hab, Finset.sum_range_succ'] at hb
  rw [hau, Finset.sum_range_succ'] at hu
  have hR : ∑ x ∈ Finset.range r, ((N - 1 + r).choose (x + 1) : ℤ) *
        ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - (x + 1)),
          intNumL F W (rootList (-b) α ++ List.replicate (x + 1) a ++ Y) =
      ∑ x ∈ Finset.range r, ((N - 1 + r).choose (x + 1) : ℤ) *
        ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - (x + 1)),
          intNumL F W (rootList (-u) α ++ List.replicate (x + 1) a ++ Y) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    congr 1
    simp only [List.append_assoc]
    exact ih (r - (x + 1)) (by omega) (List.replicate (x + 1) a ++ Y) (by simp; omega)
  rw [hS r Y hrY, hu, hR] at hb
  have h0 := (add_left_cancel hb).symm
  simpa using h0

private theorem genNum_smul (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)) {N : ℕ} (b : Fin N → K → ℤ)
    (c : ℝ) (P : MvPolynomial (Fin N) ℝ) (Q : List (K → ℤ)) :
    genNum F W b (c • P) Q = c * genNum F W b P Q := by
  classical
  rw [genNum_eq_sum_of_support_subset F K ι W b (c • P) Q P.support (MvPolynomial.support_smul),
    genNum_eq_sum_of_support_subset F K ι W b P Q P.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_assoc]

private theorem genNum_hsymm_eq_of_intNumL_rootList_sum_eq (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)) (e : ℕ) (hP : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι F ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (N : ℕ) (b u : Fin N → K → ℤ)
    (hneg : ∀ (r : ℕ) (Y : List (K → ℤ)), r + Y.length = e →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (-b) α ++ Y) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (-u) α ++ Y))
    (r : ℕ) (Q : List (K → ℤ)) (hrQ : r + Q.length = e) :
    genNum F W b (hsymm (Fin N) ℝ r) Q = genNum F W u (hsymm (Fin N) ℝ r) Q := by
  have key : ∀ x : Fin N → K → ℤ, genNum F W (-x) (hsymm (Fin N) ℝ r) Q =
      (-1) ^ r * genNum F W x (hsymm (Fin N) ℝ r) Q := by
    intro x
    have h1 := genNum_neg F K ι W e hP hdim x (hsymm (Fin N) ℝ r) r
      (isHomogeneous_hsymm_real N r) Q hrQ
    rw [aeval_neg_hsymm, C_mul', genNum_smul] at h1
    exact h1.symm
  have h2 : genNum F W (-b) (hsymm (Fin N) ℝ r) Q = genNum F W (-u) (hsymm (Fin N) ℝ r) Q := by
    rw [genNum_hsymm, genNum_hsymm, hneg r Q hrQ]
  rw [key b, key u] at h2
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2

theorem field_flag_indep : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  intro F _ Ω _ _ K _ _ ι _ y e hP hdim N V _ _ B w v b u hw hv c G hsymG hG Y hY
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hbu : b = u := funext fun i => i.elim0
    rw [hbu]
  obtain ⟨a₁, ha⟩ := TwistedDualGensExist.proof F Ω K ι y N V B
  obtain ⟨M, φ, hφ⟩ := ha a₁ le_rfl
  have hrel := relDim_eq_of_ringKrullDim_quotient F K ι (pointIdeal F y) e hdim
  have hneg := negs_agree_lemma_6 F K ι (pointIdeal F y) hP e hrel N hN b u a₁
    (fun r Y' hr => shift_agree_lemma_5 F Ω K ι y e hP hdim N hN V B w v b u hw hv a₁ M φ hφ r Y' hr)
  have hh : ∀ (r : ℕ) (Q : List (K → ℤ)), r + Q.length = e →
      genNum F (pointIdeal F y) b (hsymm (Fin N) ℝ r) Q =
        genNum F (pointIdeal F y) u (hsymm (Fin N) ℝ r) Q :=
    fun r Q hrQ => genNum_hsymm_eq_of_intNumL_rootList_sum_eq F K ι (pointIdeal F y) e hP hdim N b u hneg r Q hrQ
  have hspan := SymmetricSpanHsymm.proof N c G hG hsymG
  apply Int.cast_injective (α := ℝ)
  rw [cast_num F K ι (pointIdeal F y) b G Y, cast_num F K ι (pointIdeal F y) u G Y]
  clear hG hsymG
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    have hm : MvPolynomial.map (Int.castRingHom ℝ) (hsymmPart (Fin N) ℤ μ) =
        (μ.parts.map (hsymm (Fin N) ℝ)).prod := by
      simp only [hsymmPart, hsymm, map_multiset_prod, Multiset.map_map, Function.comp_def, map_sum,
        MvPolynomial.map_X]
      rfl
    rw [hm]
    exact (agree_prod F K ι (pointIdeal F y) e b u (fun a Q h => hh a Q h) μ.parts).2 Y
      (by rw [μ.parts_sum]; omega)
  | zero => simp [genNum]
  | add x z _ _ hx hz =>
    rw [map_add, genNum_add, genNum_add, hx, hz]
  | smul n x _ hx =>
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, genNum_smul, genNum_smul, hx]

end PositivityTheory.HtPt.Pflag
