import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimpleLabelOfSeriesIdempotentPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharactStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.GoodFactor

open Formalism.L2.NT

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]

theorem isChar_prod [DecidableEq ι] {ψ : ∀ i, G i → ℂ} (h : ∀ i, IsChar (ψ i)) :
    IsChar (fun g : (∀ i, G i) => ∏ i, ψ i (g i)) := by
  choose n ρ hρ using h
  let J := ∀ i, Fin (n i)
  let Mf : (∀ i, G i) → Matrix J J ℂ := fun g => Matrix.of fun p q =>
    ∏ i, (ρ i (g i) : Matrix (Fin (n i)) (Fin (n i)) ℂ) (p i) (q i)
  have hM1 : Mf 1 = 1 := by
    ext p q
    simp only [Mf, Matrix.of_apply, Pi.one_apply, map_one, Units.val_one, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hpq
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hMm : ∀ g h, Mf (g * h) = Mf g * Mf h := by
    intro g h
    ext p q
    rw [Matrix.mul_apply]
    simp only [Mf, Matrix.of_apply, Pi.mul_apply, map_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    rfl
  let M : (∀ i, G i) →* Matrix J J ℂ := { toFun := Mf, map_one' := hM1, map_mul' := hMm }
  let e := Fintype.equivFin J
  let φ : (∀ i, G i) →* Matrix (Fin (Fintype.card J)) (Fin (Fintype.card J)) ℂ :=
    ((Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom : _ →* _).comp M
  refine ⟨Fintype.card J, MonoidHom.toHomUnits φ, fun g => ?_⟩
  have h1 : Matrix.trace (MonoidHom.toHomUnits φ g).val = Matrix.trace (M g) := by
    show Matrix.trace (Matrix.reindex e e (M g)) = _
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun j => M g j j)
  rw [h1]
  simp only [hρ]
  show _ = ∑ p : J, ∏ i, (ρ i (g i) : Matrix (Fin (n i)) (Fin (n i)) ℂ) (p i) (p i)
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rfl

variable [∀ i, Fintype (G i)]

theorem ipG_prod [DecidableEq ι] (ψ ψ' : ∀ i, G i → ℂ) :
    ipG (fun g : (∀ i, G i) => ∏ i, ψ i (g i)) (fun g => ∏ i, ψ' i (g i)) = ∏ i, ipG (ψ i) (ψ' i) := by
  unfold ipG
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, star_prod]

theorem isIrrChar_prod [DecidableEq ι] {ψ : ∀ i, G i → ℂ} (h : ∀ i, IsIrrChar (ψ i)) :
    IsIrrChar (fun g : (∀ i, G i) => ∏ i, ψ i (g i)) := by
  refine ⟨isChar_prod fun i => (h i).1, ?_⟩
  rw [ipG_prod, Finset.prod_congr rfl fun i _ => (h i).2, Fintype.card_pi]
  push_cast
  rfl

section One
variable {H : Type} [Group H] [Fintype H]

theorem exists_simple {ψ : H → ℂ} (h : IsIrrChar ψ) : ∃ V : FDRep ℂ H, Simple V ∧ ψ = V.character :=
  (PI.SerBridgeGLW.irrCharIff_of PI.SerBridgeGLW.conjugate_character_formula H ψ).1 h

theorem isIrrChar_character (V : FDRep ℂ H) (h : Simple V) : IsIrrChar V.character :=
  (PI.SerBridgeGLW.irrCharIff_of PI.SerBridgeGLW.conjugate_character_formula H _).2 ⟨V, h, rfl⟩

theorem irr_one_ne_zero {ψ : H → ℂ} (h : IsIrrChar ψ) : ψ 1 ≠ 0 := by
  obtain ⟨V, hV, rfl⟩ := exists_simple h
  haveI := hV
  haveI := PI.CharIdemW.nontrivial_of_simple V
  rw [FDRep.char_one]
  exact_mod_cast Module.finrank_pos.ne'

theorem eq_of_sum_ne_zero {χ ψ : H → ℂ} (hχ : IsIrrChar χ) (hψ : IsIrrChar ψ)
    (h : ∑ x, χ x * ψ x⁻¹ ≠ 0) : χ = ψ := by
  classical
  obtain ⟨V, hV, rfl⟩ := exists_simple hχ
  obtain ⟨W, hW, rfl⟩ := exists_simple hψ
  haveI := hV
  haveI := hW
  have hc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  haveI := invertibleOfNonzero hc
  have ho := FDRep.char_orthonormal V W
  by_cases hi : Nonempty (V ≅ W)
  · obtain ⟨i⟩ := hi
    exact FDRep.char_iso i
  · rw [if_neg hi] at ho
    exact absurd ((mul_eq_zero.mp ho).resolve_left (inv_ne_zero hc)) h

theorem sum_single (e : MonoidAlgebra ℂ H) : ∑ g : H, MonoidAlgebra.single g (e.coeff g) = e := by
  classical
  apply MonoidAlgebra.ext
  ext t
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp [Finsupp.single_apply]

theorem asAlg_eq {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (e : MonoidAlgebra ℂ H) :
    ρ.asAlgebraHom e = ∑ g : H, e.coeff g • ρ g := by
  conv_lhs => rw [← sum_single e]
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single ρ g _

theorem coeff_conj {e : MonoidAlgebra ℂ H} (he : ∀ x, e * x = x * e) (g k : H) :
    e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun x : MonoidAlgebra ℂ H => x.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at h
  exact h

theorem central_idem_term {e : MonoidAlgebra ℂ H} (hc : ∀ x, e * x = x * e) (hi : e * e = e) {ψ : H → ℂ}
    (hψ : IsIrrChar ψ) : ∑ g, e.coeff g * ψ g = ψ 1 ∨ ∑ g, e.coeff g * ψ g = 0 := by
  classical
  obtain ⟨V, hVs, rfl⟩ := exists_simple hψ
  haveI := hVs
  haveI := PI.CharIdemW.nontrivial_of_simple V
  have hcomm : ∀ k : H, V.ρ k * (∑ g, e.coeff g • V.ρ g) = (∑ g, e.coeff g • V.ρ g) * V.ρ k :=
    PI.CharIdemW.comm_of_class V (fun g => e.coeff g) (fun g k => coeff_conj hc g k)
  obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar V _ hcomm
  have hT : Representation.asAlgebraHom V.ρ e = μ • (1 : Module.End ℂ V) := by
    rw [asAlg_eq V.ρ e]; exact hμ
  have hμμ : μ * μ = μ := by
    have h2 : Representation.asAlgebraHom V.ρ (e * e) = Representation.asAlgebraHom V.ρ e := by rw [hi]
    rw [map_mul, hT, smul_mul_smul_comm, one_mul] at h2
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h3 := congrArg (fun f : Module.End ℂ V => f v) h2
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h3
    have : (μ * μ - μ) • v = 0 := by rw [sub_smul, h3, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv)
  have htr : ∑ g, e.coeff g * V.character g = μ * V.character 1 := by
    have h1 : LinearMap.trace ℂ V (∑ g, e.coeff g • V.ρ g) = ∑ g, e.coeff g * V.character g := by
      simp only [FDRep.character, map_sum, map_smul, smul_eq_mul]
    rw [← h1, hμ]
    simp [FDRep.character]
  have hμ01 : μ * (μ - 1) = 0 := by linear_combination hμμ
  rcases mul_eq_zero.mp hμ01 with h0 | h0
  · right; rw [htr, h0, zero_mul]
  · left; rw [htr, sub_eq_zero.mp h0, one_mul]

end One

theorem exists_factor [DecidableEq ι] {χ : (∀ i, G i) → ℂ} (hχ : IsIrrChar χ) :
    ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar (ψ i)) ∧ ∀ g, χ g = ∏ i, ψ i (g i) := by
  classical
  let Z : ∀ i, Finset (MonoidAlgebra ℂ (G i)) := fun i => (GlobalTheory.SerOSys.ZSum.zIdem_set_finite (Γ := G i)).toFinset
  have hZ : ∀ i, ∑ z ∈ Z i, z = 1 := fun i => by
    rw [← finsum_mem_eq_finite_toFinset_sum]
    exact GlobalTheory.SerOSys.ZSum.zIdem_set_finsum
  have hone : ∀ (i) (t : G i), ∑ z ∈ Z i, z.coeff t = if t = 1 then 1 else 0 := fun i t => by
    have h := congrArg (fun a : MonoidAlgebra ℂ (G i) => a.coeff t) (hZ i)
    simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.one_def,
      MonoidAlgebra.coeff_single, Finsupp.single_apply] at h
    rw [h]
    by_cases ht : t = 1
    · rw [if_pos ht.symm, if_pos ht]
    · rw [if_neg (Ne.symm ht), if_neg ht]
  have hdelta : ∀ x : (∀ i, G i), ∑ p ∈ Fintype.piFinset Z, ∏ i, (p i).coeff (x i) = if x = 1 then 1 else 0 := by
    intro x
    rw [← Finset.prod_univ_sum Z (fun i z => z.coeff (x i))]
    simp only [hone]
    by_cases hx : x = 1
    · subst hx; simp
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hkey : χ 1 = ∑ p ∈ Fintype.piFinset Z, ∑ x, χ x * ∏ i, (p i).coeff (x i) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hdelta]
    simp
  obtain ⟨p, hp, hne⟩ : ∃ p ∈ Fintype.piFinset Z, ∑ x, χ x * ∏ i, (p i).coeff (x i) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact irr_one_ne_zero hχ (hkey.trans (Finset.sum_eq_zero hno))
  have hτ : ∀ i, ∃ τ : FDRep ℂ (G i), Simple τ ∧ zIdem τ = p i := fun i => by
    have := Fintype.mem_piFinset.1 hp i
    simpa [Z] using this
  choose τ hτs hτz using hτ
  have hirr : ∀ i, IsIrrChar (τ i).character := fun i => isIrrChar_character _ (hτs i)
  refine ⟨fun i => (τ i).character, hirr, fun g => ?_⟩
  have hP := isIrrChar_prod hirr
  have := eq_of_sum_ne_zero hχ hP (fun h0 => hne ?_)
  · exact congrFun this g
  · have hco : ∀ x : (∀ i, G i), ∏ i, (p i).coeff (x i) =
        (∏ i, ((Module.finrank ℂ (τ i) : ℂ) / Fintype.card (G i))) * ∏ i, (τ i).character (x⁻¹ i) := by
      intro x
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hτz i, zIdem_coeff]
      rfl
    simp only [hco]
    simp only [mul_left_comm _ (∏ i, ((Module.finrank ℂ (τ i) : ℂ) / Fintype.card (G i))) _]
    rw [← Finset.mul_sum, h0, mul_zero]

theorem exists_good_factor {A : ι → Type} [∀ i, Fintype (A i)] [inst : Fintype (∀ i, G i)]
    (E : ∀ i, A i → MonoidAlgebra ℂ (G i))
    (hI : ∀ i b, E i b * E i b = E i b) (hC : ∀ i b x, E i b * x = x * E i b)
    (P : (∀ i, A i) → Prop) [DecidablePred P] (e : MonoidAlgebra ℂ (∀ i, G i))
    [DecidableEq ι]
    (he : ∀ g, e.coeff g = ∑ a : (∀ i, A i), if P a then ∏ i, (E i (a i)).coeff (g i) else 0)
    {χ : (∀ i, G i) → ℂ} (hχ : IsIrrChar χ) (h : ∑ g, e.coeff g * χ g = χ 1) :
    ∃ (ψ : ∀ i, G i → ℂ) (a : ∀ i, A i), P a ∧ (∀ i, IsIrrChar (ψ i)) ∧
      (∀ i, ∑ x, (E i (a i)).coeff x * ψ i x = ψ i 1) ∧ ∀ g, χ g = ∏ i, ψ i (g i) := by
  obtain rfl : inst = Pi.instFintype := Subsingleton.elim _ _
  obtain ⟨ψ, hψ, hχe⟩ := exists_factor hχ
  by_contra hno
  have hz : ∀ a : (∀ i, A i), P a → ∏ i, ∑ x, (E i (a i)).coeff x * ψ i x = 0 := by
    intro a ha
    by_contra hne
    refine hno ⟨ψ, a, ha, hψ, fun i => ?_, hχe⟩
    rcases central_idem_term (hC i (a i)) (hI i (a i)) (hψ i) with h1 | h1
    · exact h1
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ i) h1) hne
  have hsum : ∑ g, e.coeff g * χ g = ∑ a : (∀ i, A i), if P a then ∏ i, ∑ x, (E i (a i)).coeff x * ψ i x else 0 := by
    simp only [he, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · rw [Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, hχe]
    · simp
  rw [hsum, Finset.sum_eq_zero fun a _ => ?_] at h
  · exact irr_one_ne_zero hχ h.symm
  · split_ifs with ha
    · exact hz a ha
    · rfl

theorem irreducible_character_good_idempotent_cuspidal_product : ∀ (D : D7) [Fintype (G0g D.nd)], (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∃ θ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GL (Fin D.R.r) (ZMod (D.host.g kv.1)) → ℂ, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩; GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (θ kv)) ∧ ∀ g, χ g = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv (g kv) := by
  intro D _ hO χ hχ h
  classical
  haveI hF : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI hN : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  choose C O hCO using hO
  obtain ⟨ψ, a, hP, hψ, hs, hχe⟩ := exists_good_factor
    (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (A := fun kv => Fin D.R.r → ZMod (D.host.g kv.1))
    (fun kv b => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf b))
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0
    (fun g => by
      unfold Formalism.BasicNotions.NTypes.e0
      rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, finsum_eq_sum_of_fintype])
    hχ h
  refine ⟨ψ, fun kv => ?_, hχe⟩
  have hsq : Squarefree (Formalism.CyclotomicNorms.monicOf (a kv)) := (hP kv.1).1.2.1 kv.2
  have h1 := hs kv
  simp only [hCO] at h1
  obtain ⟨τ, hτ, hl, hc⟩ := GlobalTheory.T.exists_simple_label_of_seriesIdempotent_pair (D.host.g kv.1) (C kv.1) (O kv.1) D.R.r (Formalism.CyclotomicNorms.monicOf (a kv)) (ψ kv)
    (hψ kv) h1
  have h2 := GlobalTheory.T.squarefreeLabel_isCuspidalParabolicProductCharacter (ZMod (D.host.g kv.1)) (C kv.1) (O kv.1) D.R.r τ _ hτ hl hsq
  have e : ψ kv = fun x => τ.character x := funext fun x => (hc x).symm
  rw [e]
  exact h2

end GlobalTheory.GoodFactor
