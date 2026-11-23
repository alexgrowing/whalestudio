import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

noncomputable section

namespace GlobalTheory.UniLevelIndex

open IsDedekindDomain.HeightOneSpectrum

section Count

theorem card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = ∑ i : Fin n, (i : ℕ) := by
  let e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun x => ⟨(⟨x.2.val, lt_trans x.2.2 x.1.2⟩, x.1), x.2.2⟩
      left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
      right_inv := by rintro ⟨j, i⟩; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp

theorem coprime_prod_pow_sub_one {q p : ℕ} (n : ℕ) (hp : p.Prime) (hpq : p ∣ q) (hq : 0 < q) :
    Nat.Coprime (∏ i : Fin n, (q ^ (n - i) - 1)) p := by
  refine Nat.Coprime.prod_left fun i _ => ?_
  have hm : n - (i : ℕ) ≠ 0 := by have := i.2; omega
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hd
  have h2 : p ∣ q ^ (n - i) := dvd_pow hpq hm
  have h1 : 1 ≤ q ^ (n - i) := Nat.one_le_pow _ _ hq
  have h3 := Nat.dvd_sub h2 hd
  rw [Nat.sub_sub_self h1] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

variable (κ : Type) [Field κ] [Finite κ]

theorem unip_index (n : ℕ) : (Formalism.L2.DIV.unip κ n).index = ∏ i : Fin n, (Nat.card κ ^ (n - i) - 1) := by
  classical
  letI := Fintype.ofFinite κ
  have h1 := Subgroup.card_mul_index (Formalism.L2.DIV.unip κ n)
  rw [GlobalTheory.Mem.GrpCount.card_unip, card_pairs_lt, Matrix.card_GL_field, ← Nat.card_eq_fintype_card] at h1
  have h2 : ∏ i : Fin n, (Nat.card κ ^ n - Nat.card κ ^ (i : ℕ)) =
      Nat.card κ ^ (∑ i : Fin n, (i : ℕ)) * ∏ i : Fin n, (Nat.card κ ^ (n - i) - 1) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [h2] at h1
  have hq : 0 < Nat.card κ ^ (∑ i : Fin n, (i : ℕ)) := pow_pos Nat.card_pos _
  exact Nat.eq_of_mul_eq_mul_left hq h1

end Count

section Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

variable (v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L)))

def toVS : (v.adicCompletionIntegers L⁺).toSubring →+* v.adicCompletionIntegers L⁺ where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def ofVS : v.adicCompletionIntegers L⁺ →+* (v.adicCompletionIntegers L⁺).toSubring where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def redGL (n : ℕ) : GL (Fin n) (v.adicCompletionIntegers L⁺).toSubring →*
    GL (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) :=
  Matrix.GeneralLinearGroup.map ((IsLocalRing.residue (v.adicCompletionIntegers L⁺)).comp (toVS v))

theorem residue_eq_zero_iff' (x : v.adicCompletionIntegers L⁺) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) x = 0 ↔ Valued.v (x : v.adicCompletion L⁺) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L⁺) (WithZero (Multiplicative ℤ))))

theorem res_toVS_eq_zero_iff (x : (v.adicCompletionIntegers L⁺).toSubring) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) (toVS v x) = 0 ↔ Valued.v (x : v.adicCompletion L⁺) < 1 :=
  residue_eq_zero_iff' v (toVS v x)

theorem res_toVS_eq_one_iff (x : (v.adicCompletionIntegers L⁺).toSubring) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) (toVS v x) = 1 ↔ Valued.v ((x : v.adicCompletion L⁺) - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (v.adicCompletionIntegers L⁺)), ← map_sub, residue_eq_zero_iff']
  exact Iff.rfl

theorem redGL_surjective (n : ℕ) : Function.Surjective (redGL v n) := by
  intro M
  choose A hA using fun i j => (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers L⁺))
    ((M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))) i j)
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L⁺).toSubring := fun i j => ofVS v (A i j)
  have hB : ((IsLocalRing.residue (v.adicCompletionIntegers L⁺)).comp (toVS v)).mapMatrix B = M := by
    ext i j
    exact hA i j
  have hu : IsUnit ((toVS v).mapMatrix B).det := by
    have e : (IsLocalRing.residue (v.adicCompletionIntegers L⁺)).mapMatrix ((toVS v).mapMatrix B) =
        (M : Matrix (Fin n) (Fin n) _) := by
      rw [← hB]; ext i j; rfl
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, e]
    exact (Matrix.isUnits_det_units M).ne_zero
  have hBB : (ofVS v).mapMatrix ((toVS v).mapMatrix B) = B := by
    ext i j
    rfl
  have hdet : IsUnit B.det := by
    rw [← hBB, ← RingHom.map_det]
    exact hu.map (ofVS v)
  exact ⟨Matrix.nonsingInvUnit B hdet, Units.ext hB⟩

end Loc

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem prime_dvd_card_residue (v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L))) {p : ℕ} (hp : p.Prime)
    (hv : ((p : ℕ) : 𝓞 L⁺) ∈ v.asIdeal) [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))] :
    p ∣ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = 0 := by
    have : (IsLocalRing.residue (v.adicCompletionIntegers L⁺))
        (algebraMap (𝓞 L⁺) (v.adicCompletionIntegers L⁺) ((p : ℕ) : 𝓞 L⁺)) = 0 := by
      rw [residue_eq_zero_iff', algebraMap_adicCompletionIntegers_apply,
        adicCompletion.valued_coe (K := L⁺) (v := v), valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem v _).2 hv
    simpa using this
  have h1 : ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = p :=
    (hp.eq_one_or_self_of_dvd _ (ringChar.dvd h0)).resolve_left CharP.ringChar_ne_one
  have h2 := ringChar.dvd (FiniteField.cast_card_eq_zero (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)))
  rw [h1, ← Nat.card_eq_fintype_card] at h2
  exact h2

end Main

theorem relIndex_coprime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r p : ℕ)
    (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), p.Prime → s.Above p → r ≤ n →
    (∀ g, g ∈ H ↔ NG.UniRT s r g) →
    Nat.Coprime (H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring)) p := by
  intro L _ _ _ n s r p H hp hA _ hH
  classical
  haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) :=
    Formalism.UG.P.glint_finite_residueField s.v
  let ι := Formalism.UG.bc (n := Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.subtype
  have hG : Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring = ι.range := rfl
  rw [hG, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
  have hmem : ∀ g, g ∈ H.comap ι ↔ NG.UniRT s r (ι g) := fun g => hH (ι g)
  have hker : (redGL s.v n).ker ≤ H.comap ι := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have he : ∀ a b, IsLocalRing.residue _ (toVS s.v ((g : Matrix (Fin n) (Fin n) _) a b)) =
        (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b :=
      fun a b => by
        have := congrArg (fun M : GL (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) => (M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b) hg
        exact this
    have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
      intro a b hab
      have h2 := he a b
      rw [Matrix.one_apply_ne hab] at h2
      exact (res_toVS_eq_zero_iff s.v _).1 h2
    refine (hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hoff a b ?_⟩, fun a b _ _ => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · intro h; subst h; omega
    · intro h; subst h; exact lt_irrefl _ hba
    · subst hab
      have h2 := he a a
      rw [Matrix.one_apply_eq] at h2
      exact (res_toVS_eq_one_iff s.v _).1 h2
  rw [← Subgroup.index_map_eq (H.comap ι) (redGL_surjective s.v n) hker]
  have hU : Formalism.L2.DIV.unip (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) n ≤
      (H.comap ι).map (redGL s.v n) := by
    intro M hM
    obtain ⟨h0, h1⟩ := hM
    let lift := Function.surjInv (IsLocalRing.residue_surjective (R := s.v.adicCompletionIntegers (maximalRealSubfield L)))
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun i j =>
      if j < i then 0 else if i = j then 1 else ofVS s.v (lift ((M : Matrix (Fin n) (Fin n) _) i j))
    have hlow : ∀ i j, j < i → B i j = 0 := by intro i j h; simp [B, h]
    have hdiag : ∀ i, B i i = 1 := by intro i; simp [B]
    have hdet : B.det = 1 := by
      rw [Matrix.det_of_upperTriangular hlow]
      simp [hdiag]
    let g := Matrix.nonsingInvUnit B (by rw [hdet]; exact isUnit_one)
    have hgB : ((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = fun i j => ((B i j : _) : s.v.adicCompletion (maximalRealSubfield L)) := rfl
    have hlowK : ∀ a b : Fin n, b < a → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
      intro a b h
      rw [hgB]
      simp only [hlow a b h, ZeroMemClass.coe_zero, map_zero]
      exact zero_lt_one
    refine ⟨g, (hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hlowK a b ?_⟩, fun a b _ _ => ⟨fun hba => hlowK a b hba, fun hab => ?_⟩⟩, ?_⟩
    · exact Fin.lt_def.2 (by omega)
    · subst hab
      rw [hgB]
      simp only [hdiag, OneMemClass.coe_one, sub_self, map_zero]
      exact zero_lt_one
    · apply Units.ext
      ext i j
      show IsLocalRing.residue _ (toVS s.v (B i j)) = (M : Matrix (Fin n) (Fin n) _) i j
      by_cases hji : j < i
      · rw [hlow i j hji, map_zero, map_zero]
        exact (h0 hji).symm
      · by_cases hij : i = j
        · subst hij
          rw [hdiag, map_one, map_one, h1]
        · simp only [B, if_neg hji, if_neg hij]
          exact Function.surjInv_eq _ _
  refine Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hU) ?_
  rw [unip_index]
  exact coprime_prod_pow_sub_one n hp (prime_dvd_card_residue s.v hp hA) Nat.card_pos

end GlobalTheory.UniLevelIndex
