import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

open Formalism.UG

namespace Unimod

theorem mem_GLint_iff' {L : Type} [Field L] (O : Subring L) {m : ℕ} (M : GL (Fin m) L) :
    M ∈ GLint (Fin m) O ↔ (∀ i j, M.val i j ∈ O) ∧ (∀ i j, (M⁻¹).val i j ∈ O) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp [bc]
    · rw [← map_inv]
      simp [bc]
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin m) (Fin m) O := Matrix.of fun i j => ⟨M.val i j, h1 i j⟩
    let B : Matrix (Fin m) (Fin m) O := Matrix.of fun i j => ⟨(M⁻¹).val i j, h2 i j⟩
    have hA : A.map O.subtype = M.val := by ext i j; rfl
    have hB : B.map O.subtype = (M⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun X : Matrix (Fin m) (Fin m) O => X.map O.subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
    have hBA : B * A = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    refine ⟨⟨A, B, hAB, hBA⟩, Units.ext ?_⟩
    change A.map O.subtype = M.val
    exact hA

section HermLemmas
variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_smul_left {ι : Type} (s : Finset ι) (a : ι → K.E) (y : ι → B.A) (β z : B.A) :
    B.herm β (∑ i ∈ s, a i • y i) z = ∑ i ∈ s, a i * B.herm β (y i) z := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, Algebra.smul_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show β * (algebraMap K.E B.A (a i) * y i) * B.σ z = a i • (β * y i * B.σ z) by
    rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul]

theorem herm_sum_smul_right {ι : Type} (s : Finset ι) (a : ι → K.E) (z : ι → B.A) (β y : B.A) :
    B.herm β y (∑ i ∈ s, a i • z i) = ∑ i ∈ s, K.c (a i) * B.herm β y (z i) := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_sum, Finset.mul_sum, Algebra.smul_def, map_mul, B.σ_alg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show β * y * (algebraMap K.E B.A (K.c (a i)) * B.σ (z i)) = K.c (a i) • (β * y * B.σ (z i)) by
    rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul]

end HermLemmas

section Dual
variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem c_mem_range {x : K.E} (hx : x ∈ (algebraMap K.O K.E).range) : K.c x ∈ (algebraMap K.O K.E).range := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := K.c_int y
  exact ⟨z, hz.symm⟩

theorem mem_span_iff {m : ℕ} (v : Fin m → B.A) (z : B.A) :
    z ∈ Submodule.span K.O (Set.range v) ↔
      ∃ o : Fin m → K.O, ∑ k, (algebraMap K.O K.E (o k)) • v k = z := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]

theorem herm_span_right {m : ℕ} (v : Fin m → B.A) (β y : B.A) (d : Fin m → K.E) :
    B.herm β y (∑ k, d k • v k) = ∑ k, K.c (d k) * B.herm β y (v k) :=
  herm_sum_smul_right B _ _ _ _ _

theorem selfDual_iff {m : ℕ} (β : B.A) (v : Fin m → B.A) (hv : ∀ z, ∃ d : Fin m → K.E, z = ∑ k, d k • v k)
    (hH : IsUnit (Matrix.of fun j k => B.herm β (v j) (v k)).det) :
    ((∀ j k, (Matrix.of fun j k => B.herm β (v j) (v k)) j k ∈ (algebraMap K.O K.E).range) ∧
      (∀ j k, (Matrix.of fun j k => B.herm β (v j) (v k))⁻¹ j k ∈ (algebraMap K.O K.E).range)) ↔
    ∀ z, z ∈ Submodule.span K.O (Set.range v) ↔
      ∀ y ∈ Submodule.span K.O (Set.range v), B.herm β y z ∈ (algebraMap K.O K.E).range := by
  set H : Matrix (Fin m) (Fin m) K.E := Matrix.of fun j k => B.herm β (v j) (v k) with hHdef
  set R := (algebraMap K.O K.E).range

  have hgen : ∀ z, (∀ y ∈ Submodule.span K.O (Set.range v), B.herm β y z ∈ R) ↔ ∀ j, B.herm β (v j) z ∈ R := by
    intro z
    refine ⟨fun h j => h _ (Submodule.subset_span ⟨j, rfl⟩), fun h y hy => ?_⟩
    obtain ⟨o, rfl⟩ := (mem_span_iff B v y).1 hy
    rw [herm_sum_smul_left]
    exact R.sum_mem fun k _ => R.mul_mem ⟨o k, rfl⟩ (h k)
  have hmv : ∀ (d : Fin m → K.E) j, B.herm β (v j) (∑ k, d k • v k) = (H *ᵥ fun k => K.c (d k)) j := by
    intro d j
    rw [herm_span_right, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hHdef, Matrix.of_apply, mul_comm]
  have hinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hH
  have hinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hH
  constructor
  · rintro ⟨h1, h2⟩ z
    rw [hgen]
    constructor
    · intro hz j
      obtain ⟨o, rfl⟩ := (mem_span_iff B v z).1 hz
      rw [hmv, Matrix.mulVec, dotProduct]
      exact R.sum_mem fun k _ => R.mul_mem (h1 j k) (c_mem_range ⟨o k, rfl⟩)
    · intro hz
      obtain ⟨d, rfl⟩ := hv z
      have hu : ∀ j, (H *ᵥ fun k => K.c (d k)) j ∈ R := fun j => by rw [← hmv]; exact hz j
      have hd : (fun k => K.c (d k)) = H⁻¹ *ᵥ (H *ᵥ fun k => K.c (d k)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      have hk : ∀ k, d k ∈ R := by
        intro k
        have : K.c (d k) ∈ R := by
          rw [show K.c (d k) = (fun k => K.c (d k)) k from rfl, hd, Matrix.mulVec, dotProduct]
          exact R.sum_mem fun l _ => R.mul_mem (h2 k l) (hu l)
        have h' := c_mem_range this
        rwa [K.c_c] at h'
      rw [mem_span_iff]
      refine ⟨fun k => (hk k).choose, ?_⟩
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hk k).choose_spec]
  · intro h
    have hvd : ∀ k, v k ∈ Submodule.span K.O (Set.range v) := fun k => Submodule.subset_span ⟨k, rfl⟩
    have h1 : ∀ j k, H j k ∈ R := fun j k => by
      have := ((hgen (v k)).1 ((h (v k)).1 (hvd k))) j
      simpa [hHdef] using this
    refine ⟨h1, fun l k => ?_⟩

    let z : B.A := ∑ i, K.c (H⁻¹ i k) • v i
    have hz : ∀ j, B.herm β (v j) z = (1 : Matrix (Fin m) (Fin m) K.E) j k := by
      intro j
      rw [hmv]
      simp only [K.c_c]
      rw [Matrix.mulVec, dotProduct, ← hinv', Matrix.mul_apply]
    have hzl : z ∈ Submodule.span K.O (Set.range v) := by
      rw [h, hgen]
      intro j
      rw [hz j]
      by_cases hjk : j = k
      · subst hjk; rw [Matrix.one_apply_eq]; exact R.one_mem
      · rw [Matrix.one_apply_ne hjk]; exact R.zero_mem
    obtain ⟨o, ho⟩ := (mem_span_iff B v z).1 hzl

    have e1 : (H *ᵥ fun i => K.c (algebraMap K.O K.E (o i))) = H *ᵥ fun i => H⁻¹ i k := by
      funext j
      rw [← hmv, ho]
      show B.herm β (v j) z = _
      rw [hz j, Matrix.mulVec, dotProduct, ← Matrix.mul_apply, hinv']
    have e2 := congrArg (fun x => H⁻¹ *ᵥ x) e1
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at e2
    have hl : K.c (algebraMap K.O K.E (o l)) = H⁻¹ l k := congrFun e2 l
    rw [← hl]
    exact c_mem_range ⟨o l, rfl⟩
end Dual

section GroupPart

theorem invT_invT {a : ℕ} {R : Type} [CommRing R] (x : GL (Fin a) R) : invT a R (invT a R x) = x := by
  apply Units.ext
  change ((invT a R x)⁻¹).valᵀ = x.val
  rw [← map_inv]
  change (((x⁻¹)⁻¹).valᵀ)ᵀ = x.val
  rw [inv_inv, Matrix.transpose_transpose]

theorem invT_mem {L : Type} [Field L] (O : Subring L) {a : ℕ} {x : GL (Fin a) L} (hx : x ∈ GLint (Fin a) O) :
    invT a L x ∈ GLint (Fin a) O := by
  rw [mem_GLint_iff'] at hx ⊢
  refine ⟨fun i j => hx.2 j i, fun i j => ?_⟩
  rw [← map_inv]
  change ((x⁻¹)⁻¹).val j i ∈ O
  rw [inv_inv]
  exact hx.1 j i

theorem invT_mem_iff {L : Type} [Field L] (O : Subring L) {a : ℕ} (x : GL (Fin a) L) :
    invT a L x ∈ GLint (Fin a) O ↔ x ∈ GLint (Fin a) O :=
  ⟨fun h => by simpa [invT_invT] using invT_mem O h, invT_mem O⟩

theorem PhiU_mem {L : Type} [Field L] (O : Subring L) (a : ℕ) : PhiU a L ∈ GLint (Fin a) O := by
  rw [mem_GLint_iff']
  have hP : ∀ i j, GlobalTheory.Tw.Phi a L i j ∈ O := by
    intro i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact O.pow_mem (O.neg_mem O.one_mem) _
    · exact O.zero_mem
  exact ⟨fun i j => hP i j, fun i j => hP j i⟩

end GroupPart

theorem mem_Ov_iff {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ Ov E w ↔ Valued.v x ≤ 1 := by
  show x ∈ (w.adicCompletionIntegers E) ↔ _
  exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem unimodular_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → ∀ g : GLw m w, (g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ∈ GlobalTheory.LFun.KGL w m ↔ ∀ z, z ∈ GlobalTheory.TwLat.lat e b g ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.herm β y z ∈ (algebraMap K.O K.E).range) := by
  intro E _ _ _ _ w hw K e hc hv _ B m b β hG g
  set R := (algebraMap K.O K.E).range with hR
  set v : Fin m → B.A := fun j => ∑ i, e.symm (g.val i j) • b i with hvdef
  set H : Matrix (Fin m) (Fin m) K.E := Matrix.of fun j k => B.herm β (v j) (v k) with hHdef
  set M : GLw m w := invT m _ g⁻¹ * hG.unit * Matrix.GeneralLinearGroup.map (cj w) g with hMdef

  have hX : g⁻¹ * dlt e b β * thL m w g = invT m _ M * (PhiU m _)⁻¹ := by
    rw [dlt, dif_pos hG, thL, if_neg hw, hMdef, map_mul, map_mul, invT_invT]
    simp only [thetaGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

  have hmemX : (g⁻¹ * dlt e b β * thL m w g ∈ GlobalTheory.LFun.KGL w m) ↔ M ∈ GLint (Fin m) (Ov E w) := by
    rw [hX, Subgroup.mul_mem_cancel_right _ (inv_mem (PhiU_mem _ m))]
    exact invT_mem_iff _ M

  have hMval : M.val = H.map e := by
    have h1 : M.val = g.valᵀ * gram e b β * g.val.map (cj w) := by
      rw [hMdef, Units.val_mul, Units.val_mul, IsUnit.unit_spec]
      congr 2
    rw [h1]
    ext j k
    simp only [hHdef, hvdef, Matrix.map_apply, Matrix.of_apply, herm_sum_smul_left, herm_sum_smul_right,
      map_sum, map_mul, hc, RingEquiv.apply_symm_apply, Matrix.mul_apply, Matrix.transpose_apply, gram,
      Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hH : IsUnit H.det := by
    have h1 : IsUnit (M.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
    have hd : (H.map e).det = e H.det := (RingHom.map_det (e : K.E →+* w.adicCompletion E) H).symm
    rw [hMval, hd] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  have hMinv : (M⁻¹).val = H⁻¹.map e := by
    rw [Matrix.coe_units_inv, hMval]
    refine Matrix.inv_eq_left_inv ?_
    have hm : H⁻¹.map e * H.map e = (H⁻¹ * H).map e := (Matrix.map_mul (f := (e : K.E →+* w.adicCompletion E))).symm
    rw [hm, Matrix.nonsing_inv_mul _ hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMem : M ∈ GLint (Fin m) (Ov E w) ↔
      (∀ j k, H j k ∈ R) ∧ (∀ j k, H⁻¹ j k ∈ R) := by
    rw [mem_GLint_iff', hMval, hMinv]
    simp only [Matrix.map_apply, mem_Ov_iff, hv]
  have hbasis : ∀ z, ∃ d : Fin m → K.E, z = ∑ k, d k • v k := by
    intro z
    set P : Matrix (Fin m) (Fin m) K.E := g.val.map e.symm with hPdef
    have hP : IsUnit P.det := by
      have h1 : IsUnit (g.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hd : P.det = e.symm g.val.det := (RingHom.map_det (e.symm : w.adicCompletion E →+* K.E) g.val).symm
      rw [hd]
      exact h1.map _
    refine ⟨P⁻¹ *ᵥ (b.repr z), ?_⟩
    conv_lhs => rw [← b.sum_repr z]
    simp only [hvdef, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have h2 : P *ᵥ (P⁻¹ *ᵥ (b.repr z)) = b.repr z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
    conv_lhs => rw [← h2]
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hPdef, Matrix.map_apply, mul_comm]
  rw [hmemX, hMem]
  exact selfDual_iff B β v hbasis hH

end Unimod

end GlobalTheory.TwLat
