import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.GoodAlmostAll

open GlobalTheory.HL.GoodClass

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]

theorem unitIn_one (O : Subring R) : UnitIn O 1 := ⟨O.one_mem, 1, O.one_mem, one_mul 1⟩

theorem unitIn_pow {O : Subring R} {x : R} (hx : UnitIn O x) (n : ℕ) : UnitIn O (x ^ n) := by
  induction n with
  | zero => simpa using unitIn_one O
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem alg_mem (L : LocE K R) (x : 𝒪[K]) : algebraMap K R (x : K) ∈ L.O :=
  (L.O_def _).2 (isIntegral_algebraMap (R := 𝒪[K]) (x := x))

theorem coe_inv_unit (u : (𝒪[K])ˣ) : (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) = ((u : 𝒪[K]) : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun x : 𝒪[K] => (x : K)) u.inv_mul
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
  exact h

theorem unitIn_alg (L : LocE K R) (u : (𝒪[K])ˣ) : UnitIn L.O (algebraMap K R ((u : 𝒪[K]) : K)) := by
  refine ⟨alg_mem L u, _, alg_mem L ((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]), ?_⟩
  rw [← map_mul]
  have h := congrArg (fun x : 𝒪[K] => (x : K)) u.mul_inv
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
  rw [h, map_one]

theorem hf_smul (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R) (s t : R) (x y : Fin n → R) :
    hf L Hm (s • x) (t • y) = s * L.cj t * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Local

theorem lead_scale {R R' : Type} [CommRing R] [CommRing R'] (ι : R' →+* R) {N : ℕ}
    (Z : Matrix (Fin N) (Fin N) R') (Z' : Matrix (Fin N) (Fin N) R) (β : ℕ → R)
    (h : ∀ a b, Z' a b = β b * β a * ι (Z a b)) (l : Fin (N + 1)) :
    lead Z' l = (∏ i ∈ Finset.range l, β i) ^ 2 * ι (lead Z l) := by
  unfold lead
  set e := Fin.castLE (Nat.lt_succ_iff.mp l.2)
  have h1 : Z'.submatrix e e = Matrix.of fun i j => β (e j) *
      (Matrix.of fun i j => β (e i) * ((Z.submatrix e e).map ι) i j) i j := by
    ext i j
    simp only [Matrix.submatrix_apply, h, Matrix.of_apply, Matrix.map_apply]
    ring
  rw [h1, Matrix.det_mul_row, Matrix.det_mul_column, RingHom.map_det, RingHom.mapMatrix_apply]
  have h2 : ∏ i : Fin l, β (e i) = ∏ i ∈ Finset.range l, β i := by
    rw [← Fin.prod_univ_eq_prod_range]
    rfl
  rw [h2]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

def sc (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp))⁻¹ ^ (r - n))

theorem sc_last : sc G p r = 1 := by simp [sc]

theorem cj_sc (n : ℕ) : (A.L p).cj (sc G p n) = sc G p n := (A.L p).cj.commutes _

theorem cj_ι (x : E) : (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
  rw [A.L_cj, (A.loc p).cj_ιE]

theorem f_scale (a : Fin (r + 1)) : (G.S p).f a = sc G p a • A.bc p (G.f a) := by
  rw [sc, ← G.f_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem f'_scale (a : Fin (r + 1)) : (G.S p).f' a = sc G p a • A.bc p (G.f' a) := by
  rw [sc, ← G.f'_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem herm_bc (x y : Fin (k + 2 * r + 1) → E) :
    hf (A.L p) (G.S p).Hm (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * G.Hm i j * sig (y j)) := by
  rw [G.Hm_eq p]
  exact (RatExt.rational_extend A _ p).2.2.2.2.1 G.Hm x y

theorem Zh_scale (a b : Fin (r + 1)) :
    (G.S p).Zh a b = sc G p b * sc G p a * (A.loc p).ιE (G.Zh a b) := by
  simp only [Frames.Zh, Frames.h, Matrix.of_apply, GFrames.Zh]
  rw [f_scale, f'_scale, hf_smul, cj_sc, herm_bc]

theorem D_scale (l : Fin (r + 2)) :
    (G.S p).D l = (∏ i ∈ Finset.range l, sc G p i) ^ 2 * (A.loc p).ιE (G.D l) :=
  lead_scale (A.loc p).ιE G.Zh (G.S p).Zh (sc G p) (Zh_scale G p) l

theorem TT_eq : algebraMap (A.loc p).Fp (A.loc p).Ep (((G.S p).T : (A.loc p).Fp) * (G.S p).T') =
    (A.loc p).ιE G.TT := by
  have h1 := (G.S p).gram (Fin.last r) (Fin.last r)
  have h2 := (G.S p).gram' (Fin.last r) (Fin.last r)
  simp only [and_self, if_true] at h1 h2
  rw [f_scale, Fin.val_last, sc_last, one_smul, herm_bc] at h1
  rw [f'_scale, Fin.val_last, sc_last, one_smul, herm_bc] at h2
  rw [map_mul, GFrames.TT, map_mul, h1, h2]
  ring

theorem G_scale : (G.S p).G = (∏ i ∈ Finset.range r, sc G p i) ^ 4 * (A.loc p).ιE G.Gr := by
  have hP : ∏ i ∈ Finset.range (r + 1), sc G p i = ∏ i ∈ Finset.range r, sc G p i := by
    rw [Finset.prod_range_succ, sc_last, mul_one]
  have hcj : (A.L p).cj (∏ i ∈ Finset.range r, sc G p i) = ∏ i ∈ Finset.range r, sc G p i := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => cj_sc G p i
  unfold Frames.G
  rw [D_scale, D_scale, TT_eq]
  simp only [Fin.val_last, Fin.coe_castSucc, hP, map_mul, map_pow, hcj, cj_ι, GFrames.Gr, map_sub]
  ring

end GlobalTheory.HL.GoodAlmostAll

namespace GlobalTheory.HL.GoodAlmostAll

open GlobalTheory.HL.GoodClass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

def Ok (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) : Prop :=
  (A.loc p).ιE x ∈ (A.L p).O ∧ (A.loc p).ιE x⁻¹ ∈ (A.L p).O

theorem ok_fin (A : Places F E sig) (x : E) : {p | ¬ Ok A p x}.Finite := by
  refine (((PlacesInt.integers_local A).2.1 x).union ((PlacesInt.integers_local A).2.1 x⁻¹)).subset ?_
  intro p hp
  simp only [Ok, not_and_or, Set.mem_setOf_eq] at hp
  exact hp

theorem unitIn_ok {A : Places F E sig} {p : HeightOneSpectrum (𝓞 F)} {x : E} (h : Ok A p x) (hx : x ≠ 0) :
    UnitIn (A.L p).O ((A.loc p).ιE x) :=
  ⟨h.1, _, h.2, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem unitIn_sc (u : (𝒪[(A.loc p).Fp])ˣ) (hu : ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) (n : ℕ) :
    UnitIn (A.L p).O (sc G p n) := by
  rw [sc, map_pow, ← hu, ← coe_inv_unit]
  exact unitIn_pow (unitIn_alg (A.L p) u⁻¹) _

theorem good_of (hgg : (G.S p).gg = false) (u : (𝒪[(A.loc p).Fp])ˣ)
    (hu : ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p)
    (hHm : ∀ i j, Ok A p (G.Hm i j)) (hdet : Ok A p G.Hm.det)
    (hf : ∀ a i, Ok A p (G.f a i)) (hf' : ∀ a i, Ok A p (G.f' a i))
    (hes : ∀ a i, Ok A p (G.es a i)) (hes' : ∀ a i, Ok A p (G.es' a i))
    (hD : ∀ l, Ok A p (G.D l)) (hGr : Ok A p G.Gr) : Good (G.S p) := by
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  have hc : UnitIn (A.L p).O (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p)) := hu ▸ unitIn_alg (A.L p) u
  have hP : ∀ n, UnitIn (A.L p).O (∏ i ∈ Finset.range n, sc G p i) := fun n =>
    unitIn_prod _ _ _ fun i _ => unitIn_sc G p u hu i
  refine ⟨hgg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [G.Hm_eq p]
    exact (hHm i j).1
  · have hdet' : (G.S p).Hm.det = (A.loc p).ιE G.Hm.det := by
      rw [G.Hm_eq p, RingHom.map_det, RingHom.mapMatrix_apply]
    have hne : G.Hm.det ≠ 0 := by
      intro h0
      have := (G.S p).herm.2
      rw [hdet', h0, map_zero] at this
      exact not_isUnit_zero this
    obtain ⟨-, y, hy, hxy⟩ := unitIn_ok hdet hne
    exact ⟨y, hy, hdet' ▸ hxy⟩
  · intro a i
    rw [f_scale G p a]
    exact (A.L p).O.mul_mem (unitIn_sc G p u hu a).1 (hf a i).1
  · intro a i
    rw [f'_scale G p a]
    exact (A.L p).O.mul_mem (unitIn_sc G p u hu a).1 (hf' a i).1
  · intro a i
    rw [G.es_eq p a]
    exact (A.L p).O.mul_mem (by rw [map_pow]; exact (unitIn_pow hc _).1) (hes a i).1
  · intro a i
    rw [G.es'_eq p a]
    exact (A.L p).O.mul_mem (by rw [map_pow]; exact (unitIn_pow hc _).1) (hes' a i).1
  · have hne : G.Gr ≠ 0 := by
      intro h0
      apply (G.S p).G_ne
      change (G.S p).G = 0
      rw [G_scale, h0, map_zero, mul_zero]
    have := (unitIn_pow (hP r) 4).mul (unitIn_ok hGr hne)
    rw [← G_scale] at this
    exact this
  · intro l hl
    have hne : G.D l ≠ 0 := by
      intro h0
      apply hl
      rw [D_scale, h0, map_zero, mul_zero]
    have := (unitIn_pow (hP l) 2).mul (unitIn_ok (hD l) hne)
    rw [← D_scale] at this
    exact this

end GlobalTheory.HL.GoodAlmostAll

theorem GlobalTheory.HL.StdPlace.good_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), {p | ¬ Good (G.S p)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G
  open GlobalTheory.HL.GoodAlmostAll in
  have H : ({p | (G.S p).gg = true} ∪
      {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p} ∪
      (⋃ i, ⋃ j, {p | ¬ Ok A p (G.Hm i j)}) ∪ {p | ¬ Ok A p G.Hm.det} ∪
      (⋃ a, ⋃ i, {p | ¬ Ok A p (G.f a i)}) ∪ (⋃ a, ⋃ i, {p | ¬ Ok A p (G.f' a i)}) ∪
      (⋃ a, ⋃ i, {p | ¬ Ok A p (G.es a i)}) ∪ (⋃ a, ⋃ i, {p | ¬ Ok A p (G.es' a i)}) ∪
      (⋃ l, {p | ¬ Ok A p (G.D l)}) ∪ {p | ¬ Ok A p G.Gr}).Finite := by
    refine (((((((((G.gg_fin.union G.c_unit).union ?_).union (ok_fin A _)).union ?_).union ?_).union ?_).union
      ?_).union ?_).union (ok_fin A _))
    all_goals first
      | exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => ok_fin A _
      | exact Set.finite_iUnion fun _ => ok_fin A _
  refine H.subset fun p hp => ?_
  by_contra hB
  apply hp
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not,
    Bool.not_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgg, hu⟩, hHm⟩, hdet⟩, hf⟩, hf'⟩, hes⟩, hes'⟩, hD⟩, hGr⟩ := hB
  obtain ⟨u, hu⟩ := not_forall_not.mp hu
  exact GlobalTheory.HL.GoodAlmostAll.good_of G p hgg u hu hHm hdet hf hf' hes hes' hD hGr
