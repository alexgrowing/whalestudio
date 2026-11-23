import ReciprocityTheory.DualLattices.TensorSpan
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem hopfOrder_exists_algebraMap_eq_of_mem (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (x : N) :
    ∃ r : R, algebraMap R C r = f x := by
  exact AA.le_int hf x

theorem hopfOrder_translate_mem (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (y : N) :
    (fun x => f (x + y)) ∈ AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      AA.carrier.comap (LinearMap.funLeft R C (fun x : N => (x, y))) := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := AA.le_int hh y
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : LinearMap.funLeft R C (fun x : N => (x, y)) (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x; simp [Algebra.smul_def, hr, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)

theorem coset_functional_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (φ : (K → C) →ₗ[C] C)
    (hφ : ∀ h ∈ AA.carrier.map (resK (R := R) K), ∃ r : R, algebraMap R C r = φ h)
    {f : N → C} (hf : f ∈ AA.carrier) :
    (fun x => φ (fun k : K => f (x + k))) ∈ AA.carrier := by
  let φR := φ.restrictScalars R
  let Ψ : (N × N → C) →ₗ[R] (N → C) :=
    (φR.compLeft N) ∘ₗ (LinearEquiv.curry R C N K).toLinearMap ∘ₗ
      LinearMap.funLeft R C (fun p : N × K => (p.1, (p.2 : N)))
  have key : tensorSpan R AA.carrier ≤ AA.carrier.comap Ψ := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := hφ (resK (R := R) K h) (Submodule.mem_map_of_mem hh)
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : Ψ (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x
      have : (fun k : K => g x * h k) = g x • resK (R := R) K h := by
        ext k; simp [resK]
      simp only [Ψ, φR, LinearMap.coe_comp, Function.comp_apply, LinearMap.compLeft_apply,
        LinearEquiv.coe_coe, LinearMap.restrictScalars_apply]
      show φ (fun k : K => g x * h k) = (r • g) x
      rw [this, φ.map_smul, ← hr]
      simp [Algebra.smul_def, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)

def h3co (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : N → C) (x : N) : K → C :=
  β⁻¹ *ᵥ fun k : K => f (x + k)

theorem cosetCoordinates_expand (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : N → C)
    (x : N) (k : K) : f (x + k) = ∑ l, β k l * h3co K β f x l := by
  have e : β *ᵥ (β⁻¹ *ᵥ fun k' : K => f (x + k')) = fun k' : K => f (x + k') := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hβ, Matrix.one_mulVec]
  exact (congrFun e k).symm

theorem exists_algebraMap_eq_inv_mulVec (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {h : K → C} (hh : h ∈ AA.carrier.map (resK (R := R) K)) (l : K) :
    ∃ r : R, algebraMap R C r = (β⁻¹ *ᵥ h) l := by
  rw [hAK] at hh
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    have e : β⁻¹ *ᵥ (fun k => β k j) = Pi.single j 1 := by
      ext l'
      have := congrFun (congrFun (Matrix.nonsing_inv_mul β hβ) l') j
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    rw [e]
    by_cases hl : l = j
    · exact ⟨1, by simp [hl]⟩
    · exact ⟨0, by simp [hl]⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨s, hs⟩ := hb
    exact ⟨r + s, by simp [Matrix.mulVec_add, hr, hs]⟩
  | smul c a _ ha =>
    obtain ⟨r, hr⟩ := ha
    exact ⟨c * r, by rw [Matrix.mulVec_smul]; simp [hr, Algebra.smul_def]⟩

theorem cosetCoordinates_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {f : N → C} (hf : f ∈ AA.carrier) (l : K) :
    (fun x => h3co K β f x l) ∈ AA.carrier := by
  exact coset_functional_mem AA K ((LinearMap.proj l).comp (Matrix.mulVecLin β⁻¹))
    (fun h hh => exists_algebraMap_eq_inv_mulVec AA K β hβ hAK hh l) hf

def h3T (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (k : K) : Matrix K K C :=
  Matrix.of fun l l' => (β⁻¹ *ᵥ fun k' : K => β (k + k') l) l'

theorem cosetCoordinates_add (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : N → C)
    (x : N) (k : K) : h3co K β f (x + k) = h3co K β f x ᵥ* h3T K β k := by
  ext l'
  have hw : (fun k' : K => f (x + k + k')) =
      ∑ l, h3co K β f x l • (fun k' : K => β (k + k') l) := by
    ext k'
    rw [show (x + (k : N) + (k' : N)) = x + ((k + k' : K) : N) by simp [add_assoc],
      cosetCoordinates_expand K β hβ f x (k + k')]
    simp [Finset.sum_apply, mul_comm]
  show (β⁻¹ *ᵥ fun k' : K => f (x + k + k')) l' = _
  rw [hw, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul,
    dotProduct, h3T, Matrix.of_apply]

theorem valuation_det_le_one_of_entries_integral (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X C) (hM : ∀ i j, ∃ r : R, algebraMap R C r = M i j) : v M.det ≤ 1 := by
  choose Mr hMr using hM
  have e : M = (algebraMap R C).mapMatrix (Matrix.of Mr) := by
    ext i j; simp [hMr]
  rw [e, ← RingHom.map_det]
  exact hv.map_le_one _

def h3mm (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : K → N → C) (x : N) : Matrix K K C :=
  Matrix.of fun j l => h3co K β (f j) x l

theorem cosetCoordinateMatrix_add (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : K → N → C)
    (x : N) (k : K) : h3mm K β f (x + k) = h3mm K β f x * h3T K β k := by
  ext j l'
  simp only [h3mm, Matrix.of_apply, Matrix.mul_apply]
  rw [cosetCoordinates_add K β hβ (f j) x k]
  simp [Matrix.vecMul, dotProduct]

theorem valuation_det_cosetCoordinateMatrix_add (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    (f : K → N → C) (x : N) (k : K) :
    v (h3mm K β f (x + k)).det = v (h3mm K β f x).det := by
  rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, map_mul]
  suffices h : v (h3T K β k).det = 1 by rw [h, mul_one]
  have hT : h3T K β k = (β⁻¹ * β.submatrix (Equiv.addLeft k) id)ᵀ := by
    ext l l'
    simp [h3T, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hT, Matrix.det_transpose, Matrix.det_mul, Matrix.det_permute, Matrix.det_nonsing_inv]
  have hd : β.det ≠ 0 := hβ.ne_zero
  have hs : v ((Equiv.Perm.sign (Equiv.addLeft k) : ℤ) : C) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.addLeft k)) with h | h <;>
      simp [h, Valuation.map_neg]
  rw [Ring.inverse_eq_inv', map_mul, map_mul, hs, one_mul, map_inv₀, inv_mul_cancel₀]
  exact (Valuation.ne_zero_iff v).mpr hd

def hopfOrderSubgroup (AA : HopfOrder (C := C) R N) : Subring (N → C) where
  carrier := AA.carrier
  mul_mem' := fun ha hb => AA.mul_mem _ _ ha hb
  one_mem' := AA.one_mem
  add_mem' := fun ha hb => AA.carrier.add_mem ha hb
  zero_mem' := AA.carrier.zero_mem
  neg_mem' := fun ha => AA.carrier.neg_mem ha

theorem det_mem_and_adjugate_mem (AA : HopfOrder (C := C) R N) {X : Type} [Fintype X] [DecidableEq X]
    (F : Matrix X X (N → C)) (hF : ∀ i j, F i j ∈ AA.carrier) :
    (fun x => (F.map fun g => g x).det) ∈ AA.carrier ∧
      ∀ i j, (fun x => (F.map fun g => g x).adjugate i j) ∈ AA.carrier := by
  let F' : Matrix X X (hopfOrderSubgroup AA) := Matrix.of fun i j => ⟨F i j, hF i j⟩
  have hF' : F = (hopfOrderSubgroup AA).subtype.mapMatrix F' := Matrix.ext fun i j => rfl
  refine ⟨?_, fun i j => ?_⟩
  · have e : (fun x => (F.map fun g => g x).det) = F.det := by
      funext x
      exact ((Pi.evalRingHom (fun _ : N => C) x).map_det F).symm
    rw [e, hF', ← RingHom.map_det]
    exact (F'.det).2
  · have e : (fun x => (F.map fun g => g x).adjugate i j) = F.adjugate i j := by
      funext x
      have := (Pi.evalRingHom (fun _ : N => C) x).map_adjugate F
      exact (congrFun (congrFun this i) j).symm
    rw [e, hF', ← RingHom.map_adjugate]
    exact (F'.adjugate i j).2

theorem cosetCoordinates_pullbackQuotient_mul (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (e : N ⧸ K → C) (f : N → C)
    (x : N) : h3co K β (pullQ (R := R) K e * f) x = e (x : N ⧸ K) • h3co K β f x := by
  have hE : (fun k : K => (pullQ (R := R) K e * f) (x + k)) =
      e (x : N ⧸ K) • fun k : K => f (x + k) := by
    ext k
    show e ((x + k : N) : N ⧸ K) * f (x + k) = e (x : N ⧸ K) * f (x + k)
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]
  show β⁻¹ *ᵥ (fun k : K => (pullQ (R := R) K e * f) (x + k)) = _
  rw [hE, Matrix.mulVec_smul]
  rfl

end ReciprocityTheory.PGsh.L2
