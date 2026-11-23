import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
  (Λ : Set (Fin n → E))

theorem hR_mem_oEv (hSD : IsSDLoc σ J v Λ) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := (hSD y).1 hy x hx

theorem oEv_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) {o : Fv F v ⊗[F] E} (ho : o ∈ OEv (E := E) v)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v (L : Set (Fin n → E))) :
    o • x ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
  unfold latLoc OEv at *
  simp only [SetLike.mem_coe] at ho hx ⊢
  induction ho using Submodule.span_induction with
  | mem o' ho' =>
    obtain ⟨e, -, rfl⟩ := ho'
    induction hx using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨l, hl, rfl⟩ := hx'
      apply Submodule.subset_span
      refine ⟨e • l, L.smul_mem e hl, ?_⟩
      funext i
      show inclR (F := F) (Fv F v) ((e • l) i) =
        inclR (F := F) (Fv F v) (e : E) * inclR (F := F) (Fv F v) (l i)
      rw [← map_mul]
      congr 1
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ r ha

section Alg

variable {R : Type} [CommRing R] [Algebra F R]

def crossM {a : ℕ} (x W : Fin a → Fin n → R ⊗[F] E) : Matrix (Fin a) (Fin a) (R ⊗[F] E) :=
  fun i j => hR R σ J (x i) (W j) + hR R σ J (W i) (x j)

theorem hR_add_left (x x' y : Fin n → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  unfold hR
  simp only [Formalism.UG.hform]
  simp [Finset.sum_add_distrib, add_mul, mul_add, map_add, Pi.add_apply, Matrix.mulVec_add,
    Matrix.add_mulVec, dotProduct_add, add_dotProduct]

theorem hR_add_right (x y y' : Fin n → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  unfold hR
  simp only [Formalism.UG.hform]
  simp [Finset.sum_add_distrib, add_mul, mul_add, map_add, Pi.add_apply, Matrix.mulVec_add,
    Matrix.add_mulVec, dotProduct_add, add_dotProduct]

theorem gramR_add {a : ℕ} (x W : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (x + W) = gramR R σ J x + crossM σ J x W + gramR R σ J W := by
  ext i j
  first
  | (simp only [gramR, crossM, Matrix.add_apply, Pi.add_apply, Matrix.of_apply, hR_add_left, hR_add_right]; abel)
  | (simp [gramR, crossM, hR_add_left, hR_add_right]; abel)

theorem crossM_add_left {a : ℕ} (x x' W : Fin a → Fin n → R ⊗[F] E) :
    crossM σ J (x + x') W = crossM σ J x W + crossM σ J x' W := by
  ext i j
  simp only [crossM, Matrix.add_apply, Pi.add_apply, hR_add_left, hR_add_right]
  abel

theorem gram_rem {a : ℕ} (y Z W : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (y + Z + W) - gramR R σ J (y + Z) -
        (gramR R σ J (y + W) - gramR R σ J y - gramR R σ J W) =
      crossM σ J Z W + gramR R σ J W := by
  rw [gramR_add σ J (y + Z) W, gramR_add σ J y W, crossM_add_left]
  abel

end Alg

section Rem

theorem sigR_sc (r : Fv F v) : sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r := by
  first
  | (simp [sigR, sc]; done)
  | (unfold sigR sc; done)

theorem hR_smul_smul (r t : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (r • x) (t • y) = sc (E := E) v (r * t) * hR (Fv F v) σ J x y := by
  have hs : ∀ u : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = sc (E := E) v u := fun u => rfl
  have hm : sc (E := E) v (r * t) = sc (E := E) v r * sc (E := E) v t := by
    rw [← hs, ← hs, ← hs, map_mul]
  unfold hR
  simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, hs, sigR_sc, hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sc_mul_mem_oEv {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {o : Fv F v ⊗[F] E}
    (ho : o ∈ OEv (E := E) v) : sc (E := E) v r * o ∈ OEv (E := E) v := by
  unfold OEv at ho ⊢
  have h : sc (E := E) v r * o = (⟨r, hr⟩ : v.adicCompletionIntegers F) • o := by
    first
    | (rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (v.adicCompletionIntegers F) (Fv F v)
        (Fv F v ⊗[F] E)]; rfl)
    | (rw [Algebra.smul_def]; rfl)
    | rfl
  rw [h]
  exact Submodule.smul_mem _ _ ho

theorem mem_hN (ϖ : Fv F v) (h0 : ϖ ≠ 0) (a k : ℕ) (z : HermR (Fv F v) σ a) :
    z ∈ hN σ v ϖ a k ↔ ∀ i j, ∃ c ∈ OEv (E := E) v,
      (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sc (E := E) v (ϖ ^ (k + 1)) * c := by
  have ht : ϖ ^ (k + 1) ≠ 0 := pow_ne_zero _ h0
  unfold hN PI.VolStabSW.smulSub
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩ i j
    refine ⟨(w : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hw i j, ?_⟩
    show ((ϖ ^ (k + 1)) • (w : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) i j = _
    rw [Matrix.smul_apply, Algebra.smul_def]
    rfl
  · intro h
    choose c hc hzc using h
    refine ⟨(ϖ ^ (k + 1))⁻¹ • z, ?_, ?_⟩
    · intro i j
      show ((ϖ ^ (k + 1))⁻¹ • (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) i j ∈ OEv (E := E) v
      rw [Matrix.smul_apply, hzc i j, Algebra.smul_def, ← mul_assoc]
      have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ ^ (k + 1))⁻¹ * sc (E := E) v (ϖ ^ (k + 1)) = 1 := by
        show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ ^ (k + 1))⁻¹ *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ ^ (k + 1)) = 1
        rw [← map_mul, inv_mul_cancel₀ ht, map_one]
      rw [e, one_mul]
      exact hc i j
    · show (ϖ ^ (k + 1)) • ((ϖ ^ (k + 1))⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem rem_mem (hSD : IsSDLoc σ J v Λ) (ϖ : Fv F v) (h0 : ϖ ≠ 0)
    (hint : ϖ ∈ v.adicCompletionIntegers F) {a k : ℕ} {Z W : TupV (E := E) v n a}
    (hZ : Z ∈ lamN v Λ ϖ a 0) (hW : W ∈ lamN v Λ ϖ a k) (z : HermR (Fv F v) σ a)
    (hz : (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = crossM σ J Z W + gramR (Fv F v) σ J W) :
    z ∈ hN σ v ϖ a (k + 1) := by
  unfold lamN PI.VolStabSW.smulSub at hZ hW
  obtain ⟨Z', hZ', rfl⟩ := AddSubgroup.mem_map.1 hZ
  obtain ⟨W', hW', rfl⟩ := AddSubgroup.mem_map.1 hW
  rw [mem_hN σ v ϖ h0]
  intro i j
  have hm : ∀ r t : Fv F v, sc (E := E) v (r * t) = sc (E := E) v r * sc (E := E) v t := by
    intro r t
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r * t) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) r * algebraMap (Fv F v) (Fv F v ⊗[F] E) t
    exact map_mul _ _ _
  refine ⟨hR (Fv F v) σ J (Z' i) (W' j) + hR (Fv F v) σ J (W' i) (Z' j) +
      sc (E := E) v (ϖ ^ k) * hR (Fv F v) σ J (W' i) (W' j),
    oEv_add v (oEv_add v (hR_mem_oEv σ J v Λ hSD (hZ' i) (hW' j)) (hR_mem_oEv σ J v Λ hSD (hW' i) (hZ' j)))
      (sc_mul_mem_oEv v (pow_mem hint k) (hR_mem_oEv σ J v Λ hSD (hW' i) (hW' j))), ?_⟩
  rw [hz]
  show hR (Fv F v) σ J ((ϖ ^ (0 + 1)) • Z' i) ((ϖ ^ (k + 1)) • W' j) +
      hR (Fv F v) σ J ((ϖ ^ (k + 1)) • W' i) ((ϖ ^ (0 + 1)) • Z' j) +
      hR (Fv F v) σ J ((ϖ ^ (k + 1)) • W' i) ((ϖ ^ (k + 1)) • W' j) = _
  rw [hR_smul_smul, hR_smul_smul, hR_smul_smul]
  have e1 : ϖ ^ (0 + 1) * ϖ ^ (k + 1) = ϖ ^ (k + 1 + 1) := by ring
  have e2 : ϖ ^ (k + 1) * ϖ ^ (0 + 1) = ϖ ^ (k + 1 + 1) := by ring
  have e3 : ϖ ^ (k + 1) * ϖ ^ (k + 1) = ϖ ^ (k + 1 + 1) * ϖ ^ k := by ring
  rw [e1, e2, e3, hm]
  ring

end Rem

section D

theorem crossM_add_right {R : Type} [CommRing R] [Algebra F R] {a : ℕ} (x W W' : Fin a → Fin n → R ⊗[F] E) :
    crossM σ J x (W + W') = crossM σ J x W + crossM σ J x W' := by
  ext i j
  simp only [crossM, Matrix.add_apply, Pi.add_apply, hR_add_left, hR_add_right]
  abel

theorem crossM_zero_right {R : Type} [CommRing R] [Algebra F R] {a : ℕ} (x : Fin a → Fin n → R ⊗[F] E) :
    crossM σ J x 0 = 0 := by
  have h0 : ∀ u : Fin n → R ⊗[F] E, hR R σ J u 0 = 0 := by
    intro u
    have h := hR_add_right σ J u 0 0
    rw [add_zero] at h
    linear_combination -h
  have h0' : ∀ u : Fin n → R ⊗[F] E, hR R σ J 0 u = 0 := by
    intro u
    have h := hR_add_left σ J 0 0 u
    rw [add_zero] at h
    linear_combination -h
  ext i j
  simp only [crossM, Pi.zero_apply, Matrix.zero_apply, h0, h0', add_zero]

theorem crossM_smul_right {a : ℕ} (t : Fv F v) (x W : TupV (E := E) v n a) (i j : Fin a) :
    crossM σ J x (t • W) i j = sc (E := E) v t * crossM σ J x W i j := by
  simp only [crossM, Pi.smul_apply]
  have h1 := hR_smul_smul σ J v 1 t (x i) (W j)
  have h2 := hR_smul_smul σ J v t 1 (W i) (x j)
  rw [one_smul, one_mul] at h1
  rw [one_smul, mul_one] at h2
  rw [h1, h2, mul_add]

variable (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)

def dH {a : ℕ} (y : TupV (E := E) v n a) : TupV (E := E) v n a →+ HermR (Fv F v) σ a where
  toFun W := PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + W) - PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
    PI.VolStabSW.gramH (Fv F v) σ hσ J hJ W
  map_zero' := by
    apply Subtype.ext
    show gramR (Fv F v) σ J (y + 0) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J 0 = 0
    rw [gramR_add, crossM_zero_right]
    abel
  map_add' W W' := by
    apply Subtype.ext
    show gramR (Fv F v) σ J (y + (W + W')) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J (W + W') =
      (gramR (Fv F v) σ J (y + W) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W) +
      (gramR (Fv F v) σ J (y + W') - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W')
    rw [gramR_add σ J y (W + W'), gramR_add σ J y W, gramR_add σ J y W', crossM_add_right]
    abel

theorem coe_dH {a : ℕ} (y W : TupV (E := E) v n a) :
    ((dH σ J v hσ hJ y W : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      crossM σ J y W := by
  show gramR (Fv F v) σ J (y + W) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W = crossM σ J y W
  rw [gramR_add]
  abel

end D

section Hens

variable (ψ : AddChar (AF F) ℂ)

def HensOnto (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ y ∈ LamT v Λ a,
    (∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ) →
    ∀ S : HermR (Fv F v) σ a, S ∈ hermOE σ v a →
      ∃ W0 ∈ LamT v Λ a, crossM σ J y W0 = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))

theorem fibHens_of (a : ℕ) (Y : TupV (E := E) v n a) (h : HensOnto σ J v Λ ψ a Y) :
    FibHens σ J ψ v Λ a Y := by
  intro hG ϖ hϖ hσ hJ y hy hyY
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro hz
    unfold IsUnif at hϖ
    rw [hz, Valuation.map_zero] at hϖ
    exact WithZero.coe_ne_zero hϖ.symm
  have hint : ϖ ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    unfold IsUnif at hϖ
    rw [hϖ]
    first
    | (exact WithZero.coe_le_one.2 (by decide))
    | decide
    | simp
    | (norm_num [← WithZero.coe_one])
  have hPO : ∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ := by
    intro i j
    obtain ⟨c, hc, e⟩ := (mem_hN σ v ϖ h0 a 0 _).1 hyY i j
    refine ⟨c, hc, ?_⟩
    rw [zero_add, pow_one] at e
    exact e
  refine ⟨dH σ J v hσ hJ y, fun k => ?_, fun k Z hZ W hW => ?_⟩
  · ext S
    constructor
    · rintro ⟨W, hW, rfl⟩
      unfold lamN PI.VolStabSW.smulSub at hW
      obtain ⟨W', hW', rfl⟩ := AddSubgroup.mem_map.1 hW
      rw [mem_hN σ v ϖ h0]
      intro i j
      refine ⟨crossM σ J y W' i j, oEv_add v (hR_mem_oEv σ J v Λ hSD (hy i) (hW' j))
        (hR_mem_oEv σ J v Λ hSD (hW' i) (hy j)), ?_⟩
      rw [coe_dH]
      exact crossM_smul_right σ J v _ y W' i j
    · intro hS
      unfold hN PI.VolStabSW.smulSub at hS
      obtain ⟨S', hS', rfl⟩ := AddSubgroup.mem_map.1 hS
      obtain ⟨W0, hW0, hW0e⟩ := h hG ϖ hϖ y hy hPO S' hS'
      refine AddSubgroup.mem_map.2 ⟨(ϖ ^ (k + 1)) • W0, ?_, ?_⟩
      · unfold lamN PI.VolStabSW.smulSub
        exact AddSubgroup.mem_map.2 ⟨W0, hW0, rfl⟩
      · apply Subtype.ext
        ext i j
        rw [coe_dH]
        show crossM σ J y ((ϖ ^ (k + 1)) • W0) i j =
          ((ϖ ^ (k + 1)) • (S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) i j
        rw [crossM_smul_right, hW0e, Matrix.smul_apply, Algebra.smul_def]
        rfl
  · refine rem_mem σ J v Λ hSD ϖ h0 hint hZ hW _ ?_
    show gramR (Fv F v) σ J (y + Z + W) - gramR (Fv F v) σ J (y + Z) -
      ((dH σ J v hσ hJ y W : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = _
    rw [coe_dH, gramR_add σ J (y + Z) W, crossM_add_left]
    abel

end Hens

end PI.OmLocU
