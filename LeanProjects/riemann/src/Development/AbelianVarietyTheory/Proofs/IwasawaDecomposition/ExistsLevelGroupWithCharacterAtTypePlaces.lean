import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevGChar

section Reformulated
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_int (s : SplitPlace L) {z : AL L} (hz : z ∈ ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have key : ALint L ≤ ((s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring).comap s.proj := by
    rw [ALint, Subring.closure_le]
    rintro y (⟨o, rfl⟩ | ⟨a, ha, rfl⟩)
    · show s.proj _ ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring
      have e : s.proj ((o : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) = s.i (o : L) := by
        simp [SplitPlace.proj]
      rw [e]
      exact s.split_le_one o
    · show s.proj _ ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring
      have e : s.proj ((1 : L) ⊗ₜ[maximalRealSubfield L] a) = a s.v := by
        simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one,
          one_mul]
        rfl
      rw [e]
      exact ha s.v
  exact key hz

theorem locM_int (s : SplitPlace L) {κ : GAf L n} (h : κ ∈ Umax L n) (a b : Fin n) :
    NX.locM s κ a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := proj_int s (h a b)

theorem locM_mul (s : SplitPlace L) (κ κ' : GAf L n) : NX.locM s (κ * κ') = NX.locM s κ * NX.locM s κ' := by
  simp only [NX.locM, map_mul, Units.val_mul]

theorem locM_one (s : SplitPlace L) : NX.locM s (1 : GAf L n) = 1 := by
  simp only [NX.locM, map_one, Units.val_one]

theorem proj_eq_lift (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem locM_triv (s : SplitPlace L) {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {κ : GAf L n}
    (h : TrivOutside Bᶜ κ) (hv : s.v ∈ B) : NX.locM s κ = 1 := by
  have hc := h s.v (fun h' => h' hv)
  refine Matrix.ext fun a b => ?_
  have e := congrFun (congrFun hc a) b
  simp only [Matrix.map_apply] at e
  change s.proj ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) = _
  rw [proj_eq_lift, e]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

theorem natCast_lt {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {N : ℕ}
    (hN : (N : 𝓞 (maximalRealSubfield L)) ∈ v.asIdeal) : Valued.v ((N : v.adicCompletion (maximalRealSubfield L))) < 1 := by
  have e : ((N : ℕ) : v.adicCompletion (maximalRealSubfield L)) =
      ((algebraMap (𝓞 (maximalRealSubfield L)) (v.adicCompletionIntegers (maximalRealSubfield L)) (N : 𝓞 (maximalRealSubfield L)) : v.adicCompletionIntegers (maximalRealSubfield L)) : v.adicCompletion (maximalRealSubfield L)) := by
    rw [map_natCast]
    simp
  rw [e, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_lt_one_iff_mem (K := maximalRealSubfield L) _).2 hN

theorem locM_cong (s : SplitPlace L) {N : ℕ} (hN : (N : 𝓞 (maximalRealSubfield L)) ∈ s.v.asIdeal) (κ : GAf L n)
    (hκ : NG.Cong L n N κ) (a b : Fin n) :
    Valued.v (NX.locM s κ a b - (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
  obtain ⟨y, hy, e⟩ := hκ.2 a b
  have h1 : NX.locM s κ a b - (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b =
      s.proj ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) := by
    rw [map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, e, map_mul, map_natCast, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_int s hy)))
    (natCast_lt hN)

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}

theorem int_of_cong {z c : v.adicCompletion (maximalRealSubfield L)} (hc : Valued.v c ≤ 1) (h : Valued.v (z - c) < 1) :
    z ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : z = (z - c) + c := by ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le h.le hc)

theorem red_intLift {R : Type} [CommRing R] (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L), Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) {z : v.adicCompletion (maximalRealSubfield L)} (c : v.adicCompletionIntegers (maximalRealSubfield L))
    (h : Valued.v (z - (c : v.adicCompletion (maximalRealSubfield L))) < 1) : red (NX.intLift v z) = red c := by
  have hz : z ∈ v.adicCompletionIntegers (maximalRealSubfield L) := int_of_cong ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2) h
  rw [NX.intLift, dif_pos hz]
  have h0 : red (⟨z, hz⟩ - c) = 0 := hred _ (by simpa using h)
  rwa [map_sub, sub_eq_zero] at h0

theorem levG_of_cong (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (h : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) : NX.InLevG v r x := by
  have hoff : ∀ a b, a ≠ b → Valued.v (x a b) < 1 := fun a b hab => by simpa [Matrix.one_apply_ne hab] using h a b
  refine ⟨⟨fun a b => int_of_cong (c := (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) ?_ (h a b), fun a b ha hb => hoff a b ?_⟩,
    fun a b _ _ => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
  · by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro e; subst e; omega
  · intro e; subst e; exact lt_irrefl _ hba
  · subst hab; simpa using h a a

theorem isUnit_int {z : v.adicCompletion (maximalRealSubfield L)} (hz : Valued.v z = 1) (hi : z ∈ v.adicCompletionIntegers (maximalRealSubfield L)) : IsUnit (⟨z, hi⟩ : v.adicCompletionIntegers (maximalRealSubfield L)) := by
  have h0 : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
  have hi' : z⁻¹ ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hz, inv_one]
  exact ⟨⟨⟨z, hi⟩, ⟨z⁻¹, hi'⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem glOf_mul {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M N : Matrix ι ι R) (hM : IsUnit M.det)
    (hN : IsUnit N.det) : NX.glOf (M * N) = NX.glOf M * NX.glOf N := by
  apply Units.ext
  rw [Units.val_mul, NX.glOf_val _ (by rw [Matrix.det_mul]; exact hM.mul hN), NX.glOf_val _ hM, NX.glOf_val _ hN]

theorem det_uniTri {r : ℕ} {R : Type} [CommRing R] {M : Matrix (Fin r) (Fin r) R} (h : NX.IsUniTri r M) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular h.1]
  simp [h.2]

theorem uniTri_red {R : Type} [CommRing R] {r : ℕ} (hr : r ≤ n) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L), Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : NX.InLevG v r x) :
    NX.IsUniTri r (NX.redMat v red (NX.topR hr x)) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show red (NX.intLift v (x (Fin.castLE hr a) (Fin.castLE hr b))) = 0
    have hlt : Fin.castLE hr b < Fin.castLE hr a := by rw [Fin.lt_def] at hab ⊢; exact hab
    rw [red_intLift red hred 0 (by simpa using (hx.2 (Fin.castLE hr a) (Fin.castLE hr b) a.2 b.2).1 hlt), map_zero]
  · show red (NX.intLift v (x (Fin.castLE hr a) (Fin.castLE hr a))) = 1
    rw [red_intLift red hred 1 (by simpa using (hx.2 (Fin.castLE hr a) (Fin.castLE hr a) a.2 a.2).2 rfl), map_one]

theorem redMat_one {R : Type} [CommRing R] {r : ℕ} (hr : r ≤ n) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L), Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) : NX.redMat v red (NX.topR hr x) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v (x (Fin.castLE hr a) (Fin.castLE hr b))) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, red_intLift red hred 1 (by simpa using hx (Fin.castLE hr a) (Fin.castLE hr a)), map_one]
  · have hab' : Fin.castLE hr a ≠ Fin.castLE hr b := fun e => hab (Fin.castLE_injective hr e)
    rw [Matrix.one_apply_ne hab, red_intLift red hred 0
      (by simpa [Matrix.one_apply_ne hab'] using hx (Fin.castLE hr a) (Fin.castLE hr b)), map_zero]

end Reformulated

section Res
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}

def intM (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) : Matrix (Fin n) (Fin n) ↥(v.adicCompletionIntegers (maximalRealSubfield L)) := fun a b => ⟨x a b, hx a b⟩

theorem intM_map (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) : (intM x hx).map (v.adicCompletionIntegers (maximalRealSubfield L)).subtype = x := rfl

theorem int_mul {x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (hy : ∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ∀ a b, (x * y) a b ∈ v.adicCompletionIntegers (maximalRealSubfield L) := fun a b => by
  have e : x * y = (intM x hx * intM y hy).map (v.adicCompletionIntegers (maximalRealSubfield L)).subtype := by rw [Matrix.map_mul, intM_map, intM_map]
  rw [e]
  exact ((intM x hx * intM y hy) a b).2

theorem intM_mul {x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (hy : ∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    intM (x * y) (int_mul hx hy) = intM x hx * intM y hy := by
  refine Matrix.map_injective (f := (v.adicCompletionIntegers (maximalRealSubfield L)).subtype) Subtype.val_injective ?_
  beta_reduce
  rw [Matrix.map_mul, intM_map, intM_map, intM_map]

theorem res_zero (z : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L)) z = 0 ↔ Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))))

theorem res_one (z : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L)) z = 1 ↔ Valued.v ((z : v.adicCompletion (maximalRealSubfield L)) - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L))), ← map_sub, res_zero]
  simp

def resM (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField ↥(v.adicCompletionIntegers (maximalRealSubfield L))) := (intM x hx).map (IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L)))

theorem resM_mul {x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (hy : ∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    resM (x * y) (int_mul hx hy) = resM x hx * resM y hy := by
  rw [resM, intM_mul, Matrix.map_mul]; rfl

theorem resM_zero {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (a b : Fin n) :
    resM x hx a b = 0 ↔ Valued.v (x a b) < 1 := res_zero _

theorem resM_one {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (a b : Fin n) :
    resM x hx a b = 1 ↔ Valued.v (x a b - 1) < 1 := res_one _

def bP (r : ℕ) (a : Fin n) : ℕ := if r ≤ (a : ℕ) then 1 else 0

def bG (r : ℕ) (a : Fin n) : ℕ := if (a : ℕ) < r then (a : ℕ) else r

theorem bt_parah {r : ℕ} {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : NX.InParah v r x) : (resM x hx.1).BlockTriangular (bP r) := by
  intro a b hab
  by_cases ha : r ≤ (a : ℕ) <;> by_cases hb : r ≤ (b : ℕ) <;> simp [bP, ha, hb] at hab
  exact (resM_zero hx.1 a b).2 (hx.2 a b ha (by omega))

theorem parah_of_bt {r : ℕ} {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (h : (resM x hx).BlockTriangular (bP r)) :
    NX.InParah v r x :=
  ⟨hx, fun a b ha hb => (resM_zero hx a b).1 (h (by simp only [bP]; rw [if_pos ha, if_neg (by omega)]; omega))⟩

theorem bt_levG {r : ℕ} {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : NX.InLevG v r x) : (resM x hx.1.1).BlockTriangular (bG r) := by
  intro a b hab
  refine (resM_zero hx.1.1 a b).2 ?_
  by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp only [bG, ha, hb, if_true, if_false] at hab
  · exact (hx.2 a b ha hb).1 (by rw [Fin.lt_def]; exact hab)
  · omega
  · exact hx.1.2 a b (by omega) hb
  · omega

theorem levG_top_of_bt {r : ℕ} {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) (h : (resM x hx).BlockTriangular (bG r))
    (hd : ∀ a : Fin n, (a : ℕ) < r → resM x hx a a = 1) :
    ∀ a b : Fin n, (a : ℕ) < r → (b : ℕ) < r → (b < a → Valued.v (x a b) < 1) ∧ (a = b → Valued.v (x a b - 1) < 1) :=
  fun a b ha hb => ⟨fun hba => (resM_zero hx a b).1 (h (by simp only [bG]; rw [if_pos ha, if_pos hb]; exact hba)),
    fun hab => by subst hab; exact (resM_one hx a a).1 (hd a ha)⟩

theorem diag_mul {r : ℕ} {K : Type} [CommRing K] {M N : Matrix (Fin n) (Fin n) K} (hM : M.BlockTriangular (bG r))
    (hN : N.BlockTriangular (bG r)) (a : Fin n) (ha : (a : ℕ) < r) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)
  rcases lt_trichotomy (bG r c) (bG r a) with h | h | h
  · rw [hM h, zero_mul]
  · exfalso
    simp only [bG] at h
    split_ifs at h with h1 h2 <;> first | omega | exact hc (Fin.ext h)
  · rw [hN h, mul_zero]

end Res

section ResProofs
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem resM_one_of {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))} (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L))
    (h : x = 1) : resM x hx = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    exact (resM_one hx a a).2 (by simp)
  · rw [Matrix.one_apply_ne hab]
    exact (resM_zero hx a b).2 (by simp [Matrix.one_apply_ne hab])

theorem lr_mul {K : Type} [CommRing K] {r : ℕ} {M N : Matrix (Fin n) (Fin n) K} (hM : M.BlockTriangular (bP r)) :
    (M * N).submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) =
      M.submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) *
        N.submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun c : Fin n => r ≤ (c : ℕ))]
  have hz : ∑ c : {c : Fin n // ¬ r ≤ (c : ℕ)}, M a.1 c.1 * N c.1 b.1 = 0 := Finset.sum_eq_zero fun c _ => by
    rw [hM (by simp only [bP]; rw [if_pos a.2, if_neg c.2]; omega), zero_mul]
  rw [hz, add_zero]

theorem detT_mul_of {K : Type} [CommRing K] {r : ℕ} {M N : Matrix (Fin n) (Fin n) K} (hM : M.BlockTriangular (bP r)) :
    NX.detT r (M * N) = NX.detT r M * NX.detT r N := by
  unfold NX.detT
  rw [lr_mul hM, Matrix.det_mul]

theorem detT_one' {K : Type} [CommRing K] (r : ℕ) : NX.detT r (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold NX.detT
  rw [Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}

theorem detT_coe (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((NX.detT r (intM x hx) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) = NX.detT r x :=
  RingHom.map_det (v.adicCompletionIntegers (maximalRealSubfield L)).subtype _

theorem detT_res (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L)) (NX.detT r (intM x hx)) = NX.detT r (resM x hx) :=
  RingHom.map_det _ _

theorem i_parah_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    NX.InParah v r x → NX.InParah v r y → NX.InParah v r (x * y) := by
  intro hx hy
  refine parah_of_bt (int_mul hx.1 hy.1) ?_
  rw [resM_mul hx.1 hy.1]
  exact (bt_parah hx).mul (bt_parah hy)

theorem i_levG_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    NX.InLevG v r x → NX.InLevG v r y → ∀ a b : Fin n, (a : ℕ) < r → (b : ℕ) < r →
      (b < a → Valued.v ((x * y) a b) < 1) ∧ (a = b → Valued.v ((x * y) a b - 1) < 1) := by
  intro hx hy
  refine levG_top_of_bt (int_mul hx.1.1 hy.1.1) ?_ ?_
  · rw [resM_mul hx.1.1 hy.1.1]; exact (bt_levG hx).mul (bt_levG hy)
  · intro a ha
    rw [resM_mul hx.1.1 hy.1.1, diag_mul (bt_levG hx) (bt_levG hy) a ha, (resM_one _ a a).2 ((hx.2 a a ha ha).2 rfl),
      (resM_one _ a a).2 ((hy.2 a a ha ha).2 rfl), one_mul]

theorem i_parah_inv (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    x * y = 1 → (∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) → NX.InParah v r x → NX.InParah v r y := by
  intro hxy hy hx
  refine parah_of_bt hy ?_
  have h1 : resM x hx.1 * resM y hy = 1 := by rw [← resM_mul]; exact resM_one_of _ hxy
  haveI : Invertible (resM x hx.1) := Matrix.invertibleOfIsUnitDet _ (Units.mkOfMulEqOne (resM x hx.1).det (resM y hy).det (by rw [← Matrix.det_mul, h1, Matrix.det_one])).isUnit
  rw [(Matrix.inv_eq_right_inv h1).symm]
  exact Matrix.blockTriangular_inv_of_blockTriangular (bt_parah hx)

theorem i_levG_inv (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    x * y = 1 → (∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) → NX.InLevG v r x → ∀ a b : Fin n, (a : ℕ) < r → (b : ℕ) < r →
      (b < a → Valued.v (y a b) < 1) ∧ (a = b → Valued.v (y a b - 1) < 1) := by
  intro hxy hy hx
  have h1 : resM x hx.1.1 * resM y hy = 1 := by rw [← resM_mul]; exact resM_one_of _ hxy
  haveI : Invertible (resM x hx.1.1) := Matrix.invertibleOfIsUnitDet _ (Units.mkOfMulEqOne (resM x hx.1.1).det (resM y hy).det (by rw [← Matrix.det_mul, h1, Matrix.det_one])).isUnit
  have hbt : (resM y hy).BlockTriangular (bG r) := by
    rw [(Matrix.inv_eq_right_inv h1).symm]
    exact Matrix.blockTriangular_inv_of_blockTriangular (bt_levG hx)
  refine levG_top_of_bt hy hbt fun a ha => ?_
  have e := congrFun (congrFun h1 a) a
  rw [diag_mul (bt_levG hx) hbt a ha, (resM_one _ a a).2 ((hx.2 a a ha ha).2 rfl), one_mul, Matrix.one_apply_eq] at e
  exact e

theorem i_detT_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    x * y = 1 → (∀ a b, y a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)) → NX.InParah v r x → Valued.v (NX.detT r x) = 1 := by
  intro hxy hy hx
  have h1 : resM x hx.1 * resM y hy = 1 := by rw [← resM_mul]; exact resM_one_of _ hxy
  haveI : Invertible (resM x hx.1) := Matrix.invertibleOfIsUnitDet _ (Units.mkOfMulEqOne (resM x hx.1).det (resM y hy).det (by rw [← Matrix.det_mul, h1, Matrix.det_one])).isUnit
  have h2 : NX.detT r (resM x hx.1) * NX.detT r (resM y hy) = 1 := by
    rw [← detT_mul_of (bt_parah hx), h1, detT_one']
  have hne : IsLocalRing.residue ↥(v.adicCompletionIntegers (maximalRealSubfield L)) (NX.detT r (intM x hx.1)) ≠ 0 := by
    rw [detT_res]; exact left_ne_zero_of_mul_eq_one h2
  rw [← detT_coe r x hx.1]
  have hle : Valued.v ((NX.detT r (intM x hx.1) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (NX.detT r (intM x hx.1)).2
  exact le_antisymm hle (not_lt.1 fun h => hne ((res_zero _).2 h))

theorem i_detT_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    NX.InParah v r x → NX.InParah v r y → Valued.v (NX.detT r (x * y) - NX.detT r x * NX.detT r y) < 1 := by
  intro hx hy
  rw [← detT_coe r (x * y) (int_mul hx.1 hy.1), ← detT_coe r x hx.1, ← detT_coe r y hy.1]
  have e : ((NX.detT r (intM (x * y) (int_mul hx.1 hy.1)) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) -
      ((NX.detT r (intM x hx.1) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) * ((NX.detT r (intM y hy.1) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) =
      ((NX.detT r (intM (x * y) (int_mul hx.1 hy.1)) - NX.detT r (intM x hx.1) * NX.detT r (intM y hy.1) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) := by
    push_cast; rfl
  rw [e, ← res_zero, map_sub, map_mul, detT_res, detT_res, detT_res, resM_mul hx.1 hy.1, detT_mul_of (bt_parah hx), sub_self]

theorem i_detT_cong (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    (∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) → Valued.v (NX.detT r x - 1) < 1 := by
  intro hx1
  have hx : ∀ a b, x a b ∈ v.adicCompletionIntegers (maximalRealSubfield L) := fun a b => int_of_cong (c := (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b)
    (by by_cases hab : a = b <;> simp [Matrix.one_apply, hab]) (hx1 a b)
  have hres : resM x hx = 1 := by
    refine Matrix.ext fun a b => ?_
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      exact (resM_one hx a a).2 (by simpa using hx1 a a)
    · rw [Matrix.one_apply_ne hab]
      exact (resM_zero hx a b).2 (by simpa [Matrix.one_apply_ne hab] using hx1 a b)
  rw [← detT_coe r x hx]
  have e : ((NX.detT r (intM x hx) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) - 1 = ((NX.detT r (intM x hx) - 1 : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) := by
    push_cast; rfl
  rw [e, ← res_zero, map_sub, map_one, detT_res, hres, detT_one', sub_self]

end ResProofs

section ResProofs2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem i_red_zero {p : ℕ} [Fact p.Prime] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (red : ↥(v.adicCompletionIntegers (maximalRealSubfield L)) →+* ZMod p) (z : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0 := by
  intro hz
  by_contra hne
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, red z * c = 1 := ⟨(red z)⁻¹, mul_inv_cancel₀ hne⟩
  have h1 : Valued.v ((((c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)))) : v.adicCompletion (maximalRealSubfield L)) < 1 := by
    have hle : Valued.v (((c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))).2
    rw [show ((((c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)))) : v.adicCompletion (maximalRealSubfield L)) = ((c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) : v.adicCompletion (maximalRealSubfield L)) * (z : v.adicCompletion (maximalRealSubfield L)) from rfl, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) hz
  have hw : Valued.v (((1 - (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)))) : v.adicCompletion (maximalRealSubfield L)) = 1 := by
    rw [show (((1 - (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)))) : v.adicCompletion (maximalRealSubfield L)) = 1 + -((((c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)))) : v.adicCompletion (maximalRealSubfield L)) by
      push_cast; ring]
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact h1), map_one]
  have hu : IsUnit (1 - (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z) := isUnit_int hw (1 - (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z).2
  have h0 : red (1 - (c.val : ↥(v.adicCompletionIntegers (maximalRealSubfield L))) * z) = 0 := by
    rw [map_sub, map_one, map_mul, map_natCast, ZMod.natCast_zmod_val, mul_comm, hc, sub_self]
  exact not_isUnit_zero (h0 ▸ hu.map red)

theorem i_redMat_mul {R : Type} [CommRing R] {r : ℕ} (h : r ≤ n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (red : ↥(v.adicCompletionIntegers (maximalRealSubfield L)) →+* R) (hred : ∀ z : ↥(v.adicCompletionIntegers (maximalRealSubfield L)), Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) :
    NX.InParah v r x → NX.InParah v r y →
      NX.redMat v red (NX.topR h (x * y)) = NX.redMat v red (NX.topR h x) * NX.redMat v red (NX.topR h y) := by
  intro hx hy
  have hl : ∀ (z : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hz : ∀ a b, z a b ∈ v.adicCompletionIntegers (maximalRealSubfield L)),
      NX.redMat v red (NX.topR h z) = ((intM z hz).map red).submatrix (Fin.castLE h) (Fin.castLE h) := by
    intro z hz
    refine Matrix.ext fun a b => ?_
    show red (NX.intLift v (z (Fin.castLE h a) (Fin.castLE h b))) = red ⟨z (Fin.castLE h a) (Fin.castLE h b), _⟩
    rw [NX.intLift, dif_pos (hz _ _)]
  rw [hl _ (int_mul hx.1 hy.1), hl _ hx.1, hl _ hy.1, intM_mul hx.1 hy.1, Matrix.map_mul]
  refine Matrix.ext fun a b => ?_
  set A := (intM x hx.1).map red with hA
  set B := (intM y hy.1).map red with hB
  have hB0 : ∀ c : Fin n, r ≤ (c : ℕ) → B c (Fin.castLE h b) = 0 := fun c hc => by
    rw [hB, Matrix.map_apply]
    exact hred _ (hy.2 c (Fin.castLE h b) hc b.2)
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  symm
  calc ∑ c : Fin r, A.submatrix (Fin.castLE h) (Fin.castLE h) a c * B.submatrix (Fin.castLE h) (Fin.castLE h) c b
        = ∑ c ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, A (Fin.castLE h a) c * B c (Fin.castLE h b) :=
          (Finset.sum_map Finset.univ ⟨Fin.castLE h, Fin.castLE_injective h⟩
            (fun c => A (Fin.castLE h a) c * B c (Fin.castLE h b))).symm
    _ = ∑ c : Fin n, A (Fin.castLE h a) c * B c (Fin.castLE h b) := by
          refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
          have hrc : r ≤ (c : ℕ) := by
            by_contra hlt
            exact hc (Finset.mem_map.2 ⟨⟨c, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          rw [hB0 c hrc, mul_zero]

end ResProofs2

section ResRepProof
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem i_resRep (s : SplitPlace L) (z : s.v.adicCompletion (maximalRealSubfield L)) :
    Valued.v z = 1 → Valued.v (s.i ((NX.resRep s s.w z : 𝓞 L) : L) - z) < 1 := by
  intro hz
  obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx s.v z (le_of_eq hz)
  have e : s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L) =
      algebraMap (𝓞 (maximalRealSubfield L)) (s.v.adicCompletion (maximalRealSubfield L)) a := by
    rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes]; rfl
  have h1 : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L) - z) < 1 := by
    rw [e, ← Valuation.map_neg, neg_sub]; exact ha
  have hex : ∃ u : 𝓞 L, u ∉ s.w.asIdeal ∧ Valued.v (s.i (u : L) - z) < 1 := by
    refine ⟨_, fun hm => ?_, h1⟩
    have hlt : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L)) < 1 := hm
    have h2 : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L)) = 1 := by
      have e2 : s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L) =
          z + (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L) - z) := by ring
      rw [e2, Valuation.map_add_eq_of_lt_left _ (by rw [hz]; exact h1), hz]
    rw [h2] at hlt
    exact lt_irrefl _ hlt
  unfold NX.resRep
  rw [dif_pos hex]
  exact hex.choose_spec.2

end ResRepProof

section Tame
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem resRep_not_mem (s : SplitPlace L) (P : HeightOneSpectrum (𝓞 L))
    (x : s.v.adicCompletion (maximalRealSubfield L)) : NX.resRep s P x ∉ P.asIdeal := by
  unfold NX.resRep
  split_ifs with h
  · exact h.choose_spec.1
  · exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem tame_mul {M : Type} [Group M] (s : SplitPlace L) (P : HeightOneSpectrum (𝓞 L)) (hP : s.w = P) (t : 𝓞 L → M)
    (hm : ∀ u u' : 𝓞 L, u ∉ P.asIdeal → u' ∉ P.asIdeal → t (u * u') = t u * t u')
    (hc : ∀ u u' : 𝓞 L, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → t u = t u')
    {z z' z'' : s.v.adicCompletion (maximalRealSubfield L)} (hz : Valued.v z = 1) (hz' : Valued.v z' = 1)
    (h : Valued.v (z'' - z * z') < 1) :
    t (NX.resRep s P z'') = t (NX.resRep s P z) * t (NX.resRep s P z') := by
  subst hP
  have hzz : Valued.v (z * z') = 1 := by rw [map_mul, hz, hz', one_mul]
  have hz'' : Valued.v z'' = 1 := by
    have e : z'' = z * z' + (z'' - z * z') := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [hzz]; exact h), hzz]
  have hu := i_resRep s z hz
  have hu' := i_resRep s z' hz'
  have hw := i_resRep s z'' hz''
  have hle : Valued.v (s.i (NX.resRep s s.w z' : L)) ≤ 1 := s.split_le_one _
  have key : NX.resRep s s.w z'' - NX.resRep s s.w z * NX.resRep s s.w z' ∈ s.w.asIdeal := by
    show Valued.v (s.i (((NX.resRep s s.w z'' - NX.resRep s s.w z * NX.resRep s s.w z' : 𝓞 L)) : L)) < 1
    have e : s.i (((NX.resRep s s.w z'' - NX.resRep s s.w z * NX.resRep s s.w z' : 𝓞 L)) : L) =
        (s.i (NX.resRep s s.w z'' : L) - z'') + (z'' - z * z') -
        ((s.i (NX.resRep s s.w z : L) - z) * s.i (NX.resRep s s.w z' : L) + z * (s.i (NX.resRep s s.w z' : L) - z')) := by
      push_cast; rw [map_sub, map_mul]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hw h)) ?_)
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hu
    · rw [map_mul, hz, one_mul]; exact hu'
  rw [hc _ _ (resRep_not_mem s s.w z'') key, hm _ _ (resRep_not_mem s s.w z) (resRep_not_mem s s.w z')]

theorem tame_one {M : Type} [Group M] (s : SplitPlace L) (P : HeightOneSpectrum (𝓞 L)) (hP : s.w = P) (t : 𝓞 L → M)
    (hm : ∀ u u' : 𝓞 L, u ∉ P.asIdeal → u' ∉ P.asIdeal → t (u * u') = t u * t u')
    (hc : ∀ u u' : 𝓞 L, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → t u = t u')
    {z : s.v.adicCompletion (maximalRealSubfield L)} (h : Valued.v (z - 1) < 1) : t (NX.resRep s P z) = 1 := by
  subst hP
  have hz : Valued.v z = 1 := by
    have e : z = 1 + (z - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact h), map_one]
  have hu := i_resRep s z hz
  have h1 : (1 : 𝓞 L) ∉ s.w.asIdeal := fun h1 => s.w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have key : NX.resRep s s.w z - 1 ∈ s.w.asIdeal := by
    show Valued.v (s.i (((NX.resRep s s.w z - 1 : 𝓞 L)) : L)) < 1
    have e : s.i (((NX.resRep s s.w z - 1 : 𝓞 L)) : L) = (s.i (NX.resRep s s.w z : L) - z) + (z - 1) := by
      push_cast; rw [map_sub, map_one]; ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu h)
  rw [hc _ 1 (resRep_not_mem s s.w z) key]
  have e1 := hm 1 1 h1 h1
  rw [mul_one] at e1
  have e2 : t 1 * t 1 = t 1 * 1 := by rw [mul_one]; exact e1.symm
  exact mul_left_cancel e2

end Tame

section Glob
variable (D : D7) (T : TwR D.LL0 D.nd)

open Classical in

def psiUnitT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (b : Bool) (u : G0g D.nd) :
    (FractionRing (T.O i))ˣ :=
  if h : u ∈ Formalism.IndefR.NX.U D.nd then psiUT D T θ i b ⟨u, h⟩ else 1

variable (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)

theorem psiUnitT_val (i : T.Tw) (b : Bool) (u : G0g D.nd) :
    ((psiUnitT D T θ i b u : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) = psiUTotT D T θ i b u := by
  unfold psiUnitT psiUTotT
  split_ifs <;> rfl

theorem psiUnitT_mul (i : T.Tw) (b : Bool) {u u' : G0g D.nd} (hu : u ∈ Formalism.IndefR.NX.U D.nd)
    (hu' : u' ∈ Formalism.IndefR.NX.U D.nd) :
    psiUnitT D T θ i b (u * u') = psiUnitT D T θ i b u * psiUnitT D T θ i b u' := by
  unfold psiUnitT
  rw [dif_pos (mul_mem hu hu'), dif_pos hu, dif_pos hu', ← map_mul]
  rfl

theorem psiUnitT_one (i : T.Tw) (b : Bool) : psiUnitT D T θ i b 1 = 1 := by
  unfold psiUnitT
  rw [dif_pos (one_mem _)]
  exact map_one _

open Classical in
theorem mulSingle_mem_U (kv : Σ kk : Fin 2, D.nd.PlG kk) (M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (hM : NX.IsUniTri D.R.r M) : (Pi.mulSingle kv (NX.glOf M) : G0g D.nd) ∈ Formalism.IndefR.NX.U D.nd := by
  rw [Formalism.IndefR.NX.U_eq_Uup, NX.mem_Uup]
  intro kv'
  by_cases h : kv' = kv
  · subst h
    rw [Pi.mulSingle_eq_same, NX.glOf_val _ (by rw [det_uniTri hM]; exact isUnit_one)]
    exact hM
  · rw [Pi.mulSingle_eq_of_ne h]
    exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩

open Classical in

def gU (i : T.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
    (FractionRing (T.Ok i k))ˣ :=
  Units.map (toKkT D T i k).toMonoidHom (psiUnitT D T θ i b (Pi.mulSingle kv
    (NX.glOf (NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x))))) *
  (if h : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) then Units.map (toKkT D T i k).toMonoidHom (τ h.unit) else 1)

variable (i : T.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ)

theorem gU_val (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
    ((gU D T θ i k b kv s red τ x : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
      gValT D T θ i k b kv s red τ x := by
  unfold gU gValT
  split_ifs <;> simp [psiUnitT_val]

open Classical in
theorem gU_one
    (hred : ∀ z : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → red z = 0)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) :
    gU D T θ i k b kv s red τ x = 1 := by
  have hM := redMat_one (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) red hred x hx
  have hd : red (NX.intLift s.v (NX.detT D.R.r x)) = 1 := by
    rw [red_intLift red hred 1 (by simpa using i_detT_cong s.v D.R.r x hx), map_one]
  have hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) := by rw [hd]; exact isUnit_one
  have hg : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (by rw [NX.glOf_val _ (by simp)]; rfl)
  have hun : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
  unfold gU
  rw [hM, hg, Pi.mulSingle_one, psiUnitT_one, map_one, one_mul, dif_pos hu, hun, map_one, map_one]

open Classical in
theorem gU_eq (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))) :
    gU D T θ i k b kv s red τ x = Units.map (toKkT D T i k).toMonoidHom (psiUnitT D T θ i b (Pi.mulSingle kv
      (NX.glOf (NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x))))) *
      Units.map (toKkT D T i k).toMonoidHom (τ hu.unit) := by
  unfold gU
  rw [dif_pos hu]

open Classical in
theorem gU_mul
    (hred : ∀ z : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → red z = 0)
    (x y : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hx : NX.InLevG s.v D.R.r x) (hy : NX.InLevG s.v D.R.r y)
    (hdx : Valued.v (NX.detT D.R.r x) = 1) (hdy : Valued.v (NX.detT D.R.r y) = 1) :
    gU D T θ i k b kv s red τ (x * y) = gU D T θ i k b kv s red τ x * gU D T θ i k b kv s red τ y := by
  have hMxy : NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) (x * y)) =
      NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x) *
        NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) y) :=
    i_redMat_mul _ s.v red hred x y hx.1 hy.1
  have tx := uniTri_red (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) red hred x hx
  have ty := uniTri_red (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) red hred y hy
  have hg := glOf_mul _ _ (by rw [det_uniTri tx]; exact isUnit_one) (by rw [det_uniTri ty]; exact isUnit_one)
  have hix : NX.detT D.R.r x ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have hiy : NX.detT D.R.r y ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdy]
  have ex : NX.intLift s.v (NX.detT D.R.r x) = ⟨_, hix⟩ := by rw [NX.intLift, dif_pos hix]
  have ey : NX.intLift s.v (NX.detT D.R.r y) = ⟨_, hiy⟩ := by rw [NX.intLift, dif_pos hiy]
  have hxy : red (NX.intLift s.v (NX.detT D.R.r (x * y))) =
      red (NX.intLift s.v (NX.detT D.R.r x)) * red (NX.intLift s.v (NX.detT D.R.r y)) := by
    rw [ex, ey, ← map_mul]
    exact red_intLift red hred _ (by simpa using i_detT_mul s.v D.R.r x y hx.1 hy.1)
  have hux : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) := by rw [ex]; exact (isUnit_int hdx hix).map red
  have huy : IsUnit (red (NX.intLift s.v (NX.detT D.R.r y))) := by rw [ey]; exact (isUnit_int hdy hiy).map red
  have huxy : IsUnit (red (NX.intLift s.v (NX.detT D.R.r (x * y)))) := by rw [hxy]; exact hux.mul huy
  have e : huxy.unit = hux.unit * huy.unit := Units.ext (by simp [hxy])
  have hp := psiUnitT_mul D T θ i b (mulSingle_mem_U D kv _ tx) (mulSingle_mem_U D kv _ ty)
  rw [gU_eq D T θ i k b kv s red τ _ huxy, gU_eq D T θ i k b kv s red τ _ hux, gU_eq D T θ i k b kv s red τ _ huy, hMxy, hg,
    Pi.mulSingle_mul]
  erw [hp]
  rw [e, map_mul τ, MonoidHom.map_mul, MonoidHom.map_mul]
  exact mul_mul_mul_comm _ _ _ _

end Glob

section Lev
variable (D : D7)

def levJ (sp : PlE D.host → SplitPlace D.host.E) (QP DP : Finset (PlE D.host)) : Subgroup (GAf D.host.E D.R.nV) where
  carrier := {κ | κ ∈ Umax D.host.E D.R.nV ∧
    (∀ kv, NX.InLevG (sp (NX.pG D kv)).v D.R.r (NX.locM (sp (NX.pG D kv)) κ)) ∧
    (∀ P ∈ QP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ)) ∧
    (∀ P ∈ DP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ))}
  mul_mem' := by
    rintro κ κ' ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨mul_mem h1 h1', fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · rw [locM_mul]
      exact ⟨i_parah_mul _ _ _ _ (h2 kv).1 (h2' kv).1, i_levG_mul _ _ _ _ (h2 kv) (h2' kv)⟩
    · rw [locM_mul]; exact i_parah_mul _ _ _ _ (h3 P hP) (h3' P hP)
    · rw [locM_mul]; exact i_parah_mul _ _ _ _ (h4 P hP) (h4' P hP)
  one_mem' := ⟨one_mem _, fun kv => by rw [locM_one]; exact NX.inLevG_one _ _,
    fun P _ => by rw [locM_one]; exact NX.inParah_one _ _, fun P _ => by rw [locM_one]; exact NX.inParah_one _ _⟩
  inv_mem' := by
    rintro κ ⟨h1, h2, h3, h4⟩
    have hinv : ∀ s : SplitPlace D.host.E, NX.locM s κ * NX.locM s κ⁻¹ = 1 := fun s => by
      rw [← locM_mul, mul_inv_cancel, locM_one]
    have hint : ∀ s : SplitPlace D.host.E, ∀ a b, NX.locM s κ⁻¹ a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
      fun s => locM_int s (inv_mem h1)
    exact ⟨inv_mem h1, fun kv => ⟨i_parah_inv _ _ _ _ (hinv _) (hint _) (h2 kv).1,
      i_levG_inv _ _ _ _ (hinv _) (hint _) (h2 kv)⟩, fun P hP => i_parah_inv _ _ _ _ (hinv _) (hint _) (h3 P hP),
      fun P hP => i_parah_inv _ _ _ _ (hinv _) (hint _) (h4 P hP)⟩

variable (T : TwR D.LL0 D.nd)

def chiU (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) (QP DP : Finset (PlE D.host)) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (κ : GAf D.host.E D.R.nV) : (FractionRing (T.Ok i k))ˣ :=
  (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gU D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
      (NX.locM (sp (NX.pG D kv)) κ)) *
    (∏ P ∈ QP, Units.map (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).toMonoidHom
      (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ))))) *
    (∏ P ∈ DP, Units.map (baseCoeffToExtFractionRing D T i k).toMonoidHom
      (NX.tameVal (T.delta i) P (if b then 1 else -1) (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))))

end Lev

theorem levGroup_exists : ∀ (D : D7) (T : TwR D.LL0 D.nd) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ)
    (QP DP : Finset (PlE D.host)) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)),
    (∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (P' ∈ QP ∨ P' ∈ DP ∨ ∃ kv, P' = NX.pG D kv) →
      (sp P).v = (sp P').v → P = P') →
    (∀ P ∈ QP, P ∉ DP) → (∀ kv, NX.pG D kv ∉ QP ∧ NX.pG D kv ∉ DP) → (∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv') →
    QP ⊆ Q → DP ⊆ T.pD i →
    (∀ P ∈ QP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal ψ P 1 (u * u') = NX.tameVal ψ P 1 u * NX.tameVal ψ P 1 u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal ψ P 1 u = NX.tameVal ψ P 1 u') →
    (∀ P ∈ DP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) (u * u') =
          NX.tameVal (T.delta i) P (if b then 1 else -1) u * NX.tameVal (T.delta i) P (if b then 1 else -1) u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) u = NX.tameVal (T.delta i) P (if b then 1 else -1) u') →
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* (FractionRing (T.Ok i k))ˣ),
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      NX.HypOutsideF J χ (badVT D T i Q) ∧
      (∀ κ : GAf D.host.E D.R.nV, κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV ∧
        (∀ kv, NX.InLevG (sp (NX.pG D kv)).v D.R.r (NX.locM (sp (NX.pG D kv)) κ)) ∧
        (∀ P ∈ QP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ)) ∧
        (∀ P ∈ DP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ))) ∧
      ∀ κ (h : κ ∈ J), ((χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ)) *
        (∏ P ∈ QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) *
        (∏ P ∈ DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
          (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) := by
  intro D T θ i j b k Q ψ QP DP sp redG hsw hinj hQD hG hGinj hQP hDP hψ hδ
  classical
  have hred : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      ∀ z : (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : (sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → redG kv z = 0 := by
    intro kv z hz
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact i_red_zero _ (redG kv) z hz
  have hdet : ∀ (s : SplitPlace D.host.E) (κ : GAf D.host.E D.R.nV), κ ∈ Umax D.host.E D.R.nV →
      NX.InParah s.v D.R.r (NX.locM s κ) → Valued.v (NX.detT D.R.r (NX.locM s κ)) = 1 := fun s κ hU hp =>
    i_detT_one _ _ _ (NX.locM s κ⁻¹) (by rw [← locM_mul, mul_inv_cancel, locM_one]) (locM_int s (inv_mem hU)) hp
  have hmul : ∀ κ κ' : levJ D sp QP DP,
      chiU D T θ i j b k ψ QP DP sp redG ((κ * κ' : levJ D sp QP DP) : GAf D.host.E D.R.nV) =
        chiU D T θ i j b k ψ QP DP sp redG κ * chiU D T θ i j b k ψ QP DP sp redG κ' := by
    rintro ⟨κ, h1, h2, h3, h4⟩ ⟨κ', h1', h2', h3', h4'⟩
    have hA : (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gU D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
        (NX.locM (sp (NX.pG D kv)) (κ * κ'))) =
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gU D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ)) *
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gU D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ')) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun kv _ => ?_
      rw [locM_mul]
      exact gU_mul D T θ i k b kv _ _ _ (hred kv) _ _ (h2 kv) (h2' kv) (hdet _ _ h1 (h2 kv).1) (hdet _ _ h1' (h2' kv).1)
    have hB : (∏ P ∈ QP, Units.map (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).toMonoidHom
        (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) (κ * κ')))))) =
        (∏ P ∈ QP, Units.map (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).toMonoidHom
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ))))) *
        (∏ P ∈ QP, Units.map (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).toMonoidHom
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ'))))) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← MonoidHom.map_mul, locM_mul]
      congr 1
      exact tame_mul (sp P) P (hsw P (Or.inl hP)) (fun u => NX.tameVal ψ P 1 u) (hψ P hP).1 (hψ P hP).2
        (hdet _ _ h1 (h3 P hP)) (hdet _ _ h1' (h3' P hP)) (i_detT_mul _ _ _ _ (h3 P hP) (h3' P hP))
    have hC : (∏ P ∈ DP, Units.map (baseCoeffToExtFractionRing D T i k).toMonoidHom
        (NX.tameVal (T.delta i) P (if b then 1 else -1) (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) (κ * κ')))))) =
        (∏ P ∈ DP, Units.map (baseCoeffToExtFractionRing D T i k).toMonoidHom
          (NX.tameVal (T.delta i) P (if b then 1 else -1) (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ))))) *
        (∏ P ∈ DP, Units.map (baseCoeffToExtFractionRing D T i k).toMonoidHom
          (NX.tameVal (T.delta i) P (if b then 1 else -1) (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ'))))) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← MonoidHom.map_mul, locM_mul]
      congr 1
      exact tame_mul (sp P) P (hsw P (Or.inr (Or.inl hP))) (fun u => NX.tameVal (T.delta i) P (if b then 1 else -1) u)
        (hδ P hP).1 (hδ P hP).2 (hdet _ _ h1 (h4 P hP)) (hdet _ _ h1' (h4' P hP)) (i_detT_mul _ _ _ _ (h4 P hP) (h4' P hP))
    show chiU D T θ i j b k ψ QP DP sp redG (κ * κ') =
      chiU D T θ i j b k ψ QP DP sp redG κ * chiU D T θ i j b k ψ QP DP sp redG κ'
    unfold chiU
    rw [hA, hB, hC]
    ac_rfl
  have hone : ∀ κ : GAf D.host.E D.R.nV,
      (∀ kv a b, Valued.v (NX.locM (sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) →
      (∀ P ∈ QP, ∀ a b, Valued.v (NX.locM (sp P) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp P).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) →
      (∀ P ∈ DP, ∀ a b, Valued.v (NX.locM (sp P) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp P).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) →
      chiU D T θ i j b k ψ QP DP sp redG κ = 1 := by
    intro κ hg hq hd
    unfold chiU
    rw [Finset.prod_eq_one (fun kv _ => gU_one D T θ i k b kv _ _ _ (hred kv) _ (hg kv)),
      Finset.prod_eq_one (fun P hP => ?_), Finset.prod_eq_one (fun P hP => ?_), one_mul, one_mul]
    · have e := tame_one (sp P) P (hsw P (Or.inr (Or.inl hP))) (fun u => NX.tameVal (T.delta i) P (if b then 1 else -1) u)
        (hδ P hP).1 (hδ P hP).2 (i_detT_cong _ D.R.r _ (hd P hP))
      beta_reduce at e
      rw [e, map_one]
    · have e := tame_one (sp P) P (hsw P (Or.inl hP)) (fun u => NX.tameVal ψ P 1 u) (hψ P hP).1 (hψ P hP).2
        (i_detT_cong _ D.R.r _ (hq P hP))
      beta_reduce at e
      rw [e, map_one]
  refine ⟨levJ D sp QP DP, MonoidHom.mk' (fun κ => chiU D T θ i j b k ψ QP DP sp redG κ) hmul, ?_, ?_,
    fun κ => Iff.rfl, ?_⟩
  · have hpos : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), 0 < Ideal.absNorm v.asIdeal := fun v =>
      Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    have hmem : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (N : ℕ), Ideal.absNorm v.asIdeal ∣ N →
        (N : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := fun v N h =>
      Ideal.mem_of_dvd _ (Nat.cast_dvd_cast h) (Ideal.absNorm_mem _)
    refine ⟨(∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), Ideal.absNorm (sp (NX.pG D kv)).v.asIdeal) *
        ((∏ P ∈ QP, Ideal.absNorm (sp P).v.asIdeal) * (∏ P ∈ DP, Ideal.absNorm (sp P).v.asIdeal)),
      Nat.mul_pos (Finset.prod_pos fun _ _ => hpos _)
        (Nat.mul_pos (Finset.prod_pos fun _ _ => hpos _) (Finset.prod_pos fun _ _ => hpos _)), fun κ hκ => ?_⟩
    have cg : ∀ kv, ∀ a b, Valued.v (NX.locM (sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1 := fun kv =>
      locM_cong _ (hmem _ _ (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ kv)) _)) κ hκ
    have cq : ∀ P ∈ QP, ∀ a b, Valued.v (NX.locM (sp P) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp P).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1 := fun P hP =>
      locM_cong _ (hmem _ _ (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hP) _) _)) κ hκ
    have cd : ∀ P ∈ DP, ∀ a b, Valued.v (NX.locM (sp P) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((sp P).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1 := fun P hP =>
      locM_cong _ (hmem _ _ (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hP) _) _)) κ hκ
    have hJ : κ ∈ levJ D sp QP DP := ⟨hκ.1, fun kv => levG_of_cong _ _ (cg kv),
      fun P hP => (levG_of_cong _ _ (cq P hP)).1, fun P hP => (levG_of_cong _ _ (cd P hP)).1⟩
    exact ⟨hJ, hone κ cg cq cd⟩
  · intro κ hκ
    have hover : ∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (sp P).v ∈ badVT D T i Q := by
      intro P hP
      have hw := (sp P).w_under
      rw [hsw P hP] at hw
      refine ⟨P, hw, ?_⟩
      rcases hP with hP | hP | ⟨kv, rfl⟩
      · exact Or.inl (hQP hP)
      · exact Or.inr (Or.inr (hDP hP))
      · exact Or.inr (Or.inl ⟨kv.1, D.naut.plGw_over kv.1 kv.2⟩)
    have hl : ∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → NX.locM (sp P) κ = 1 := fun P hP =>
      locM_triv (sp P) hκ (hover P hP)
    have h1 : ∀ (s : SplitPlace D.host.E) (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))),
        x = 1 → ∀ a b, Valued.v (x a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
          (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1 := by
      rintro s x rfl a b
      simp
    refine ⟨⟨fun h => h.1, fun hU => ⟨hU, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩⟩, fun hJ => ?_⟩
    · rw [hl _ (Or.inr (Or.inr ⟨kv, rfl⟩))]; exact NX.inLevG_one _ _
    · rw [hl _ (Or.inl hP)]; exact NX.inParah_one _ _
    · rw [hl _ (Or.inr (Or.inl hP))]; exact NX.inParah_one _ _
    · exact hone κ (fun kv => h1 _ _ (hl _ (Or.inr (Or.inr ⟨kv, rfl⟩)))) (fun P hP => h1 _ _ (hl _ (Or.inl hP)))
        (fun P hP => h1 _ _ (hl _ (Or.inr (Or.inl hP))))
  · intro κ h
    show ((chiU D T θ i j b k ψ QP DP sp redG κ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) = _
    unfold chiU
    simp only [Units.val_mul, Units.coe_prod, gU_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

end GlobalTheory.LevGChar
