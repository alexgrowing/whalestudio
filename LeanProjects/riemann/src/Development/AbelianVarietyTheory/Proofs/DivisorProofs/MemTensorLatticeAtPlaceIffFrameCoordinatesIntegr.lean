import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.Lat

theorem mem_of_bil {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (g : A →+ B →+ C)
    {SA : Set A} {SB : Set B} {T : AddSubgroup C} (h : ∀ a ∈ SA, ∀ b ∈ SB, g a b ∈ T) {a : A} {b : B}
    (ha : a ∈ AddSubgroup.closure SA) (hb : b ∈ AddSubgroup.closure SB) : g a b ∈ T := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | zero => simpa using T.zero_mem
    | add b b' _ _ h1 h2 => simpa using T.add_mem h1 h2
    | neg b _ h1 => simpa using T.neg_mem h1
  | zero => simpa using T.zero_mem
  | add a a' _ _ h1 h2 => simpa using T.add_mem h1 h2
  | neg a _ h1 => simpa using T.neg_mem h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (v : Pl F) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
    evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl F} {a : AF F} (b : AF F) (ha : At (evFin F v) a) : At (evFin F v) (a * b) := by
  intro u hu
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]

theorem int_mul {v : Pl F} {a b : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    (hb : evFin F v b ∈ v.adicCompletionIntegers F) : evFin F v (a * b) ∈ v.adicCompletionIntegers F := by
  rw [map_mul]
  exact mul_mem ha hb

def smulHom (n : ℕ) : AE F E →+ (Fin n → AE F E) →+ (Fin n → AE F E) :=
  AddMonoidHom.mk' (fun c => DistribMulAction.toAddMonoidHom _ c)
    (fun c c' => AddMonoidHom.ext fun x => by funext i; simp [add_mul])

theorem smul_mem_latAt {v : Pl F} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {x : Fin n → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) : c • x ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) ?_ hc hx
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ ⟨a, ha, hai, y, hy, rfl⟩
  refine AddSubgroup.subset_closure ⟨b * a, at_mul a hb, int_mul hbi hai, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem smul_incl_mem_latAt {v : Pl F} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {y : Fin n → E}
    (hy : y ∈ X.L) : (c • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) (SB := {fun i => inclR (F := F) (AF F) (y i)}) ?_ hc (AddSubgroup.subset_closure rfl)
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ rfl
  refine AddSubgroup.subset_closure ⟨b, hb, hbi, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem vecMulVec_mem {v : Pl F} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) {x : Fin n → AE F E} {y : Fin d → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) (hy : y ∈ GlobalTheory.InertSph.latAt W v) : Matrix.vecMulVec x y ∈ latAtV X W v := by
  let g : (Fin n → AE F E) →+ (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Matrix.vecMulVec x y)
        (fun y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]))
      (fun x x' => AddMonoidHom.ext fun y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
  refine mem_of_bil g ?_ hx hy
  rintro _ ⟨a, ha, hai, x0, hx0, rfl⟩ _ ⟨b, hb, hbi, y0, hy0, rfl⟩
  refine AddSubgroup.subset_closure ⟨a * b, at_mul b ha, int_mul hai hbi, x0, hx0, y0, hy0, ?_⟩
  ext i j
  simp only [g, AddMonoidHom.mk'_apply, Matrix.vecMulVec_apply, incM, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Algebra.smul_def, map_mul]
  ring

end GlobalTheory.InertLocFrame.Lat

namespace GlobalTheory.InertLocFrame

open GlobalTheory.InertLocFrame.Lat in

theorem mem_latAtV_iff_xm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  intro F E _ _ _ _ _ v n d X W L _ _ ι hinj hsupp hmul hint PV PW hPV hPW z
  have hsing : ∀ {m : ℕ} (j i : Fin m), (Pi.single j (1 : L) : Fin m → L) i ∈ Formalism.UG.intL L := by
    intro m j i
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
      have h1 : ι 1 ∈ intAt (E := E) v := (hint 1).1 (one_mem _)
      have h1s : At (evFin F v) (ι 1) := (hsupp _).2 ⟨1, rfl⟩
      let X' : Fin n → AE F E := a • fun i => inclR (F := F) (AF F) (x i)
      let Y' : Fin d → AE F E := ι 1 • fun k => inclR (F := F) (AF F) (y k)
      have hX'm : X' ∈ GlobalTheory.InertSph.latAt X v := AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
      have hY'm : Y' ∈ GlobalTheory.InertSph.latAt W v := smul_incl_mem_latAt W h1 hy
      have hX's : ∀ i, ∃ t, ι t = X' i := fun i => (hsupp _).1 fun u hu => by
        show u • (a • inclR (F := F) (AF F) (x i)) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      have hY's : ∀ k, ∃ t, ι t = Y' k := fun k => (hsupp _).1 fun u hu => by
        show u • (ι 1 * inclR (F := F) (AF F) (y k)) = 0
        rw [← smul_mul_assoc, h1s u hu, zero_mul]
      let xt : Fin n → L := fun i => pre ι (X' i)
      let yt : Fin d → L := fun k => pre ι (Y' k)
      have hxt : ∀ i, ι (xt i) = X' i := fun i => pre_spec ι (hX's i)
      have hyt : ∀ k, ι (yt k) = Y' k := fun k => pre_spec ι (hY's k)
      let c : Fin n → L := ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ xt
      let c' : Fin d → L := ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) *ᵥ yt
      have hPc : (PV : Matrix (Fin n) (Fin n) L) *ᵥ c = xt := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hPc' : (PW : Matrix (Fin d) (Fin d) L) *ᵥ c' = yt := by
        simp only [c']
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hc : ∀ i, c i ∈ Formalism.UG.intL L := (hPV c).2 (by
        rw [hPc]
        convert hX'm using 1
        funext i
        exact hxt i)
      have hc' : ∀ k, c' k ∈ Formalism.UG.intL L := (hPW c').2 (by
        rw [hPc']
        convert hY'm using 1
        funext k
        exact hyt k)
      refine ⟨Matrix.vecMulVec c' c, fun i j => mul_mem (hc' i) (hc j), ?_⟩
      ext i k
      rw [xm_apply, Matrix.map_apply]
      have e1 : ((PV : Matrix (Fin n) (Fin n) L) * (Matrix.vecMulVec c' c)ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i k = xt i * yt k := by
        rw [← hPc, ← hPc']
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ι 1 * X' i = X' i := by rw [← hxt i, ← hmul, one_mul]
      rw [e1, hmul, hxt, hyt]
      show X' i * (ι 1 * inclR (F := F) (AF F) (y k)) = (a • incM F (Matrix.vecMulVec x y)) i k
      rw [← mul_assoc, mul_comm (X' i), e2]
      simp only [X', incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul,
        smul_mul_assoc]
    | zero => exact ⟨0, fun _ _ => zero_mem _, map_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := h'
      exact ⟨u + u', fun i j => add_mem (hu i j) (hu' i j), map_add _ _ _⟩
    | neg z _ h =>
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨-u, fun i j => neg_mem (hu i j), map_neg _ _⟩
  · rintro ⟨u, hu, rfl⟩
    have e : xm ι PV PW u = ∑ j, ∑ l, Matrix.vecMulVec (ι (u l j) • fun i => ι ((PV : Matrix _ _ L) i j))
        (fun k => ι ((PW : Matrix _ _ L) k l)) := by
      ext i k
      simp only [xm_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_sum, hmul]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine sum_mem fun j _ => sum_mem fun l _ => vecMulVec_mem X W (smul_mem_latAt X ((hint _).1 (hu l j)) ?_) ?_
    · have h := (hPV (Pi.single j 1)).1 (hsing j)
      simpa [Matrix.mulVec_single_one] using h
    · have h := (hPW (Pi.single l 1)).1 (hsing l)
      simpa [Matrix.mulVec_single_one] using h

end GlobalTheory.InertLocFrame

end
