import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertGram

open GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def intAt (v : Pl F) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
    evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

def hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U V : Fin n → AE F E) : AE F E :=
  ∑ k, ∑ l, U k * inclR (F := F) (AF F) (J k l) * cA σ (V l)

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U U' V : Fin n → AE F E) :
    hA σ J (U + U') V = hA σ J U V + hA σ J U' V := by
  simp only [hA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U V V' : Fin n → AE F E) :
    hA σ J U (V + V') = hA σ J U V + hA σ J U V' := by
  simp only [hA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U V : Fin n → AE F E) :
    hA σ J (-U) V = -hA σ J U V := by
  simp only [hA, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem hA_neg_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U V : Fin n → AE F E) :
    hA σ J U (-V) = -hA σ J U V := by
  simp only [hA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem hA_zero_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (V : Fin n → AE F E) :
    hA σ J 0 V = 0 := by simp [hA]

theorem hA_zero_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (U : Fin n → AE F E) :
    hA σ J U 0 = 0 := by simp [hA]

theorem at_mul {v : Pl F} {a b : AF F} (ha : At (evFin F v) a) : At (evFin F v) (a * b) := fun u hu => by
  have := ha u hu
  rw [smul_eq_mul] at this ⊢
  rw [← mul_assoc, this, zero_mul]

theorem hA_gen (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : AF F) (y y' : Fin n → E) :
    hA σ J (a • fun i => inclR (F := F) (AF F) (y i)) (b • fun i => inclR (F := F) (AF F) (y' i)) =
      (a * b) • inclR (F := F) (AF F) (form σ J y y') := by
  simp only [hA, form, dotProduct, Matrix.mulVec, Pi.smul_apply, map_sum, map_mul, Algebra.smul_def,
    AlgHom.commutes, GlobalTheory.InertSelfDual.cA_inclR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hA_mem (σ : E →ₐ[F] E) (B : Base F E) {n r s : ℕ} (X : Spc F E n) (hX : X.IsHerm σ B r s) (v : Pl F)
    {U V : Fin n → AE F E} (hU : U ∈ GlobalTheory.InertSph.latAt X v) (hV : V ∈ GlobalTheory.InertSph.latAt X v) :
    hA σ X.J U V ∈ intAt (E := E) v := by
  induction hU using AddSubgroup.closure_induction with
  | mem U hU' =>
    induction hV using AddSubgroup.closure_induction with
    | mem V hV' =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hU'
      obtain ⟨b, hb, hbv, y', hy', rfl⟩ := hV'
      rw [hA_gen]
      have hi : IsIntegral ℤ (form σ X.J y y') := (hX.dual y).1 hy y' hy'
      refine AddSubgroup.subset_closure ⟨a * b, at_mul ha, ?_, ⟨_, hi⟩, rfl⟩
      rw [map_mul]; exact mul_mem hav hbv
    | zero => rw [hA_zero_right]; exact zero_mem _
    | add V V' _ _ h1 h2 => rw [hA_add_right]; exact add_mem h1 h2
    | neg V _ h => rw [hA_neg_right]; exact neg_mem h
  | zero => rw [hA_zero_left]; exact zero_mem _
  | add U U' _ _ h1 h2 => rw [hA_add_left]; exact add_mem h1 h2
  | neg U _ h => rw [hA_neg_left]; exact neg_mem h

theorem mul_lat_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {c : AE F E} (hc : c ∈ intAt (E := E) v) {y : Fin d → E}
    (hy : y ∈ W.L) : (fun k => c * inclR (F := F) (AF F) (y k)) ∈ GlobalTheory.InertSph.latAt W v := by
  induction hc using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, o • y, W.L.smul_mem o hy, ?_⟩
    ext k
    simp only [Pi.smul_apply, smul_mul_assoc, ← map_mul]
    congr 2
  | zero => convert (GlobalTheory.InertSph.latAt W v).zero_mem using 1; ext k; simp
  | add x z _ _ hx hz => convert add_mem hx hz using 1; ext k; simp [add_mul]
  | neg x _ hx => convert neg_mem hx using 1; ext k; simp [neg_mul]

end GlobalTheory.InertGram

noncomputable section
namespace GlobalTheory.InertGram

open GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem at_mul_left' {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) (w : AE F E) : At (evFin F v) (z * w) :=
  fun u hu => by rw [← smul_mul_assoc, hz u hu, zero_mul]

section Emb

variable {v : Pl F} {ι : L →+ AE F E} (himg : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
  (hmul : ∀ x y, ι (x * y) = ι x * ι y)
include himg hmul

theorem tJ_spec {m p : Type} (M : Matrix m p E) (i : m) (j : p) :
    ι (tJ ι M i j) = ι 1 * inclR (F := F) (AF F) (M i j) :=
  pre_spec ι ((himg _).1 (at_mul_left' ((himg _).2 ⟨1, rfl⟩) _))

theorem tJ_eq (hinj : Function.Injective ι) {m p : Type} {M : Matrix m p E} {N : Matrix m p L}
    (h : ∀ i j, ι (N i j) = ι 1 * inclR (F := F) (AF F) (M i j)) : N = tJ ι M := by
  ext i j; apply hinj; rw [h, tJ_spec himg hmul]

theorem one_one : ι 1 * ι 1 = ι 1 := by rw [← hmul, one_mul]

theorem mul_one_right (x : L) : ι x * ι 1 = ι x := by rw [← hmul, mul_one]

theorem tJ_mul (hinj : Function.Injective ι) {m p q : Type} [Fintype p] (M : Matrix m p E) (N : Matrix p q E) :
    tJ ι (M * N) = tJ ι M * tJ ι N := by
  symm; apply tJ_eq himg hmul hinj; intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmul, tJ_spec himg hmul, tJ_spec himg hmul, map_mul]
  calc ι 1 * inclR (F := F) (AF F) (M i k) * (ι 1 * inclR (F := F) (AF F) (N k j))
      = (ι 1 * ι 1) * (inclR (F := F) (AF F) (M i k) * inclR (F := F) (AF F) (N k j)) := by ring
    _ = _ := by rw [one_one himg hmul]

theorem tJ_one (hinj : Function.Injective ι) {n : ℕ} : tJ ι (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  symm; apply tJ_eq himg hmul hinj; intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem tJ_transpose {m p : Type} (M : Matrix m p E) : tJ ι Mᵀ = (tJ ι M)ᵀ := rfl

theorem tJ_map (hinj : Function.Injective ι) (σ : E →ₐ[F] E) (σL : L →+* L) (hσ : ∀ x, ι (σL x) = cA σ (ι x))
    {m p : Type} (M : Matrix m p E) : tJ ι (M.map σ) = (tJ ι M).map σL := by
  symm; apply tJ_eq himg hmul hinj; intro i j
  have h1 : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  simp only [Matrix.map_apply]
  rw [hσ, tJ_spec himg hmul, map_mul, h1, GlobalTheory.InertSelfDual.cA_inclR]

end Emb

end GlobalTheory.InertGram

namespace GlobalTheory.InertGram

open GlobalTheory.InertLocFrame

theorem exists_gram_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n r s : ℕ) (X : Spc F E n), X.IsHerm σ B r s →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∃ JS : GL (Fin n) L, JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι P X.J ∧
        ∀ i j, σL ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i := by
  intro F E _ _ _ _ _ σ B _ v w _ n r s X hX L _ _ ϖ σL q ι hun hinj himg hmul hσ hint P hP
  have hint' : ∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ intAt (E := E) v := hint
  have hPPi : (P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 :=
    Units.mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = 1 :=
    Units.inv_mul P
  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L) with hPm
  set Pi' : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPi
  have hσσ : ∀ x, σL (σL x) = x := hun.1
  have hσint : ∀ x, x ∈ Formalism.UG.intL L → σL x ∈ Formalism.UG.intL L := fun x hx => by
    unfold Formalism.UG.intL at hx ⊢
    rw [Valuation.mem_integer_iff] at hx ⊢
    rw [hun.2.1]; exact hx

  have hcol : ∀ {k : ℕ} (N : Matrix (Fin n) (Fin k) L) (j : Fin k),
      (fun i => ι (N i j)) ∈ GlobalTheory.InertSph.latAt X v → ∀ a, (Pi' * N) a j ∈ Formalism.UG.intL L := by
    intro k N j hN
    refine (hP (fun a => (Pi' * N) a j)).2 ?_
    convert hN using 1
    ext i
    congr 1
    have : (Pm * (Pi' * N)) i j = N i j := by rw [← Matrix.mul_assoc, hPPi, Matrix.one_mul]
    rw [← this]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hcolP : ∀ i, (fun k => ι (Pm k i)) ∈ GlobalTheory.InertSph.latAt X v := by
    intro i
    have := (hP (Pi.single i 1)).1 (fun a => by
      by_cases h : a = i
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
    convert this using 1
    ext k
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

  have hdet := GlobalTheory.InertSelfDual.det_ne_zero_of_herm σ B hX
  obtain ⟨k, S, T, hS, hT, hTS⟩ := GlobalTheory.InertSelfDual.exists_formFrame σ X.J hdet X.L hX.lat
    (fun y hy => (hX.dual y).2 fun x hx => by
      obtain ⟨r, hr⟩ := hy x hx
      rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
  have hframe : tJ ι T * (tJ ι X.J * (tJ ι S).map σL)ᵀ = 1 := by
    rw [← tJ_map himg hmul hinj σ σL hσ, ← tJ_mul himg hmul hinj, ← tJ_transpose himg hmul, ← tJ_mul himg hmul hinj, hTS,
      tJ_one himg hmul hinj]
  have hTA : tJ ι X.J * ((tJ ι S).map σL * (tJ ι T)ᵀ) = 1 := by
    have := congrArg Matrix.transpose hframe
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    rw [← Matrix.mul_assoc]; exact this

  have hGdef : gram σL ι P X.J = Pmᵀ * tJ ι X.J * Pm.map σL := rfl
  have hσP : Pm.map σL * Pi'.map σL = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGH : gram σL ι P X.J * ((Pi' * tJ ι S).map σL * (Pi' * tJ ι T)ᵀ) = 1 := by
    rw [hGdef]
    calc Pmᵀ * tJ ι X.J * Pm.map σL * ((Pi' * tJ ι S).map σL * (Pi' * tJ ι T)ᵀ)
        = Pmᵀ * (tJ ι X.J * (Pm.map σL * Pi'.map σL) * ((tJ ι S).map σL * (tJ ι T)ᵀ)) * Pi'ᵀ := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hσP, Matrix.mul_one, hTA, Matrix.mul_one, ← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have hHG : ((Pi' * tJ ι S).map σL * (Pi' * tJ ι T)ᵀ) * gram σL ι P X.J = 1 := mul_eq_one_comm.1 hGH

  have hGint : ∀ i j, gram σL ι P X.J i j ∈ Formalism.UG.intL L := by
    intro i j
    rw [hint']
    have : ι (gram σL ι P X.J i j) = hA σ X.J (fun k => ι (Pm k i)) (fun k => ι (Pm k j)) := by
      rw [hGdef]
      simp only [hA, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, hmul,
        tJ_spec himg hmul, hσ, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_assoc (ι (Pm a i)), mul_one_right himg hmul]
    rw [this]; exact hA_mem σ B X hX v (hcolP i) (hcolP j)

  have h1mem : ι 1 ∈ intAt (E := E) v := (hint' 1).1 (one_mem _)
  have hXs : ∀ a j, (Pi' * tJ ι S) a j ∈ Formalism.UG.intL L := fun a j => hcol (tJ ι S) j (by
    have : (fun i => ι (tJ ι S i j)) = fun i => ι 1 * inclR (F := F) (AF F) (S i j) :=
      funext fun i => tJ_spec himg hmul S i j
    rw [this]; exact mul_lat_mem X v h1mem (hS j)) a
  have hXt : ∀ a j, (Pi' * tJ ι T) a j ∈ Formalism.UG.intL L := fun a j => hcol (tJ ι T) j (by
    have : (fun i => ι (tJ ι T i j)) = fun i => ι 1 * inclR (F := F) (AF F) (T i j) :=
      funext fun i => tJ_spec himg hmul T i j
    rw [this]; exact mul_lat_mem X v h1mem (hT j)) a
  have hHint : ∀ i j, ((Pi' * tJ ι S).map σL * (Pi' * tJ ι T)ᵀ) i j ∈ Formalism.UG.intL L := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    exact sum_mem fun l _ => mul_mem (hσint _ (hXs i l)) (hXt j l)

  have hJσ : X.J.map σ = X.Jᵀ := by ext i j; exact hX.herm j i
  have hTmσ : (tJ ι X.J).map σL = (tJ ι X.J)ᵀ := by
    rw [← tJ_map himg hmul hinj σ σL hσ, hJσ, tJ_transpose himg hmul]
  have hσσf : (⇑σL ∘ ⇑σL) = id := funext hσσ
  have hGσ : (gram σL ι P X.J).map σL = (gram σL ι P X.J)ᵀ := by
    rw [hGdef]
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, hTmσ, Matrix.map_map, hσσf,
      Matrix.map_id, Matrix.transpose_transpose, Matrix.mul_assoc]
  set G := gram σL ι P X.J with hG
  set H := (Pi' * tJ ι S).map σL * (Pi' * tJ ι T)ᵀ with hH
  have hHσ : H.map σL = Hᵀ := by
    have h1 : Gᵀ * H.map σL = 1 := by
      rw [← hGσ, ← Matrix.map_mul, hGH, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Hᵀ * Gᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
    calc H.map σL = (Hᵀ * Gᵀ) * H.map σL := by rw [h2, Matrix.one_mul]
      _ = Hᵀ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  let JS : GL (Fin n) L := ⟨H, G, hHG, hGH⟩
  refine ⟨JS, ?_, rfl, fun i j => congrFun (congrFun hHσ i) j⟩
  let Ho : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := Matrix.of fun i j => ⟨H i j, hHint i j⟩
  let Go : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := Matrix.of fun i j => ⟨G i j, hGint i j⟩
  have hinjM : Function.Injective (RingHom.mapMatrix (m := Fin n) (Formalism.UG.intL L).subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hHo : RingHom.mapMatrix (m := Fin n) (Formalism.UG.intL L).subtype Ho = H := by ext i j; rfl
  have hGo : RingHom.mapMatrix (m := Fin n) (Formalism.UG.intL L).subtype Go = G := by ext i j; rfl
  have e1 : Ho * Go = 1 := hinjM (by rw [map_mul, hHo, hGo, hHG, map_one])
  have e2 : Go * Ho = 1 := hinjM (by rw [map_mul, hHo, hGo, hGH, map_one])
  refine ⟨⟨Ho, Go, e1, e2⟩, ?_⟩
  apply Units.ext
  exact hHo

end GlobalTheory.InertGram
