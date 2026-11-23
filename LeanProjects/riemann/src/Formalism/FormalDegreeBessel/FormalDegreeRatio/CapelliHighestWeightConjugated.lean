import Formalism.FormalDegreeBessel.StatementIO
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOCentral
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Transport

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ioh_exp_conj (P Q X : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    NormedSpace.exp (P * X * Q) = P * NormedSpace.exp X * Q := by
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨P, Q, hPQ, hQP⟩
  exact Matrix.exp_units_conj U X

lemma ioh_rdV (P Q X x : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    RdV X f x = RdV (P * X * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold RdV
  congr 1
  funext t
  have h1 : ((t : ℂ) • (P * X * Q)) = P * ((t : ℂ) • X) * Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, ioh_exp_conj P Q _ hQP hPQ]
  congr 1
  have e : Q * (P * x * Q * (P * NormedSpace.exp ((t : ℂ) • X) * Q)) * P
      = (Q * P) * x * (Q * P) * NormedSpace.exp ((t : ℂ) • X) * (Q * P) := by
    simp only [Matrix.mul_assoc]
  rw [e, hQP]; simp

lemma ioh_Hinv (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) : H⁻¹ = Q * Jm ε * Qᴴ := by
  apply Matrix.inv_eq_right_inv
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = Pᴴ * Qᴴ := by
        rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
    _ = 1 := hc

lemma ioh_conj_part (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * (H⁻¹ * Zᴴ * H) * Q = Jm ε * (P * Z * Q)ᴴ * Jm ε := by
  rw [ioh_Hinv ε H P Q hQP hPQ hH, hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul, Matrix.mul_one]

lemma ioh_hpart1 (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * hpart1 H Z * Q = cpart1 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart1 cpart1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← h]

lemma ioh_hpart2 (ε : Fin n → Bool) (H P Q Z : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) :
    P * hpart2 H Z * Q = cpart2 ε (P * Z * Q) := by
  have h := ioh_conj_part ε H P Q Z hQP hPQ hH
  unfold hpart2 cpart2
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← h]

lemma ioh_EabH_eq (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (x : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b f x = EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold EabH EcV
  rw [ioh_rdV P Q _ x f hQP hPQ, ioh_rdV P Q (hpart2 H _) x f hQP hPQ,
    ioh_hpart1 ε H P Q _ hQP hPQ hH, ioh_hpart2 ε H P Q _ hQP hPQ hH]

lemma ioh_EabH_fun (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) :
    (fun y => EabH H a b f (Q * y * P)) =
      EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) := by
  funext y
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH]
  congr 1
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp

lemma ioh_inUJ (ε : Fin n → Bool) (H P Q g : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hg : inUH H g) : inUJ ε (P * g * Q) := by
  unfold inUH at hg
  unfold inUJ
  have hc : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  calc (P * g * Q)ᴴ * Jm ε * (P * g * Q) = Qᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * Pᴴ * Jm ε * (P * Q) := by rw [← hH, hg, hH]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hc, hPQ]; simp

lemma ioh_inUH (ε : Fin n → Bool) (H P Q x : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hx : inUJ ε x) : inUH H (Q * x * P) := by
  unfold inUJ at hx
  unfold inUH
  rw [hH]
  have e : (Q * x * P)ᴴ * (Pᴴ * Jm ε * P) * (Q * x * P)
      = Pᴴ * (xᴴ * ((P * Q)ᴴ * Jm ε * (P * Q)) * x) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hPQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hx]

lemma ioh_single (P Q : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * Q) c d = P c a * Q b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

lemma ioh_smooth (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hf : SmoothOnH H f) : SmoothOnGV ε (fun x => f (Q * x * P)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf (Q * g₀ * P) (ioh_inUH ε H P Q g₀ hPQ hH hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.mulLeft ℝ Q).comp (LinearMap.mulRight ℝ P)).toContinuousLinearMap
  have hL : ∀ x, L x = Q * x * P := by
    intro x; simp [L, Matrix.mul_assoc]
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hg₀U, ?_, ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun x hx => hx)
  · intro x hx hxJ
    simp only [Set.mem_preimage, hL] at hx
    simp only [hL]
    exact hfF _ hx (ioh_inUH ε H P Q x hPQ hH hxJ)

end Transport

theorem conjugated_generator_transport : EabHTransport := by
  intro n ε E _ _ H P Q f a b g hQP hPQ hH hsm hg
  rw [ioh_EabH_eq ε H P Q f a b hQP hPQ hH g,
    ecSumV n ε E _ _ _ hsm (ioh_inUJ ε H P Q g hPQ hH hg)]
  simp only [ioh_single]

theorem conjugated_generator_gl_relation : EabHGl := by
  intro n ε E _ _ H P Q f a b c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  rw [ioh_EabH_eq ε H P Q (EabH H c d f) a b hQP hPQ hH g, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q (EabH H a b f) c d hQP hPQ hH g, ioh_EabH_fun ε H P Q f a b hQP hPQ hH,
    vector_complexified_derivative_commutator rdLinV rdBracketV rdSmoothV ε _ _ _ _ hsm hg']
  have hQPX : ∀ X : Matrix (Fin n) (Fin n) ℂ, Q * (P * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  have hm2 : P * Matrix.single a b (1 : ℂ) * Q * (P * Matrix.single c d 1 * Q) -
      P * Matrix.single c d 1 * Q * (P * Matrix.single a b 1 * Q) =
      P * (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 -
        Matrix.single c d 1 * Matrix.single a b 1) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hQPX]
  rw [hm2, hm, Matrix.mul_sub, Matrix.sub_mul, vector_complexified_derivative_sub rdLinV hsm hg']
  split_ifs <;> simp only [Matrix.mul_zero, Matrix.zero_mul, vector_complexified_derivative_zero, sub_zero, zero_sub,
    ioh_EabH_eq ε H P Q f _ _ hQP hPQ hH g]

section Central

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def IOHRepr (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)) : Prop :=
  ∀ (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (x : ioS ε E), IORep F x.1 →
    IORep (Eop a b F) (Ealg a b x).1

lemma ioh_Tm_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {F : Matrix (Fin n) (Fin n) ℂ → E} {x : ioS ε E} (h : IORep F x.1) (u : ℂ)
    (a b : Fin n) : IORep (Top Eop u a b F) (Tm Ealg u a b x).1 := by
  intro g hg
  have he := hR a b F x h g hg
  unfold Top Tm
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, he, h g hg]
  · rw [if_neg hab, if_neg hab, zero_add, zero_add, he]

lemma ioh_foldr_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top Eop p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact ioh_Tm_rep hR ih _ _ _

lemma ioh_qminor_apply {t : ℕ} (Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E))
    (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor Ealg a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.intCast_apply, List.map_ofFn, Int.cast_smul_eq_zsmul]
  rfl

lemma ioh_qminor_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp Eop a b u F) (qminor Ealg a b u x).1 := by
  intro g hg
  rw [ioh_qminor_apply]
  have hs := io_rep_sum (fun σ : Equiv.Perm (Fin t) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => ioh_foldr_rep hR (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h) g hg
  rw [← hs]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, List.map_ofFn]
  rfl

variable (ε E) in

def iohE (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : Module.End ℂ (ioS ε E) :=
  ∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d

lemma ioh_repr (P Q : Matrix (Fin n) (Fin n) ℂ) :
    IOHRepr (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) (iohE ε E P Q) := by
  intro a b F x h g hg
  have hF : SmoothOnGV ε F :=
    io_smooth_congr (fun g' hg' => (io_rep_ext x g' hg').trans (h g' hg').symm) (io_mem_smooth x)
  show EcV ε (P * Matrix.single a b 1 * Q) F g =
    (((∑ c, ∑ d, (P c a * Q b d) • ioE ε E c d) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩
  rw [ecSumV n ε E F _ g hF hg]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, ioh_single]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [ioE_rep h c d g hg]

lemma ioh_gl (hAd : GlRelAd) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) :
    GlRel (iohE ε E P Q) :=
  hAd (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E) hQP

end Central

section Conj

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ioh_PQ (P Q y : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) : P * (Q * y * P) * Q = y := by
  have : P * (Q * y * P) * Q = (P * Q) * y * (P * Q) := by simp only [Matrix.mul_assoc]
  rw [this, hPQ]; simp

lemma ioh_QP (P Q y : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) : Q * (P * y * Q) * P = y := by
  have : Q * (P * y * Q) * P = (Q * P) * y * (Q * P) := by simp only [Matrix.mul_assoc]
  rw [this, hQP]; simp

lemma ioh_Top (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (u : ℂ) (a b : Fin n)
    (R : Matrix (Fin n) (Fin n) ℂ → E) :
    Top (EabH H) u a b (fun x => R (P * x * Q)) =
      fun x => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) u a b R (P * x * Q) := by
  funext x
  unfold Top
  rw [ioh_EabH_eq ε H P Q _ a b hQP hPQ hH x]
  have : (fun y => (fun x => R (P * x * Q)) (Q * y * P)) = R := by
    funext y; simp only [ioh_PQ P Q y hPQ]
  rw [this]

lemma ioh_foldr (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (l : List (ℂ × Fin n × Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (l.map fun p => Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) G =
      fun x => (l.map fun p => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) p.1 p.2.1 p.2.2).foldr
        (fun T h => T h) (fun y => G (Q * y * P)) (P * x * Q) := by
  induction l with
  | nil =>
    funext x
    simp only [List.map_nil, List.foldr_nil, ioh_QP P Q x hQP]
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ioh_Top ε H P Q hQP hPQ hH]

lemma ioh_qminor (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) (x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) α β u G x =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P))
        (P * x * Q) := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∀ (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)),
      (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (α (σ k)) (β k)) =
        (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), α (σ k), β k)).map
          fun p => Top Eop p.1 p.2.1 p.2.2 := by
    intro Eop; rw [List.map_ofFn]; rfl
  rw [e1, e1, ioh_foldr ε H P Q hQP hPQ hH]

lemma ioh_qminor_fun (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (fun y => qminorOp (EabH H) α β u G (Q * y * P)) =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P)) := by
  funext y
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_PQ P Q y hPQ]

end Conj

theorem capCentralH_of (hAd : GlRelAd) : CapCentralH := by
  intro n ε E _ _ H P Q f u c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q _ c d hQP hPQ hH g, ioh_qminor_fun ε H P Q hQP hPQ hH]
  have h1 := ioh_qminor_rep hR id id u (hR c d _ x hx) _ hg'
  have h2 := hR c d _ _ (ioh_qminor_rep hR id id u hx) _ hg'
  have hc := qDetCentral (Module.End ℂ (ioS ε E)) n (iohE ε E P Q) (ioh_gl hAd P Q hQP) u c d
  dsimp only at h1 h2
  rw [h1, h2]
  unfold qdet at hc
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc

theorem capHWH_of (hAd : GlRelAd) : CapHWH := by
  intro n ε E _ _ H P Q f ν hQP hPQ hH hf hhw g hg u
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  have hEW : ∀ a b y, EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) y =
      EabH H a b f (Q * y * P) := fun a b y =>
    (congrFun (ioh_EabH_fun ε H P Q f a b hQP hPQ hH) y).symm
  have hHW : IsHW (iohE ε E P Q) ν x := by
    refine ⟨fun a => io_rep_unique (hR a a _ x hx) (fun g' hg' => ?_),
      fun a b hab => io_rep_unique (hR a b _ x hx) (fun g' hg' => ?_)⟩
    · show EcV ε (P * Matrix.single a a 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).1 a, Submodule.coe_smul,
        Pi.smul_apply, ← hx g' hg']
    · show EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).2 a b hab]; rfl
  have h1 := ioh_qminor_rep hR id id u hx _ hg'
  have h2 := qDetHW (ioS ε E) n (iohE ε E P Q) ν x (ioh_gl hAd P Q hQP) hHW u
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1]
  unfold qdet at h2
  rw [h2]
  show (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x.1 ⟨_, hg'⟩ = _
  rw [← hx _ hg']
  show _ • f (Q * (P * g * Q) * P) = _
  rw [ioh_QP P Q g hQP]

theorem capelli_central_conjugated : CapCentralH := capCentralH_of gl_relation_adjoint_holds

theorem capelli_highest_weight_conjugated : CapHWH := capHWH_of gl_relation_adjoint_holds

end Formalism.QuantumDeterminants
