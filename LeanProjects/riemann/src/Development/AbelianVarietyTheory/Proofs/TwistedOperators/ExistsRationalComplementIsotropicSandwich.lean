import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoCompl

section Core

variable {E : Type} [Field E]

theorem exists_left_inv {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (S : Matrix m n E) (h : Function.Injective S.mulVecLin) : ∃ L : Matrix n m E, L * S = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective S.mulVecLin (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_right_inv {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (S : Matrix m n E) (h : Function.Surjective S.mulVecLin) : ∃ L : Matrix n m E, S * L = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective S.mulVecLin (LinearMap.range_eq_top.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_left_inv_of_rank {w a : ℕ} (P : Matrix (Fin w) (Fin a) E) (h : P.rank = a) :
    ∃ L : Matrix (Fin a) (Fin w) E, L * P = 1 := by
  refine exists_left_inv P ?_
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [Matrix.rank] at h
  rw [h, Module.finrank_fin_fun] at e
  omega

theorem exists_right_inv_of_rank {b v : ℕ} (Q : Matrix (Fin b) (Fin v) E) (h : Q.rank = b) :
    ∃ L : Matrix (Fin v) (Fin b) E, Q * L = 1 := by
  refine exists_right_inv Q ?_
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank, h, Module.finrank_fin_fun]

end Core

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

section Core2

variable {E R : Type} [Field E] [CommRing R] {k w v a b : ℕ}

def smat (B : Fin k → Matrix (Fin w) (Fin v) E) (P : Matrix (Fin w) (Fin a) E) (Q : Matrix (Fin b) (Fin v) E) :
    Matrix (Fin w × Fin v) (Fin k ⊕ Fin a × Fin b) E :=
  Matrix.of fun pq j => Sum.elim (fun i => B i pq.1 pq.2) (fun rs => P pq.1 rs.1 * Q rs.2 pq.2) j

theorem smat_mulVec (ι : E →+* R) (B : Fin k → Matrix (Fin w) (Fin v) E) (P : Matrix (Fin w) (Fin a) E)
    (Q : Matrix (Fin b) (Fin v) E) (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R) (p : Fin w) (q : Fin v) :
    ((smat B P Q).map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2)) (p, q) =
      (∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι) p q := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, smat, Matrix.map_apply,
    Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, map_mul, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring

theorem sandwich_single_apply (f : Matrix (Fin w) (Fin w) E) (g : Matrix (Fin v) (Fin v) E) (p p' : Fin w)
    (q q' : Fin v) : (f * Matrix.single p' q' (1 : E) * g) p q = f p p' * g q' q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

end Core2

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

theorem proj_sum {E R : Type} [Field E] [CommRing R] {w v : ℕ} (ι : E →+* R) (f : Matrix (Fin w) (Fin w) E)
    (g : Matrix (Fin v) (Fin v) E) (x : Matrix (Fin w) (Fin v) R) (hfx : f.map ι * x * g.map ι = 0) (p : Fin w) (q : Fin v) :
    ∑ pq' : Fin w × Fin v, ι ((Matrix.single pq'.1 pq'.2 (1 : E) - f * Matrix.single pq'.1 pq'.2 (1 : E) * g) p q) *
      x pq'.1 pq'.2 = x p q := by
  have h2 := congrFun (congrFun hfx p) q
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Finset.sum_mul] at h2
  simp only [Matrix.sub_apply, sandwich_single_apply, map_sub, sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type,
    map_mul]
  have h3 : ∑ p' : Fin w, ∑ q' : Fin v, ι (Matrix.single p' q' (1 : E) p q) * x p' q' = x p q := by
    simp only [Matrix.single_apply, ite_and, apply_ite ι, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single p (fun p' hp' => by simp [hp']), Fintype.sum_eq_single q (fun q' hq' => by simp [hq'])]
    simp
  rw [h3, Finset.sum_comm, sub_eq_self]
  rw [← h2]
  exact Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun p' _ => by ring

theorem proj_ker {E : Type} [Field E] {w v a b : ℕ} (A : Matrix (Fin a) (Fin w) E) (C : Matrix (Fin v) (Fin b) E)
    (A' : Matrix (Fin w) (Fin a) E) (C' : Matrix (Fin b) (Fin v) E) (hA : A * A' = 1) (hC : C' * C = 1)
    (γ : Matrix (Fin w) (Fin v) E) : A * (γ - A' * A * γ * (C * C')) * C = 0 := by
  have e : A * (A' * A * γ * (C * C')) * C = A * A' * A * γ * C * (C' * C) := by simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, e, hA, hC, Matrix.one_mul, Matrix.mul_one, sub_self]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

section Core3

variable {E R : Type} [Field E] [CommRing R] {w v a b : ℕ}

theorem map_id_eq {m n : Type} (M : Matrix m n E) : M.map (RingHom.id E) = M := by ext; rfl

theorem core (ι : E →+* R) (P : Matrix (Fin w) (Fin a) E) (Q : Matrix (Fin b) (Fin v) E)
    (A : Matrix (Fin a) (Fin w) E) (C : Matrix (Fin v) (Fin b) E)
    (A' : Matrix (Fin w) (Fin a) E) (C' : Matrix (Fin b) (Fin v) E)
    (P' : Matrix (Fin a) (Fin w) E) (Q' : Matrix (Fin v) (Fin b) E)
    (hA : A * A' = 1) (hC : C' * C = 1) (hP : P' * P = 1) (hQ : Q * Q' = 1)
    (hiso : ∀ y : Matrix (Fin a) (Fin b) E, A * (P * y * Q) * C = 0) :
    ∃ (k : ℕ) (B : Fin k → Matrix (Fin w) (Fin v) E),
      (∀ i, A * B i * C = 0) ∧
      (∀ κ : Matrix (Fin w) (Fin v) E, A * κ * C = 0 →
        ∃ (c : Fin k → E) (y : Matrix (Fin a) (Fin b) E), κ = ∑ i, c i • B i + P * y * Q) ∧
      (∀ x : Matrix (Fin w) (Fin v) R, A.map ι * x * C.map ι = 0 →
        ∃ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R), x = ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι) ∧
      (∀ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R),
        ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι = 0 → z = 0 ∧ y = 0) ∧
      (∀ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R) (γ : Matrix (Fin w) (Fin v) E),
        ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι = γ.map ι →
          (∃ c : Fin k → E, z = ι ∘ c) ∧ ∃ y₀ : Matrix (Fin a) (Fin b) E, y = y₀.map ι) := by
  classical
  let K : Submodule E (Matrix (Fin w) (Fin v) E) :=
    { carrier := {κ | A * κ * C = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_smul, Matrix.smul_mul, hx, smul_zero] }
  let Xs : Submodule E (Matrix (Fin w) (Fin v) E) :=
    { carrier := {x | ∃ y : Matrix (Fin a) (Fin b) E, x = P * y * Q}
      add_mem' := fun {x x'} hx hx' => by
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [hy, hy', Matrix.mul_add, Matrix.add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c x hx => by
        obtain ⟨y, hy⟩ := hx
        exact ⟨c • y, by rw [hy, Matrix.mul_smul, Matrix.smul_mul]⟩ }
  have hXK : Xs ≤ K := by
    rintro _ ⟨y, rfl⟩
    exact hiso y
  obtain ⟨Cm, hCm⟩ := Submodule.exists_isCompl Xs
  have hsup : Xs ⊔ (Cm ⊓ K) = K := by
    rw [← sup_inf_assoc_of_le Cm hXK, hCm.sup_eq_top, top_inf_eq]
  have hinf : ∀ x, x ∈ Xs → x ∈ Cm ⊓ K → x = 0 := fun x h1 h2 => by
    have : x ∈ Xs ⊓ Cm := ⟨h1, h2.1⟩
    rwa [hCm.inf_eq_bot, Submodule.mem_bot] at this
  let bZ := Module.finBasis E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))
  let B : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → Matrix (Fin w) (Fin v) E :=
    fun i => (bZ i : Matrix (Fin w) (Fin v) E)
  have hBZ : ∀ c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E, ∑ i, c i • B i = ((∑ i, c i • bZ i : (Cm ⊓ K : Submodule E _)) : Matrix (Fin w) (Fin v) E) :=
    fun c => by simp [B, Submodule.coe_sum]
  have hind : ∀ (c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E) (y : Matrix (Fin a) (Fin b) E), ∑ i, c i • B i + P * y * Q = 0 → c = 0 ∧ y = 0 := by
    intro c y h
    have h1 : ∑ i, c i • B i = P * (-y) * Q := by
      rw [eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, Matrix.neg_mul]
    have h0 : ∑ i, c i • B i = 0 := hinf _ ⟨-y, h1⟩ (by rw [hBZ]; exact Subtype.property _)
    have hc : (∑ i, c i • bZ i : (Cm ⊓ K : Submodule E _)) = 0 := Subtype.ext (by rw [← hBZ]; exact h0)
    refine ⟨funext fun i => Fintype.linearIndependent_iff.1 bZ.linearIndependent c hc i, ?_⟩
    rw [h0, zero_add] at h
    calc y = (P' * P) * y * (Q * Q') := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]
      _ = P' * (P * y * Q) * Q' := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have hspan : ∀ κ : Matrix (Fin w) (Fin v) E, A * κ * C = 0 →
      ∃ (c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E) (y : Matrix (Fin a) (Fin b) E), κ = ∑ i, c i • B i + P * y * Q := by
    intro κ hκ
    have hκ' : κ ∈ Xs ⊔ (Cm ⊓ K) := by rw [hsup]; exact hκ
    obtain ⟨x1, hx1, z1, hz1, hsum⟩ := Submodule.mem_sup.1 hκ'
    obtain ⟨y, rfl⟩ := hx1
    refine ⟨fun i => bZ.repr ⟨z1, hz1⟩ i, y, ?_⟩
    rw [hBZ, bZ.sum_repr, ← hsum, add_comm]

  let Sm := smat B P Q
  have hinj : Function.Injective Sm.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : Sum.elim (u ∘ Sum.inl)
        (fun rs : Fin a × Fin b => (Matrix.of fun r s => u (Sum.inr (r, s)) : Matrix (Fin a) (Fin b) E) rs.1 rs.2) = u := by
      funext j; rcases j with i | ⟨r, s⟩ <;> rfl
    have h0 : ∑ i, (u ∘ Sum.inl) i • B i + P * (Matrix.of fun r s => u (Sum.inr (r, s))) * Q = 0 := by
      ext p q
      have := smat_mulVec (RingHom.id E) B P Q (u ∘ Sum.inl) (Matrix.of fun r s => u (Sum.inr (r, s))) p q
      simp only [map_id_eq] at this
      rw [← this, hu']
      exact congrFun hu (p, q)
    obtain ⟨h1, h2⟩ := hind (u ∘ Sum.inl) (Matrix.of fun r s => u (Sum.inr (r, s))) h0
    funext j
    rcases j with i | ⟨r, s⟩
    · exact congrFun h1 i
    · exact congrFun (congrFun h2 r) s
  obtain ⟨Rm, hRm⟩ := exists_left_inv Sm hinj
  have hleft : ∀ u : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) ⊕ Fin a × Fin b → R, u = Rm.map ι *ᵥ (Sm.map ι *ᵥ u) := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hRm, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.one_mulVec]
  refine ⟨_, B, fun i => (bZ i).2.2, hspan, ?_, ?_, ?_⟩
  · intro x hx
    let κ : Fin w × Fin v → Matrix (Fin w) (Fin v) E := fun pq' =>
      Matrix.single pq'.1 pq'.2 (1 : E) - A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * (C * C')
    have hκK : ∀ pq', A * κ pq' * C = 0 := fun pq' => by
      have e : A * (A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * (C * C')) * C =
          A * A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * C * (C' * C) := by simp only [Matrix.mul_assoc]
      simp only [κ]
      rw [Matrix.mul_sub, Matrix.sub_mul, e, hA, hC, Matrix.one_mul, Matrix.mul_one, sub_self]
    choose cc yy hcy using fun pq' => hspan (κ pq') (hκK pq')
    let Cm2 : Matrix (Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) ⊕ Fin a × Fin b)
        (Fin w × Fin v) E := Matrix.of fun j pq' => Sum.elim (cc pq') (fun rs => yy pq' rs.1 rs.2) j
    let Pm : Matrix (Fin w × Fin v) (Fin w × Fin v) E := Matrix.of fun pq pq' => κ pq' pq.1 pq.2
    have hPm : Sm * Cm2 = Pm := by
      ext pq pq'
      have := smat_mulVec (RingHom.id E) B P Q (cc pq') (yy pq') pq.1 pq.2
      simp only [map_id_eq] at this
      rw [← hcy pq'] at this
      exact this
    have hfx : (A' * A).map ι * x * (C * C').map ι = 0 := by
      calc (A' * A).map ι * x * (C * C').map ι = A'.map ι * (A.map ι * x * C.map ι) * C'.map ι := by
            rw [Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hx, Matrix.mul_zero, Matrix.zero_mul]
    have hPx : Pm.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2) = fun pq => x pq.1 pq.2 := by
      funext pq
      exact proj_sum ι (A' * A) (C * C') x hfx pq.1 pq.2
    refine ⟨fun i => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inl i),
      Matrix.of fun r s => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inr (r, s)), ?_⟩
    ext p q
    rw [← smat_mulVec]
    have hu' : Sum.elim (fun i => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inl i))
        (fun rs : Fin a × Fin b => (Matrix.of fun r s => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2))
          (Sum.inr (r, s)) : Matrix (Fin a) (Fin b) R) rs.1 rs.2) =
        Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2) := by
      funext j; rcases j with i | ⟨r, s⟩ <;> rfl
    rw [hu', Matrix.mulVec_mulVec, ← Matrix.map_mul, hPm, hPx]
  · intro z y h
    have hS : Sm.map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2) = 0 := funext fun pq => by
      rw [smat_mulVec, h]; rfl
    have hu := hleft (Sum.elim z (fun rs => y rs.1 rs.2))
    rw [hS, Matrix.mulVec_zero] at hu
    exact ⟨funext fun i => congrFun hu (Sum.inl i), Matrix.ext fun r s => congrFun hu (Sum.inr (r, s))⟩
  · intro z y γ h
    have hS : Sm.map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2) = ι ∘ (fun pq : Fin w × Fin v => γ pq.1 pq.2) :=
      funext fun pq => by rw [smat_mulVec, h]; rfl
    have hu := hleft (Sum.elim z (fun rs => y rs.1 rs.2))
    rw [hS] at hu
    have hu2 : ∀ j, Sum.elim z (fun rs => y rs.1 rs.2) j =
        ι ((Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) j) := fun j => by
      rw [RingHom.map_mulVec, ← hu]
    exact ⟨⟨fun i => (Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) (Sum.inl i), funext fun i => hu2 (Sum.inl i)⟩,
      Matrix.of fun r s => (Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) (Sum.inr (r, s)),
      Matrix.ext fun r s => hu2 (Sum.inr (r, s))⟩

end Core3

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

theorem trace_nondeg {D : D7} (t : AE D)
    (h : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e * t) = 0) : t = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨e₀, he₀⟩ := GlobalTheory.RatAnnih.tensor_rat t fun e => ⟨0, by rw [map_zero]; exact h e⟩
  by_contra hne
  have he : e₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [he₀, TensorProduct.tmul_zero])
  have h1 := h e₀⁻¹
  rw [he₀, show incA D e₀⁻¹ = (1 : AF D.host.F) ⊗ₜ[D.host.F] e₀⁻¹ from rfl, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, inv_mul_cancel₀ he, GlobalTheory.LatVac.trace_tmul, one_mul, ← map_one (algebraMap D.host.F D.host.E),
    Algebra.trace_algebraMap, D.sp.cm.deg2] at h1
  have h2 := NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F (h1.trans (map_zero _).symm)
  norm_num at h2

theorem trace_single_mul {D : D7} {a b : ℕ} (r : Fin a) (s : Fin b) (t : AE D) (M : Mx D a b) :
    (Matrix.single s r t * M).trace = t * M r s := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms

variable {D : D7} (V W : HSp D)

theorem hO_add_right (x y y' : WO V W) : hO V W x (y + y') = hO V W x y + hO V W x y' := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, adj_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

theorem hO_sub_right (x y y' : WO V W) : hO V W x (y - y') = hO V W x y - hO V W x y' := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, adj_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]

theorem hO_sub_left (x x' y : WO V W) : hO V W (x - x') y = hO V W x y - hO V W x' y := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub]

theorem hO_emb {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x : WO V W) (y : Mx D a b) :
    hO V W x (GlobalTheory.IsoMean.emb V W P Q y) =
      (adj y * ((Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D))).trace := by
  rw [hO_eq_trace]
  have e : adj (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.MixModel.rat Qᴴ ⬝ adj y ⬝ GlobalTheory.MixModel.rat Pᴴ := by
    show adj (GlobalTheory.MixModel.rat P ⬝ y ⬝ GlobalTheory.MixModel.rat Q) = _
    rw [adj_mul, adj_mul, ← rat_conjTranspose, ← rat_conjTranspose, Matrix.mul_assoc]
  rw [e]
  calc (giA V ⬝ (GlobalTheory.MixModel.rat Qᴴ ⬝ adj y ⬝ GlobalTheory.MixModel.rat Pᴴ ⬝ (gA W ⬝ x))).trace
      = ((giA V ⬝ GlobalTheory.MixModel.rat Qᴴ) ⬝ (adj y ⬝ GlobalTheory.MixModel.rat Pᴴ ⬝ gA W ⬝ x)).trace := by simp only [Matrix.mul_assoc]
    _ = ((adj y ⬝ GlobalTheory.MixModel.rat Pᴴ ⬝ gA W ⬝ x) ⬝ (giA V ⬝ GlobalTheory.MixModel.rat Qᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = _ := by
      simp only [giA, gA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]

end Forms

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms2

variable {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
  (Q : Matrix (Fin b) (Fin V.rank) D.host.E)

theorem T_zero_of_orth (x : WO V W) (h : ∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) :
    (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0 := by
  refine Matrix.ext fun r s => trace_nondeg _ fun e => ?_
  have h1 := h (Matrix.single r s (incA D (star (D.host.xi0⁻¹ * e))))
  have h2 : adj (Matrix.single r s (incA D (star (D.host.xi0⁻¹ * e))) : Mx D a b) =
      Matrix.single s r (incA D (D.host.xi0⁻¹ * e)) := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : r = j <;> by_cases h2 : s = i <;>
      simp only [h1, h2, and_true, true_and, and_false, false_and, if_true, if_false, map_zero,
        GlobalTheory.DualPairCheck.cA_incA, star_star]
  rw [symplO_eq, hO_emb, h2, trace_single_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] at h1
  exact h1

theorem orth_of_T_zero (x : WO V W) (h : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0)
    (y : Mx D a b) : symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0 := by
  rw [symplO_eq, hO_emb, h, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem hO_emb_eq_zero (x : WO V W)
    (h : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0) (y : Mx D a b) :
    hO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0 := by
  rw [hO_emb, h, Matrix.mul_zero, Matrix.trace_zero]

end Forms2

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms3

variable {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
  (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (P' : Matrix (Fin a) (Fin W.rank) D.host.E)
  (Q' : Matrix (Fin V.rank) (Fin b) D.host.E)

theorem adj_f_gram : adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D)) ⬝ gA W =
    GlobalTheory.MixModel.rat (W.gram * P * P') := by
  show adj (GlobalTheory.MixModel.rat _) ⬝ GlobalTheory.MixModel.rat W.gram = _
  rw [← rat_conjTranspose, ← rat_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    gramInv_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det W), Matrix.mul_one]

theorem giA_adj_g : giA V ⬝ adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) =
    GlobalTheory.MixModel.rat (Q' * Q * V.gram⁻¹) := by
  show GlobalTheory.MixModel.rat V.gram⁻¹ ⬝ adj (GlobalTheory.MixModel.rat _) = _
  rw [← rat_conjTranspose, ← rat_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    gramInv_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (gram_isUnit_det V)]

theorem hO_proj (x γ : WO V W) :
    hO V W (GlobalTheory.IsoMean.emb V W P Q (P'.map (incA D) ⬝ x ⬝ Q'.map (incA D) : Mx D a b)) γ =
      hO V W x ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D) ⬝ γ ⬝ (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D) : WO V W) := by
  rw [hO_eq_trace, hO_eq_trace, adj_mul, adj_mul]
  have e : (giA V ⬝ (adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) ⬝ (adj γ ⬝
      adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D))) ⬝ (gA W ⬝ x)) : Mx D V.rank V.rank) =
      ((giA V ⬝ adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) : Mx D V.rank V.rank) ⬝ (adj γ : Mx D V.rank W.rank) ⬝
        (adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D)) ⬝ gA W : Mx D W.rank W.rank) ⬝ x : Mx D V.rank V.rank) := by
    simp only [Matrix.mul_assoc]
  rw [e, adj_f_gram, giA_adj_g]
  calc _ = (((giA V ⬝ (adj γ : Mx D V.rank W.rank) ⬝ GlobalTheory.MixModel.rat (W.gram * P * P') ⬝ x : Mx D V.rank V.rank)) ⬝ GlobalTheory.MixModel.rat (Q' * Q)).trace := by
        simp only [GlobalTheory.IsoMean.emb, giA, gA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]
    _ = (GlobalTheory.MixModel.rat (Q' * Q) ⬝ (giA V ⬝ (adj γ : Mx D V.rank W.rank) ⬝ GlobalTheory.MixModel.rat (W.gram * P * P') ⬝ x : Mx D V.rank V.rank)).trace :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [giA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]

end Forms3

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

theorem annih_step {D : D7} (V W : HSp D) {a b k : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (P' : Matrix (Fin a) (Fin W.rank) D.host.E)
    (Q' : Matrix (Fin V.rank) (Fin b) D.host.E) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (x : WO V W)
    (hxo : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0)
    (γ₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (c : Fin k → D.host.E) (y₁ : Matrix (Fin a) (Fin b) D.host.E)
    (hcy : γ₀ - W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram) * γ₀ * (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)) = ∑ i, c i • B i + P * y₁ * Q) :
    symplO V W (x - GlobalTheory.IsoMean.emb V W P Q (P'.map (incA D) ⬝ x ⬝ Q'.map (incA D) : Mx D a b)) (γ₀.map (incA D)) =
      symplO V W x (GlobalTheory.IsoMean.cplx V W B ((Matrix.of fun (_ : Fin 1) i => c i).map (incA D))) := by
  rw [symplO_eq, symplO_eq, hO_sub_left, hO_proj, ← hO_sub_right]
  have e : γ₀.map (incA D) - ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D) ⬝ γ₀.map (incA D) ⬝
      (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D) : WO V W) =
      GlobalTheory.IsoMean.cplx V W B ((Matrix.of fun (_ : Fin 1) i => c i).map (incA D)) +
        GlobalTheory.IsoMean.emb V W P Q (y₁.map (incA D)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub (incA D)), hcy, Matrix.map_add _ (map_add (incA D)),
      GlobalTheory.IsoMean.cplx_rat]
    simp only [Matrix.of_apply, GlobalTheory.IsoMean.emb, Matrix.map_mul]
  rw [e, hO_add_right, hO_emb_eq_zero V W P Q x hxo, add_zero]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

set_option maxHeartbeats 400000 in

theorem ratCompl : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  intro D V W a b P Q hPr hQr hiso ψ hψ
  obtain ⟨P', hP'⟩ := exists_left_inv_of_rank P hPr
  obtain ⟨Q', hQ'⟩ := exists_right_inv_of_rank Q hQr
  have hA : (Pᴴ * W.gram) * (W.gram⁻¹ * P'ᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W), ← Matrix.conjTranspose_mul, hP',
      Matrix.conjTranspose_one]
  have hC : (Q'ᴴ * V.gram) * (V.gram⁻¹ * Qᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det V), ← Matrix.conjTranspose_mul, hQ',
      Matrix.conjTranspose_one]
  have hisoR : ∀ y : Matrix (Fin a) (Fin b) D.host.E, (Pᴴ * W.gram) * (P * y * Q) * (V.gram⁻¹ * Qᴴ) = 0 := by
    intro y
    apply rat_injective
    have h := T_zero_of_orth V W P Q _ (fun y' => hiso (GlobalTheory.MixModel.rat y) y')
    rw [rat_zero, ← h]
    simp only [GlobalTheory.IsoMean.emb, GlobalTheory.MixModel.rat, Matrix.map_mul]
  obtain ⟨k, B, hB, hspan, hdec, huniq, hrat⟩ := core (incA D) P Q (Pᴴ * W.gram) (V.gram⁻¹ * Qᴴ)
    (W.gram⁻¹ * P'ᴴ) (Q'ᴴ * V.gram) P' Q' hA hC hP' hQ' hisoR
  have hce : ∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y =
      ∑ i, z 0 i • (B i).map (incA D) + P.map (incA D) * y * Q.map (incA D) := fun _ _ => rfl
  have hcplx : ∀ z : Mx D 1 k, GlobalTheory.IsoMean.cplx V W B z = ∑ i, z 0 i • (B i).map (incA D) := fun z => rfl
  have horth : ∀ z : Mx D 1 k,
      (Pᴴ * W.gram).map (incA D) * GlobalTheory.IsoMean.cplx V W B z * (V.gram⁻¹ * Qᴴ).map (incA D) = 0 := by
    intro z
    rw [hcplx, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, hB i, Matrix.map_zero _ (map_zero _),
      smul_zero]
  have h4 : ∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V →
      z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b := by
    rintro z y ⟨γ, hγ⟩
    obtain ⟨⟨c, hc⟩, y₀, hy₀⟩ := hrat (fun i => z 0 i) y γ hγ.symm
    refine ⟨⟨Matrix.of fun _ i => c i, Matrix.ext fun r i => ?_⟩, ⟨y₀, hy₀.symm⟩⟩
    rw [Subsingleton.elim r 0]
    exact (congrFun hc i).symm
  refine ⟨k, B, fun z y => orth_of_T_zero V W P Q _ (horth z) y, ?_, ?_, h4, ?_⟩
  · intro x hx
    obtain ⟨z, y, hxy⟩ := hdec x (T_zero_of_orth V W P Q x hx)
    refine ⟨(Matrix.of fun (_ : Fin 1) (i : Fin k) => z i : Mx D 1 k), y, ?_⟩
    rw [hce]
    simp only [Matrix.of_apply]
    exact hxy
  · intro z y h
    rw [hce] at h
    obtain ⟨h1, h2⟩ := huniq (fun i => z 0 i) y h
    refine ⟨Matrix.ext fun r i => ?_, h2⟩
    rw [Subsingleton.elim r 0]
    exact congrFun h1 i
  · intro z
    constructor
    · intro h
      have hx' : GlobalTheory.IsoMean.cplx V W B z - GlobalTheory.IsoMean.emb V W P Q
          (P'.map (incA D) ⬝ GlobalTheory.IsoMean.cplx V W B z ⬝ Q'.map (incA D) : Mx D a b) ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 ?_
        rintro _ ⟨γ₀, rfl⟩
        obtain ⟨c, y₁, hcy⟩ := hspan _
          (proj_ker (Pᴴ * W.gram) (V.gram⁻¹ * Qᴴ) (W.gram⁻¹ * P'ᴴ) (Q'ᴴ * V.gram) hA hC γ₀)
        have e := annih_step V W P Q P' Q' B _ (horth z) γ₀ c y₁ hcy
        exact (congrArg ψ e).trans (h _ (rat_mem _))
      have hneg : GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q
          (-(P'.map (incA D) ⬝ GlobalTheory.IsoMean.cplx V W B z ⬝ Q'.map (incA D)) : Mx D a b) =
          GlobalTheory.IsoMean.cplx V W B z - GlobalTheory.IsoMean.emb V W P Q
            (P'.map (incA D) ⬝ GlobalTheory.IsoMean.cplx V W B z ⬝ Q'.map (incA D) : Mx D a b) := by
        rw [sub_eq_add_neg]
        congr 1
        simp only [GlobalTheory.IsoMean.emb, Matrix.mul_neg, Matrix.neg_mul]
      exact (h4 z _ (hneg ▸ hx')).1
    · rintro ⟨z₀, rfl⟩ _ ⟨c₀, rfl⟩
      have hx : ∀ c : Matrix (Fin 1) (Fin k) D.host.E,
          GlobalTheory.IsoMean.cplx V W B ((incA D).toAddMonoidHom.mapMatrix c) ∈ ratL W V :=
        fun c => ⟨∑ i, c 0 i • B i, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 (hx z₀) _ (hx c₀)

end GlobalTheory.IsoCompl
