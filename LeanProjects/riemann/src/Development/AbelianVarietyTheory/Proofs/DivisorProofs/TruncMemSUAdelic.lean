import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem idem_mul (e : R) (he : e * e = e) (A B : Matrix n n R) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 + e • (A * B - 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem idem_cT (c : R →+* R) (e : R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, hc, eq_comm]

theorem idem_unitary (c : R →+* R) (e : R) (he : e * e = e) (hc : c e = e) (J A : Matrix n n R)
    (hA : Formalism.UG.cT c A * J * A = J) :
    Formalism.UG.cT c (1 + e • (A - 1)) * J * (1 + e • (A - 1)) = J := by
  rw [idem_cT c e hc]
  have : (1 + e • (Formalism.UG.cT c A - 1)) * J * (1 + e • (A - 1)) =
      J + e • (Formalism.UG.cT c A * J * A - J) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [this, hA, sub_self, smul_zero, add_zero]

theorem idem_det (e : R) (he : e * e = e) (A : Matrix n n R) (hA : A.det = 1) :
    (1 + e • (A - 1)).det = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Matrix.det_isEmpty
  have hpow : ∀ f : R, f * f = f → ∀ k : ℕ, f ^ (k + 1) = f := by
    intro f hf k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have hk : Fintype.card n = (Fintype.card n - 1) + 1 := by
    have := Fintype.card_pos (α := n); omega
  have h1 : e • (1 + e • (A - 1)) = e • A := by
    rw [smul_add, smul_smul, he, smul_sub]; abel
  have h2 : (1 - e) • (1 + e • (A - 1)) = (1 - e) • (1 : Matrix n n R) := by
    rw [smul_add, smul_smul, show (1 - e) * e = 0 by rw [sub_mul, one_mul, he, sub_self], zero_smul, add_zero]
  have he' : (1 - e) * (1 - e) = 1 - e := by ring_nf; rw [sq, he]; ring
  have d1 := congrArg Matrix.det h1
  have d2 := congrArg Matrix.det h2
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow e he, hA] at d1
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow _ he', Matrix.det_one] at d2
  linear_combination d1 + d2

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qr (x : Fin M → E) (u : E) : Matrix (Fin M) (Fin M) E :=
  1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) J)

theorem sigR_inclR (e : E) : sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

def rmat (g : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  RingHom.mapMatrix (inclR (AF F)) (g : Matrix (Fin M) (Fin M) E)

theorem cT_rmat (g : GL (Fin M) E) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) =
      RingHom.mapMatrix (inclR (AF F)) (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) := by
  ext i j
  simp [rmat, Formalism.UG.cT, sigR_inclR]

theorem rmat_unitary {g : GL (Fin M) E} (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) * JR (AF F) J * rmat (F := F) g = JR (AF F) J := by
  have h : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  rw [cT_rmat, show JR (AF F) J = RingHom.mapMatrix (inclR (AF F)) J from rfl, rmat, ← map_mul, ← map_mul, h]

def tm (η : AF F) (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  1 + algebraMap (AF F) (AF F ⊗[F] E) η • (A - 1)

theorem tm_mul (η : AF F) (hη : η * η = η) (A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    tm η A * tm η B = tm η (A * B) :=
  idem_mul _ (by rw [← map_mul, hη]) A B

def trunc (η : AF F) (hη : η * η = η) : Formalism.UG.UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨⟨tm η (rmat g.1), tm η (rmat g.1⁻¹),
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero],
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero]⟩,
    idem_unitary _ _ (by rw [← map_mul, hη]) (StrongApprox.sigR_algebraMap σ η) _ _ (rmat_unitary σ J g.2)⟩ : HR (AF F) σ J)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (1 : GL (Fin M) E)) = 1
    rw [rmat, Units.val_one, map_one, tm, sub_self, smul_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (g.1 * h.1)) = tm η (rmat g.1) * tm η (rmat h.1)
    rw [tm_mul η hη, rmat, rmat, rmat, ← map_mul, Units.val_mul]

theorem mv_trunc (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) :
    ((HA.mat (AF F) σ J (trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g.1 - 1) := rfl

theorem trunc_mem_SUAdelic (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J)
    (hg : (g.1 : Matrix (Fin M) (Fin M) E).det = 1) : trunc σ J η hη g ∈ SUAdelic σ J := by
  rw [StrongApprox.mem_SUAdelic, mv_trunc]
  refine idem_det _ (by rw [← map_mul, hη]) _ ?_
  rw [rmat, ← RingHom.map_det, hg, map_one]

theorem idem_mul_of_sub {S₁ S₁' : Finset (InfinitePlace F)} {S₂ S₂' : Finset (HeightOneSpectrum (𝓞 F))}
    {ε ε' : AF F} (h : IsPlacesIdem S₁ S₂ ε) (h' : IsPlacesIdem S₁' S₂' ε') (hS₁ : S₁' ⊆ S₁) (hS₂ : S₂' ⊆ S₂) :
    ε * ε' = ε' := by
  obtain ⟨a1, -, b1, -⟩ := h
  obtain ⟨-, a0', -, b0'⟩ := h'
  apply Prod.ext
  · funext w
    change fstA F ε w * fstA F ε' w = fstA F ε' w
    by_cases hw : w ∈ S₁'
    · rw [a1 w (hS₁ hw), one_mul]
    · rw [a0' w hw, mul_zero]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε') = evalV F v (sndA F ε')
    by_cases hv : v ∈ S₂'
    · rw [b1 v (hS₂ hv), one_mul]
    · rw [b0' v hv, mul_zero]

theorem idem_sq {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε :=
  idem_mul_of_sub h h subset_rfl subset_rfl

theorem SUSupp_mono {ε ε' : AF F} (hε : ε * ε' = ε') {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J ε') :
    g ∈ SUSupp σ J ε := by
  refine ⟨hg.1, fun i j => ?_⟩
  rw [← hg.2 i j, ← mul_assoc, ← map_mul, hε]

end GlobalTheory.SUAssemble
