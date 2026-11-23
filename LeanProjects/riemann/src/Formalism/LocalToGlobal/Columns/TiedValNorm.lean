import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ}

end Poly

section Pair

variable {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

theorem vn_bVV_star (lam : ι → DomWeight n) (s : K →+* ℂ) (i : VVIdx lam) (m : ι × Fin n × Fin n →₀ ℕ) :
    s (star ((bVV K lam i).1.coeff m)) = star (s ((bVV K lam i).1.coeff m)) := by
  rw [bVV_coe]
  obtain ⟨P, hP⟩ := bVVfun_int K lam i
  rw [hP, MvPolynomial.coeff_map]
  simp

theorem vn_pairS (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) (ho : ∀ τ, (o.1 τ)ᴴ * gramC J (embAt s emb) τ * o.1 τ = 1) (F F' : VV K lam) :
    ∑ i, ∑ j, starRingEnd ℂ (s ((bVV K lam).repr F i)) * s (pairVr emb lam J (bVV K lam i) (bVV K lam j)) *
        s ((bVV K lam).repr F' j) =
      ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) : ℝ) : ℂ) *
        nfAll lam (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F'.1)) (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1)) := by
  have hexp : ∀ G : VV K lam, Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s G.1) =
      ∑ i, s ((bVV K lam).repr G i) • Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s (bVV K lam i).1) := by
    intro G
    conv_lhs => rw [← (bVV K lam).sum_repr G]
    rw [Submodule.coe_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_mul, MvPolynomial.smul_eq_C_mul]
    congr 1
    exact (Formalism.GradedWeylDivisibility.blockAct ℂ o.1).commutes _
  rw [← nfL_apply, hexp F, hexp F']
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, nfL_apply, Finset.mul_sum,
    RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [pairVr_nfAll emb J lam s o ho (bVV K lam i) (bVV K lam j) (vn_bVV_star lam s i)]
  ring

end Pair

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (lam : X.Tau → DomWeight n) (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

theorem vn_inv_natCast_re (m : ℕ) : (((m : ℕ) : ℂ)⁻¹).re = ((m : ℕ) : ℝ)⁻¹ := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

theorem vn_inv_natCast_mul_re (m : ℕ) (z : ℂ) : (((m : ℕ) : ℂ)⁻¹ * z).re = (((m : ℕ) : ℂ)⁻¹).re * z.re := by
  rw [vn_inv_natCast_re, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem vn_pairAt_re (s : X.K →+* ℂ) (o : Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb)))
    (ho : ∀ τ, (o.1 τ)ᴴ * gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb) τ * o.1 τ = 1) (F : VV X.K lam) :
    ((formGSD (roundPk X lam L) Λ).pairAt (InfinitePlace.mk s) F F).re =
      (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ)) *
        (nfAll lam (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1)) (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1))).re := by
  have key := vn_pairS X.emb 1 lam s o ho F F
  rw [← Complex.re_ofReal_mul, ← key]
  rcases InfinitePlace.embedding_mk_eq s with h | h
  · unfold GSD.pairAt
    rw [h]
    rfl
  · rw [← Complex.conj_re]
    congr 1
    unfold GSD.pairAt
    rw [h]
    simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rfl

set_option maxHeartbeats 1000000 in

theorem vn_norm_round (h : (formGSD (roundPk X lam L) Λ).Ok) (R : (formGSD (roundPk X lam L) Λ).Rat) (s : X.K →+* ℂ)
    (o : Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb))) (ho : o.IsON)
    (φ : (formGSD (roundPk X lam L) Λ).EqFun) :
    (majAt ((formGSD (roundPk X lam L) Λ).hB h) (stdFrame ((formGSD (roundPk X lam L) Λ).hGram h)) (InfinitePlace.mk s) φ φ).re =
      (letI := h.fintypeCl
       ∑ c : (formGSD (roundPk X lam L) Λ).Cl,
        (((Nat.card (MulAction.stabilizer (formGSD (roundPk X lam L) Λ).G ((formGSD (roundPk X lam L) Λ).outSec.rep c)) : ℕ) : ℂ)⁻¹).re *
          (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ)) *
          (nfAll lam
            (subP o.1 (MvPolynomial.map s
              (φ.1 ((formGSD (roundPk X lam L) Λ).outSec.rep c) : VV X.K lam).1))
            (subP o.1 (MvPolynomial.map s
              (φ.1 ((formGSD (roundPk X lam L) Λ).outSec.rep c) : VV X.K lam).1))).re) := by
  let _ := h.fintypeCl
  rw [R.maj_eq h]
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hw : ((((formGSD (roundPk X lam L) Λ).toCSD h).wt c : ℕ) : ℂ) =
      ((Nat.card (MulAction.stabilizer (formGSD (roundPk X lam L) Λ).G ((formGSD (roundPk X lam L) Λ).outSec.rep c)) : ℕ) : ℂ) := by
    congr 1
    exact (@Nat.card_eq_fintype_card _ (h.fintypeStab ((formGSD (roundPk X lam L) Λ).outSec.rep c))).symm
  rw [hw, vn_inv_natCast_mul_re, mul_assoc]
  congr 1
  exact vn_pairAt_re lam L Λ s o (frame_std _ o ho) _

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)

def Val.Norm (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (s : X.K →+* ℂ) (x : (stepGSD W Λ u i).EqFun)
    (Pc : StCl W Λ u i → MvPolynomial (X.Tau × Fin (R.N i) × Fin (R.N i)) X.K),
    (∀ c z, (stepEv W Λ σ₀ hσ u i).emb x c z =
      fnOf _ (shiftOf Q.lt) 1 (MvPolynomial.map σ₀ (Pc c)) (valEY W Λ σ₀ u i Q z)) →
    ∀ o : Frames (gramC Q.J (embAt s X.emb)), o.IsON →
      (majAt (stepH (W := W) (Λ := Λ) hX u i).b (stepH (W := W) (Λ := Λ) hX u i).X (InfinitePlace.mk s) x x).re =
        (letI := (stepOk W Λ hX u i).fintypeCl
         ∑ c : StCl W Λ u i, (((Nat.card (StStab W Λ u i c) : ℕ) : ℂ)⁻¹).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf Q.lt τ)) *
          (nfAll (W.lamN u i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re)

set_option maxHeartbeats 1000000 in
theorem Val.norm (Q : ValCrd W Λ σ₀ u i) : Val.Norm W Λ hX σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro s x Pc hPc o ho
  have hval : ∀ c, (x.1 ((stepGSD W Λ u i).outSec.rep c) : VV X.K (W.lamTrue u i)).1 = Pc c := by
    intro c
    apply evFr_injective (gramC (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) (embAt σ₀ X.emb)) (shiftOf (W.lamTrue u i)) σ₀
      (stdFrC _)
    funext z
    rw [evFr_eq_fnOf, evFr_eq_fnOf]
    exact hPc c z
  have h := vn_norm_round (W.lamTrue u i) (fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i) (stepOk W Λ hX u i)
    (stepRat W Λ hX u i) s o ho x
  refine h.trans ?_
  let _ := (stepOk W Λ hX u i).fintypeCl
  refine Finset.sum_congr rfl fun c _ => ?_
  have hv : (x.1 ((formGSD (roundPk X (W.lamTrue u i) fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i)).outSec.rep c) :
      VV X.K (W.lamTrue u i)).1 = Pc c := hval c
  have h2 : ∀ p q, nfAll (W.lamTrue u i) p q = nfAll (W.lamN u i) p q := by
    intro p q
    rw [lamTrue_eq_shW]
    exact nfAll_shW _ _ _ _
  rw [hv, h2]
  rfl

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m) (eV : ((d.colRec a).mem u).A.vT ≃ CF.PlT (d.colRec a) u)

set_option maxHeartbeats 1000000 in

theorem normTie (V : CF.ValTied (D := d.colRec a) u eV i hi (classAgreement a hS hH hP u i hi))
    (hV : V.eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi)) : CF.NormTie V := by
  intro s x Pc hPc o ho
  rw [hV] at hPc
  exact Val.norm (Pr := d.Pr) d.W d.lev d.hX d.σ₀ d.star_cx u i (valCrd a hS hH u i hi) s x Pc hPc o ho

end Rec

end Formalism.L2.Col
