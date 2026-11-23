import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm
import Formalism.AdmissibleDesigns.DesignOfAdmittedObjects

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Norm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.MainNotions.N
  Formalism.MainNotions.N.RepresentationBoundsCohomology Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

section Gen2

variable {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem blockPoly_conj (P Q e a : Matrix n n K) (h1 : P * Q = 1) :
    blockPoly (P * e * Q) (P * a * Q) = blockPoly e a := by
  rw [blockPoly_eq, blockPoly_eq]
  have hm : ∀ M N : Matrix n n K, (M * N).map (Polynomial.C (R := K)) =
      M.map (Polynomial.C (R := K)) * N.map (Polynomial.C (R := K)) :=
    fun M N => Matrix.map_mul
  have h1' : P.map (Polynomial.C (R := K)) * Q.map (Polynomial.C (R := K)) = 1 := by
    rw [← hm, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  set P' := P.map (Polynomial.C (R := K))
  set Q' := Q.map (Polynomial.C (R := K))
  have e1 : (Polynomial.X : Polynomial K) • (P' * e.map Polynomial.C * Q') - P' * a.map Polynomial.C * Q' + 1 -
      P' * e.map Polynomial.C * Q' =
      P' * ((Polynomial.X : Polynomial K) • e.map Polynomial.C - a.map Polynomial.C + 1 - e.map Polynomial.C) * Q' := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_one, h1', Matrix.mul_smul, Matrix.smul_mul]
  rw [hm, hm, hm, hm, e1, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det P'), mul_assoc,
    ← Matrix.det_mul, h1', Matrix.det_one, mul_one]

theorem rank_conj {F : Type} [Field F] (P Q M : Matrix n n F) (h1 : P * Q = 1) (_h2 : Q * P = 1) :
    (P * M * Q).rank = M.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse h1),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h1)]

end Gen2

section D51

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

def cInt (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (A : MatN D.nd i) : MatN D.nd i :=
  if h : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * A.map (toK D.nd i) * Q then h.choose else 0

theorem cInt_spec {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} {A : MatN D.nd i}
    (h : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * A.map (toK D.nd i) * Q) :
    (cInt i P Q A).map (toK D.nd i) = P * A.map (toK D.nd i) * Q := by
  unfold cInt
  rw [dif_pos h]
  exact h.choose_spec

def phiC (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i) :
    D.nd.X i → MatN D.nd i :=
  Function.update a π (cInt i P Q (a π))

theorem phiC_ne (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i)
    {x : D.nd.X i} (hx : x ≠ π) : phiC i π P Q a x = a x :=
  Function.update_of_ne hx _ _

theorem phiC_self (P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (a : D.nd.X i → MatN D.nd i) :
    phiC i π P Q a π = cInt i P Q (a π) :=
  Function.update_self _ _ _

theorem map_smul_toK (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

theorem inR_phiC {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)}
    (hconj : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q)
    {a : D.nd.X i → MatN D.nd i} (ha : InR D.nd i r a) :
    InR D.nd i (rN i r ρ π) (phiC i π P Q a) ∧
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  have hπ : ((∑ k, fun x => f k x • rO D.nd i (rN i r ρ π) x (g k)) π).map (toK D.nd i) =
      P * ((∑ k, fun x => f k x • rO D.nd i r x (g k)) π).map (toK D.nd i) * Q := by
    simp only [Finset.sum_apply]
    change (toK D.nd i).mapMatrix (∑ k, f k π • rO D.nd i (rN i r ρ π) π (g k)) =
      P * (toK D.nd i).mapMatrix (∑ k, f k π • rO D.nd i r π (g k)) * Q
    rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_smul_toK, map_smul_toK, hconj, Matrix.mul_smul,
      Matrix.smul_mul]
  have heq : phiC i π P Q (∑ k, fun x => f k x • rO D.nd i r x (g k)) =
      ∑ k, fun x => f k x • rO D.nd i (rN i r ρ π) x (g k) := by
    funext x
    by_cases hx : x = π
    · subst hx
      rw [phiC_self]
      apply Matrix.map_injective (toK_inj i)
      show (cInt i P Q _).map (toK D.nd i) = _
      rw [cInt_spec i ⟨_, hπ⟩]
      exact hπ.symm
    · rw [phiC_ne i π P Q _ hx]
      simp only [Finset.sum_apply, rO_rN_ne i r ρ π hx]
  refine ⟨⟨m, f, g, hf, heq⟩, ?_⟩
  rw [heq]
  exact hπ

theorem phiC_rel {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} (hQP : Q * P = 1)
    {a b c : D.nd.X i → MatN D.nd i} (hab : a * b = c)
    (ha : (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q)
    (hb : (phiC i π P Q b π).map (toK D.nd i) = P * (b π).map (toK D.nd i) * Q)
    (hc : (phiC i π P Q c π).map (toK D.nd i) = P * (c π).map (toK D.nd i) * Q) :
    phiC i π P Q a * phiC i π P Q b = phiC i π P Q c := by
  funext x
  by_cases hx : x = π
  · subst hx
    apply Matrix.map_injective (toK_inj i)
    show (phiC i x P Q a x * phiC i x P Q b x).map (toK D.nd i) = (phiC i x P Q c x).map (toK D.nd i)
    rw [Matrix.map_mul, ha, hb, hc, ← congrFun hab x, Pi.mul_apply, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  · rw [Pi.mul_apply, phiC_ne i π P Q _ hx, phiC_ne i π P Q _ hx, phiC_ne i π P Q _ hx, ← Pi.mul_apply, hab]

theorem phiC_zero {P Q : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)} :
    (phiC i π P Q 0 π).map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q ∧
      phiC i π P Q 0 = 0 := by
  have h0 : ∃ M : MatN D.nd i, M.map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q :=
    ⟨0, by simp⟩
  have h1 : (phiC i π P Q 0 π).map (toK D.nd i) = P * ((0 : D.nd.X i → MatN D.nd i) π).map (toK D.nd i) * Q := by
    rw [phiC_self]
    exact cInt_spec i h0
  refine ⟨h1, ?_⟩
  funext x
  by_cases hx : x = π
  · subst hx
    apply Matrix.map_injective (toK_inj i)
    show (phiC i x P Q 0 x).map (toK D.nd i) = (0 : MatN D.nd i).map (toK D.nd i)
    rw [h1]
    simp
  · rw [phiC_ne i π P Q _ hx]

end D51

section D51b

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem design_normalized (S : IdempotentChoiceData D.nd i) (hG : GoodCongruenceObjects D.nd r ρ π S) : InertiaElementIdempotentChoice D.nd (rN i r ρ π) π := by
  obtain ⟨hbd, hχ, hρ⟩ := normAt_rN i r ρ π
  have hG0 := hG
  obtain ⟨⟨heB, he1, heBB, he11, heB1, he1B, hrkB, hrk1⟩, hdec, hact, -, hg0, hε, ⟨hX0m, heX, hXe, hX0π⟩,
    ⟨hT, -, -, -, hcard⟩, hroots, ⟨hπ, -⟩, -⟩ := hG0
  obtain ⟨P, Q, hPQ, hQP, hc⟩ := conjK_self i r ρ π ⟨S.e, hdec⟩
  have hA' : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q :=
    fun g => by
      have h := hc g
      beta_reduce at h
      rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨heB', hmB⟩ := inR_phiC i r ρ π hA' heB
  obtain ⟨he1', hm1⟩ := inR_phiC i r ρ π hA' he1
  obtain ⟨hX0m', hmX⟩ := inR_phiC i r ρ π hA' hX0m
  have z := phiC_zero i π (P := P) (Q := Q)
  have heBB' := phiC_rel i π hQP heBB hmB hmB hmB
  have he11' := phiC_rel i π hQP he11 hm1 hm1 hm1
  have heB1' : phiC i π P Q S.eB * phiC i π P Q S.e1 = 0 := by
    rw [← z.2]
    exact phiC_rel i π hQP heB1 hmB hm1 z.1
  have he1B' : phiC i π P Q S.e1 * phiC i π P Q S.eB = 0 := by
    rw [← z.2]
    exact phiC_rel i π hQP he1B hm1 hmB z.1
  have heX' := phiC_rel i π hQP heX hmB hmX hmX
  have hXe' := phiC_rel i π hQP hXe hmX hmB hmX
  have hrk : ∀ (a : D.nd.X i → MatN D.nd i),
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q →
      ∀ x, ((phiC i π P Q a x).map (toK D.nd i)).rank = ((a x).map (toK D.nd i)).rank := by
    intro a ha x
    by_cases hx : x = π
    · subst hx
      rw [ha, rank_conj P Q _ hPQ hQP]
    · rw [phiC_ne i π P Q a hx]
  have hrkB' : ∀ x, ((phiC i π P Q S.eB x).map (toK D.nd i)).rank = D.R.t := fun x => (hrk _ hmB x).trans (hrkB x)
  have hrk1' : ∀ x, ((phiC i π P Q S.e1 x).map (toK D.nd i)).rank = 1 := fun x => (hrk _ hm1 x).trans (hrk1 x)
  let e' : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)) :=
    (matEquiv Q P hQP hPQ).trans S.e
  have he' : ∀ u, e' u = S.e (Q.mulVec u) := fun u => rfl
  have hΦ : ∀ γ u, e' ((mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π) γ).mulVec u) = Dg D.nd ρ π γ (e' u) := by
    intro γ u
    rw [he', he']
    show S.e (Q.mulVec (((rO D.nd i (rN i r ρ π) π γ).map (toK D.nd i)).mulVec u)) = _
    rw [hA', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact hdec γ (Q.mulVec u)
  have hΨ : ∀ γ u, eG D.R.r D.R.t (KK D.nd i) ((mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π) γ).mulVec u) =
      Dg D.nd ρ π γ (eG D.R.r D.R.t (KK D.nd i) u) :=
    fun γ u => e_of_bd D.nd (rO D.nd i (rN i r ρ π) π γ) (hbd γ) (rhoO D.nd i ρ π γ) (hρ γ) _ (hχ γ) u
  have haB : InR' D.nd r S (fun x' => S.eB (S.p x')) := Inst.inR'_of_inR D.nd (r := r) hT heB
  have h3 : ∀ u, S.e (((S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (S.e u).1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * (S.e u).2 c) := by
    intro u
    have h := hact _ haB u
    beta_reduce at h
    rw [hπ] at h
    exact h
  have hconjv : ∀ (a : D.nd.X i → MatN D.nd i),
      (phiC i π P Q a π).map (toK D.nd i) = P * (a π).map (toK D.nd i) * Q →
      ∀ u, e' (((phiC i π P Q a π).map (toK D.nd i)).mulVec u) = S.e (((a π).map (toK D.nd i)).mulVec (Q.mulVec u)) := by
    intro a ha u
    rw [he', ha, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
  have h3' : ∀ u, e' (((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (e' u).1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * (e' u).2 c) := by
    intro u
    rw [hconjv _ hmB u, h3, he']
  have hE : ∀ u, eG D.R.r D.R.t (KK D.nd i) (((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u) =
      (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec (eG D.R.r D.R.t (KK D.nd i) u).1,
        (eG D.R.r D.R.t (KK D.nd i) u).2) := by
    obtain ⟨Hm, hH⟩ := act_inR D.nd (rN i r ρ π) ρ π heB'
    have h := transfer e' (eG D.R.r D.R.t (KK D.nd i)) (fun u => ((phiC i π P Q S.eB π).map (toK D.nd i)).mulVec u)
      (fun z => (((S.ψρ (fun x' => S.eB (S.p x'))).map (toK D.nd i)).mulVec z.1,
        fun c => toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * z.2 c)) Hm
      (hH e' hΦ) (hH _ hΨ) h3'
    intro u
    refine (h u).trans (Prod.ext rfl (funext fun c => ?_))
    show toK D.nd i (S.ψχ c (fun x' => S.eB (S.p x'))) * _ = _
    rw [Inst.psiChi_eB D.nd hG c, map_one, one_mul]
    rfl
  have heBπ : phiC i π P Q S.eB π = Matrix.diagonal fun a => if blk D.R a = 0 then (0 : D.nd.O i) else 1 := by
    have hD := eq_diag_of (r := D.R.r) (t := D.R.t) ((phiC i π P Q S.eB π).map (toK D.nd i)) _ hE (hrkB' π)
    apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
    show (phiC i π P Q S.eB π).map (toK D.nd i) =
      (Matrix.diagonal fun a => if blk D.R a = 0 then (0 : D.nd.O i) else 1).map (toK D.nd i)
    rw [hD, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    by_cases h0 : blkG D.R.r D.R.t a = 0 <;> simp [h0]
  have hX0π' : ∀ u, e' (((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u) =
      ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e' u).2 c) := by
    intro u
    rw [hconjv _ hmX u, hX0π, he']
  have hX0std : ∀ u, eG D.R.r D.R.t (KK D.nd i) (((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u) =
      ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * (eG D.R.r D.R.t (KK D.nd i) u).2 c) := by
    obtain ⟨Hm, hH⟩ := act_inR D.nd (rN i r ρ π) ρ π hX0m'
    exact transfer e' (eG D.R.r D.R.t (KK D.nd i)) (fun u => ((phiC i π P Q S.X0 π).map (toK D.nd i)).mulVec u)
      (fun z => ((0 : Fin D.R.r → KK D.nd i), fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) S.g0 : (D.nd.O i)ˣ) : D.nd.O i) * z.2 c)) Hm
      (hH e' hΦ) (hH _ hΨ) hX0π'
  have hX0eq : phiC i π P Q S.X0 π =
      Matrix.diagonal fun a => if blk D.R a = 0 then 0 else rO D.nd i (rN i r ρ π) π S.g0 a a := by
    apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    apply (eG D.R.r D.R.t (KK D.nd i)).injective
    refine (hX0std u).trans (Eq.symm ((e_of_diag D.nd (fun a => rO D.nd i (rN i r ρ π) π S.g0 a a) u).trans
      (Prod.ext rfl (funext fun c => ?_))))
    show toK D.nd i (rO D.nd i (rN i r ρ π) π S.g0 (Fin.natAdd D.R.r c) (Fin.natAdd D.R.r c)) * _ = _
    rw [hχ]
  have he1π : ∀ a b, (blk D.R a ≠ 0 ∨ blk D.R b ≠ 0) → phiC i π P Q S.e1 π a b = 0 := by
    intro a b hab
    rcases hab with ha | hb
    · have h' : (phiC i π P Q S.eB π * phiC i π P Q S.e1 π) a b = 0 :=
        congrFun (congrFun (congrFun heB1' π) a) b
      rw [heBπ] at h'
      simpa [Matrix.diagonal_mul, ha] using h'
    · have h' : (phiC i π P Q S.e1 π * phiC i π P Q S.eB π) a b = 0 :=
        congrFun (congrFun (congrFun he1B' π) a) b
      rw [heBπ] at h'
      simpa [Matrix.mul_diagonal, hb] using h'
  let s' : D.nd.X i → MatN D.nd i :=
    phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB
  have hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd (rN i r ρ π)) π (blk D.R) (phiC i π P Q S.eB)
      (phiC i π P Q S.e1) :=
    ⟨tSpan_of_inR D.nd (rN i r ρ π) heB', tSpan_of_inR D.nd (rN i r ρ π) he1', heBB', he11', heB1', he1B',
      hrkB', hrk1', heBπ, he1π⟩
  have hX0t := tSpan_of_inR D.nd (rN i r ρ π) hX0m'
  have hs : s' ∈ tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) := by
    have h1 := smul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) (f := -1) (neg_mem (D.nd.T i).one_mem)
      (mul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π))
        (mul_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) (tSpan_of_inR D.nd (rN i r ρ π) heB')
        (repX_mem D.nd (rN i r ρ π) S.g0)) (tSpan_of_inR D.nd (rN i r ρ π) heB'))
    have h2 := add_mem_tSpan (D.nd.T i) (repX D.nd (rN i r ρ π)) hX0t h1
    have e : s' = phiC i π P Q S.X0 + fun x => algebraMap (D.nd.O i) (D.nd.O i) ((-1 : D.nd.X i → D.nd.O i) x) •
        (phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) x := by
      funext x
      simp [s', sub_eq_add_neg]
    rw [e]
    exact h2
  have hes : phiC i π P Q S.eB * s' = s' := by
    show phiC i π P Q S.eB * (phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) = _
    rw [mul_sub, heX', ← mul_assoc, ← mul_assoc, heBB']
  have hse : s' * phiC i π P Q S.eB = s' := by
    show (phiC i π P Q S.X0 - phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0 * phiC i π P Q S.eB) * phiC i π P Q S.eB = _
    rw [sub_mul, hXe', mul_assoc (phiC i π P Q S.eB * repX D.nd (rN i r ρ π) S.g0), heBB']
  have hsπ : s' π = 0 := by
    show phiC i π P Q S.X0 π - phiC i π P Q S.eB π * rO D.nd i (rN i r ρ π) π S.g0 * phiC i π P Q S.eB π = 0
    rw [hX0eq, heBπ]
    exact sub_eq_zero.mpr (diag_conj (r := D.R.r) (t := D.R.t) (rO D.nd i (rN i r ρ π) π S.g0) (hbd S.g0)).symm
  refine ⟨S.g0, hg0, hε, phiC i π P Q S.eB, phiC i π P Q S.e1, s', hI, hs, hes, hse, hsπ, fun x => ?_⟩
  have hx : phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x + s' x = phiC i π P Q S.X0 x := by
    show phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x +
      (phiC i π P Q S.X0 x - phiC i π P Q S.eB x * repX D.nd (rN i r ρ π) S.g0 x * phiC i π P Q S.eB x) =
      phiC i π P Q S.X0 x
    abel
  rw [hx]
  have hbp : blockPoly ((phiC i π P Q S.eB x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
      ((phiC i π P Q S.X0 x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) =
      blockPoly ((S.eB x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
        ((S.X0 x).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    by_cases hxπ : x = π
    · subst hxπ
      erw [hmB, hmX]
      exact blockPoly_conj P Q _ _ hPQ
    · rw [phiC_ne i π P Q _ hxπ, phiC_ne i π P Q _ hxπ]
  rw [hbp]
  have hne : 0 < Nat.card {x' // S.p x' = x} := by
    rw [hcard x]
    exact Nat.factorial_pos _
  obtain ⟨⟨x', hx'⟩⟩ := (Nat.card_pos_iff.mp hne).1
  subst hx'
  refine ⟨fun c => toK D.nd i (S.rr (1 + (c : ℕ)) x'),
    fun a b hab => rr_inj D.nd r ρ π hG x' (IsFractionRing.injective (D.nd.O i) (KK D.nd i) hab), ?_⟩
  rw [← blockPoly_map, blockPoly_eq, ← hroots x', prod_Icc_fin D.nd D.R.t, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  try rfl

theorem design_normalized_of_admitted (hA : LargeLevelLemmas.adm51 i r ρ π) (hZ : π ∈ D.nd.Z i) : InertiaElementIdempotentChoice D.nd (rN i r ρ π) π := by
  obtain ⟨S, hG⟩ := hA hZ
  exact design_normalized i r ρ π S hG

theorem inputs_normalized (hA : LargeLevelLemmas.admitted i r ρ π) (hZ : π ∈ D.nd.Z i) :
    NormAt D.nd (rN i r ρ π) ρ π ∧
      (∀ (γ : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i (rN i r ρ π) x γ).charpolyRev).coeff k) ∈ D.nd.T i) ∧
      Submodule.span (kk D.nd i) (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤ ∧
      InertiaElementIdempotentChoice D.nd (rN i r ρ π) π := by
  obtain ⟨a51, -, -, -, g1, -, g3, -, -, -, -, -, -, -, -, -, dcm, -⟩ := hA
  exact ⟨normAt_rN i r ρ π, admG1_rN i r ρ π dcm g1, g3.2.2, design_normalized_of_admitted i r ρ π a51 hZ⟩

end D51b

end Formalism.MainNotions.N.K.Norm
