import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Scale

variable {S σ : Type*} [CommRing S]

noncomputable def scaleEquiv (P : σ → Prop) [DecidablePred P] (u : Sˣ) :
    MvPolynomial σ S ≃ₐ[S] MvPolynomial σ S :=
  AlgEquiv.ofAlgHom (aeval fun v => if P v then C (u : S) * X v else X v)
    (aeval fun v => if P v then C (↑u⁻¹ : S) * X v else X v)
    (by
      ext v
      by_cases hv : P v
      · simp [hv, ← mul_assoc, ← C_mul]
      · simp [hv])
    (by
      ext v
      by_cases hv : P v
      · simp [hv, ← mul_assoc, ← C_mul]
      · simp [hv])

private theorem scaleEquiv_apply' (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (p : MvPolynomial σ S) :
    scaleEquiv P u p = aeval (fun v => if P v then C (u : S) * X v else X v) p := rfl

theorem scaleEquiv_X (P : σ → Prop) [DecidablePred P] (u : Sˣ) (v : σ) :
    scaleEquiv P u (X v) = if P v then C (u : S) * X v else X v := by
  rw [scaleEquiv_apply', MvPolynomial.aeval_X]

theorem scaleEquiv_C (P : σ → Prop) [DecidablePred P] (u : Sˣ) (a : S) :
    scaleEquiv P u (C a) = C a := by
  first
    | (rw [scaleEquiv_apply', MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]; done)
    | exact (scaleEquiv P u).commutes a

theorem scaleEquiv_monomial [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (s : σ →₀ ℕ) (a : S) :
    scaleEquiv P u (monomial s a) =
      C ((u : S) ^ (∑ v ∈ Finset.univ.filter P, s v)) * monomial s a := by
  have hf : ∀ v : σ, (if P v then C (u : S) * X v else X v) ^ (s v) =
      C (if P v then (u : S) ^ (s v) else 1) * X v ^ (s v) := by
    intro v
    by_cases hv : P v
    · rw [if_pos hv, if_pos hv, mul_pow, MvPolynomial.C_pow]
    · rw [if_neg hv, if_neg hv, MvPolynomial.C_1, one_mul]
  have hc : C ((u : S) ^ (∑ v ∈ Finset.univ.filter P, s v)) =
      ∏ v, (C (if P v then (u : S) ^ (s v) else 1) : MvPolynomial σ S) := by
    rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter, map_prod]
  rw [scaleEquiv_apply', MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype s (fun v k => (if P v then C (u : S) * X v else X v) ^ k)
      (fun v => pow_zero _),
    Finsupp.prod_fintype s (fun v k => (X v : MvPolynomial σ S) ^ k) (fun v => pow_zero _), hc]
  simp only [hf, Finset.prod_mul_distrib, MvPolynomial.algebraMap_eq]
  ring

end Scale

section Blocks

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem scale_multiHomogeneous (b : Fin (D + 1)) (u : Kˣ) (a : Fin (D + 1) → ℕ)
    (F : MvPolynomial (TVar D N) K) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a F) :
    scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a b) * F := by
  have hsum : ∀ s : TVar D N →₀ ℕ,
      (∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v) = ∑ j, s (b, j) := by
    intro s
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [hx]
    · intro h
      exact absurd (Finset.mem_univ b) h
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [scaleEquiv_monomial, hsum s, hF s hs b]

def InBlock (b : Fin (D + 1)) (v : SVar D N) : Prop :=
  Sum.elim (fun _ => False) (fun w : Fin (D + 1) × Fin N => w.1 = b) v

instance (b : Fin (D + 1)) : DecidablePred (InBlock (D := D) (N := N) b) := by
  intro v
  cases v <;> simp only [InBlock, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

private theorem prop_insertNth_of_forall {n : ℕ} {M : Type*} (Q : M → Prop) (j₀ : Fin (n + 1))
    (a : M) (f : Fin n → M) (ha : Q a) (hf : ∀ k, Q (f k)) (j : Fin (n + 1)) :
    Q (Fin.insertNth (α := fun _ => M) j₀ a f j) := by
  by_cases hj : j = j₀
  · subst hj
    rw [Fin.insertNth_apply_same]
    exact ha
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Fin.insertNth_apply_succAbove]
    exact hf k

theorem scale_sImg_expr (b : Fin (D + 1)) (hb : b ≠ 0) (u : Ωˣ) (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (p : TVar D N) :
    scaleEquiv (InBlock (D := D) (N := N) b) u
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2) =
      (if p.1 = b then C (u : Ω) else 1) *
      Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2 := by
  obtain ⟨i, j⟩ := p
  have hX : ∀ k : Fin N, scaleEquiv (InBlock (D := D) (N := N) b) u
      (MvPolynomial.X (Sum.inr (i, k))) =
        (if i = b then C (u : Ω) else 1) * MvPolynomial.X (Sum.inr (i, k)) := by
    intro k
    rw [scaleEquiv_X]
    by_cases h : i = b
    · simp [InBlock, h]
    · simp [InBlock, h]
  have hA : scaleEquiv (InBlock (D := D) (N := N) b) u
      (if i = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) =
      (if i = b then C (u : Ω) else 1) *
        (if i = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) := by
    by_cases h0 : i = 0
    · subst h0
      have hb' : ¬ ((0 : Fin (D + 1)) = b) := fun h => hb h.symm
      rw [if_pos rfl, if_neg hb', one_mul, scaleEquiv_X]
      simp [InBlock]
    · rw [if_neg h0, map_neg, map_sum, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hX, scaleEquiv_C, mul_assoc]
  exact prop_insertNth_of_forall
    (fun m => scaleEquiv (InBlock (D := D) (N := N) b) u m = (if i = b then C (u : Ω) else 1) * m)
    j₀ _ _ hA hX j

end Blocks

section Norm

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

noncomputable def sigP (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (TVar D N) K ≃ₐ[K] MvPolynomial (TVar D N) K :=
  scaleEquiv (fun v : TVar D N => v.1 = b) u

noncomputable def tauP (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  scaleEquiv (InBlock b) (Units.map (algebraMap K Ω).toMonoidHom u)

noncomputable def sigF (b : Fin (D + 1)) (u : Kˣ) : KTf K D N ≃+* KTf K D N :=
  IsFractionRing.ringEquivOfRingEquiv (sigP (N := N) b u).toRingEquiv

noncomputable def tauF (b : Fin (D + 1)) (u : Kˣ) : OmS Ω D N ≃+* OmS Ω D N :=
  IsFractionRing.ringEquivOfRingEquiv (tauP (Ω := Ω) (D := D) (N := N) b u).toRingEquiv

theorem algebraMap_K_OmS (κ : K) :
    algebraMap K (OmS Ω D N) κ =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.C (algebraMap K Ω κ)) := by
  first
    | (rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply]; done)
    | exact IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N) κ
    | rfl

private theorem tauF_algebraMap' (b : Fin (D + 1)) (u : Kˣ)
    (q : MvPolynomial (SVar D N) Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) q) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (scaleEquiv (InBlock b) (Units.map (algebraMap K Ω).toMonoidHom u) q) := by
  unfold tauF
  first
    | (rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]; rfl)
    | exact IsLocalization.ringEquivOfRingEquiv_eq _ _

theorem tauF_algebraMap (b : Fin (D + 1)) (u : Kˣ) (r : Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap Ω (OmS Ω D N) r) =
      algebraMap Ω (OmS Ω D N) r := by
  have h1 : algebraMap Ω (OmS Ω D N) r =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.C r) := by
    first
      | exact IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N) r
      | rfl
  rw [h1, tauF_algebraMap', scaleEquiv_C]

theorem tauF_sHom (b : Fin (D + 1)) (hb : b ≠ 0) (u : Kˣ) (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (F : MvPolynomial (TVar D N) K) :
    tauF b u (sHom j₀ x F) = sHom j₀ x (sigP b u F) := by
  induction F using MvPolynomial.induction_on
  next a =>
    have e1 : (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (C a) =
        algebraMap K (OmS Ω D N) a :=
      (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x).commutes a
    have e2 : sigP (K := K) (D := D) (N := N) b u (C a) = C a := scaleEquiv_C _ _ _
    rw [e2, e1, algebraMap_K_OmS, tauF_algebraMap', scaleEquiv_C]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp]
    congr 1
    have hs : ∀ w : TVar D N, (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (X w) =
        sImg j₀ x w := fun w => MvPolynomial.aeval_X _ _
    have e2 : sigP (K := K) (D := D) (N := N) b u (X v) =
        if v.1 = b then C (u : K) * X v else X v := scaleEquiv_X _ _ _
    have e3 : (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (C (u : K)) =
        algebraMap K (OmS Ω D N) (u : K) :=
      (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x).commutes (u : K)
    rw [e2, hs, sImg, tauF_algebraMap', scale_sImg_expr b hb _ j₀ x v]
    by_cases hv : v.1 = b
    · rw [if_pos hv]
      try rw [if_pos hv]
      simp only [map_mul]
      rw [hs, sImg, e3, algebraMap_K_OmS]
      rfl
    · rw [if_neg hv]
      try rw [if_neg hv]
      rw [one_mul, hs, sImg]

end Norm

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]

variable (d : Data K ι Ω WT A)

theorem tauF_KTtoS (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (hb : b ≠ 0) (u : Kˣ)
    (z : KTf K d.D d.N) :
    tauF (Ω := Ω c) b u (d.KTtoS h c z) = d.KTtoS h c (sigF b u z) := by
  have hl : ∀ G : KTp K d.D d.N,
      d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) G) = d.sH c G := by
    intro G
    first
      | exact IsFractionRing.lift_algebraMap _ _
      | exact IsFractionRing.lift_algebraMap _
      | simp [Data.KTtoS]
  have key : ∀ F : KTp K d.D d.N,
      tauF (Ω := Ω c) b u (d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F)) =
        d.KTtoS h c (sigF b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F)) := by
    intro F
    rw [hl, sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hl]
    exact tauF_sHom b hb u (d.jc c) (d.x c) F
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) z
  simp only [map_div₀, key]

theorem sigF_norm (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (hb : b ≠ 0) (u : Kˣ) (r : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)) =
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) := by
  try intro _
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp
      ((sigF (N := d.N) b u : KTf K d.D d.N ≃+* KTf K d.D d.N) : KTf K d.D d.N →+* KTf K d.D d.N) =
      ((tauF (Ω := Ω c) (D := d.D) (N := d.N) b u :
          OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N) : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp
        (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun z => ?_
    exact (tauF_KTtoS d h c b hb u z).symm
  have hn := Algebra.norm_eq_of_equiv_equiv (sigF (N := d.N) b u)
    (tauF (Ω := Ω c) (D := d.D) (N := d.N) b u) he (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)
  rw [tauF_algebraMap] at hn
  have h2 := congrArg (sigF (N := d.N) b u) hn
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
