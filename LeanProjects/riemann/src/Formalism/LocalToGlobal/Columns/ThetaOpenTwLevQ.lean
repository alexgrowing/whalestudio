import Formalism.LocalToGlobal.Columns.QthConjClose

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Tw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem qth_lamQB_one {P : HeightOneSpectrum (𝓞 X.E)} (hq : ((qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) {j : ℕ}
    (ξ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ) (y : AutY X R j) (hy : QClose P (qOf P) y) :
    LocE.lamQB ξ (R.k + j) (R.N j) (y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) = 1 := by
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (R.N j - (R.k + j))) (Fin (R.N j - (R.k + j))) X.E := Matrix.of fun s t : Fin (R.N j - (R.k + j)) =>
    Loc.atN ((y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1) with hD
  have hent : ∀ s t : Fin (R.N j - (R.k + j)), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 X.E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : R.k + j + s.1 < R.N j + cOf R j := by have := s.2; omega
    have ht : R.k + j + t.1 < R.N j + cOf R j := by have := t.2; omega
    have e1 : Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1) = Pi.single ⟨R.k + j + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = ((toGLm X.E (R.N j + cOf R j) y : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E) ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩ := by
      rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dif_pos hs]
      rfl
    obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
  have hdet : redP P D.det = 1 := by
    rw [redP_det D fun s t => (hent s t).1]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

theorem qth_exists_e (P : HeightOneSpectrum (𝓞 X.E)) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) :
    ∃ e : ℕ, WithZero.exp (-(e : ℤ)) ≤ P.valuation X.E ((qOf P : ℕ) : X.E) := by
  have hv0 : P.valuation X.E ((qOf P : ℕ) : X.E) ≠ 0 := (map_ne_zero _).2 hq0
  refine ⟨(-(WithZero.log (P.valuation X.E ((qOf P : ℕ) : X.E)))).toNat, ?_⟩
  conv_rhs => rw [← WithZero.exp_log hv0]
  rw [WithZero.exp_le_exp]
  have := Int.self_le_toNat (-(WithZero.log (P.valuation X.E ((qOf P : ℕ) : X.E))))
  omega

open Classical in
set_option maxHeartbeats 4000000 in

theorem thetaOpen_twLevQ (hc : cst.Ok) (hQg : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (j : ℕ)
    (hh : rowSG Pr sel mu → AutY X R j) : ThetaOpen (twLevQ Ch sel mu cst j hh) := by
  intro P
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := hh P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b, hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (qth_princ_inv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  refine ⟨Subgroup.mem_subgroupOf.2 hmem, ?_⟩
  show twLam Ch sel mu cst j P' h ⟨g, Subgroup.mem_subgroupOf.2 hmem⟩ = 1
  unfold twLam
  split_ifs with hok
  · apply Units.ext
    show twChiVal Ch sel mu cst j P' h g.1 = 1
    rw [twChiVal_eq hok hC (twZrExt_inX g.1)]
    have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
      twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
    have hint : IntAt P.1 (Loc.n1Arg r) := by
      unfold Loc.n1Arg
      refine ciIntAt_sum _ _ fun i _ => ?_
      have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
        (hstd _).2 (twZr_eN_mem P.1 _ _)
      rw [ciMem_stdAt] at hv
      unfold Loc.atN
      split_ifs
      · exact hv _
      · exact ciIntAt_zero
    unfold chiInv
    rw [hc.psi_int P' _ hint, inv_one, one_mul]
    unfold lamRow
    rw [if_neg hPg]
    exact qth_lamQB_one hq hq0 _ _ hy
  · rfl

open Classical in

theorem thetaOpen_twIdx (hc : cst.Ok) (hQg : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (m2 j : ℕ)
    (b : (twIdx Ch sel mu cst m2).β j) : ThetaOpen ((twIdx Ch sel mu cst m2).levQ j b) := by
  show ThetaOpen (if j = 0 then LevQFam.top X.E X.K (R.N j) _ else twLevQ Ch sel mu cst j ((twSt Ch sel mu cst m2 j).h b))
  split_ifs
  · exact thetaOpen_top _
  · exact thetaOpen_twLevQ Ch sel mu cst hc hQg j _

end Tw

end Formalism.L2.Col
