import Formalism.LocalToGlobal.Columns.ChainLawXiQ
import Formalism.LocalToGlobal.Columns.XiFirstLawAllLevels
import Formalism.LocalToGlobal.Columns.ChainTwOk
import Formalism.LocalToGlobal.Columns.ChainTwAn
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section PhiQ

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

theorem clXQ_redMQ_one (n : ℕ) : redMQ P ((1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap) = 1 := by
  ext l s
  show redP P ((Pi.single s (1 : E) : Sp E n) l) = _
  rw [Matrix.one_apply]
  by_cases h : l = s
  · subst h
    rw [Pi.single_eq_same, if_pos rfl, redP_one]
  · rw [Pi.single_eq_of_ne h, if_neg h, redP_zero]

theorem clXQ_tl_one (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ c n r : ℕ) (h : k₀ ≤ n) (hr : r ≤ n + c) :
    xiZ ξ (((redMQ P (1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix
      (Fin.castLE hr) (Fin.castLE hr)).det = 1 := by
  rw [clXQ_redMQ_one, Matrix.submatrix_one_equiv, Matrix.submatrix_one _ (Fin.castLE_injective hr), Matrix.det_one]
  simpa using xiZ_unit ξ 1

theorem clXQ_scal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ kj n c r : ℕ} (h : k₀ ≤ n) (hk : k₀ ≤ kj) (hkn : kj ≤ n) (e : kj + c = r) (hr : r ≤ n + c)
    {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c) :
    xiZ ξ (((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix (Fin.castLE hr) (Fin.castLE hr)).det =
      LocE.unitV ξ ((LinearEquiv.det g : Eˣ) : E) * LocE.lamQB ξ kj n g.toLinearMap := by
  rw [jq_scal hq (ciQ_ne_zero hu) ξ h hk hkn e hr hg, unitV_eq, redP_detEquiv P hg.1]

theorem clXQ_phiQ_tgt {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' c n kj' kj : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) (hk' : k₀ ≤ kj') (hk : k₀ ≤ kj) (hkn : kj ≤ n) (e' : kj' + c' = r)
    (e : kj + c = r) (hr' : r ≤ n' + c') (hr : r ≤ n + c) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c)
    (y : HomE E (n' + c') (n + c)) :
    LocE.PhiQ q ξ k₀ r c' n' c n (g.toLinearMap ∘ₗ y) =
      LocE.unitV ξ ((LinearEquiv.det g : Eˣ) : E) * LocE.lamQB ξ kj n g.toLinearMap * LocE.PhiQ q ξ k₀ r c' n' c n y := by
  have e0 := phiQ_lawG hq hu ξ k₀ r c' n' c n kj' kj h' h hk' hk e' e hr' hr (one_mem (LocE.JQ P q kj' n' c')) hg y
  rw [clXQ_tl_one, mul_one, clXQ_scal hq hu ξ h hk hkn e hr hg] at e0
  exact e0

theorem phi_source_change_of_level {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' c n kj' kj : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) (hk' : k₀ ≤ kj') (hk : k₀ ≤ kj) (hkn' : kj' ≤ n') (e' : kj' + c' = r)
    (e : kj + c = r) (hr' : r ≤ n' + c') (hr : r ≤ n + c) {f : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hf : f ∈ LocE.JQ P q kj' n' c')
    (y : HomE E (n' + c') (n + c)) :
    LocE.PhiQ q ξ k₀ r c' n' c n (y ∘ₗ f.toLinearMap) =
      LocE.unitV ξ ((LinearEquiv.det f : Eˣ) : E) * LocE.lamQB ξ kj' n' f.toLinearMap * LocE.PhiQ q ξ k₀ r c' n' c n y := by
  have e0 := phiQ_lawG hq hu ξ k₀ r c' n' c n kj' kj h' h hk' hk e' e hr' hr hf (one_mem (LocE.JQ P q kj n c)) y
  rw [clXQ_tl_one, one_mul, clXQ_scal hq hu ξ h' hk' hkn' e' hr' hf] at e0
  exact e0

end PhiQ

section Om

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_kj_le (j : ℕ) : R.k + j ≤ R.N j := by
  unfold Ranks.N
  have : j * (R.t + 1) = j * R.t + j := by ring
  omega

theorem clXQ_kj_c {j : ℕ} (hj : j + 1 ≤ R.m) : R.k + j + cOf R j = R.r := by
  unfold cOf Ranks.r
  omega

theorem clXQ_conj_mem {j : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) {h r : AutY X R j}
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) h) :
    (h⁻¹ * r * h : AutY X R j) ∈ LocE.JQ w.1 (qOf w.1) (R.k + j) (R.N j) (cOf R j) := by
  have h1 := (Subgroup.mem_inf.1 hr).2
  rw [Subgroup.mem_comap, twJat_Q _ _ hw] at h1
  simpa [MulAut.conj_apply] using h1

theorem clXQ_det_conj {j : ℕ} (h r : AutY X R j) : LinearEquiv.det (h⁻¹ * r * h : AutY X R j) = LinearEquiv.det r := by
  rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

theorem clXQ_omPhi_tgt {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (hi : i + 2 ≤ R.m) (hal : AutY X R i) {hbe r' : AutY X R (i + 1)}
    (hr' : r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i w hal hbe (r'.toLinearMap ∘ₗ x) =
      LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det r' : X.Eˣ) : X.E) *
        lamRow Ch mu cst.sharp (i + 1) w.1 ((hbe⁻¹ * r' * hbe : AutY X R (i + 1))).toLinearMap * omPhi Ch sel mu cst i w hal hbe x := by
  classical
  have hk := clXQ_conj_mem hw hr'
  have hcomp : hbe.symm.toLinearMap ∘ₗ (r'.toLinearMap ∘ₗ x) ∘ₗ hal.toLinearMap =
      (hbe⁻¹ * r' * hbe : AutY X R (i + 1)).toLinearMap ∘ₗ (hbe.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) := by
    refine LinearMap.ext fun v => ?_
    show hbe.symm (r' (x (hal v))) = hbe.symm (r' (hbe (hbe.symm (x (hal v)))))
    rw [LinearEquiv.apply_symm_apply]
  have hlaw := clXQ_phiQ_tgt (ciQ_mem w.1) hu (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
    (R.k + i) (R.k + (i + 1)) (twAn_k_le i) (twAn_k_le (i + 1)) (by omega) (by omega) (clXQ_kj_le (i + 1)) (clXQ_kj_c (by omega))
    (clXQ_kj_c (by omega)) (twAn_r_le (by omega)) (twAn_r_le (by omega)) hk (hbe.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap)
  unfold omPhi Loc.om PhiAt lamRow
  simp only [if_neg hw]
  rw [hcomp, hlaw, clXQ_det_conj]
  ring

theorem unfoldingPhi_comp_leftUnipotent_source {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (hi : i + 2 ≤ R.m) {hal r : AutY X R i} (hbe : AutY X R (i + 1))
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp i w.1) hal) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i w hal hbe (x ∘ₗ r.toLinearMap) =
      LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det r : X.Eˣ) : X.E) *
        lamRow Ch mu cst.sharp i w.1 ((hal⁻¹ * r * hal : AutY X R i)).toLinearMap * omPhi Ch sel mu cst i w hal hbe x := by
  classical
  have hk := clXQ_conj_mem hw hr
  have hcomp : hbe.symm.toLinearMap ∘ₗ (x ∘ₗ r.toLinearMap) ∘ₗ hal.toLinearMap =
      (hbe.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) ∘ₗ (hal⁻¹ * r * hal : AutY X R i).toLinearMap := by
    refine LinearMap.ext fun v => ?_
    show hbe.symm (x (r (hal v))) = hbe.symm (x (hal (hal.symm (r (hal v)))))
    rw [LinearEquiv.apply_symm_apply]
  have hlaw := phi_source_change_of_level (ciQ_mem w.1) hu (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
    (R.k + i) (R.k + (i + 1)) (twAn_k_le i) (twAn_k_le (i + 1)) (by omega) (by omega) (clXQ_kj_le i) (clXQ_kj_c (by omega))
    (clXQ_kj_c (by omega)) (twAn_r_le (by omega)) (twAn_r_le (by omega)) hk (hbe.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap)
  unfold omPhi Loc.om PhiAt lamRow
  simp only [if_neg hw]
  rw [hcomp, hlaw, clXQ_det_conj]
  ring

theorem clXQ_C_bdd {j : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) {h r : AutY X R j} (hb : TwBdd (Pr := Pr) j w.1 h)
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) h) (v : Sp X.E (R.N j + cOf R j)) (hv : ∀ l, IntAt w.1 (v l))
    (l : Fin (R.N j + cOf R j)) : IntAt w.1 ((qOf w.1 : X.E) ^ j * r v l) := by
  have hk := (clXQ_conj_mem hw hr).1
  have h1 : ∀ l, IntAt w.1 ((h⁻¹ : AutY X R j) v l) := twAn_bdd_inv hw hb v hv
  have h2 : ∀ l, IntAt w.1 ((h⁻¹ * r * h : AutY X R j) ((h⁻¹ : AutY X R j) v) l) :=
    (ciMem_stdAt w.1 _).1 ((hk _).2 ((ciMem_stdAt w.1 _).2 h1))
  have h3 := twAn_bdd_q hw hb _ h2 l
  have e : h ((h⁻¹ * r * h : AutY X R j) ((h⁻¹ : AutY X R j) v)) = r v := by
    show h (h.symm (r (h (h.symm v)))) = r v
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rwa [e] at h3

theorem clXQ_psi_ne (hc : cst.Ok) {j : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) {h r : AutY X R j} (hb : TwBdd (Pr := Pr) j w.1 h)
    (hD : j ≤ cst.D w) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) h) : cst.psi w (Loc.n1Arg r) ≠ 0 := by
  have hn : IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * Loc.n1Arg r) := by
    unfold Loc.n1Arg
    rw [Finset.mul_sum]
    refine ciIntAt_sum _ _ fun a _ => ?_
    unfold Loc.atN
    split_ifs with hl
    · have h1 := clXQ_C_bdd hw hb hr (Loc.eN X.E (R.N j + cOf R j) (R.N j + a + 1)) (fun l => by
        unfold Loc.eN
        split_ifs
        · exact ciIntAt_one
        · exact ciIntAt_zero) ⟨R.N j + a, hl⟩
      have e : (qOf w.1 : X.E) ^ cst.D w = (qOf w.1 : X.E) ^ (cst.D w - j) * (qOf w.1 : X.E) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hD]
      rw [e, mul_assoc]
      have hqk : IntAt w.1 ((qOf w.1 : X.E) ^ (cst.D w - j)) := by
        have h0 := ciIntAt_prod (P := w.1) (Finset.range (cst.D w - j)) (fun _ => (qOf w.1 : X.E)) (fun _ _ => ciIntAt_q)
        simpa using h0
      exact hqk.mul h1
    · rw [mul_zero]
      exact ciIntAt_zero
  have hn' : IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * -Loc.n1Arg r) := by
    rw [mul_neg]
    exact ciIntAt_neg hn
  have e := hc.psi_add w _ _ hn hn'
  rw [add_neg_cancel, hc.psi_int w 0 ciIntAt_zero] at e
  exact left_ne_zero_of_mul (e ▸ one_ne_zero)

end Om

section Cov

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

def XiCovTgtQ (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∀ r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe, ∀ c' ∈ GLint X.E (R.N (i + 1)) w.1,
    (∀ x, r' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (c' x)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi w) (LocE.valsQ X.E (qOf w.1) cst.A cst.B)
          (((qOf w.1 : X.K) ^ cst.B)⁻¹) (fun x => omPhi Ch sel mu cst i w hal hbe (r'.toLinearMap ∘ₗ x)) y =
        cst.psi w (Loc.n1Arg r') * E1at Ch sel mu cst i w hal hbe (c'.toLinearMap ∘ₗ y)

def XiCovSrcQ (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp i w.1) hal, ∀ c ∈ GLint X.E (R.N i) w.1,
    (∀ x, r (Loc.inX X.E (R.N i) (cOf R i) x) = Loc.inX X.E (R.N i) (cOf R i) (c x)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi w) (LocE.valsQ X.E (qOf w.1) cst.A cst.B)
          (((qOf w.1 : X.K) ^ cst.B)⁻¹) (fun x => omPhi Ch sel mu cst i w hal hbe (x ∘ₗ r.toLinearMap)) y =
        cst.psi w (Loc.n1Arg r) * E1at Ch sel mu cst i w hal hbe (y ∘ₗ c.toLinearMap)

variable {Ch sel mu cst}

theorem clXQ_tgt_of_cov {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (hi : i + 2 ≤ R.m) {hal : AutY X R i} {hbe : AutY X R (i + 1)}
    (hψ : ∀ r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe, cst.psi w (Loc.n1Arg r') ≠ 0)
    (hcov : XiCovTgtQ Ch sel mu cst i w hal hbe) : TargetEquivarianceAtPrime Ch sel mu cst i w hal hbe := by
  classical
  intro r' hr' c' hc' hx y
  have e := hcov r' hr' c' hc' hx y
  rw [show (fun x => omPhi Ch sel mu cst i w hal hbe (r'.toLinearMap ∘ₗ x)) = fun x => _ * omPhi Ch sel mu cst i w hal hbe x from
    funext (clXQ_omPhi_tgt hw hu hi hal hr'), first_sum_scalar_mul] at e
  change _ * E1at Ch sel mu cst i w hal hbe y = _ at e
  rw [det_first_parabolic_eq_det_block (Subgroup.mem_inf.1 hr').1.1 hx] at e
  have hd := intAt_det c' hc'
  have hd' := intAt_det_inv c' hc'
  have hd0 : ((LinearEquiv.det c' : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hne := clX_unitV_ne (resChar (mu : Chr X.F X.E X.K) w.1) (isUnit_reduction_of_integralAt_inv hd hd' hd0)
  have hp := hψ r' hr'
  have hT : rhoT Ch sel mu i w ((LinearEquiv.det c'⁻¹ : X.Eˣ) : X.E) =
      (LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det c' : X.Eˣ) : X.E))⁻¹ := by
    unfold rhoT
    rw [if_neg hw, map_inv, Units.val_inv_eq_inv_val, clX_unitV_inv _ hd hd' hd0]
  have e2 : E1at Ch sel mu cst i w hal hbe (c'.toLinearMap ∘ₗ y) = (cst.psi w (Loc.n1Arg r'))⁻¹ *
      (LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det c' : X.Eˣ) : X.E) *
        lamRow Ch mu cst.sharp (i + 1) w.1 ((hbe⁻¹ * r' * hbe : AutY X R (i + 1))).toLinearMap * E1at Ch sel mu cst i w hal hbe y) := by
    rw [e]
    field_simp
  rw [hT, e2]
  unfold chiInv
  field_simp

theorem clXQ_src_of_cov {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (hi : i + 2 ≤ R.m) {hal : AutY X R i} {hbe : AutY X R (i + 1)}
    (hψ : ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp i w.1) hal, cst.psi w (Loc.n1Arg r) ≠ 0)
    (hcov : XiCovSrcQ Ch sel mu cst i w hal hbe) : SourceEquivarianceAtPrime Ch sel mu cst i w hal hbe := by
  classical
  intro r hr c hc hx y
  have e := hcov r hr c hc hx (y ∘ₗ (c⁻¹).toLinearMap)
  rw [show (fun x => omPhi Ch sel mu cst i w hal hbe (x ∘ₗ r.toLinearMap)) = fun x => _ * omPhi Ch sel mu cst i w hal hbe x from
    funext (unfoldingPhi_comp_leftUnipotent_source hw hu hi hbe hr), first_sum_scalar_mul] at e
  change _ * E1at Ch sel mu cst i w hal hbe (y ∘ₗ (c⁻¹).toLinearMap) = _ at e
  have e3 : (y ∘ₗ (c⁻¹).toLinearMap) ∘ₗ c.toLinearMap = y := by
    refine LinearMap.ext fun v => ?_
    show y (c.symm (c v)) = y v
    rw [LinearEquiv.symm_apply_apply]
  rw [e3, det_first_parabolic_eq_det_block (Subgroup.mem_inf.1 hr).1.1 hx] at e
  have hd := intAt_det c hc
  have hd' := intAt_det_inv c hc
  have hd0 : ((LinearEquiv.det c : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hne := clX_unitV_ne (resChar (mu : Chr X.F X.E X.K) w.1) (isUnit_reduction_of_integralAt_inv hd hd' hd0)
  have hp := hψ r hr
  have hS : rhoS Ch sel mu i w ((LinearEquiv.det c⁻¹ : X.Eˣ) : X.E) =
      LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det c : X.Eˣ) : X.E) := by
    unfold rhoS
    rw [if_neg hw, map_inv, Units.val_inv_eq_inv_val, clX_unitV_inv _ hd hd' hd0, unitV_inv, inv_inv]
  rw [hS]
  unfold chiInv
  have e4 : E1at Ch sel mu cst i w hal hbe y = (cst.psi w (Loc.n1Arg r))⁻¹ *
      (LocE.unitV (resChar (mu : Chr X.F X.E X.K) w.1) ((LinearEquiv.det c : X.Eˣ) : X.E) *
        lamRow Ch mu cst.sharp i w.1 ((hal⁻¹ * r * hal : AutY X R i)).toLinearMap *
          E1at Ch sel mu cst i w hal hbe (y ∘ₗ (c⁻¹).toLinearMap)) := by
    rw [e]
    field_simp
  rw [e4]
  ring

end Cov

section Gen

def TruncatedUnfoldingChangeOfVarsTarget : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (n' c' n c : ℕ), c' = c + 1 →
    (qOf P).Prime → ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (psi : E → K) (D a b e : ℕ),
    (∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y) →
    (∀ x : E, IntAt P x → psi x = 1) → ∀ Ψ : Loc.SF E K (n' + c') (n + c),
    (∀ x, Ψ x ≠ 0 → ∀ s l, IntAt P ((qOf P : E) ^ a * x (Pi.single s 1) l)) → a ≤ D →
    (∀ x z, (∀ s l, IntAt P (((qOf P : E) ^ b)⁻¹ * z (Pi.single s 1) l)) → Ψ (x + z) = Ψ x) →
    ∀ r ∈ Loc.R1 E n c, ∀ g ∈ GLint E n P, (∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) →
    (∀ s l, IntAt P ((qOf P : E) ^ e * r (Pi.single s 1) l)) → (∀ s l, IntAt P ((qOf P : E) ^ e * r⁻¹ (Pi.single s 1) l)) → e ≤ D →
    ∀ A B : ℕ, a + (c + 1) * e ≤ A → b ≤ B → 1 ≤ B → ∀ (wt : K) (y : HomE E n' n),
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E (qOf P) A B) wt (fun x => Ψ (r.toLinearMap ∘ₗ x)) y =
        psi (Loc.n1Arg r) * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E (qOf P) A B) wt Ψ (g.toLinearMap ∘ₗ y)

def TruncatedUnfoldingChangeOfVarsSource : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (n' c' n c : ℕ), c' = c + 1 →
    (qOf P).Prime → ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (psi : E → K) (D a b e : ℕ),
    (∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y) →
    (∀ x : E, IntAt P x → psi x = 1) → ∀ Ψ : Loc.SF E K (n' + c') (n + c),
    (∀ x, Ψ x ≠ 0 → ∀ s l, IntAt P ((qOf P : E) ^ a * x (Pi.single s 1) l)) → a ≤ D →
    (∀ x z, (∀ s l, IntAt P (((qOf P : E) ^ b)⁻¹ * z (Pi.single s 1) l)) → Ψ (x + z) = Ψ x) →
    ∀ r ∈ Loc.R1 E n' c', ∀ g ∈ GLint E n' P, (∀ x, r (Loc.inX E n' c' x) = Loc.inX E n' c' (g x)) →
    (∀ s l, IntAt P ((qOf P : E) ^ e * r (Pi.single s 1) l)) → (∀ s l, IntAt P ((qOf P : E) ^ e * r⁻¹ (Pi.single s 1) l)) → e ≤ D →
    ∀ A B : ℕ, a + (c + 1) * e ≤ A → b ≤ B → 1 ≤ B → ∀ (wt : K) (y : HomE E n' n),
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E (qOf P) A B) wt (fun x => Ψ (x ∘ₗ r.toLinearMap)) y =
        psi (Loc.n1Arg r) * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E (qOf P) A B) wt Ψ (y ∘ₗ g.toLinearMap)

end Gen

section Close

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_cOf {i : ℕ} (hi : i + 2 ≤ R.m) : cOf R i = cOf R (i + 1) + 1 := by
  unfold cOf
  omega

theorem clXQ_omPhi_inv {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hq : (qOf w.1).Prime) (hi : i + 2 ≤ R.m) {hal : AutY X R i}
    {hbe : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal) (hbb : TwBdd (Pr := Pr) (i + 1) w.1 hbe)
    (x z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hz : ∀ s l, IntAt w.1 (((qOf w.1 : X.E) ^ (i + 1))⁻¹ * z (Pi.single s 1) l)) :
    omPhi Ch sel mu cst i w hal hbe (x + z) = omPhi Ch sel mu cst i w hal hbe x :=
  twAn_omPhi_congr w hw hq hi hal hbe hba hbb le_rfl x (x + z) fun s l => by
    have e : (x + z) (Pi.single s 1) l - x (Pi.single s 1) l = z (Pi.single s 1) l := by
      simp [LinearMap.add_apply]
    rw [e]
    exact hz s l

theorem clXQ_tgtEv (hCT : TruncatedUnfoldingChangeOfVarsTarget) (hc : cst.Ok) {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hd : TwDegOne X w.1) (hi : i + 2 ≤ R.m)
    (hD : i + 1 ≤ cst.D w) {hal : AutY X R i} {hbe : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal)
    (hbb : TwBdd (Pr := Pr) (i + 1) w.1 hbe) : TargetEquivarianceLargeDepths Ch sel mu cst i w hal hbe := by
  refine ⟨(i + 1) + (cOf R (i + 1) + 1) * (i + 1), i + 1, fun A' B' hA hB => ?_⟩
  refine clXQ_tgt_of_cov (cst := { cst with A := A', B := B' }) hw hd.2 hi (fun r' hr' => clXQ_psi_ne hc hw hbb hD hr') ?_
  intro r' hr' c' hc' hx y
  exact hCT X.E w.1 X.K (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) (clXQ_cOf hi) hd.1 hd.2 (cst.psi w) (cst.D w) (i + 1) (i + 1) (i + 1)
    (hc.psi_add w) (hc.psi_int w) (omPhi Ch sel mu cst i w hal hbe) (fun x hx' => twAn_omPhi_supp w hw hal hbe hba hbb x hx') hD
    (clXQ_omPhi_inv hw hd.1 hi hba hbb) r' (Subgroup.mem_inf.1 hr').1 c' hc' hx
    (fun s l => clXQ_C_bdd hw hbb hr' _ (twAn_single_int s) l)
    (fun s l => clXQ_C_bdd hw hbb ((Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe).inv_mem hr') _ (twAn_single_int s) l) hD
    A' B' hA hB (by omega) _ y

theorem clXQ_srcEv (hCS : TruncatedUnfoldingChangeOfVarsSource) (hc : cst.Ok) {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hd : TwDegOne X w.1) (hi : i + 2 ≤ R.m)
    (hD : i + 1 ≤ cst.D w) {hal : AutY X R i} {hbe : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal)
    (hbb : TwBdd (Pr := Pr) (i + 1) w.1 hbe) : SourceEquivarianceLargeDepths Ch sel mu cst i w hal hbe := by
  refine ⟨(i + 1) + (cOf R (i + 1) + 1) * i, i + 1, fun A' B' hA hB => ?_⟩
  refine clXQ_src_of_cov (cst := { cst with A := A', B := B' }) hw hd.2 hi (fun r hr => clXQ_psi_ne hc hw hba (by omega) hr) ?_
  intro r hr c hc' hx y
  exact hCS X.E w.1 X.K (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) (clXQ_cOf hi) hd.1 hd.2 (cst.psi w) (cst.D w) (i + 1) (i + 1) i
    (hc.psi_add w) (hc.psi_int w) (omPhi Ch sel mu cst i w hal hbe) (fun x hx' => twAn_omPhi_supp w hw hal hbe hba hbb x hx') hD
    (clXQ_omPhi_inv hw hd.1 hi hba hbb) r (Subgroup.mem_inf.1 hr).1 c hc' hx
    (fun s l => clXQ_C_bdd hw hba hr _ (twAn_single_int s) l)
    (fun s l => clXQ_C_bdd hw hba ((Loc.Cbe (Jat (Pr := Pr) cst.sharp i w.1) hal).inv_mem hr) _ (twAn_single_int s) l) (by omega)
    A' B' hA hB (by omega) _ y

theorem clXQ_xiLawQ_of {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ} (hCT : TruncatedUnfoldingChangeOfVarsTarget) (hCS : TruncatedUnfoldingChangeOfVarsSource)
    (hok : L.Ok Ch sel mu cst G m2) (hd : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → TwDegOne X w.1)
    (hb : ∀ j (b : L.β j) (w : rowSG Pr sel mu), w.1 ∉ Pr.vGs → TwBdd (Pr := Pr) j w.1 (L.h j b w))
    (hD : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → m2 ≤ cst.D w) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) :
    XiLawQ Ch sel mu cst L i al be :=
  clXQ_xiLawQ_ev hok hi al be
    (fun w hw => clXQ_tgtEv hCT hok.cst_ok hw (hd w hw) (by have := hok.hm; omega) (by have := hD w hw; omega) (hb i al w hw)
      (hb (i + 1) be w hw))
    (fun w hw => clXQ_srcEv hCS hok.cst_ok hw (hd w hw) (by have := hok.hm; omega) (by have := hD w hw; omega) (hb i al w hw)
      (hb (i + 1) be w hw))

theorem clXQ_chrOk_of (hCT : TruncatedUnfoldingChangeOfVarsTarget) (hc : cst.Ok) {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hd : TwDegOne X w.1) (hi : i + 2 ≤ R.m)
    (hD : i + 1 ≤ cst.D w) {hal : AutY X R i} {h : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal)
    (hbb : TwBdd (Pr := Pr) (i + 1) w.1 h) (hint : prCat (Pr := Pr) cst.sharp (i + 1) w.1 h ≤ GLint X.E (R.N (i + 1)) w.1)
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu cst i w hal h) : TwChrOk Ch sel mu cst (i + 1) w h :=
  clXQ_chrOk hint (clXQ_tgtEv hCT hc hw hd hi hD hba hbb) hne

end Close

end Formalism.L2.Col
