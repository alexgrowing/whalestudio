import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTopLaw

open Matrix

section Alg

variable {k K : Type} [CommRing k] [Field K]

theorem br_mul_of_LLz {n r d : ℕ} (hn : n = r + d) (A B : Matrix (Fin n) (Fin n) k) (hA : LLz r A) :
    (A * B).submatrix (brI hn) (brI hn) = A.submatrix (brI hn) (brI hn) * B.submatrix (brI hn) (brI hn) := by
  subst hn
  ext s t
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add, Matrix.mul_apply]
  have h0 : ∑ i : Fin r, A (brI rfl s) (Fin.castAdd d i) * B (Fin.castAdd d i) (brI rfl t) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [hA _ _ (show r ≤ (brI (rfl : r + d = r + d) s).1 from Nat.le_add_right _ _) (show (Fin.castAdd d i).1 < r from i.2), zero_mul]
  rw [h0, zero_add]
  rfl

theorem xiZ_one_val (ξ : kˣ →* Kˣ) : xiZ ξ (1 : k) = 1 := by
  have h := xiZ_unit ξ 1
  simpa using h

theorem xiZ_br_inv (ξ : kˣ →* Kˣ) {n r d : ℕ} (hn : n = r + d) (A B : Matrix (Fin n) (Fin n) k) (hA : LLz r A) (h : A * B = 1) :
    xiZ ξ (A.submatrix (brI hn) (brI hn)).det * xiZ ξ (B.submatrix (brI hn) (brI hn)).det = 1 := by
  have hinj : Function.Injective (brI (r := r) hn) := fun a b hab => Fin.ext (by
    have := congrArg Fin.val hab
    simp only [brI] at this
    omega)
  rw [← xiZ_mul, ← Matrix.det_mul, ← br_mul_of_LLz hn A B hA, h, Matrix.submatrix_one _ hinj, Matrix.det_one, xiZ_one_val]

theorem fin_alg {K : Type} [Field K] (a bb x y s1 s2 XA XB c d : K) (hS : s1 * s2 * (XA * XB) = x⁻¹ * y) (k1 : x * a = 1)
    (k2 : y * bb = 1) : a⁻¹ * (XA * XB * c * d) * s1 * s2 = bb⁻¹ * (c * d) := by
  have ha : a ≠ 0 := right_ne_zero_of_mul_eq_one k1
  have hx : x⁻¹ = a := inv_eq_of_mul_eq_one_right k1
  have hy : y = bb⁻¹ := eq_inv_of_mul_eq_one_left k2
  rw [hx, hy] at hS
  have key : s1 * s2 * (XA * XB) * a⁻¹ = bb⁻¹ := by rw [hS, mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  linear_combination (c * d) * key

end Alg

section Det

variable {E : Type} [Field E]

theorem det_eq_of_blk {N : ℕ} (hN : 1 ≤ N) (G : Sp E N ≃ₗ[E] Sp E N) (J : Sp E ((N - 1) + 0) ≃ₗ[E] Sp E ((N - 1) + 0))
    (h1 : prXpG E N ∘ₗ G.toLinearMap = J.toLinearMap ∘ₗ prXpG E N)
    (h2 : atNL E N (N - 1) ∘ₗ G.toLinearMap = atNL E N (N - 1)) :
    (LinearEquiv.det G : E) = (LinearEquiv.det J : E) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hpr : ∀ (v : Sp E (n + 1)) (i : Fin n), J (prXpG E (n + 1) v) i = G v (Fin.castSucc i) := by
    intro v i
    have := congrArg (fun f => f i) (LinearMap.congr_fun h1 v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [← this]
    rfl
  have hat : ∀ v : Sp E (n + 1), G v (Fin.last n) = v (Fin.last n) := by
    intro v
    have := LinearMap.congr_fun h2 v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, atNL, show n + 1 - 1 < n + 1 by omega, dif_pos] at this
    exact this
  have hsingle : ∀ k : Fin n, prXpG E (n + 1) (Pi.single (Fin.castSucc k) 1) = (Pi.single k 1 : Sp E n) := by
    intro k
    funext l
    show (Pi.single (Fin.castSucc k) (1 : E) : Sp E (n + 1)) (Fin.castSucc l) = (Pi.single k (1 : E) : Sp E n) l
    by_cases hl : l = k
    · subst hl
      simp
    · rw [Pi.single_eq_of_ne (fun h => hl (Fin.castSucc_injective _ h)), Pi.single_eq_of_ne hl]
  have hlast : prXpG E (n + 1) (Pi.single (Fin.last n) 1) = 0 := by
    funext l
    show (Pi.single (Fin.last n) (1 : E) : Sp E (n + 1)) (Fin.castSucc l) = 0
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last l) _
  set M := LinearMap.toMatrix' G.toLinearMap with hM
  have hMe : ∀ i k, M i k = G (Pi.single k 1) i := fun i k => by
    simp [hM, LinearMap.toMatrix'_apply]
  have hB : LastRowColIdentity M := by
    refine ⟨fun k => ?_, fun i => ?_, ?_⟩
    · rw [hMe, hat]
      exact Pi.single_eq_of_ne (Fin.castSucc_ne_last k).symm _
    · rw [hMe, ← hpr, hlast, map_zero]
      rfl
    · rw [hMe, hat]
      simp
  have hsub : M.submatrix Fin.castSucc Fin.castSucc = LinearMap.toMatrix' J.toLinearMap := by
    ext i k
    rw [Matrix.submatrix_apply, hMe, ← hpr, hsingle]
    simp [LinearMap.toMatrix'_apply]
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix' J.toLinearMap, ← hM,
    blk_det M hB, hsub]

end Det

set_option maxHeartbeats 4000000 in

theorem topLawQ_midTop : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  intro X Pr R Ch sel S mu cst L G m2 hOk hU b P hP g z hmid g' z' htop y y₁ y₂ hδ hq
  classical
  have hm := hOk.hm
  have hcst := hOk.cst_ok
  have hD := hOk.depthQ P hP
  have hwQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
  have hqm : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := qOf_memB P.1
  have hu := hU P.1 hwQ
  have hq0 := ciQ_ne_zero hu
  have hNpos := R.N_pos (m2 + 1 + 1)
  have hNm : R.N (m2 + 1 + 1) = R.N R.m := by rw [hm]
  have hn' : R.N (m2 + 1) = R.r + (m2 + 1) * R.t := rank_midQ (R := R) hm
  have hr' : R.r ≤ R.N (m2 + 1) := by rw [hn']; exact Nat.le_add_right _ _
  have hnA : R.N (m2 + 1 + 1) - 1 + 0 = R.r + R.m * R.t := by rw [hNm, Nat.add_zero]; exact rank_X'_eq R
  have hrA : R.r ≤ R.N (m2 + 1 + 1) - 1 + 0 := by rw [hnA]; exact Nat.le_add_right _ _
  have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
  have hkj := kj_midQ (R := R) hm
  set ξ := resChar (mu : Chr X.F X.E X.K) P.1 with hξ

  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hOk.int (m2 + 1) b P hgC
  have hgiI : g⁻¹ ∈ GLint X.E (R.N (m2 + 1)) P.1 := (GLint X.E (R.N (m2 + 1)) P.1).inv_mem hgI
  have hJ : ∀ rr : AutY X R (m2 + 1), rr ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P) →
      rr ∈ LocE.JQ P.1 (qOf P.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) (cOf R (m2 + 1)) := by
    intro rr hrr
    have h2 := hrr.2
    rw [hOk.last_h] at h2
    have h3 : rr ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) P.1 := by simpa [MulAut.conj_apply] using h2
    unfold Jat at h3
    rwa [if_neg hP] at h3
  obtain ⟨rc, hrc, hxc, rfl⟩ := hmid
  have hgiC : g⁻¹ ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := Subgroup.inv_mem _ hgC
  unfold prCat at hgiC
  obtain ⟨ri, hri, hxi⟩ := hgiC
  have lB : LLz R.r (redMQ P.1 g.toLinearMap) := by
    have := jq_LLz hqm hq0 (hJ rc hrc) hxc
    rwa [hkj] at this
  have lC : LLz R.r (redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap) := by
    have := jq_LLz hqm hq0 (hJ ri hri) hxi
    rwa [hkj] at this

  obtain ⟨j, hj, hpr, hat, rfl⟩ := htop
  unfold rowLevTop at hj
  rw [if_neg hP] at hj
  have hjI : j ∈ GLint X.E (R.N (m2 + 1 + 1) - 1 + 0) P.1 := hj.1
  have hjiI : j⁻¹ ∈ GLint X.E (R.N (m2 + 1 + 1) - 1 + 0) P.1 := (GLint X.E _ P.1).inv_mem hjI
  have hji : j⁻¹ ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N (m2 + 1 + 1) - 1) 0 := Subgroup.inv_mem _ hj
  have lAi : LLz R.r (redMQ P.1 j.toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1) - 1) (c := 0) (g := j) (rr := j) hqm hq0 hj (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have lA : LLz R.r (redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1) - 1) (c := 0) (g := j⁻¹) (rr := j⁻¹) hqm hq0 hji (fun x => by rw [tlq_inX_zero, tlq_inX_zero])

  have hpr' : ∀ v, prXpG X.E (R.N (m2 + 1 + 1)) (g'.symm v) = j⁻¹ (prXpG X.E (R.N (m2 + 1 + 1)) v) := by
    intro v
    have := LinearMap.congr_fun hpr (g'.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [this]
    show _ = j.symm (j _)
    rw [LinearEquiv.symm_apply_apply]
  have hat' : ∀ v, atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) (g'.symm v) = atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) v := by
    intro v
    have := LinearMap.congr_fun hat (g'.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have eX : prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
      (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap ∘ₗ (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ
        g.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hpr' _
  have eT : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) =
      (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) ∘ₗ ((⟨g, hgI⟩ : ↥(GLint X.E (R.N (m2 + 1)) P.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hat' _
  have hδ' : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((⟨g, hgI⟩ : ↥(GLint X.E (R.N (m2 + 1)) P.1)).1 (g.symm y₁) - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := by
    show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (g (g.symm y₁) - y₂) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact hδ
  have hft := ftY_moveQ sel mu cst hcst P hP hD ⟨g, hgI⟩ (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ (g.symm y₁) hδ' hq
  have h1 : redMQ P.1 j.toLinearMap * redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap = 1 := by
    have := redMQ_mul_inv P.1 hjiI
    rwa [inv_inv] at this
  have h2 : redMQ P.1 g.toLinearMap * redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap = 1 := by
    have := redMQ_mul_inv P.1 hgiI
    rwa [inv_inv] at this
  have hphi : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
      ((j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap ∘ₗ (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ
        g.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
      xiZ ξ ((redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap).submatrix (Fin.castLE hrA) (Fin.castLE hrA)).det *
        xiZ ξ ((redMQ P.1 g.toLinearMap).submatrix (Fin.castLE hr') (Fin.castLE hr')).det *
        PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
          (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
    unfold PhiTopG
    rw [if_neg hP]
    exact phiQ_law hqm hu ξ R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0 hr' hrA hgI hjiI _ _ _
      (fun v hv => redV_map P.1 _ (glint_int P.1 hjiI) hv) lA lAi lB lC h1 h2 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y)

  have hs1 : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) = xiZ ξ⁻¹ (redMQ P.1 g.toLinearMap).det := by
    unfold rhoS
    rw [if_neg hP, unitV_eq, redP_detEquiv P.1 hgI]
  have hdet : ((LinearEquiv.det g' : X.Eˣ) : X.E) = ((LinearEquiv.det j : X.Eˣ) : X.E) :=
    det_eq_of_blk (by omega) g' j hpr hat
  have hs2 : rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) = xiZ ξ (redMQ P.1 j.toLinearMap).det := by
    unfold rhoT
    rw [if_neg hP, unitV_eq, hdet, redP_detEquiv P.1 hjI]
  have hz' : rowChrTop Ch mu cst.sharp (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1 j.toLinearMap =
      (xiZ ξ ((redMQ P.1 j.toLinearMap).submatrix (brI hnA) (brI hnA)).det)⁻¹ := by
    unfold rowChrTop
    rw [if_neg hP]
    exact lamQB_eq ξ (kj := R.r) (r := R.r) (n := R.N (m2 + 1 + 1) - 1 + 0) (c := 0) (d := R.m * R.t) rfl hnA hjI (rr := j)
      (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have hz : chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) rc =
      (xiZ ξ ((redMQ P.1 g.toLinearMap).submatrix (brI hn') (brI hn')).det)⁻¹ := by
    unfold chiInv
    rw [hOk.last_h]
    have hrange : Finset.range (cOf R (m2 + 1) - 1) = ∅ := by
      rw [cOf_topB hm]
      rfl
    have hn1 : Loc.n1Arg rc = 0 := by
      unfold Loc.n1Arg
      rw [hrange, Finset.sum_empty]
    have hone : ((1 : AutY X R (m2 + 1))⁻¹ * rc * 1 : AutY X R (m2 + 1)) = rc := by simp
    rw [hn1, hcst.psi_int _ 0 ciIntAt_zero, inv_one, one_mul, hone]
    unfold lamRow
    rw [if_neg hP, lamQB_eq _ hkj hn' hgI hxc]
  have hS := scal_law ξ hnA hn' hrA hr' (redMQ P.1 (j⁻¹ : Sp X.E (R.N (m2 + 1 + 1) - 1 + 0) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1) - 1 + 0)).toLinearMap)
    (redMQ P.1 j.toLinearMap) (redMQ P.1 g.toLinearMap) (redMQ P.1 (g⁻¹ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap) lA lC h1 h2
  have k1 := xiZ_br_inv ξ hnA _ _ lA (redMQ_mul_inv P.1 hjI)
  have k2 := xiZ_br_inv ξ hn' _ _ lC (redMQ_mul_inv P.1 hgI)
  unfold topDat
  rw [eX, hphi, hz', hz, hs1, hs2, eT, hft]
  exact fin_alg _ _ _ _ _ _ _ _ _ _ hS k1 k2

end GlobalTheory.TwTopLaw
