import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalApproximationsDifferByCongruentToOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldIsoMatrixCongruenceAutomorphismCongruenceStatement

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplLev

theorem cong_of_nearAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E)
    (hn : 0 < n) (h₁ : NearAt P n x g₁) (h₂ : NearAt P n x g₂) (a b : Fin N) :
    IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) :=
  GlobalTheory.T.rationalApproximations_differ_by_congruent_to_one P n x g₁ g₂ hn h₁ h₂ a b

theorem cong_seam {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (g : Sp X.E N ≃ₗ[X.E] Sp X.E N)
    (h : ∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) :
    ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) :=
  GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence s P n g h

section Cong1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine GlobalTheory.T.mem_parahoric_of_cong_one_mod_q P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end Cong1

section Lift

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem levAt_mul {n : ℕ} {Λ : LevFam X.E X.K n Pr.vGs} {Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))} {P : rowSG Pr sel mu}
    {κ κ₂ : GLint X.E n P.1} {c c₂ : X.Kˣ} (h : LevAt Λ Θ P κ c) (h₂ : LevAt Λ Θ P κ₂ c₂) : LevAt Λ Θ P (κ * κ₂) (c * c₂) := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · obtain ⟨h1, e1⟩ := h.1 hP
    obtain ⟨h2, e2⟩ := h₂.1 hP
    refine ⟨by rw [map_mul]; exact mul_mem h1 h2, ?_⟩
    rw [e1, e2, ← map_mul]
    exact congrArg _ (Subtype.ext (map_mul _ _ _).symm)
  · obtain ⟨h1, e1⟩ := h.2 hQ hP
    obtain ⟨h2, e2⟩ := h₂.2 hQ hP
    exact ⟨mul_mem h1 h2, by rw [e1, e2, ← map_mul]; rfl⟩

theorem levAt_of_lift (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (b : L.β j) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N j) P.1)
    (r : AutY X R j) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P))
    (hrx : ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (κ.1 x)) :
    ∃ c : X.Kˣ, LevAt (L.levG j b) (L.levQ j b) P κ c ∧ (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · have hmem : GlobalTheory.TopStep.redGL _ P.1 κ ∈ (L.levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨κ.1, ⟨r, hr, hrx⟩, fun x hx => GlobalTheory.TopStep.redV_redGL κ hx⟩
    refine ⟨(L.levG j b ⟨P.1, hP⟩).lam ⟨_, hmem⟩, ⟨fun hP' => ⟨hmem, rfl⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
    exact hL.chrG j b ⟨P.1, hP⟩ ⟨_, hmem⟩ κ.1 r hr hrx fun x hx => GlobalTheory.TopStep.redV_redGL κ hx
  · have hQ := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    have hmem : κ ∈ (L.levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ, Subgroup.mem_subgroupOf]
      exact ⟨r, hr, hrx⟩
    refine ⟨(L.levQ j b ⟨P.1, hQ⟩).lam ⟨κ, hmem⟩, ⟨fun hP' => absurd hP' hP, fun _ _ => ⟨hmem, rfl⟩⟩, ?_⟩
    exact hL.chrQ j b ⟨P.1, hQ⟩ ⟨κ, hmem⟩ r hr hrx

end Lift

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem levAt_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β' κ' κ'' hfr
  classical
  have hL := t.idx_ok μ
  have hC := hTie.levCpl β'
  have hU := (((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U_eq κ'.1).1 κ'.2
  have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
    intro P
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g zz hg using fun P : SB t μ => hC.1 P _ (hov P) κ'.1 hU.1 (hU.2 _)
  have hchi := hC.2.2 κ' g zz hg
  have key : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
      ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P)⁻¹ c ∧ (c : t.X.K) = zz P := by
    intro P
    obtain ⟨⟨r, hr, hrx, hz⟩, -⟩ := (hg P).1
    have hgint : g P ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := hL.int _ _ P ⟨r, hr, hrx⟩
    set κg : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := ⟨g P, hgint⟩ with hκg
    set k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := κg⁻¹ * (κ'' P)⁻¹ with hk
    have hcg := cong_of_nearAt (seamP t.seam P.1) ((t.cst μ).D P) _ _ _ (hL.cst_ok.D_pos P) (hg P).2 (hfr P)
    rw [← map_inv, ← map_mul] at hcg
    have hk1 := cong_seam t.seam P.1 ((t.cst μ).D P) k.1 hcg
    obtain ⟨rk, hrk, hrkx, hchik⟩ := cong_mem_level_chr_one t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hPin.fields t.pr_ok hL
      (t.m2 + 1) le_rfl (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k.1 hk1
    obtain ⟨c1, hl1, hc1⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P κg r hr hrx
    obtain ⟨c2, hl2, hc2⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k rk hrk hrkx
    have e : κg * k = (κ'' P)⁻¹ := by rw [hk, mul_inv_cancel_left]
    refine ⟨c1 * c2, e ▸ levAt_mul hl1 hl2, ?_⟩
    rw [Units.val_mul, hc1, hc2, hchik, mul_one, hz]
  choose c hc hcv using key
  refine ⟨fun P => (c P)⁻¹, fun P => by have h := (hc P).inv; rwa [inv_inv] at h, ?_⟩
  have e1 : ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (∏ P, zz P)⁻¹ := by
    rw [Units.coe_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun P _ => by rw [Units.val_inv_eq_inv_val, hcv P]
  have e2 := eq_inv_of_mul_eq_one_left hchi
  have e3 : t.seam.σ₀ ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (t.seam.σ₀ (∏ P, zz P))⁻¹ := by
    rw [e1, map_inv₀]
  exact e3.trans e2.symm

end Main

end GlobalTheory.CplLev

end
