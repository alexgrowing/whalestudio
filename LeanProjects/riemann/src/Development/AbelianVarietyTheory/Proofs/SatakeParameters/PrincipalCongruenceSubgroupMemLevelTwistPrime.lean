import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TwistCong

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem sclLat_zero (q N : ℕ) : LocE.sclLat P q N (fun _ => 0) = stdAt E N P := by
  ext x
  rw [CongLevel.mem_sclLat, mem_stdAt]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P := by
  have e : LocE.scE n 0 = fun _ => (0 : ℤ) := by
    funext l
    unfold LocE.scE
    split_ifs <;> simp
  unfold LocE.lamY
  rw [e, sclLat_zero]

theorem inX_mem_std {n : ℕ} (c : ℕ) {x : Sp E n} (hx : x ∈ stdAt E n P) : Loc.inX E n c x ∈ stdAt E (n + c) P := by
  refine mem_stdAt.2 fun l => ?_
  rw [CongLevel.inX_apply]
  split_ifs
  · exact mem_stdAt.1 hx _
  · exact intAt_zero

theorem resX_mem_std {n : ℕ} (c : ℕ) {v : Sp E (n + c)} (hv : v ∈ stdAt E (n + c) P) :
    CongLevel.resX c v ∈ stdAt E n P :=
  mem_stdAt.2 fun i => mem_stdAt.1 hv (Fin.castAdd c i)

theorem stab_of_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P)
    (hg' : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) : g ∈ stabL E N (stdAt E N P) := by
  have hq := qOf_ne_zero (P := P)
  have maps : ∀ f : Sp E N ≃ₗ[E] Sp E N, (∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (f x - x) ∈ stdAt E N P) →
      ∀ x ∈ stdAt E N P, f x ∈ stdAt E N P := by
    intro f hf x hx
    have e : f x = x + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (f x - x)) := by
      rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
    rw [e]
    exact add_mem hx (smul_mem_locP (intAt_nat _) (hf x hx))
  intro x
  refine ⟨fun hx => ?_, maps g hg x⟩
  have := maps g⁻¹ hg' _ hx
  rwa [show g⁻¹ (g x) = x from LinearEquiv.symm_apply_apply _ x] at this

theorem conj_extE_cong {n c : ℕ} (j D : ℕ) (hjD : j + 1 ≤ D) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hb : ∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ (((qOf P : ℕ) : E) ^ j) • h x ∈ stdAt E (n + c) P)
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : ∀ y ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ D)⁻¹ • (κ y - y) ∈ stdAt E n P) :
    ∀ x ∈ stdAt E (n + c) P, ((qOf P : ℕ) : E)⁻¹ • ((h⁻¹ * CongLevel.extE c κ * h) x - x) ∈ stdAt E (n + c) P := by
  intro x hx
  have hq := qOf_ne_zero (P := P)
  set q : E := ((qOf P : ℕ) : E) with hqdef
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjD
  have hy := (hb x hx).2
  set y := q ^ j • h x with hydef
  have hhx : h x = (q ^ j)⁻¹ • y := by
    rw [hydef, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hq), one_smul]
  have hres := resX_mem_std c hy
  have hk := hκ _ hres
  have e1 : (h⁻¹ * CongLevel.extE c κ * h) x - x = h⁻¹ (CongLevel.extE c κ (h x) - h x) := by
    rw [map_sub]
    show h.symm (CongLevel.extE c κ (h x)) - x = h.symm (CongLevel.extE c κ (h x)) - h.symm (h x)
    rw [LinearEquiv.symm_apply_apply]
  have e2 : CongLevel.extE c κ (h x) - h x =
      Loc.inX E n c ((q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [CongLevel.extE_apply, add_sub_cancel_left, hhx, map_smul, map_smul, smul_sub]
  have e3 : q⁻¹ • (q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y) =
      q ^ d • ((q ^ (j + 1 + d))⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
    ring
  rw [e1, e2, ← map_smul, ← map_smul, e3]
  refine (hb _ (inX_mem_std c ?_)).1
  exact smul_mem_locP (intAt_pow (intAt_nat _) d) hk

theorem entry_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P) (l i : ℕ) (hl : l < N) (hi : i < N) :
    IntAt P (Loc.atN (g (Loc.eN E N l)) i) ∧ redP P (Loc.atN (g (Loc.eN E N l)) i) = if i = l then 1 else 0 := by
  have hq := qOf_ne_zero (P := P)
  have he : Loc.eN E N l ∈ stdAt E N P := mem_stdAt.2 fun m => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hy := mem_stdAt.1 (hg _ he) ⟨i, hi⟩
  have e : g (Loc.eN E N l) = Loc.eN E N l + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) := by
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
  have ee : Loc.atN (g (Loc.eN E N l)) i = (if i = l then (1 : E) else 0) +
      ((qOf P : ℕ) : E) * (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) ⟨i, hi⟩ := by
    conv_lhs => rw [e]
    unfold Loc.atN
    rw [dif_pos hi]
    simp [Loc.eN]
  have h1 : IntAt P (if i = l then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have h2 := (intAt_nat (P := P) (qOf P)).mul hy
  rw [ee]
  refine ⟨h1.add h2, ?_⟩
  rw [reduction_add h1 h2, reduction_mul (intAt_nat _) hy, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Lat

open GlobalTheory.TopStep in

theorem cong_mem_prCat_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P hP C hC
  have hq := qOf_ne_zero (P := P.1)
  have hstd : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E (R.N j + cOf R j) P.1 := by
    unfold lamYat
    rw [if_neg hP]
    exact lamY_zero _ _ _
  have hD : j + 1 ≤ cst.D P := by
    have h1 := hL.depthQ' P hP
    have h2 := hL.hm
    omega
  have hb : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
      (((qOf P.1 : ℕ) : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    intro x hx
    rw [← hstd] at hx ⊢
    exact hL.boundQ j b P hP x hx
  have hκ : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1 y - y) ∈ stdAt X.E (R.N j) P.1 :=
    mem_prinCong.1 hC
  have hκ' : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1⁻¹ y - y) ∈ stdAt X.E (R.N j) P.1 :=
by
    intro y hy
    have h0 := mem_prinCong.1 (inv_mem hC) y hy
    rwa [Subgroup.coe_inv] at h0
  have hg := conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1 hκ
  have hg' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, ((qOf P.1 : ℕ) : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ x - x) ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    have e : ((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1⁻¹ * L.h j b P := by
      rw [← CongLevel.extE_inv]
      group
    rw [e]
    exact conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1⁻¹ hκ'
  have hs := stab_of_cong _ hg hg'
  refine ⟨CongLevel.extE (cOf R j) C.1, ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ C.1, ?_⟩, CongLevel.extE_inX _ C.1, ?_⟩
  · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P := by simp
    show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) ∈ Jat (Pr := Pr) cst.sharp j P.1
    rw [e]
    unfold Jat
    rw [if_neg hP]
    refine ⟨hs, ?_⟩
    have ep : LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) =
        LocE.sclLat P.1 (qOf P.1) (R.N j + cOf R j)
          (fun l => (fun _ => (0 : ℤ)) l + if R.k + j ≤ l ∧ l < R.N j then 1 else 0) := by
      unfold LocE.parL
      congr 1
      funext l
      simp
    have hM : ∀ _s : ℕ, LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) ≤ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro _
      rw [ep, ← sclLat_zero (P := P.1) (qOf P.1)]
      exact CongLevel.sclLat_le P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j)
    have hM' : ∀ (_s : ℕ) (x : Sp X.E (R.N j + cOf R j)), ((qOf P.1 : ℕ) : X.E)⁻¹ • x ∈ stdAt X.E (R.N j + cOf R j) P.1 →
        x ∈ LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
      intro _ x hx
      rw [ep]
      rw [← sclLat_zero (P := P.1) (qOf P.1)] at hx
      exact CongLevel.smul_mem_sclLat P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j) x hx
    exact (CongLevel.mem_flagU (qOf P.1) (stdAt X.E (R.N j + cOf R j) P.1)
      (fun _ => LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j)) (fun _ => 0) 0 Set.univ hM hM'
      (fun _ => zero_mem _) _ hs hg).1 0 trivial
  · unfold chiInv
    have hn : Loc.n1Arg (CongLevel.extE (cOf R j) C.1) = 0 := by
      unfold Loc.n1Arg
      refine Finset.sum_eq_zero fun i _ => ?_
      have e : CongLevel.extE (cOf R j) C.1 (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) =
          Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1) := by
        rw [show R.N j + i + 1 = R.N j + (i + 1) by ring, CongLevel.extE_apply, CongLevel.resX_eN]
        simp
      rw [e]
      unfold Loc.atN
      split_ifs with h1
      · simp [Loc.eN]
      · rfl
    rw [hn, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul]
    unfold lamRow
    rw [if_neg hP]
    unfold LocE.lamQB
    rw [GlobalTheory.LamRowCong.unitV_det_eq_one, inv_one]
    · intro s t
      have := s.2
      have := t.2
      exact (entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).1
    · ext s t
      have := s.2
      have := t.2
      rw [Matrix.map_apply, Matrix.one_apply]
      show redP P.1 (Loc.atN (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)
        (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1)) = _
      rw [(entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).2]
      by_cases hst : s = t
      · subst hst
        simp
      · rw [if_neg (fun e => hst (Fin.ext (by omega))), if_neg hst]

end GlobalTheory.TwistCong
