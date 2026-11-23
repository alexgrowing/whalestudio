import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut.FL

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

variable {k r : ℕ}

def InW (k r : ℕ) (z x : Fin (2 * r + k + 1) → ℂ) : Prop := inWb k r x ∧ herm (Hpk k r) x z = 0

theorem herm_alt {z : Fin (2 * r + k + 1) → ℂ} : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := P.Qx2.herm_star (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem blockProjection_add (x y : Fin (2 * r + k + 1) → ℂ) : SSn.wbP k r (x + y) = SSn.wbP k r x + SSn.wbP k r y := by
  funext i; simp only [SSn.wbP, Pi.add_apply]; split_ifs <;> simp

theorem blockProjection_smul (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) : SSn.wbP k r (c • x) = c • SSn.wbP k r x := by
  funext i; simp only [SSn.wbP, Pi.smul_apply]; split_ifs <;> simp

theorem blockProjection_mem_block (x : Fin (2 * r + k + 1) → ℂ) : inWb k r (SSn.wbP k r x) := by
  intro i hi; unfold SSn.wbP; rw [if_neg (by omega)]

theorem prWv_add (z x y : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (x + y) = SSn.prWv k r z x + SSn.prWv k r z y := by
  unfold SSn.prWv
  rw [blockProjection_add, P.Qx8.herm_add_left', add_div, add_smul]
  abel

theorem prWv_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (c • x) = c • SSn.prWv k r z x := by
  unfold SSn.prWv
  rw [blockProjection_smul, P.Qx8.herm_smul_left', smul_add, smul_smul, mul_div_assoc]

theorem inWb_add {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x + y) := by
  intro i hi; simp [hx i hi, hy i hi]

theorem inWb_smul (c : ℂ) {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : inWb k r (c • x) := by
  intro i hi; simp [hx i hi]

theorem prWv_inW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (y : Fin (2 * r + k + 1) → ℂ) :
    InW k r z (SSn.prWv k r z y) := by
  refine ⟨inWb_add (blockProjection_mem_block y) (inWb_smul _ hz), ?_⟩
  unfold SSn.prWv
  rw [P.Qx8.herm_add_left', P.Qx8.herm_smul_left', herm_alt]
  have : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp
  push_cast
  ring

theorem herm_cdAt {m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Fin m → ℂ} {x : E} (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f x)
    (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => herm Hm (f y) (g y)) x := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have e : (fun y => herm Hm (f y) (g y)) = fun y => ∑ i, starRingEnd ℂ (g y i) * (Hm *ᵥ f y) i := by
    funext y; simp [herm, dotProduct]
  rw [e]
  refine ContDiffAt.sum fun i _ => ?_
  exact (hconj.contDiffAt.comp x (contDiffAt_pi.1 hg i)).mul
    (((contDiff_apply ℝ ℂ i).comp (kap_mulVec_contDiff Hm)).contDiffAt.comp x hf)

theorem prWv_contDiff (z : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => SSn.prWv k r z a) := by
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun a => SSn.prWv k r z a
      map_add' := prWv_add z
      map_smul' := fun c x => prWv_smul z c x }
  have h := ((LinearMap.toContinuousLinearMap L).contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  convert h using 1
  funext a
  rfl

def hh (k r : ℕ) (u x : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  x + (-(2 * herm (Hpk k r) x u / herm (Hpk k r) u u)) • u

theorem herm_hh (u x y : Fin (2 * r + k + 1) → ℂ) {t : ℝ} (ht : herm (Hpk k r) u u = (t : ℂ)) (ht0 : t ≠ 0) :
    herm (Hpk k r) (hh k r u x) (hh k r u y) = herm (Hpk k r) x y := by
  unfold hh
  rw [Qx8.herm_add_left', Qx8.herm_add_right', Qx8.herm_add_right', Qx8.herm_smul_left', Qx8.herm_smul_left',
    Qx8.herm_smul_right', Qx8.herm_smul_right', ht, ← Qx8.herm_conj y u]
  have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  simp only [star_neg, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, map_ofNat]
  field_simp
  ring

def phi (k r : ℕ) (e₀ b : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  starRingEnd ℂ (herm (Hpk k r) b e₀) /
    ((Real.sqrt (herm (Hpk k r) b b).re * ‖herm (Hpk k r) b e₀‖ : ℝ) : ℂ)

def ehat (k r : ℕ) (e₀ b : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := phi k r e₀ b • b

def uu (k r : ℕ) (e₀ b : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := e₀ + ehat k r e₀ b

theorem ehat_facts {e₀ b : Fin (2 * r + k + 1) → ℂ} (hN : 0 < (herm (Hpk k r) b b).re)
    (hs : herm (Hpk k r) b e₀ ≠ 0) :
    herm (Hpk k r) (ehat k r e₀ b) (ehat k r e₀ b) = 1 ∧
      herm (Hpk k r) (ehat k r e₀ b) e₀ =
        ((‖herm (Hpk k r) b e₀‖ / Real.sqrt (herm (Hpk k r) b b).re : ℝ) : ℂ) ∧ phi k r e₀ b ≠ 0 := by
  have hbb : herm (Hpk k r) b b = (((herm (Hpk k r) b b).re : ℝ) : ℂ) := SSn.Geom.herm_self_real b
  set N : ℝ := (herm (Hpk k r) b b).re with hNdef
  set sv : ℂ := herm (Hpk k r) b e₀ with hsv
  have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hm : 0 < ‖sv‖ := norm_pos_iff.2 hs
  have hq2 : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hN.le]
  have hcs : starRingEnd ℂ sv * sv = ((‖sv‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' sv
  have hq0 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm0 : ((‖sv‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold ehat
    rw [Qx8.herm_smul_left', Qx8.herm_smul_right', hbb]
    unfold phi
    rw [← hsv, ← hNdef]
    simp only [star_div₀, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
    push_cast
    rw [show starRingEnd ℂ sv / (↑(Real.sqrt N) * ↑‖sv‖) * (sv / (↑(Real.sqrt N) * ↑‖sv‖) * ↑N) =
      (starRingEnd ℂ sv * sv) * ↑N / ((↑(Real.sqrt N)) ^ 2 * (↑‖sv‖) ^ 2) by ring, hcs, hq2]
    field_simp
  · unfold ehat
    rw [Qx8.herm_smul_left']
    unfold phi
    rw [← hsv, ← hNdef]
    push_cast
    rw [show starRingEnd ℂ sv / (↑(Real.sqrt N) * ↑‖sv‖) * sv = (starRingEnd ℂ sv * sv) / (↑(Real.sqrt N) * ↑‖sv‖) by ring,
      hcs]
    field_simp
  · unfold phi
    refine div_ne_zero ?_ ?_
    · rwa [ne_eq, map_eq_zero]
    · push_cast; exact mul_ne_zero hq0 hm0

theorem uu_facts {e₀ b : Fin (2 * r + k + 1) → ℂ} (he : herm (Hpk k r) e₀ e₀ = 1) (hN : 0 < (herm (Hpk k r) b b).re)
    (hs : herm (Hpk k r) b e₀ ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ herm (Hpk k r) (uu k r e₀ b) (uu k r e₀ b) = ((2 + 2 * c : ℝ) : ℂ) ∧
      hh k r (uu k r e₀ b) e₀ = -ehat k r e₀ b := by
  obtain ⟨h1, hc, -⟩ := ehat_facts hN hs
  set c : ℝ := ‖herm (Hpk k r) b e₀‖ / Real.sqrt (herm (Hpk k r) b b).re with hcdef
  have hc0 : 0 ≤ c := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hc' : herm (Hpk k r) e₀ (ehat k r e₀ b) = (c : ℂ) := by
    rw [← Qx8.herm_conj, hc, Complex.star_def, Complex.conj_ofReal]
  have heu : herm (Hpk k r) e₀ (uu k r e₀ b) = ((1 + c : ℝ) : ℂ) := by
    unfold uu; rw [Qx8.herm_add_right', he, hc']; push_cast; ring
  have huu : herm (Hpk k r) (uu k r e₀ b) (uu k r e₀ b) = ((2 + 2 * c : ℝ) : ℂ) := by
    unfold uu
    rw [Qx8.herm_add_left', Qx8.herm_add_right', Qx8.herm_add_right', he, hc', hc, h1]
    push_cast; ring
  refine ⟨c, hc0, huu, ?_⟩
  have h2 : (2 : ℂ) + 2 * (c : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 + 2 * c := by linarith
    exact_mod_cast this.ne'
  have hco : 2 * herm (Hpk k r) e₀ (uu k r e₀ b) / herm (Hpk k r) (uu k r e₀ b) (uu k r e₀ b) = 1 := by
    have h1c : (1 : ℂ) + (c : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 1 + c := by linarith
      exact_mod_cast this.ne'
    rw [heu, huu]; push_cast; field_simp
  unfold hh
  rw [hco]
  unfold uu
  rw [neg_one_smul]
  abel

theorem frame_cast {m m' : ℕ} (h : m' = m) {vs : List (Fin (2 * r + k + 1) → ℂ)}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r vs Bs) :
    IsFrameOf k r vs (fun t : Fin m' => Bs (Fin.cast h t)) := by
  subst h
  simpa using hB

theorem frame_at {z e₀ b : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameOf k r [z, e₀] F) (he₀ : InW k r z e₀) (he : herm (Hpk k r) e₀ e₀ = 1)
    (hb : InW k r z b) (hN : 0 < (herm (Hpk k r) b b).re) (hs : herm (Hpk k r) b e₀ ≠ 0) :
    IsFrameOf k r [z, b] (fun t => hh k r (uu k r e₀ b) (F t)) := by
  obtain ⟨-, -, hφ⟩ := ehat_facts hN hs
  obtain ⟨c, hc0, huu, hhe⟩ := uu_facts he hN hs
  have hc2 : (2 + 2 * c : ℝ) ≠ 0 := by linarith
  have huW : inWb k r (uu k r e₀ b) :=
    inWb_add he₀.1 (inWb_smul _ hb.1)
  have huz : herm (Hpk k r) (uu k r e₀ b) z = 0 := by
    unfold uu ehat; rw [Qx8.herm_add_left', Qx8.herm_smul_left', he₀.2, hb.2]; ring
  refine ⟨fun t => ?_, fun t t' => ?_, fun t v hv => ?_⟩
  · unfold hh; exact inWb_add (hF.1 t) (inWb_smul _ huW)
  · rw [herm_hh _ _ _ huu hc2]; exact hF.2.1 t t'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h <;> subst h
    · unfold hh
      rw [Qx8.herm_add_left', Qx8.herm_smul_left', hF.2.2 t v (by simp), huz]; ring
    · have hkey : herm (Hpk k r) (hh k r (uu k r e₀ v) (F t)) (hh k r (uu k r e₀ v) e₀) = 0 := by
        rw [herm_hh _ _ _ huu hc2]; exact hF.2.2 t e₀ (by simp)
      have hv' : v = (-(phi k r e₀ v)⁻¹) • hh k r (uu k r e₀ v) e₀ := by
        rw [hhe]; unfold ehat; rw [smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hφ, one_smul]
      have := Qx8.herm_smul_right' (Hpk k r) (-(phi k r e₀ v)⁻¹) (hh k r (uu k r e₀ v) (F t)) (hh k r (uu k r e₀ v) e₀)
      rw [← hv', hkey, mul_zero] at this
      exact this

theorem frame_locality_holds : FrameLoc := by
  intro k r z hk hz hT a₀ ha₀
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  set b : (Fin (2 * r + k + 1) → ℂ) → (Fin (2 * r + k + 1) → ℂ) := fun a => SSn.prWv k r z a with hbdef
  have hbW : ∀ a, InW k r z (b a) := fun a => prWv_inW hz hT a
  have hbc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := prWv_contDiff z
  set N₀ : ℝ := (herm (Hpk k r) (b a₀) (b a₀)).re with hN₀def
  have hN₀ : 0 < N₀ := ha₀
  have hq : 0 < Real.sqrt N₀ := Real.sqrt_pos.2 hN₀
  set e₀ : Fin (2 * r + k + 1) → ℂ := (((Real.sqrt N₀)⁻¹ : ℝ) : ℂ) • b a₀ with he₀def
  have he₀W : InW k r z e₀ :=
    ⟨inWb_smul _ (hbW a₀).1, by rw [he₀def, Qx8.herm_smul_left', (hbW a₀).2, mul_zero]⟩
  have hbb₀ : herm (Hpk k r) (b a₀) (b a₀) = (N₀ : ℂ) := SSn.Geom.herm_self_real (b a₀)
  have he₀1 : herm (Hpk k r) e₀ e₀ = 1 := by
    rw [he₀def, Qx8.herm_smul_left', Qx8.herm_smul_right', hbb₀, Complex.star_def, Complex.conj_ofReal]
    have hq2 : ((Real.sqrt N₀ : ℝ) : ℂ) ^ 2 = (N₀ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hN₀.le]
    have hq0 : ((Real.sqrt N₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    rw [← hq2]
    field_simp
  have hs₀ : herm (Hpk k r) (b a₀) e₀ ≠ 0 := by
    rw [he₀def, Qx8.herm_smul_right', hbb₀, Complex.star_def, Complex.conj_ofReal]
    have : (0 : ℝ) < (Real.sqrt N₀)⁻¹ * N₀ := mul_pos (inv_pos.2 hq) hN₀
    exact_mod_cast this.ne'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨F₀, hF₀⟩ := exists_frame_two n r z e₀ hz hT he₀W.1 he₀W.2 he₀1
  have hF := frame_cast (m' := n + 1 - 1) (by omega) hF₀
  set F : Fin (n + 1 - 1) → Fin (2 * r + (n + 1) + 1) → ℂ := fun t => F₀ (Fin.cast (by omega) t) with hFdef
  refine ⟨fun a t => hh (n + 1) r (uu (n + 1) r e₀ (b a)) (F t), ?_, ?_⟩
  ·
    have hsa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => herm (Hpk (n + 1) r) (b a) e₀) a₀ :=
      herm_cdAt _ hbc.contDiffAt contDiffAt_const
    have hNa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => (herm (Hpk (n + 1) r) (b a) (b a)).re) a₀ :=
      Complex.reCLM.contDiff.contDiffAt.comp a₀ (herm_cdAt _ hbc.contDiffAt hbc.contDiffAt)
    have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => Real.sqrt (herm (Hpk (n + 1) r) (b a) (b a)).re) a₀ :=
      hNa.sqrt hN₀.ne'
    have hnm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ‖herm (Hpk (n + 1) r) (b a) e₀‖) a₀ :=
      hsa.norm ℝ hs₀
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun a => ((Real.sqrt (herm (Hpk (n + 1) r) (b a) (b a)).re * ‖herm (Hpk (n + 1) r) (b a) e₀‖ : ℝ) : ℂ)) a₀ :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp a₀ (hsq.mul hnm)
    have hden0 : ((Real.sqrt (herm (Hpk (n + 1) r) (b a₀) (b a₀)).re * ‖herm (Hpk (n + 1) r) (b a₀) e₀‖ : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt N₀ * ‖herm (Hpk (n + 1) r) (b a₀) e₀‖ := mul_pos hq (norm_pos_iff.2 hs₀)
      exact_mod_cast this.ne'
    have hphi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => phi (n + 1) r e₀ (b a)) a₀ :=
      by
        have h := (hconj.contDiffAt.comp a₀ hsa).mul (hden.inv hden0)
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun a => ?_)
        show phi (n + 1) r e₀ (b a) = _
        unfold phi
        rw [div_eq_mul_inv]
        rfl
    have hu : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => uu (n + 1) r e₀ (b a)) a₀ :=
      contDiffAt_const.add (hphi.smul hbc.contDiffAt)
    obtain ⟨c, hc0, huu, -⟩ := uu_facts he₀1 hN₀ hs₀
    have huu0 : herm (Hpk (n + 1) r) (uu (n + 1) r e₀ (b a₀)) (uu (n + 1) r e₀ (b a₀)) ≠ 0 := by
      rw [huu]
      have : (0 : ℝ) < 2 + 2 * c := by linarith
      exact_mod_cast this.ne'
    refine contDiffAt_pi.2 fun t => ?_
    have hq' := ((contDiffAt_const (c := (2 : ℂ))).mul (herm_cdAt (Hpk (n + 1) r) (contDiffAt_const (c := F t)) hu)).mul
      ((herm_cdAt (Hpk (n + 1) r) hu hu).inv huu0)
    have h := (contDiffAt_const (c := F t)).add ((hq'.neg).smul hu)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun a => ?_)
    show hh (n + 1) r (uu (n + 1) r e₀ (b a)) (F t) = _
    unfold hh
    rw [div_eq_mul_inv]
    rfl
  · have hsa : ContinuousAt (fun a => herm (Hpk (n + 1) r) (b a) e₀) a₀ :=
      (herm_cdAt _ hbc.contDiffAt contDiffAt_const).continuousAt
    have hNa : ContinuousAt (fun a => (herm (Hpk (n + 1) r) (b a) (b a)).re) a₀ :=
      (Complex.reCLM.contDiff.contDiffAt.comp a₀ (herm_cdAt _ hbc.contDiffAt hbc.contDiffAt)).continuousAt
    filter_upwards [hNa.eventually (lt_mem_nhds hN₀), hsa.eventually_ne hs₀] with a hNa' hsa'
    exact frame_at hF he₀W he₀1 (hbW a) hNa' hsa'

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut.FL

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

theorem frame_locality_holds : FrameLoc := FL.frame_locality_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
