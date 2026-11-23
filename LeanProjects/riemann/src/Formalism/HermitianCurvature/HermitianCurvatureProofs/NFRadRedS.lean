import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedS

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical

def LocSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ g₀ ∈ Glev k r (Fin.last r), 0 < GGl k r z z' g₀ →
      ∃ V : Set (Q.Mx k r), IsOpen V ∧ g₀ ∈ V ∧ ∃ a b : Q.Mx k r → Q.Mx k r,
        ContDiffOn ℝ ∞ a V ∧ ContDiffOn ℝ ∞ b V ∧
        ∀ g ∈ V, g ∈ Glev k r (Fin.last r) → 0 < GGl k r z z' g →
          a g ∈ UWset k r z ∧ b g ∈ UWset k r z' ∧
            g = a g * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * b g

def RepSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ h₀ ∈ UWset k r z, ∃ V : Set (Q.Mx k r), IsOpen V ∧ h₀ ∈ V ∧ ∃ P : Q.Mx k r → (Wp →L[ℂ] Wp),
      ContDiffOn ℝ ∞ P V ∧ ∀ h ∈ V, h ∈ UWset k r z → π h = P h

theorem contDiff_clm_comp {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] :
    ContDiff ℝ ∞ (fun p : (F →L[ℂ] G) × (E →L[ℂ] F) => p.1.comp p.2) := by
  have h := (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := E) (F := F) (G := G)).contDiff (n := ∞)
  exact h.restrict_scalars ℝ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {g h : Q.Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) :
    g * h ∈ UWset k r z := by
  obtain ⟨hu, hb, hz⟩ := hg
  obtain ⟨hu', hb', hz'⟩ := hh
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hu
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hu'
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · rw [← Matrix.mulVec_mulVec, (hb' a).1, (hb a).1]
  · rw [← Matrix.mulVec_mulVec, (hb' a).2, (hb a).2]
  · rw [← Matrix.mulVec_mulVec, hz', hz]

private theorem isUnit_det_of_mem_uwset {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) :
    IsUnit g.det := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
  have hH : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h2
  rw [← h2] at hH
  simp at hH

theorem uw_inv_mul {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul g (isUnit_det_of_mem_uwset hg)

theorem uw_mul_inv {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (isUnit_det_of_mem_uwset hg)

private theorem inv_mem_uwset_of_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) :
    g⁻¹ ∈ UWset k r z := by
  have hi : g⁻¹ * g = 1 := uw_inv_mul hg
  have hi' : g * g⁻¹ = 1 := uw_mul_inv hg
  have fix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := fun v hv => by
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  obtain ⟨hu, hb, hz⟩ := hg
  refine ⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hu
  have hci : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hi', Matrix.conjTranspose_one]
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [e1]
    _ = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hci, hi', Matrix.one_mul, Matrix.mul_one]

theorem wd (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π') {ζ : ℂ}
    {X : Wq →L[ℂ] Wp} (hX : X ∈ Fib k r z z' μsec π π' ζ)
    {a₁ a₂ b₁ b₂ : Q.Mx k r} (ha₁ : a₁ ∈ UWset k r z) (ha₂ : a₂ ∈ UWset k r z) (hb₁ : b₁ ∈ UWset k r z')
    (hb₂ : b₂ ∈ UWset k r z') (he : a₁ * muZ k r μsec ζ * b₁ = a₂ * muZ k r μsec ζ * b₂) :
    (π a₁).comp (X.comp (π' b₁)) = (π a₂).comp (X.comp (π' b₂)) := by
  have hp : (a₂⁻¹ * a₁, b₁ * b₂⁻¹) ∈ Stab k r z z' μsec ζ := by
    refine ⟨uw_mul (inv_mem_uwset_of_mem ha₂) ha₁, uw_mul hb₁ (inv_mem_uwset_of_mem hb₂), ?_⟩
    show a₂⁻¹ * a₁ * muZ k r μsec ζ * (b₁ * b₂⁻¹) = muZ k r μsec ζ
    calc a₂⁻¹ * a₁ * muZ k r μsec ζ * (b₁ * b₂⁻¹) = a₂⁻¹ * (a₁ * muZ k r μsec ζ * b₁) * b₂⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = a₂⁻¹ * (a₂ * muZ k r μsec ζ * b₂) * b₂⁻¹ := by rw [he]
      _ = (a₂⁻¹ * a₂) * muZ k r μsec ζ * (b₂ * b₂⁻¹) := by simp only [Matrix.mul_assoc]
      _ = muZ k r μsec ζ := by rw [uw_inv_mul ha₂, uw_mul_inv hb₂, Matrix.one_mul, Matrix.mul_one]
  have hXp : (π (a₂⁻¹ * a₁)).comp (X.comp (π' (b₁ * b₂⁻¹))) = X := hX _ hp
  have ea : π a₁ = (π a₂).comp (π (a₂⁻¹ * a₁)) := by
    rw [← hπ.2 _ ha₂ _ (uw_mul (inv_mem_uwset_of_mem ha₂) ha₁), ← Matrix.mul_assoc, uw_mul_inv ha₂,
      Matrix.one_mul]
  have eb : π' b₁ = (π' (b₁ * b₂⁻¹)).comp (π' b₂) := by
    rw [← hπ'.2 _ (uw_mul hb₁ (inv_mem_uwset_of_mem hb₂)) _ hb₂, Matrix.mul_assoc, uw_inv_mul hb₂,
      Matrix.mul_one]
  rw [ea, eb]
  conv_rhs => rw [← hXp]
  simp only [ContinuousLinearMap.comp_assoc]

def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (φ : (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp)) :
    Q.Fn k r (Wq →L[ℂ] Wp) := fun c g =>
  if h : (c, g) ∈ DomR k r z z' ∧ ∃ p : Q.Mx k r × Q.Mx k r, p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z' ∧
      g = p.1 * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * p.2 then
    (π (Classical.choose h.2).1).comp ((φ (c, zetaL k r z z' (Fin.last r) g)).comp (π' (Classical.choose h.2).2))
  else 0

theorem qr_of_dp {c : Fin r → ℂ} {g : Q.Mx k r} (hc : c ∈ OmX r) (hg : g ∈ Qx5.Dp k r z z') :
    (c, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
  have h0 : 0 < GGl k r z z' g := hg
  unfold GGl at h0
  exact ⟨hc, by linarith⟩

theorem phi_val (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π')
    {φ : (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp)} (hφ : ∀ q ∈ QR k r z z', φ q ∈ Fib k r z z' μsec π π' q.2)
    {c : Fin r → ℂ} {g : Q.Mx k r} (hx : (c, g) ∈ DomR k r z z') {a b : Q.Mx k r} (ha : a ∈ UWset k r z)
    (hb : b ∈ UWset k r z') (hg : g = a * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * b) :
    Phi k r z z' μsec π π' φ c g = (π a).comp ((φ (c, zetaL k r z z' (Fin.last r) g)).comp (π' b)) := by
  have hq : (c, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := qr_of_dp hx.1 hx.2.2
  have hex : ∃ p : Q.Mx k r × Q.Mx k r, p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z' ∧
      g = p.1 * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * p.2 := ⟨(a, b), ha, hb, hg⟩
  unfold Phi
  rw [dif_pos ⟨hx, hex⟩]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  exact wd hπ hπ' (hφ _ hq) h1 ha h2 hb (h3.symm.trans hg)

private theorem mul_mul_mem_glev_last_of_mem_uwset {g h h' : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') : h * g * h' ∈ Glev k r (Fin.last r) := by
  obtain ⟨hu, hb, -⟩ := hh
  obtain ⟨hu', hb', -⟩ := hh'
  obtain ⟨hug, hbg⟩ := hg
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · show (h * g * h')ᴴ * Hpk k r * (h * g * h') = Hpk k r
    have e1 : hᴴ * Hpk k r * h = Hpk k r := hu
    have e2 : gᴴ * Hpk k r * g = Hpk k r := hug
    have e3 : h'ᴴ * Hpk k r * h' = Hpk k r := hu'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc h'ᴴ * (gᴴ * hᴴ) * Hpk k r * (h * g * h')
        = h'ᴴ * (gᴴ * (hᴴ * Hpk k r * h) * g) * h' := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2, e3]
  · rw [← Matrix.mulVec_mulVec, (hb' a).1, ← Matrix.mulVec_mulVec, (hbg a ha).1, (hb a).1]
  · rw [← Matrix.mulVec_mulVec, (hb' a).2, ← Matrix.mulVec_mulVec, (hbg a ha).2, (hb a).2]

private theorem one_mem_uwset_of_vec {z : Fin (2 * r + k + 1) → ℂ} : (1 : Q.Mx k r) ∈ UWset k r z :=
  ⟨by show (1 : Q.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp, fun _ => ⟨by simp, by simp⟩, by simp⟩

theorem radRedSurj_of (hL : LocSec) (hR : RepSmooth) : NF.RadRedSurj := by
  intro Wp Wq _ _ _ _ _ _ k r z z' μsec π π' hB φ hφ
  obtain ⟨hk, hz, hz', hT, hT', hsec, hπ, hπ', hπc, hπc'⟩ := hB
  obtain ⟨hφs, hφf, hφ0⟩ := hφ
  have hzc : Continuous (zetaL k r z z' (Fin.last r)) := (Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous
  refine ⟨Phi k r z z' μsec π π' φ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show Phi k r z z' μsec π π' φ x.1 x.2 = 0
    unfold Phi
    rw [dif_neg]
    exact fun h => hx h.1
  · rintro ⟨c₀, g₀⟩ ⟨hc₀, hg₀l, hg₀g⟩
    obtain ⟨V, hV, hg₀V, a, b, ha_s, hb_s, hab⟩ := hL k r z z' μsec hk hz hz' hT hT' hsec g₀ hg₀l hg₀g
    obtain ⟨ha₀, hb₀, -⟩ := hab g₀ hg₀V hg₀l hg₀g
    obtain ⟨VP, hVP, haVP, P, hPs, hPeq⟩ := hR Wp k r z π hz hT hπ hπc (a g₀) ha₀
    obtain ⟨VQ, hVQ, hbVQ, P', hP's, hP'eq⟩ := hR Wq k r z' π' hz' hT' hπ' hπc' (b g₀) hb₀
    have hSa : IsOpen (V ∩ a ⁻¹' VP) := ha_s.continuousOn.isOpen_inter_preimage hV hVP
    have hSb : IsOpen (V ∩ b ⁻¹' VQ) := hb_s.continuousOn.isOpen_inter_preimage hV hVQ
    have hpc : Continuous (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, zetaL k r z z' (Fin.last r) x.2)) :=
      continuous_fst.prodMk (hzc.comp continuous_snd)
    let U : Set ((Fin r → ℂ) × Q.Mx k r) :=
      Prod.snd ⁻¹' ((V ∩ a ⁻¹' VP) ∩ (V ∩ b ⁻¹' VQ)) ∩
        (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, zetaL k r z z' (Fin.last r) x.2)) ⁻¹' QR k r z z'
    have hU : IsOpen U :=
      (continuous_snd.isOpen_preimage _ (hSa.inter hSb)).inter (hpc.isOpen_preimage _ NFRadRedA.qr_open)
    have h1 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => P (a x.2)) U := by
      have ha' : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => a x.2) U :=
        ha_s.comp contDiff_snd.contDiffOn (fun x hx => hx.1.1.1)
      exact hPs.comp ha' (fun x hx => hx.1.1.2)
    have h2 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => P' (b x.2)) U := by
      have hb' : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => b x.2) U :=
        hb_s.comp contDiff_snd.contDiffOn (fun x hx => hx.1.2.1)
      exact hP's.comp hb' (fun x hx => hx.1.2.2)
    have h3 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => φ (x.1, zetaL k r z z' (Fin.last r) x.2)) U := by
      have hp : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, zetaL k r z z' (Fin.last r) x.2)) :=
        contDiff_fst.prodMk ((Qx5.zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd)
      exact hφs.comp hp.contDiffOn (fun x hx => hx.2)
    have h4 : ContDiffOn ℝ ∞
        (fun x : (Fin r → ℂ) × Q.Mx k r => (φ (x.1, zetaL k r z z' (Fin.last r) x.2)).comp (P' (b x.2))) U :=
      contDiff_clm_comp.comp_contDiffOn (h3.prodMk h2)
    have h5 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r =>
        (P (a x.2)).comp ((φ (x.1, zetaL k r z z' (Fin.last r) x.2)).comp (P' (b x.2)))) U :=
      contDiff_clm_comp.comp_contDiffOn (h1.prodMk h4)
    refine ⟨U, _, hU, ⟨⟨⟨hg₀V, haVP⟩, ⟨hg₀V, hbVQ⟩⟩, qr_of_dp hc₀ hg₀g⟩, h5, ?_⟩
    rintro ⟨c, g⟩ ⟨⟨⟨hgV, haP⟩, ⟨-, hbQ⟩⟩, hq⟩ hgl
    have hq' : (c, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := hq
    have hgg : 0 < GGl k r z z' g := by
      unfold GGl
      exact sub_pos.mpr hq'.2
    obtain ⟨ha, hb, hfac⟩ := hab g hgV hgl hgg
    show Phi k r z z' μsec π π' φ c g = _
    rw [phi_val hπ hπ' hφf ⟨hq'.1, hgl, hgg⟩ ha hb hfac]
    show _ = (P (a g)).comp ((φ (c, zetaL k r z z' (Fin.last r) g)).comp (P' (b g)))
    rw [hPeq _ haP ha, hP'eq _ hbQ hb]
  · rintro ⟨c, g⟩ ⟨hc, hgl, hgg⟩ h hh h' hh'
    obtain ⟨V, -, hgV, a, b, -, -, hab⟩ := hL k r z z' μsec hk hz hz' hT hT' hsec g hgl hgg
    obtain ⟨ha, hb, hfac⟩ := hab g hgV hgl hgg
    have hzi : zetaL k r z z' (Fin.last r) (h * g * h') = zetaL k r z z' (Fin.last r) g :=
      Qx5.zeta_inv hh hh' g
    have hgg' : 0 < GGl k r z z' (h * g * h') := by
      have e : GGl k r z z' (h * g * h') = GGl k r z z' g := by unfold GGl; rw [hzi]
      rw [e]; exact hgg
    have hdom' : (c, h * g * h') ∈ DomR k r z z' := ⟨hc, mul_mul_mem_glev_last_of_mem_uwset hgl hh hh', hgg'⟩
    have hfac' : h * g * h' = (h * a g) * muZ k r μsec (zetaL k r z z' (Fin.last r) (h * g * h')) * (b g * h') := by
      rw [hzi]
      conv_lhs => rw [hfac]
      simp only [Matrix.mul_assoc]
    show Phi k r z z' μsec π π' φ c (h * g * h') = (π h).comp ((Phi k r z z' μsec π π' φ c g).comp (π' h'))
    rw [phi_val hπ hπ' hφf hdom' (uw_mul hh ha) (uw_mul hb hh') hfac',
      phi_val hπ hπ' hφf ⟨hc, hgl, hgg⟩ ha hb hfac, hzi, hπ.2 _ hh _ ha, hπ'.2 _ hb _ hh']
    simp only [ContinuousLinearMap.comp_assoc]
  · funext q
    obtain ⟨c, ζ⟩ := q
    show (QR k r z z').indicator (fun q => Phi k r z z' μsec π π' φ q.1 (muZ k r μsec q.2)) (c, ζ) = φ (c, ζ)
    by_cases hq : (c, ζ) ∈ QR k r z z'
    · rw [Set.indicator_of_mem hq]
      have hζ : Tz k r z * Tz k r z' < Complex.normSq ζ := hq.2
      have hzm : zetaL k r z z' (Fin.last r) (muZ k r μsec ζ) = ζ := NFRadRedA.zeta_muZ hz hz' hsec hζ
      have hmg : muZ k r μsec ζ ∈ Glev k r (Fin.last r) := by
        obtain ⟨hu, hfix⟩ := NFRadRedA.muZ_uwb hsec hζ
        exact ⟨hu, fun a _ => hfix a⟩
      have hmgg : 0 < GGl k r z z' (muZ k r μsec ζ) := by
        unfold GGl
        rw [hzm]
        linarith
      have hdom : (c, muZ k r μsec ζ) ∈ DomR k r z z' := ⟨hq.1, hmg, hmgg⟩
      have hf1 : muZ k r μsec ζ = 1 * muZ k r μsec (zetaL k r z z' (Fin.last r) (muZ k r μsec ζ)) * 1 := by
        rw [hzm, Matrix.one_mul, Matrix.mul_one]
      show Phi k r z z' μsec π π' φ c (muZ k r μsec ζ) = φ (c, ζ)
      rw [phi_val hπ hπ' hφf hdom one_mem_uwset_of_vec one_mem_uwset_of_vec hf1, hzm, hπ.1, hπ'.1]
      ext v
      simp
    · rw [Set.indicator_of_notMem hq, hφ0 _ hq]

end Formalism.FourierDecayAlt.P.NFRadRedS

namespace Formalism.FourierDecayAlt.P

theorem radical_surjective_of_parts : NFRadRedS.LocSec → NFRadRedS.RepSmooth → Formalism.FourierDecayAlt.NF.RadRedSurj :=
  fun hL hR => NFRadRedS.radRedSurj_of hL hR

end Formalism.FourierDecayAlt.P
