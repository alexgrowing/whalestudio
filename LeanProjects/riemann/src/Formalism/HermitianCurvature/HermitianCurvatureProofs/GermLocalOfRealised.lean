import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocTail

namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def gK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (p q : C.LPt × ℂ) : ℂ :=
  KB.gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)])

def gDens (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (h h' : C.LPt) (z : ℂ) : ℂ :=
  KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])

structure GermReal (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (Y : Finset C.LPt) where
  H : Type
  [nag : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  ut : C.LPt → ℂ → ℂ → H
  bt : C.LPt → ℂ → H
  β : ℂ
  ε' : ℂ
  hβ : β ≠ 0
  hε' : ‖ε'‖ = 1
  hdl : KB.dlB S b s ≠ 0
  hpsi : ∀ σ z : ℂ, G.psi β (σ * z) = KB.psiL S σ z
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  gram : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
    gK S v ε b s a (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x')
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε' (bt h) x D‖ ≤ C * ‖x‖⁻¹
  dens : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ z : ℂ, z ≠ 0 →
    gDens S v ε b s a h h' z = (KB.dlB S b s : ℂ) * ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ

attribute [instance] GermReal.nag GermReal.ips GermReal.cs

def GermRealised (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) → Nonempty (GermReal S v ε b s a Y)

def GermCont (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ h h' : C.LPt,
    D.ptSize h = b - 1 → D.ptSize h' = b - 1 → ContinuousOn (gDens S v ε b s a h h') {0}ᶜ

theorem integral_inner_self_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : ℂ → H) :
    ∫ c, ⟪f c, f c⟫_ℂ = ((∫ c, ‖f c‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ c, ⟪f c, f c⟫_ℂ = ((‖f c‖ ^ 2 : ℝ) : ℂ) := fun c => by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [h]
  exact integral_ofReal

theorem GermReal.germD {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) (hs : 2 ≤ s) (B : ℝ)
    (hB : ∀ h ∈ Y, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + s - 2) a (h ++ [(s - 1, t)]) (h ++ [(s - 1, t)])‖ ≤ B) :
    GermD s R.β R.ε' Y R.ut R.bt B := by
  refine ⟨by omega, R.hβ, R.hε', R.memU, fun h hh x hx => ?_, R.meas, R.loc, R.germ⟩
  have hg := R.gram h hh h hh x x hx hx
  have hb := hB h hh x⁻¹ (inv_ne_zero hx)
  unfold gK at hg
  dsimp only at hg
  rw [hg] at hb
  unfold gramL Uc at hb
  dsimp only at hb
  rw [integral_inner_self_eq, integral_norm_cvec_sq s (R.ut h) x hx, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hb
  exact hb

theorem GermReal.nhat_eq {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) {h h' : C.LPt} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ : ℂ) :
    Nhat s R.β R.bt σ h h' = KB.hatB S v ε b s a σ h h' := by
  have hdl : ((KB.dlB S b s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R.hdl
  have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    rw [ae_iff]; simp
  unfold KB.hatB Nhat
  have hae : (fun c => KB.gN S v ε (b + s - 1) a (h ++ [(s, c)]) (h' ++ [(s, c)]) * KB.psiL S σ c)
      =ᵐ[volume] fun c => ((KB.dlB S b s : ℝ) : ℂ) *
        (G.psi R.β (σ * c) • ⟪bz s (R.bt h) c, bz s (R.bt h') c⟫_ℂ) := by
    filter_upwards [h0] with c hc
    have hd := R.dens h hh h' hh' c hc
    unfold gDens at hd
    rw [hd, ← R.hpsi σ c, smul_eq_mul]
    ring
  rw [integral_congr_ae hae, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]

theorem ae_ne_zero : ∀ᵐ z : ℂ, z ≠ 0 := by
  rw [ae_iff]; simp

theorem germLoc_of_realised {S : C.HidaSetting E Wp Wq} {v : Fin S.f} (hR : GermRealised S v) (hC : GermCont S v) :
    KB.GermLoc S v := by
  intro ε hε b s hb hs hbs a ha Y hY hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨R⟩ := hR ε hε b s hb hs hbs a ha Y hY
  have G := R.germD hs B hB
  obtain ⟨hint, rest⟩ := G.germLoc_tail
    (fun p q => KB.gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)]))
    (fun h hh h' hh' x x' hx hx' => R.gram h hh h' hh' x x' hx hx')
    (KB.hatB S v ε b s a) (fun σ h hh h' hh' => R.nhat_eq hh hh' σ)
  refine ⟨fun h hh h' hh' => ⟨hC ε hε b s hb hs hbs a ha h h' (hY h hh) (hY h' hh'), ?_⟩, rest⟩
  have hae : (fun z => ((KB.dlB S b s : ℝ) : ℂ) * ⟪bz s (R.bt h) z, bz s (R.bt h') z⟫_ℂ) =ᵐ[volume]
      fun z => KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)]) := by
    filter_upwards [ae_ne_zero] with z hz
    exact (R.dens h hh h' hh' z hz).symm
  exact ((hint h hh h' hh').const_mul _).congr hae

end loc

def GermLocOfRealised : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f),
    GermRealised S v → GermCont S v → KB.GermLoc S v

end

end Formalism.FourierDecayAlt.P.GermRealisation

theorem Formalism.FourierDecayAlt.P.germ_local_of_realised : Formalism.FourierDecayAlt.P.GermRealisation.GermLocOfRealised := by
  intro E _ _ _ Wp Wq _ _ _ _ S v hR hC
  exact Formalism.FourierDecayAlt.P.GermRealisation.germLoc_of_realised hR hC
