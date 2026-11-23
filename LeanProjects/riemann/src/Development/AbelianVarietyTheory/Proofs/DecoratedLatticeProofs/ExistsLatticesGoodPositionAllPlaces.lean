import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittProjAnisotropicMulVecLeviEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem tau_norm {E : Type} [Field E] [StarRing E] {m n : ℕ} {G : Matrix (Fin m) (Fin m) E} {G' : Matrix (Fin n) (Fin n) E}
    {τ : Matrix (Fin m) (Fin n) E} {t lam : E} {ζ : Fin m → E} {ζ₀ : Fin n → E} (h : τᴴ * (G * τ) = t • G')
    (hτ : τ *ᵥ ζ₀ = lam • ζ) : lam * star lam * (star ζ ⬝ᵥ G *ᵥ ζ) = t * (star ζ₀ ⬝ᵥ G' *ᵥ ζ₀) := by
  have := congrArg (fun M => star ζ₀ ⬝ᵥ M *ᵥ ζ₀) h
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hτ, smul_mulVec, dotProduct_smul, smul_eq_mul,
    mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
  rw [← this, mul_assoc]

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem val_norm_xi {p : SplitPt D k} (h : p.UnitAA) : valuation k (p.pr (incA D (D.host.xi0 * star D.host.xi0))) = 1 := by
  have h1 : valuation k (p.pr (incA D D.host.xi0)) = 1 := val_eq_one (isU_xi h)
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_mul, RingHom.map_neg, map_mul, map_mul, map_neg, Valuation.map_neg, h1, one_mul]

theorem top_idele (hc : c.Is) (pre : PreT v o)
    (hs : ∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x)
    {α : (AE D)ˣ} (hα : ∀ (x : Pl D) (S : HSp D) (L : Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) :
    ∃ m₀ : (AE D)ˣ, (∀ x ∈ v.tP, IsU x (m₀ : AE D)) ∧ ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x ((m₀ : AE D) * cA D m₀ *
        incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k)) ∧
      ∀ x, x ∉ v.tP → ∀ LL : Lat (c.bes j 0 h).L, IsSelfDualC _ LL →
        (∀ a ∈ idAt D (· = x), a • ratV (c.bes j 0 h).ζ ∈ latV _ LL (· = x) ↔
          ((m₀⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) →
        ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT (j + 1 + 1) h) (c.x (j + 1 + 1)).L v.NT LZ x ∧
          ∀ w ∈ latO (c.X (j + 1)) c.Lz ((c.x (j + 1)).L : Set _) (LZ : Set _) (· = x),
            kap (v.τ j h) (c.X (j + 1)) w ∈ latO (c.bes j 0 h).L (c.X (j + 1)) (LL : Set _) ((c.x (j + 1)).L : Set _) (· = x) := by
  by_cases hex : ∃ j, j + 2 * 0 + 2 = D.R.m
  swap
  · exact ⟨1, fun x _ => IsU.one x, fun j h => absurd ⟨j, h⟩ hex⟩
  obtain ⟨j, h⟩ := hex
  obtain ⟨lam, hτ, hv⟩ := pre.lam j h
  have hn := tau_norm (pre.tau j h) hτ
  have hξ := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hlam : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hn
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hξ (star_ne_zero.2 hξ))) pre.line.2 hn.symm
  obtain ⟨μ, hμ⟩ := line_idele (c.oT (j + 1 + 1) h) pre.line (hc.x (j + 1 + 1) (by omega)).sd.1 v.NT (· ∈ v.tP)
    (hs (j + 1 + 1) h)
  obtain ⟨m₀, m1, m2⟩ := patch v.tP (fun _ => 1) (α * μ * inU lam hlam * (xiU D * cU α)⁻¹)
  refine ⟨m₀, fun x hx a ha => by rw [m1 x hx a ha, Units.val_one, one_mul], fun j' h' => ?_⟩
  obtain rfl : j = j' := by omega
  have hn' := congrArg (incA D) hn
  refine ⟨fun x hx a ha => ?_, fun i => ?_, fun x hx LL hLL hm => ?_⟩
  · obtain ⟨LZ, hLZ, ho⟩ := hs (j + 1 + 1) h x hx
    have h1 := (line_norm pre.line hLZ fun a ha => (orth_line _ ho _ a).trans (hμ x hx a ha)).neg a ha
    rw [h1]
    simp only [RingHom.map_mul, RingHom.map_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg] at hn'
    generalize incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ) = t at hn' ⊢
    generalize incA D (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀) = t₀ at hn' ⊢
    have e1 := m2 x hx _ (Ideal.mul_mem_left _ (cA D m₀ * t) ha)
    have e2 := congrArg (cA D) (m2 x hx _ (id_conj ha))
    generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m at e1 e2
    have f2 : (m : AE D) = α * μ * incA D lam * (incA D D.host.xi0⁻¹ * cA D (α⁻¹ : (AE D)ˣ)) := by
      rw [← hm', mul_inv]
      simp only [Units.val_mul, inU_val, cU_inv, xiU, inU_inv]
    have f3 : cA D (m : AE D) = cA D α * cA D μ * incA D (star lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
      rw [f2]
      simp only [RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, cA_xi_inv, FrameLat.cA_incA lam]
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, f3] at e2
    have g1 := α.mul_inv
    have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
    have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
    refine iff_of_eq (congrArg (· ∈ _) ?_)
    rw [f2] at e1
    generalize incA D D.host.xi0 = ξ at *
    generalize incA D D.host.xi0⁻¹ = ξ' at *
    generalize incA D lam = l at *
    generalize incA D (star lam) = l' at *
    generalize cA D (α : AE D) = β at *
    generalize cA D ((α⁻¹ : (AE D)ˣ) : AE D) = β' at *
    generalize ((α⁻¹ : (AE D)ˣ) : AE D) = α' at *
    generalize cA D (μ : AE D) = ν at *
    generalize cA D (m₀ : AE D) = n₀ at *
    linear_combination -e1 - (α * μ * l * ξ' * β' * t) * e2 + (α * α' * β * β' * μ * ν * ξ' * ξ' * a) * hn' +
      (μ * ν * t₀ * a * β * β' * ξ * ξ * ξ' * ξ') * g1 + (μ * ν * t₀ * a * ξ * ξ * ξ' * ξ') * g2 +
      (μ * ν * t₀ * a * (ξ * ξ' + 1)) * g3
  · have := congrArg (fun t => valuation k ((o.p i).pr t)) hn'
    simp only [RingHom.map_mul (incA D) (lam * star lam), RingHom.map_mul (incA D) lam, RingHom.map_mul (incA D) (-_),
      RingHom.map_neg, RingHom.map_mul (o.p i).pr, Valuation.map_mul, Valuation.map_neg, (hv i).1, (hv i).2, one_mul,
      val_norm_xi (pre.char i).2] at this
    rw [this, pre.normT i]
  · obtain ⟨LZ, hLZ, ho⟩ := hs (j + 1 + 1) h x hx
    refine ⟨LZ, hLZ, ho, kap_of (v.τ j h) (c.bes j 0 h).line pre.line hlam hτ hLL hLZ (hc.x (j + 1) (by omega)).sd (hα x)
      (fun a ha => (orth_line _ ho _ a).trans (hμ x hx a ha)) fun a ha => ?_⟩
    rw [hm a ha, inv_same (m2 x hx) a ha]

def gam (α : (AE D)ˣ) : (AE D)ˣ := α * (xiU D * cU α)⁻¹

theorem gam_norm (α : (AE D)ˣ) : (gam α : AE D) * cA D (gam α : AE D) * incA D (D.host.xi0 * star D.host.xi0) = 1 := by
  have g1 := α.mul_inv
  have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
  have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  rw [gam, mul_inv]
  simp only [Units.val_mul, cU_inv, xiU, inU_inv, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, cA_xi_inv, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]
  generalize incA D D.host.xi0 = ξ at *
  generalize incA D D.host.xi0⁻¹ = ξ' at *
  generalize cA D (α : AE D) = β at *
  generalize cA D ((α⁻¹ : (AE D)ˣ) : AE D) = β' at *
  generalize ((α⁻¹ : (AE D)ˣ) : AE D) = α' at *
  linear_combination (β * β' * ξ * ξ * ξ' * ξ') * g1 + (ξ * ξ * ξ' * ξ') * g2 + (ξ * ξ' + 1) * g3

theorem level_norm (pre : PreT v o) (α m₀ : (AE D)ˣ) (h0 : ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x ((m₀ : AE D) * cA D m₀ *
        incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k))) (ρ : ℕ) : ∀ j (h : j + 2 * ρ + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x (((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) * cA D ((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) *
        incA D (star (c.bes j ρ h).ζ ⬝ᵥ (c.bes j ρ h).L.gram *ᵥ (c.bes j ρ h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j ρ h).ζ ⬝ᵥ (c.bes j ρ h).L.gram *ᵥ (c.bes j ρ h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k)) := by
  induction ρ with
  | zero => simpa only [pow_zero, one_mul] using h0
  | succ σ ih =>
    intro j h
    obtain ⟨i1, i2⟩ := ih (j + 1 + 1) (idx_step h)
    have hn : star (c.bes j (σ + 1) h).ζ ⬝ᵥ (c.bes j (σ + 1) h).L.gram *ᵥ (c.bes j (σ + 1) h).ζ = _ := (c.lnk j σ h).norm
    rw [hn, RingHom.map_mul]
    refine ⟨fun x hx => ?_, fun i => ?_⟩
    · convert i1 x hx using 1
      rw [pow_succ', mul_assoc (gam α), Units.val_mul, RingHom.map_mul]
      generalize ((gam α ^ σ * m₀ : (AE D)ˣ) : AE D) = u
      generalize incA D (star (c.bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ (c.bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ
        (c.bes (j + 1 + 1) σ (idx_step h)).ζ) = t
      linear_combination (u * cA D u * t) * gam_norm α
    · rw [RingHom.map_mul, Valuation.map_mul, val_norm_xi (pre.char i).2, one_mul, i2 i]

def cond (α : (AE D)ˣ) : (AE D)ˣ := xiU D * α * cU α

def bB (α m₀ : (AE D)ˣ) (ρ : ℕ) (i : Fin ρ) : (AE D)ˣ := cond α ^ (ρ - i.1) * (gam α ^ ρ * m₀)

def bJ (α m₀ : (AE D)ˣ) (ρ : ℕ) (i : Fin ρ) : (AE D)ˣ := α⁻¹ * bB α m₀ ρ i

theorem bB_step (α m₀ : (AE D)ˣ) (ρ : ℕ) (i j : Fin ρ) (h : j.1 = i.1 + 1) : bB α m₀ ρ i = cond α * bB α m₀ ρ j := by
  have := j.2
  rw [bB, bB, show ρ - i.1 = ρ - j.1 + 1 by omega, pow_succ', mul_assoc]

theorem bJ_step (α m₀ : (AE D)ˣ) (ρ : ℕ) (i j : Fin ρ) (h : j.1 = i.1 + 1) : bJ α m₀ ρ i = cond α * bJ α m₀ ρ j := by
  rw [bJ, bJ, bB_step α m₀ ρ i j h, mul_left_comm]

theorem cond_gam (α : (AE D)ˣ) : cond α * gam α = α * α := by
  rw [cond, gam, mul_right_comm (xiU D), mul_comm α, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem bJ_succ (α m₀ : (AE D)ˣ) (σ : ℕ) (i : Fin (σ + 1)) :
    bJ α m₀ (σ + 1) i = α * (cond α ^ (σ - i.1) * (gam α ^ σ * m₀)) := by
  have := i.2
  rw [bJ, bB, show σ + 1 - i.1 = σ - i.1 + 1 by omega, pow_succ', pow_succ', mul_assoc (gam α), mul_mul_mul_comm, cond_gam,
    mul_assoc α, inv_mul_cancel_left]

theorem bJ_last (α m₀ : (AE D)ˣ) (ρ : ℕ) (r : Fin ρ) (hr : r.1 + 1 = ρ) :
    bJ α m₀ ρ r = xiU D * cU α * (gam α ^ ρ * m₀) := by
  rw [bJ, bB, show ρ - r.1 = 1 by omega, pow_one, cond, mul_comm (xiU D) α, mul_assoc α, mul_assoc α, inv_mul_cancel_left]

def HasIdeals {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (b : Fin ρ → (AE D)ˣ) : Prop :=
  ∀ x : Pl D, MonoAt d L L₀ x ∧ (∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔
    (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧
    ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x)

theorem exists_N (hc : c.Is) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (hM : ∀ j ρ h, IsSelfDualC _ (M j ρ h))
    (b b' : ∀ ρ, Fin ρ → (AE D)ˣ) : ∃ N : ∀ j, Lat (c.V j), (∀ j, IsSelfDualC _ (N j)) ∧
      (∀ j ρ h, HasIdeals (c.bes j ρ h).d (N j) (M j ρ h) (b ρ)) ∧
      ∀ j ρ h, HasIdeals (c.jac j ρ h).d (N (j + 1)) (c.x (j + 1)).L (b' ρ) := by
  have HB : ∀ j, ∃ N : Lat (c.V j), IsSelfDualC _ N ∧ ∀ ρ h, HasIdeals (c.bes j ρ h).d N (M j ρ h) (b ρ) := fun j => by
    by_cases hex : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hex
      obtain ⟨N, h1, h2⟩ := GlobalTheory.FinPl.exists_selfDual_mono_idele D _ _ ρ (c.bes j ρ h).d (M j ρ h) (hM j ρ h) (b ρ)
      refine ⟨N, h1, fun ρ' h' => ?_⟩
      obtain rfl : ρ = ρ' := by omega
      exact h2
    · exact ⟨_, GlobalTheory.WeilAtPlace.isSelfDualC_frameLat _, fun ρ h => absurd ⟨ρ, h⟩ hex⟩
  have H1 : ∀ j, ∃ N : Lat (c.V (j + 1)), IsSelfDualC _ N ∧
      (∀ ρ h, HasIdeals (c.bes (j + 1) ρ h).d N (M (j + 1) ρ h) (b ρ)) ∧
      ∀ ρ h, HasIdeals (c.jac j ρ h).d N (c.x (j + 1)).L (b' ρ) := fun j => by
    by_cases hex : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hex
      obtain ⟨N, h1, h2⟩ := GlobalTheory.FinPl.exists_selfDual_mono_idele D _ _ ρ (c.jac j ρ h).d (c.x (j + 1)).L (hc.x (j + 1) (by omega)).sd (b' ρ)
      refine ⟨N, h1, fun ρ' h' => by omega, fun ρ' h' => ?_⟩
      obtain rfl : ρ = ρ' := by omega
      exact h2
    · obtain ⟨N, h1, h2⟩ := HB (j + 1)
      exact ⟨N, h1, h2, fun ρ h => absurd ⟨ρ, h⟩ hex⟩
  obtain ⟨N₀, h0, h0'⟩ := HB 0
  choose N₁ h1 h2 h3 using H1
  refine ⟨fun j => Nat.casesOn (motive := fun j => Lat (c.V j)) j N₀ N₁, fun j => ?_, fun j => ?_, h3⟩
  · cases j
    exacts [h0, h1 _]
  · cases j
    exacts [h0', h2 _]

theorem exists_goodAt : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → IsSelfDualC c.T v.NT → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) → ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ (∀ x, GoodAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ ∀ j ρ h i, GluedCore (c.B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i) := by
  intro D c v k _ _ _ _ ι o hc _ pre hs
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D c.ψ hc.std
  obtain ⟨m₀, hT, htop⟩ := top_idele hc pre hs fun x => (hα x).1
  have hlev := level_norm pre α m₀ fun j h => ⟨(htop j h).1, (htop j h).2.1⟩
  have hP : Places o.p o.I (· ∈ v.tP) := ⟨pre.nodup, pre.all, pre.inj, pre.tP, fun i => (pre.char i).2⟩
  have hmT : ∀ ρ, ∀ x ∈ v.tP, IsU x ((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) := fun ρ x hx => by
    obtain ⟨i, rfl⟩ := (pre.tP x).1 hx
    have h1 := isU_alpha (pre.char i).2 pre.line (hα _).1
    have h2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi (pre.char i).2).mul h1.conj
    have h3 : IsU (o.p i).v (gam α : AE D) := h1.mul (h2.inv (Units.mul_inv _))
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact (h3.pow ρ).mul (hT _ hx)
  have hcore := fun j ρ (h : j + 2 * ρ + 2 = D.R.m) =>
    GlobalTheory.FinPl.CoreIdele.exists_core D k ι o.p o.I _ hP o.q (Fin (c.X j).rank) ρ (c.B j ρ h) (o.β j) (o.Q j) (c.x j).L (hc.x j (by omega)).sd
      (pre.latT j (by omega)) (hlev ρ j h).2 (gam α ^ ρ * m₀) (hmT ρ) (hlev ρ j h).1
  choose M β₀ hM hglue hoff hz using hcore
  obtain ⟨N, hN, hB, hJ⟩ := exists_N hc M hM (bB α m₀) (bJ α m₀)
  have hψ : ∀ x : Pl D, ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE c.ψ (s * o) = 1) ↔
      (((cond α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun x s hs => by
    rw [(hα x).2 s hs, cond, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  refine ⟨N, M, β₀, fun j _ => hN j, fun x => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun x hx => ⟨fun j ρ h => ?_, fun j h => ?_⟩,
    hglue⟩
  · have sx := (hc.x (j + 1) (by omega)).sd
    exact ⟨TamePlaces.tame D x, hN j, hM j ρ h, hN (j + 1), sx, (hB j ρ h x).1, (hJ j ρ h x).1,
      prim_of _ (bB_step α m₀ ρ) (hψ x) (hB j ρ h x).2.1,
      cols_bf _ _ (fun i => (mul_inv_cancel_left α _).symm) ((hα x).1 _ _) (hB j ρ h x).2.1 (hJ j ρ h x).2.1,
      last_of _ _ (hM j ρ h) (hN (j + 1)) (bJ_last α m₀ ρ) ((hα x).1 _ _) (hJ j ρ h x).2.2 (hz j ρ h x)⟩
  · have sx := (hc.x (j + 1) (by omega)).sd
    have h' := idx_step h
    exact ⟨TamePlaces.tame D x, hN (j + 1), sx, hN (j + 1 + 1), hM _ σ h', (hJ j _ h x).1, (hB _ σ h' x).1,
      prim_of _ (bJ_step α m₀ _) (hψ x) (hJ j _ h x).2.1,
      cols_fb _ _ _ (fun i => bJ_succ α m₀ σ i.castSucc)
        (by rw [bJ_succ, Fin.val_last, Nat.sub_self, pow_zero, one_mul]) ((hα x).1 _ _) (hJ j _ h x).2.1 (hB _ σ h' x).2.1
        (hB _ σ h' x).1 (hz _ σ h' x)⟩
  · obtain ⟨LL, h1, h2, -⟩ := hoff j ρ h x hx
    exact ⟨LL, h1, h2⟩
  · obtain ⟨LL, h1, h2, h3⟩ := hoff j 0 h x hx
    rw [pow_zero, one_mul] at h3
    obtain ⟨LZ, g1, g2, g3⟩ := (htop j h).2.2 x hx LL h1 h3
    exact ⟨LL, LZ, h1, g1, h2, g2, g3⟩

end GlobalTheory.GoodPos

end
