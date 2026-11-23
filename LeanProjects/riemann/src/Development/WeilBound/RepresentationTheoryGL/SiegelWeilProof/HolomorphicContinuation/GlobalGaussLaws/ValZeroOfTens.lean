import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem absA_pos (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem compAt_zero' {θ : InfFam D} {τ : D.what₂.Tau} {m : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  unfold compAt; exact Matrix.map_zero _ (by rw [RingHom.map_zero, RingHom.map_zero])

theorem compAt_sub' {θ : InfFam D} {τ : D.what₂.Tau} {m : ℕ} (a b : Mx D m n) :
    compAt θ τ (a - b) = compAt θ τ a - compAt θ τ b := by
  unfold compAt; exact Matrix.map_sub _ (fun x y => by rw [RingHom.map_sub, RingHom.map_sub]) a b

theorem phiS_eq {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  simp only [phiS, dif_pos h]

theorem val_zero_of_tens {m : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : IsAwayFn θ τ Ψ) {x₁ : Mx D m n} (hx₁ : Ψ x₁ ≠ 0) {f f' : (Fin m → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f Ψ = tens θ τ fr f' Ψ) : f 0 = f' 0 := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  set c : Mx D m n := GlobalTheory.SchwartzBruhatTensor.chartM σ m n
    (fun τ' i j => if τ' = τ then compAt θ τ x₁ i j else 0) with hc
  have hc1 : ∀ τ', compAt θ τ' c = if τ' = τ then compAt θ τ x₁ else 0 := fun τ' => by
    ext i j
    rw [hc, GlobalTheory.SchwartzBruhatTensor.compAt_chartM hσ]
    split_ifs <;> rfl
  have hc2 : c.map (finPart D) = 0 := GlobalTheory.SchwartzBruhatTensor.finPart_chartM hσ _
  have e0 : compAt θ τ (x₁ - c) = 0 := by rw [compAt_sub', hc1, if_pos rfl, sub_self]
  have e1 : Ψ (x₁ - c) = Ψ x₁ := hΨ _ _ (fun τ' h' => by rw [compAt_sub', hc1, if_neg h', sub_zero])
    (by rw [Matrix.map_sub _ (fun a₁ a₂ => RingHom.map_sub (finPart D) a₁ a₂), hc2, sub_zero])
  have := congrFun h (x₁ - c)
  simp only [tens, e0, Matrix.mul_zero, e1] at this
  exact mul_right_cancel₀ hx₁ this

set_option maxHeartbeats 2000000 in
theorem gSplit_of (hI : GIwasawa) (hAw : AwayAct) (hLF : LocFact) (hIn : AwayIn) (hSch : SchFP) (hT : TensMem) (hZ : LNZ) :
    GSplit := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hc L hL Ψ hΨ g
  have hl0 := hZ D ψ θ l hc.hψ hc.hθ hc.hl
  have hcpos : 0 < cLoc l τ := mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hl0 τ))
  have hcls : AwayCls θ τ fr Ψ := hIn D n V θ l s τ ε fr hc.hθ hc.hs hc.hfr hl0 Ψ hΨ
  obtain ⟨L', hL'⟩ := hLF D n V ψ χ θ μ ω H l s ν τ ε fr ι hc
  obtain ⟨p, hp, k, hk, rfl⟩ := hI D n g
  obtain ⟨y, hyK, hk'K, hk'τ⟩ := K_split hc.hθ hc.hι hk
  obtain ⟨A, hA⟩ := hAw D n V ψ χ θ μ ω H l s ν τ ε fr ι hc _ hk'τ
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
  have hcomm : ∀ z : GR n, ((ι y)⁻¹ * k) * ι z = ι z * ((ι y)⁻¹ * k) := comm_of_trivial hc.hθ hc.hι hk'τ
  have hf : ∀ P : PX V.rank n, IsSch (fP (cLoc l τ) P) := fun P => hSch V.rank n (cLoc l τ) hcpos P
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n := fun P => hcls.2 _ (hf P)

  have hval : ∀ (y' : GR n) (P : PX V.rank n), secF ω τ fr (cLoc l τ) Ψ P (p * ((ι y)⁻¹ * k) * ι y') =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) *
        (A Ψ 0 * L' y' (fP (cLoc l τ) P) 0) := by
    intro y' P
    have hm2 := hT D n V θ l s τ ε fr hc.hθ hl0 hc.hs hc.hfr Ψ hΨ P
    obtain ⟨𝓕, h𝓕⟩ := hc.hμ
    have hsec := SiegelSection.fock_mem_degenerate D n V ψ hc.hψ χ hc.hχ hc.hη θ hc.hθ μ 𝓕 h𝓕 ω hc.hω l hc.hl s hc.hs
      (phiS θ τ fr (cLoc l τ) Ψ P) (by rw [phiS_eq (hmem P)]; exact hm2.2)
    have hlaw := hsec.1 p hp a ha ((ι y)⁻¹ * k * ι y')
    simp only at hlaw
    unfold secF
    rw [mul_assoc, hlaw, hcomm, map_mul, Module.End.mul_apply, phiS_eq (hmem P)]
    have h1 : ω ((ι y)⁻¹ * k) ⟨_, hmem P⟩ = ⟨tens θ τ fr (fP (cLoc l τ) P) (A Ψ), (hA Ψ hcls).1.2 _ (hf P)⟩ :=
      Subtype.ext ((hA Ψ hcls).2 _ (hf P))
    rw [h1, (hL'.2 y' (A Ψ) (hA Ψ hcls).1 _ (hf P))]
    have ht : tens θ τ fr (L' y' (fP (cLoc l τ) P)) (A Ψ) 0 = L' y' (fP (cLoc l τ) P) 0 * A Ψ 0 := by
      simp only [tens]; rw [compAt_zero', Matrix.mul_zero]; rfl
    rw [ht]; ring
  by_cases hz : ∀ x, Ψ x = 0
  ·
    refine ⟨p * ((ι y)⁻¹ * k), y, 0, (absA D (Matrix.GeneralLinearGroup.det a) : ℝ), by exact_mod_cast absA_pos _, ?_, ?_⟩
    · rw [mul_assoc, hcomm y]; simp
    intro y'
    obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := locIwasawa y'
    refine ⟨?_, fun P => ?_⟩
    · obtain ⟨hqP, b, hb, hbabs⟩ := iota_mem_P hc.hθ hc.hι hq
      have e : p * ((ι y)⁻¹ * k) * ι (q * k₀) = (p * ι q) * (ι k₀ * ((ι y)⁻¹ * k)) := by
        rw [map_mul, ← mul_assoc, mul_assoc p, hcomm q, ← mul_assoc, mul_assoc (p * ι q), hcomm k₀]
      have hblk : blkA (mat (p * ι q)) = (a * b).1 := by
        rw [HeightExists.blkA_mul hqP, ha, hb, Units.val_mul]
      rw [e, hc.hH (p * ι q) ((P D n).mul_mem hp hqP) (a * b) hblk _
        ((K D n).mul_mem (iota_mem_K hc.hθ hc.hι hk₀) hk'K), map_mul, map_mul, NNReal.coe_mul, hbabs, hloc]
    · have hΨ0 : Ψ = 0 := funext hz
      have e : tens θ τ fr (fP (cLoc l τ) P) Ψ = 0 := by funext x; simp [tens, hΨ0]
      have : phiS θ τ fr (cLoc l τ) Ψ P = 0 := by rw [phiS_eq (hmem P)]; exact Subtype.ext e
      unfold secF; rw [this, map_zero, zero_mul]; rfl
  · push_neg at hz
    obtain ⟨x₁, hx₁⟩ := hz
    have hconv : ∀ (y' : GR n) (P : PX V.rank n), L' y' (fP (cLoc l τ) P) 0 = L y' (fP (cLoc l τ) P) 0 := by
      intro y' P
      have h1 := hL'.2 y' Ψ hcls _ (hf P)
      have h2 := hL y' Ψ hΨ P
      rw [phiS_eq (hmem P)] at h2
      exact val_zero_of_tens hc.hθ hcls.1 hx₁ (h1.symm.trans h2)
    refine ⟨p * ((ι y)⁻¹ * k), y,
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) *
        A Ψ 0, (absA D (Matrix.GeneralLinearGroup.det a) : ℝ), by exact_mod_cast absA_pos _, ?_, ?_⟩
    · rw [mul_assoc, hcomm y]; simp
    intro y'
    refine ⟨?_, fun P => by rw [hval, hconv]; ring⟩
    obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := locIwasawa y'
    obtain ⟨hqP, b, hb, hbabs⟩ := iota_mem_P hc.hθ hc.hι hq
    have e : p * ((ι y)⁻¹ * k) * ι (q * k₀) = (p * ι q) * (ι k₀ * ((ι y)⁻¹ * k)) := by
      rw [map_mul, ← mul_assoc, mul_assoc p, hcomm q, ← mul_assoc, mul_assoc (p * ι q), hcomm k₀]
    have hblk : blkA (mat (p * ι q)) = (a * b).1 := by
      rw [HeightExists.blkA_mul hqP, ha, hb, Units.val_mul]
    rw [e, hc.hH (p * ι q) ((P D n).mul_mem hp hqP) (a * b) hblk _
      ((K D n).mul_mem (iota_mem_K hc.hθ hc.hι hk₀) hk'K), map_mul, map_mul, NNReal.coe_mul, hbabs, hloc]

end PositivityTheory.Rg.Sw.Glob
