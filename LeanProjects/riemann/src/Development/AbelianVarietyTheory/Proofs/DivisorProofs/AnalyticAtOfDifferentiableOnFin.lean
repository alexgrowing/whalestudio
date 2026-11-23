import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD polydisc)
open scoped Classical Topology

namespace GlobalTheory.LatJet.An

theorem analyticAt_of_differentiableOn_fin {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U)
    {f : (I → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : I → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : (Fin (Fintype.card I) → ℂ) ≃L[ℂ] (I → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : I => ℂ) (Fintype.equivFin I).symm
  have hs : AnalyticAt ℂ (⇑e.symm) z := (e.symm : (I → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ)).analyticAt z
  have hU' : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hd : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' U) := hf.comp e.differentiableOn (fun _ h => h)
  have ha : AnalyticAt ℂ (f ∘ e) (e.symm z) :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hd _ (by simpa using hz)
  exact (ha.comp hs).congr
    (Filter.Eventually.of_forall fun w => by simp)

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  simp only [polydisc, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := fun i => by simp

theorem jetAnalytic_of_steps (hC : JetCalc) (hCh : JetChain) (hG : GermEx) (hK : CoordEx) (hZ : JetZeta) (hD : JetDet)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement) : JetAnalytic := by
  obtain ⟨ε₀, hK⟩ := hK
  obtain ⟨s₀, hZ⟩ := hZ
  refine ⟨s₀ * ε₀, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hf hCM hc R₀ s r m hs hr T n J Y _ hR₀ g ν u hg hu
  obtain ⟨G⟩ := hG E I 𝔠 φ c y hCM hc n T J Y
  obtain ⟨K⟩ := hK E I 𝔠 φ c y hCM hc n T J Y G
  have hζ := hZ ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨hCan, hCe⟩ := hD ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨-, hprod, hev, hconst, -, -, -⟩ := hC I n J
  have hgd : DifferentiableOn ℂ g (polydisc I) := ((((hS E I φ hf hCM).1 s hs).1 c y hc).1.2 g hg).1
  have hgan : AnalyticAt ℂ g 0 := analyticAt_of_differentiableOn_fin (isOpen_polydisc I) hgd (zero_mem_polydisc I)
  have hζan : AnalyticAt ℂ K.ζ 0 := by
    rw [analyticAt_pi_iff]
    intro i
    exact analyticAt_of_differentiableOn_fin K.isOpen (differentiableOn_pi.1 K.ζ_hol i) K.zero
  letI : Algebra R₀ G.B := ((algebraMap ℂ G.B).comp R₀.subtype).toAlgebra
  have hfan : AnalyticAt ℂ (fun z => G.y z (r.val G.B G.X trivial G.δ)) 0 :=
    analyticAt_of_differentiableOn_fin G.isOpen (G.hol _) G.zero
  have hfib : ∀ z ∈ K.V, K.C z ^ (2 * s) * G.y z (r.val G.B G.X trivial G.δ) = m * g (K.ζ z) := by
    intro z hz
    have hcomm : ∀ x : R₀, G.y z (algebraMap R₀ G.B x) = algebraMap R₀ ℂ x := fun x => by
      show G.y z (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes]; rfl
    let σ : G.B →ₐ[R₀] ℂ := { (G.y z : G.B →+* ℂ) with commutes' := hcomm }
    have hb := r.baseChange G.B ℂ σ G.X trivial (K.X z) trivial (K.q z) G.δ (K.δ z) (K.pull z) (K.corr z)
    rw [← hr g hg (K.ζ z) (K.ζ_mem z hz) (K.X z) (K.U z hz) (K.δ z) (K.C z) (K.det z hz), hb]
    rfl
  have hjB : r.val J.B Y.X' trivial G.δ'' = G.j (r.val G.B G.X trivial G.δ) := by
    have hcomm : ∀ x : R₀, G.j (algebraMap R₀ G.B x) = algebraMap R₀ J.B x := fun x => by
      show G.j (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes, hR₀]
    let σ : G.B →ₐ[R₀] J.B := { (G.j : G.B →+* J.B) with commutes' := hcomm }
    exact r.baseChange G.B J.B σ G.X trivial Y.X' trivial G.q G.δ G.δ'' G.pull G.corr
  have hhom := r.homog J.B Y.X' trivial G.δ'' Y.δ' G.e G.he
  have hpow : ∀ k : ℕ, jet J (fun z => K.C z ^ k) = jet J K.C ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have e1 : (fun z => K.C z ^ (k + 1)) = (fun z => K.C z ^ k) * K.C := by
        funext z; simp [pow_succ]
      rw [e1, (hprod (fun z => K.C z ^ k) K.C (hCan.pow k) hCan).1, ih, pow_succ]
  have hgζ : AnalyticAt ℂ (g ∘ K.ζ) 0 := by
    have : AnalyticAt ℂ g (K.ζ 0) := by rw [K.ζ_zero]; exact hgan
    exact this.comp hζan
  have hevq : (fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ)) =ᶠ[𝓝 0]
      (fun _ => m) * (g ∘ K.ζ) := by
    filter_upwards [K.isOpen.mem_nhds K.zero] with z hz using hfib z hz
  have hmain : algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ' =
      algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by
    calc algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ'
        = (G.e * jet J K.C) ^ (2 * s) * r.val J.B Y.X' trivial Y.δ' := by rw [map_pow, hCe]
      _ = jet J K.C ^ (2 * s) * (G.e ^ (2 * s) * r.val J.B Y.X' trivial Y.δ') := by ring
      _ = jet J (fun z => K.C z ^ (2 * s)) * jet J (fun z => G.y z (r.val G.B G.X trivial G.δ)) := by
        rw [hhom, hjB, G.jet_eq, hpow]
      _ = jet J ((fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ))) :=
        ((hprod (fun z => K.C z ^ (2 * s)) _ (hCan.pow _) hfan).1).symm
      _ = jet J ((fun _ => m) * (g ∘ K.ζ)) := hev _ _ hevq
      _ = algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by rw [(hprod _ _ analyticAt_const hgζ).1, hconst]
  have hrep := congrArg (fun x => J.b.repr x ν) hmain
  simp only [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] at hrep
  rw [hrep, hCh I n J K.ζ (fun i => (((s₀ * ε₀ : ℤˣ) : ℤ) : ℂ) * T.A i) g hζan K.ζ_zero hgan (fun i => hζ i) ν u hu]
  ring

end GlobalTheory.LatJet.An
