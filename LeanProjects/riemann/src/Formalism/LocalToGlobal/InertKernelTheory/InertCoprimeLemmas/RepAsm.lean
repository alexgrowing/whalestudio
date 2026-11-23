import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConstantCoeffFormalSum
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.SclY

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem k1gen_of_orth {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) {be : MvPowerSeries (Fin 2) (K0 l)} (hB : BeProp l be)
    {g2 g3 ε s2 : MaximalUnramifiedExtension l} (hC : CurveAt l be g2 g3 ε s2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]} (hO : OrthInt l g2 g3 s2 ε Th) :
    @ExtensionGeneratorCondition l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be Th := by
  obtain ⟨hg2, hg3, hε, hθ, hN, hbe0, F, hF, hTie⟩ := hC
  obtain ⟨r, Θ, σ, f, f', hσ, hP, rfl, hI⟩ := hO
  have hInt := hyperbolic_of_orthogonal l h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF (hN σ hσ) ι (Fin r) f f' hP be hbe0 hTie Θ hI
  exact @first_kernel_of_sum l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be _ hB (sum_beta_even l (by omega) ι be hB) hInt

theorem representativeCondition_of_curve_orthAll {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p))
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p be) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (hC : CurveAt p be g2 g3 ε s2)
    (hO : OrthAll X E hfin pos F g2 g3 s2 ε) :
    Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.RepresentativeCondition X E hfin be pos F := by
  intro j _ L0 h0 La' hL' φ
  exact k1gen_of_orth h5 hB hC (hO j L0 h0 La' hL' φ)

theorem adm2b_of_prv (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : Formalism.L2.G.Pend.FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT)) (g2 g3 ε s2 : MaximalUnramifiedExtension p)
    (hC : CurveAt p (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2) (hO : OrthAll X E hfin pos F g2 g3 s2 ε) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos F) :=
  (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos F).2
    (representativeCondition_of_curve_orthAll h5 X E hfin _ pos F hB g2 g3 ε s2 hC hO)

theorem curveAt_of_beCob (H : Formalism.L2.KerInert.BeCob.BeCobTie) (D : Formalism.BasicNotions.D7)
    (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) {l : ℕ} [Fact l.Prime] {g : Formalism.MainNotions.GL3Theta.G1 l}
    (hLT : Formalism.L2.G.Pend.LTIso g) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (h5 : 5 ≤ l) (hI : Formalism.MainNotions.GL3Theta.InertK D l)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) :
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 := by
  obtain ⟨-, ⟨F, hF⟩, g2, g3, ε, s2, h1, h2, h3, h4, h6, h7, h8⟩ := H D cc δ l g hLT hA h5 hI hM
  exact ⟨g2, g3, ε, s2, h1, h2, h3, h4, h6, h7, F, hF, h8 F hF⟩

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem orthAll_of {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (T : Tor D) (e : FamE D) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p)
    (hI : ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → Formalism.L2.KerInert.IntFirst D T e p lam N N' L L')
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hComb : CombAt X hfin D large₂ Lg' F T e lam) (hFr : FrameHyp X E hfin D pos large₂ Lg' F S lam c)
    (hD : DictInt D lam T.abelian₂ c g2 g3 s2 ε) :
    OrthAll X E hfin pos (fun j La La' => linSub (S j La La') (F j La La')) g2 g3 s2 ε := by
  intro j L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFr j L0 h0 La' hL' φ
  obtain ⟨C, wq, hM, hW, hDi⟩ := hD
  obtain ⟨hAdm, hCb⟩ := hComb j L0 h0 La' hL'
  exact ⟨r, thOrth D lam c b (F j L0 La'), σ, f, f', hσ, hP, hEq,
    hDi _ _ r b _ (hI _ _ _ _ hAdm (F j L0 La') hCb C wq r b hM hW hLB hON)⟩

theorem orthAll_of_intInert (hInt : Formalism.L2.KerInert.IntInert) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p)
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) lam) (hFr : FrameHyp X E hfin D pos large₂ Lg' F S lam c)
    (hD : DictInt D lam B.tor.abelian₂ c g2 g3 s2 ε) :
    OrthAll X E hfin pos (fun j La La' => linSub (S j La La') (F j La La')) g2 g3 s2 ε :=
  orthAll_of X E hfin D pos large₂ Lg' F B.tor (B.eNat χ) lam c g2 g3 s2 ε
    (fun N N' L L' hA => hInt D cc δ B hcc hδ χ hχ p h5 hin lam N N' L L' hA) S hComb hFr hD

theorem curveDict_data (hCD : CurveDict) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime]
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (h5 : 5 ≤ p)
    (hIn : Formalism.MainNotions.GL3Theta.InertK D p) (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) :
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension p, CurveAt p (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : D7, DictInt D' g.lam g.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
  obtain ⟨g2, g3, ε, s2, h⟩ := hCD D cc δ p g hLT hA h5 hIn hM
  exact ⟨g2, g3, ε, s2, by tauto⟩

theorem adm2b_of_curve_dictionary (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (hst : Formalism.L2.G.Pend.FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFr : FrameHyp X E hfin D pos large₂ Lg' F S g.lam
      (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹)) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos (fun j La La' => linSub (S j La La') (F j La La'))) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  exact adm2b_of_prv D h5 X E hfin hst hLT pos _ hB g2 g3 ε s2 hC
    (orthAll_of_intInert hInt X E hfin D pos large₂ Lg' F cc δ B hcc hδ χ hχ h5 hin g.lam _ g2 g3 s2 ε S hComb hFr hD')

theorem thOrth_sclY {p : ℕ} [Fact p.Prime] {N N' r : ℕ} (D : D7) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    thOrth D lam 1 b (sclY c G) = thOrth D lam c b G := by
  have ha : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      ∑ i, MvPowerSeries.C ((1 : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold thOrth sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, one_mul]

theorem adm2b_of_curve_dictionary_one (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (hst : Formalism.L2.G.Pend.FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hFr : ∀ j La La', Fr j La La' =
      sclY (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) (F j La La'))
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFH : FrameHyp X E hfin D pos large₂ Lg' Fr S g.lam 1) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos (fun j La La' => linSub (S j La La') (Fr j La La'))) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  obtain ⟨C, wq, hMod, hW, hDi⟩ := hD'
  refine adm2b_of_prv D h5 X E hfin hst hLT pos _ hB g2 g3 ε s2 hC ?_
  intro j L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFH j L0 h0 La' hL' φ
  obtain ⟨hAdm, hCb⟩ := hComb j L0 h0 La' hL'
  refine ⟨r, thOrth D g.lam (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) b (F j L0 La'), σ, f, f', hσ,
    hP, ?_, hDi _ _ r b _ (hInt D cc δ B hcc hδ χ hχ p h5 hin g.lam _ _ _ _ hAdm (F j L0 La') hCb C wq r b hMod hW hLB hON)⟩
  rw [hEq, hFr, thOrth_sclY]
end Glob

end Formalism.L2.KerInert.Rep
