import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Dat

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA cB : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

end Dat

section Range

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word}

theorem twDen_pos : 0 < cAof sel mu cst := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _

theorem twMod_pos (hT : 0 < Pr.T u) : 0 < cBof sel mu cst u := Nat.mul_pos hT (pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _)

theorem mem_divLat_of_loc {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j) {x : HomE X.E (R.N i) (R.N j)}
    (h1 : phiT X.K p.deco.1 p'.deco.1 x ≠ 0)
    (h2 : ∀ (P : rowSG Pr sel mu) s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * inFr (frsF sel mu p P) (frsF sel mu p' P) x (Pi.single s 1) l)) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) := by
  classical
  intro P hP y hy
  change ((cAof sel mu cst : ℕ) : 𝓞 X.E) • x y ∈ _
  have hP' : P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := Finset.mem_union.1 hP
  rcases hP' with hT | hB
  · exact Submodule.smul_mem _ _ (cond_of_ite_ne_zero h1 ⟨P, hT⟩ y hy).1
  · obtain ⟨k, hk⟩ : qOf P ^ cst.A ∣ cAof sel mu cst :=
      pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (a := ⟨P, hB⟩) (Finset.mem_univ _)) _
    have h3 := GlobalTheory.Proof.datum_support_div_lattice_interior.smul_mem_of_frames P (p.deco.1.at P) (p'.deco.1.at P) (frsF sel mu p ⟨P, hB⟩) (frsF sel mu p' ⟨P, hB⟩)
      (frsF_mem p ⟨P, hB⟩) (frsF_mem p' ⟨P, hB⟩) x _ (h2 ⟨P, hB⟩) y hy
    rw [hk, Nat.cast_smul_eq_nsmul, mul_comm, mul_smul, ← Nat.cast_smul_eq_nsmul X.E (qOf P ^ cst.A), Nat.cast_pow]
    exact nsmul_mem h3 k

theorem loc_of_mem_mulLat (hPr : Pr.Ok) {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j)
    (x : HomE X.E (R.N i) (R.N j)) {y : HomE X.E (R.N i) (R.N j)}
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    phiT X.K p.deco.1 p'.deco.1 (x + y) = phiT X.K p.deco.1 p'.deco.1 x ∧
      ∀ (P : rowSG Pr sel mu) s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * inFr (frsF sel mu p P) (frsF sel mu p' P) y (Pi.single s 1) l) := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  refine ⟨GlobalTheory.phiT_add_smul_homAt X.K _ _ p'.deco.2 Finset.subset_union_left _ (fun P => ?_) x y₀ hy₀, fun P => ?_⟩
  · rw [cBof, Nat.cast_mul, ← hPr.piT_norm u]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    have h := P.2
    unfold Primes.vT divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  · obtain ⟨r, hr⟩ : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
    exact GlobalTheory.intAt_inFr_smul_homAt (Finset.mem_union_right _ P.2) _ _ (frsF_mem p P) (frsF_mem p' P) _ (r : 𝓞 X.E) _
      (pow_ne_zero _ (GlobalTheory.TopInv.qOf_ne P.1)) (by rw [hr]; simp) y₀ hy₀

variable {m2 : ℕ}

theorem locTop_den (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)}
    {y' : Sp X.E (R.N (m2 + 1))} (h : locTop Ch sel mu cst m2 P y y' ≠ 0) (s : Fin (R.N (m2 + 1))) (l : Fin (R.N R.m)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * y (Pi.single s 1) l) := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  by_cases hl : l.1 < R.N R.m - 1
  · have h3 := GlobalTheory.SuppTop.intAt_of_phiTop Ch mu _ m2 hm P.1 _ h1 l.1 s.1 hl s.2
    have e : Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) s.1 = Pi.single (Fin.castAdd _ s) 1 := by
      funext t
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [e, LinearMap.comp_apply, LinearMap.comp_apply, castAdd_single, Loc.atN, dif_pos (show l.1 < R.N R.m - 1 + 0 from hl)] at h3
    exact (intAt_pow (intAt_nat _) _).mul h3
  · have h3 := GlobalTheory.SuppTop.intAt_of_ftY sel mu cst P _ _ h2 s
    obtain rfl : l = Br.iL (N_m_succ R) := Fin.ext (by have := l.2; show l.1 = R.N R.m - 1; omega)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_A
    rw [LinearMap.comp_apply, atNL_last] at h3
    rw [hk, add_comm, pow_add, mul_assoc]
    exact (intAt_pow (intAt_nat _) _).mul h3

open Classical in

theorem locTop_add (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hD : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {z : HomE X.E (R.N (m2 + 1)) (R.N R.m)} {y' : Sp X.E (R.N (m2 + 1))}
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l))
    (hy' : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y' i)) :
    locTop Ch sel mu cst m2 P (y + z) y' = locTop Ch sel mu cst m2 P y y' := by
  simp only [← div_eq_inv_mul] at hz
  unfold locTop
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (GlobalTheory.TopInv.PhiTop_add mu Ch _ m2 hm P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P hD _ _ _ (fun s => ?_) hy')
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; unfold cOf at this; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, castAdd_single, ← pow_one (qOf P.1 : X.E)]
    exact GlobalTheory.TopInv.intAt_div_pow_le (GlobalTheory.TopInv.qOf_ne P.1) hc.B_pos (hz s _)
  · rw [LinearMap.comp_apply, atNL_last]
    exact hz s _

end Range

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {A : Amb X} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
  {P : LevFam X.E X.K R.r Pr.vGs} {c : TopDepth R cst.M} {G : ChGlob X R.m}

variable (A) in

def twThPt (i j : ℕ) (e : j = i + 1) (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β)
    (d : (twFam W Ch sel mu cst L u m2 b hY P c i).D β) (d' : (twFam W Ch sel mu cst L u m2 b hY P c j).D β') :
    VCx X.Tau (R.N i) (R.N j) → ℂ :=
  A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (levPt i β d).deco.1.N (levPt j β' d').deco.1.N (twXi i j e β β' d d')

section Pt

variable (i j : ℕ) (e : j = i + 1) (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β)
  (d : (twFam W Ch sel mu cst L u m2 b hY P c i).D β) (d' : (twFam W Ch sel mu cst L u m2 b hY P c j).D β')

end Pt

theorem twThPt_top (e : R.m = m2 + 1 + 1) (h : m2 + 1 = m2 + 1) (h' : R.m = R.m) (d : (ybCpl W sel mu cst L u m2 b hY).Pts)
    (p' : TopPt R sel mu u) :
    twThPt (Ch := Ch) (P := P) (c := c) A (m2 + 1) R.m e (.cpl h) (.top h') d p' =
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.1.deco.1.N p'.deco.1.N
        (XiTop Ch sel mu cst m2 d.1.1 d.1.2 p') := rfl

section Vec

variable (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (h0 : A.AA ≠ ⊥)
include hPr hL h0

end Vec

abbrev twSec (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : (twFam W Ch sel mu cst L u m2 b hY P c i).D x.1 :=
  ((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2

section Def

variable (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi)

def twTh : (twSrc chi hX hm hF hK hρ).ThFam := fun i x x' => twThPt A i (i + 1) rfl x.1 x'.1 (twSec i x) (twSec (i + 1) x')

def twChain : ColumnChain R X.Tau (W.hc u) := (twSrc chi hX hm hF hK hρ).chainTh A.σ₀ (W.hc u) A.cD (twTh chi hX hm hF hK hρ)

end Def

def twChainOf {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok)
    (hχ : TaylorLogMetric.IsChi D χ) (hF : ∀ j, (chF W sel mu L u j).Ok) (hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c) :
    ColumnChain R X.Tau (W.hc u) :=
  twChain (chiLat s χ) hX hL.hm hF hK (rhoUnit_of hX hPr hsel hS ht hL hG hs hχ)

variable (W sel mu cst A u) in

def TwJets : Prop :=
  ∀ i < R.m, JetsRatDeg A (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) fun τ => ∑ a, (W.nuW u (i + 1) τ).w a

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

theorem twChain_unf (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) (x' : (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl)
    (Q : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i)) (y' : ChSrc.Fr X A.σ₀ (R.N (i + 1))) :
    (twChain chi hX hm hF hK hρ).unf i x x' (fun y : ChSrc.Fr X A.σ₀ (R.N i) => MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q) y' =
      ∑ q ∈ (derPol A.cD Q y'.1).support, MvPolynomial.coeff q (derPol A.cD Q y'.1) * derivAt0 (twTh chi hX hm hF hK hρ i x x') q :=
  (twSrc chi hX hm hF hK hρ).chainTh_unf A.σ₀ (W.hc u) A.cD _ i x x' Q y'

variable (hT : 0 < Pr.T u) (hχ : ChiSplit chi A) (hs : ∀ i < R.m, A.ESmooth (R.N i) (R.N (i + 1))) (hJ : TwJets W sel mu cst A u)
include hT hχ hs hJ

end Laws

section Same

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Same

section Of

variable {D : D7} {s : Seam D X} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Base D cc δ} {χ : TaylorLogMetric.IdE D → ℂ} {cD : D.what₂.Tau → ℂ}
  {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} {hX : X.Ok} {hPr : Pr.Ok} {hsel : IsSel X sel}
  {hS : ∀ i, Pr.g i ∈ S} {ht : Ch.Tied s.σ₀ e G.mu0 eta} {hL : L.Ok Ch sel mu cst G m2} {hG : G.σ₀ = s.σ₀} {hs : s.Ok}
  {hχ : TaylorLogMetric.IsChi D χ} {hF : ∀ j, (chF W sel mu L u j).Ok} {hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c}

end Of

example {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
    {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} (i : ℕ)
    (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) (x' : (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl)
    (y' : ChSrc.Fr X A.σ₀ (R.N (i + 1))) :
    (twChain chi hX hm hF hK hρ).unf i x x' (fun _ => 1) y' = twTh chi hX hm hF hK hρ i x x' 0 := by
  have h := twChain_unf (chi := chi) (hX := hX) (hm := hm) (hF := hF) (hK := hK) (hρ := hρ) i x x' 1 y'
  simp only [map_one, derPol] at h
  refine h.trans ?_
  rw [MvPolynomial.support_one, Finset.sum_singleton, MvPolynomial.coeff_zero_one, one_mul, derivAt0]
  have h0 : ∀ n, n = 0 → ∀ v, iteratedFDeriv ℂ n (twTh chi hX hm hF hK hρ i x x') 0 v = twTh chi hX hm hF hK hρ i x x' 0 := by
    rintro _ rfl v
    exact iteratedFDeriv_zero_apply v
  exact h0 _ (by simp) _

example [IsEmpty (rowSG Pr sel mu)] (e : R.m = m2 + 1 + 1) (d : (ybCpl W sel mu cst L u m2 b hY).Pts) (p' : TopPt R sel mu u) :
    twThPt (Ch := Ch) (P := P) (c := c) A (m2 + 1) R.m e (.cpl rfl) (.top rfl) d p' =
      A.thDat (Sall sel mu u) 1 (Pr.T u) d.1.1.deco.1.N p'.deco.1.N (phiT X.K d.1.1.deco.1 p'.deco.1) := by
  rw [twThPt_top, cAof, cBof, Fintype.prod_empty, one_pow, one_pow, mul_one]
  congr 1
  funext x
  unfold XiTop
  rw [Fintype.prod_empty, mul_one]

example (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m ≤ i) : IsEmpty (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl :=
  ⟨fun x => (SpIdx.isEmpty_of_lt (by omega) (by omega)).false x.1⟩

end Chain

example {D : D7} {EX : ErrX D} (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    (A : Amb (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recFields D)) (ξ : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.Twist D)
    (cst : LocCst (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recFields D) (rowSG (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recPrimes EX) sel ξ)) (u : D.what₂.Word) :
    TwJets (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recWts EX) sel ξ cst A u ↔ GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.FieldTie sel A ξ cst u := Iff.rfl

end GlobalTheory.GO
