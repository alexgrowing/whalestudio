import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataParamsS
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.SharpRestriction.GlobalSchurBounds.TieGlobal
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw

noncomputable section

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions

def condE (D : D7) : ℝ := (D.host.QS : ℝ) * D.host.q * D.host.d

def Vbound (D : D7) (C : ℝ) : ℝ := C * Real.exp (C * Real.log ((D.R.n : ℝ) * (D.R.t : ℝ) * condE D) ^ 2)

def LinkV_at (D : D7) (C : ℝ) : Prop :=
  ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) →
    ∑ l ∈ S, Real.log l * (∑ e ∈ Finset.Ico 1 D.R.t, (D.what₂.shaLen l e : ℝ)) ≤ Vbound D C

def LinkV {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LinkV_at (Fm.D x i) C

def ShaFinOdd (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < D.R.t → Formalism.GaloisCohomology.shaLen (D.nd.ldat p) (e : ℤ) ≠ ⊤

def LinkShaFin {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ShaFinOdd (Fm.D x i)

def vvTerm (D : D7) (l : ℕ) : ℝ :=
  if l.Prime then ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ) * Real.log l else 0

open Classical in

def etaSum {D : D7} (L : SizeData₂ D) (j : ℕ) : ℝ :=
  ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
    SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

def LinkN_at {D : D7} (L : SizeData₂ D) (j : ℕ) (C : ℝ) : Prop :=
  Summable (vvTerm D) →
    etaSum L j ≤ (L.dZ0 j : ℝ) * (C * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L ^ 2 +
      Real.log L.sc.x ^ 2 * L.Nc) + ∑' l, vvTerm D l)

def LinkN {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ShaFinOdd (Fm.D x i) →
    ∀ j ∈ SizeData₂.lifts (Fm.D x i), LinkN_at (Fm.L x i) j C

def LinkEta {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, N.LocsCoverTw (Fm.D x i)

def SmallLevelRankEq {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), (Fm.L x i).dZ0 j = (Fm.D x i).what₂.D0

def LinkIRR {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    Rows.DelpNonneg (Fm.D x i).what₂ ∧ (Fm.D x i).what₂.delp ≤ Real.exp (-(x ^ (Fm.ez / 7)))

def DIVinN_at {D : D7} (L : SizeData₂ D) (j : ℕ) (C : ℝ) : Prop :=
  etaSum L j ≤ (D.what₂.D0 : ℝ) * (C * L.sc.x ^ L.sc.eps * (L.B0 + L.Nc))

def DIVinN {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), DIVinN_at (Fm.L x i) j C

def BesselId (D : D7) : Prop :=
  D.BuRational ∧ ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧
    ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ F, D.what₂.Bu u φ F = a * D.besS u (U φ) (V F)

def NprimeMuR {D : D7} (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤ C * L.sc.X'' D.R.n

def NuFullF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).NuFull

def LinkMu {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, NprimeMuR (Fm.L x i) C

def LinkDIV_at {D : D7} (L : SizeData₂ D) (C Cabs CH : ℝ) : Prop :=
  D.div.OneMapIntoCC ∧ sFrame D.div.Nu D.div.h + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b ∧
  L.ZeroAbove ∧ BesselId D ∧ D.RRFull ∧
  (∀ u, D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
    D.div.h u) ∧
  (∀ u, D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
    C * (D.host.TT.card : ℝ) * L.sc.a * L.La +
    C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)) ∧
  (∀ u, ∀ j ∈ SizeData₂.lifts D, |(∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w)) -
    (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))| ≤ C * L.B0) ∧
  (∀ u u', |(D.div.h u + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ)) -
    (D.div.h u' + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u').A.T : ℝ))| ≤
    C * ((D.host.TT.card : ℝ) * L.sc.a * L.La + (D.R.m : ℝ) * L.B0))

def LinkDIV {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LinkDIV_at (Fm.L x i) C Cabs CH

def LinkDIVt {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) : Prop :=
  LinkEta Fm → DIVinN Fm → LinkDIV Fm Cabs CH

def InertK (D : D7) (p : ℕ) : Prop :=
  D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass

def flG {D : D7} (L : SizeData₂ D) (C : ℝ) (p : ℕ) : ℝ :=
  C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
    C * (D.R.f : ℝ) * (Real.logb p L.sc.a) ^ 2

def rG (eps : ℝ) : ℕ := ⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1

def leastPowerExponent {D : D7} (L : SizeData₂ D) (p : ℕ) : ℕ :=
  ⌈Real.logb p ((D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A))⌉₊ + 1

def loG {D : D7} (L : SizeData₂ D) (C bo : ℝ) (p : ℕ) : ℝ :=
  let s := L.sc
  let pr : ℝ := if D.host.cls p = PrimeClass.inertClass then
      (if (p : ℝ) < s.p0 D.R.k then C * (rG s.eps : ℝ) * s.b' * Real.log s.x
       else if (p : ℝ) < s.X' then
         C * (s.b' / s.x + L.etaSz + L.Sc + (s.w'' D.R.n + D.R.t) * Real.log s.x / s.delta1) + bo
       else 0) else 0
  let orr : ℝ := if D.host.cls p = PrimeClass.inertClass ∧ (p : ℝ) < s.X' then
      C * Real.log s.x * (L.LaG * s.a / ((p : ℝ) * D.R.k) +
        (if (p : ℝ) < s.p0 D.R.k then s.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ)) else s.a / (p : ℝ) ^ 2))
      else 0
  C * (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * s.a) + pr + orr

def LinkG_at {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (C bo : ℝ) : Prop :=
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u) ∧
    (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + L.io w) ∧
    (G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) = ∅ → L.tau w = 0 ∧ L.io w = 0 ∧ L.lenMN u w = 0)) ∧
  (∀ p, ∀ t0 ∈ G.VV X K (G.aL L) (G.bL L) p,
    G.Sv X K (G.aL L) (G.bL L) p t0 ≤ 2 * (D.R.m : ℝ) * (G.Nv X p t0 : ℝ) * L.sc.a / p) ∧
  (∀ w, InertK D (D.what₂.places.resChar w) → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    (∀ j ∈ SizeData₂.lifts D, 0 ≤ L.gain j w ∧
      L.gain j w ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (D.what₂.places.resChar w : ℝ)) ∧
    (∑ j ∈ SizeData₂.lifts D, ∑ t ∈ L.TTw w,
        (L.vonMangoldtClassSum j t (D.what₂.places.resChar w) - loG L C bo (D.what₂.places.resChar w))) -
      (D.R.m : ℝ) * flG L C (D.what₂.places.resChar w) ≤
      ((∑ j ∈ SizeData₂.lifts D, L.gain j w) - L.tau w)) ∧
  G.ServedOrbitsContained X K (G.aL L) (G.bL L) ∧ G.MeanKappaBound X K

def LinkG {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ (C x0 : ℝ) (δ : ℝ → ℝ), Filter.Tendsto δ Filter.atTop (nhds 0) ∧
    ∀ x ≥ x0, ∀ i : Fm.Ix x, LinkG_at (Fm.Gx x i) Fm.GK C ((Fm.L x i).sc.b ^ δ x)

def hsDiagFull (D : D7) (u : D.what₂.Word) : ℝ :=
  S.hsNormSq (S.KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def LinkS_at {D : D7} (L : SizeData₂ D) (C0 Gam eta0 eta1 e0 : ℝ) : Prop :=
  (∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * Gam ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * Gam ^ 2 / D.what₂.Dstar ≤ C0) →
  (∀ u u', u ≠ u' → L.hsSq u u' ≤ (1 + eta0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
  (∀ u, hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) ∧ (D.what₂.Dall : ℝ) ≤ (1 + eta1) * D.what₂.Dstar

def GamOf {D : D7} (L : SizeData₂ D) : ℝ := Real.exp (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L)

def LinkS {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ eta0 eta1 e0 : ℝ, 0 ≤ e0 ∧
    eta0 ≤ Real.exp (-(x ^ (eps / 8))) ∧ eta1 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    Real.sqrt e0 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    LinkS_at (Fm.L x i) C0 (GamOf (Fm.L x i)) eta0 eta1 e0

def GlobalTheoremInputs {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) : Prop :=
  LinkG Fm ∧ LinkS Fm C0 ∧ LinkIRR Fm ∧ LinkDIV Fm Cabs CH ∧
  LinkMu Fm

def LinkGLOBAL {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) : Prop :=
  ChosenE Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 →
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x

end Formalism.MainNotions

end
