import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardStabFrm

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

def JetLossAllAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    (∀ c : ℕ, 0 < c → c ∣ cAof sel mu cst * cBof sel mu cst u → e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) c N N' Ξ) →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def JetLossAll (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → IsSel (recFields D) sel → AnTie D δ χ cD →
    JetLossAllAt (recPrimes EX) D.R (ambOf (recSeam D) B χ cD) sel (badS D)

example {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA c : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (e : DVar X.Tau a b →₀ ℕ) :
    e ∈ RatIdx A S cA c N N' fun _ => 0 := fun _ _ h => absurd rfl h

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

section
variable (A : Amb X)

theorem kerOf_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hPr : Pr.Ok)
    (hc : cst.Ok) (u : Pr.Word) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    {j j' : ℕ} (hj : j < R.m) (hj' : j' = j + 1)
    (hscal : ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
      IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
      w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1)
    (hdeg : (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N j) (Pr.vT u) SG) (d' : DecoSet X.E (R.N j') (Pr.vT u) SG')
    (hs : StdOver (Pr.g i) d.1.N) (hs' : StdOver (Pr.g i) d'.1.N) {fr : Frs X.E (R.N j) (rowSG Pr sel mu)}
    {fr' : Frs X.E (R.N j') (rowSG Pr sel mu)} (hf : IsFrames d.1.N fr) (hf' : IsFrames d'.1.N fr')
    {Ξ : HomE X.E (R.N j) (R.N j') → X.K}
    (hΞ : DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w d.1.N d'.1.N Ξ)
    {v : Formalism.L2.DIV.VV X.K (W.lamTrue u j)} (hv : v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) :
    lossAt W i u j • kerOf (stepC W Ch sel mu cst A u j (W.lamTrue u j')) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
      d.1.N fr d'.1.N fr' Ξ v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j') d'.1.Lsh) := by
  classical
  subst hj'
  have hT : ∀ Q ∈ Pr.vT u, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ h =>
    natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) _ h (T_mem_of_piT_mem hPr u (mem_divs hQ))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  rw [(GlobalTheory.GO.use₃ _ hT d w hw).2] at hv
  rw [(GlobalTheory.GO.use₃ _ hT d' w hw).2, stepC,
    kerOf_thDistC A _ _ (cAof_pos sel mu cst) (cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat,
    LinearMap.smul_apply, smul_comm]
  refine smul_mem_localizationAt_of_le w _ ?_ ?_
  · rw [map_mul, map_inv₀, hscal _ _ _ hsd hs hf, hscal _ _ _ hsd' hs' hf', inv_one, one_mul]
  obtain ⟨s, s', hwt, hnu⟩ := hW X Pr R W u j hj
  refine hO X.K w X.Tau _ _ _ _ _ s s' _ hwt _ _
    (fun τ => GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ d.2.lat)
    (fun τ => GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ d'.2.lat)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d.2.lat hs w hw)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d'.2.lat hs' w hw) _ _ (fun e he => ?_) v hv
  · have h1 : ∀ τ, ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) = ∑ a, (W.nuW u (j + 1) τ).w a := fun τ => by
      rw [he τ]
      exact Finset.sum_congr rfl fun a _ => hnu τ a
    have h2 : (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) =
        ∏ τ, X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ (∑ a, (W.nuW u (j + 1) τ).w a).toNat := by
      rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      dsimp only
      rw [← h1 τ, Int.toNat_natCast, Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    have h3 : e.degree + 1 < Pr.g i := by
      have h4 : (e.degree : ℤ) = ∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a := by
        rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, Fintype.sum_prod_type]
      omega
    rw [lossAt, ← h2]
    refine hJ i w hw u mu cst hc j _ hj rfl _ _ hsd hsd' hs hs' Ξ hΞ e h3 fun c hc0 hdvd x hx _ => ?_
    refine hrat _ _ _ x ⟨hsd, hsd', hc0, hdvd, ?_⟩ e fun τ => ?_
    · change ((cAof sel mu cst * cBof sel mu cst u : ℕ) : 𝓞 X.E) • x ∈ homAt _ _ _
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hx
    · dsimp only
      rw [← h1 τ]
      have h5 : (∑ β, ∑ α, (e (τ, β, α) : ℤ)) = ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) := by
        push_cast
        rfl
      convert (GlobalTheory.ColPeriodCompare.deg_eq e τ).trans h5

end

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)

set_option maxHeartbeats 1000000 in

theorem colMu_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hM : StdMove)
    (hLP : LevelPrimes) (hSU : ScalarUnit) (hEG : EntryAtG) (hEQ : EntryAtQ) (hTQ : TopAtQ)
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (hSg : ∀ i, Pr.g i ∈ S)
    {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E}
    (hT : Ch.Tied G.σ₀ e G.mu0 eta) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hwt : ∀ j ≤ R.m, ∀ b, WtUnit w ((chF W sel mu L u j).mem b))
    (hdeg : ∀ j < R.m, (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : ∀ j < R.m, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    (φ : MfV W Ch u) (hφ : φ ∈ MfL W Ch u) (d : (evGSD W Ch sel mu P u).D) :
    (∏ j ∈ Finset.range R.m, lossAt W i u j) • (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 d ∈
      localization₂ w.asIdeal ((evGSD W Ch sel mu P u).Del d) := by
  have hm := hL.hm
  have hlp := hLP X Pr sel S mu hX hPr hsel
  have hq : ∀ Q : rowSG Pr sel mu, Q.1 ∉ Pr.vGs → ((qOf Q.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := fun Q hQ =>
    natCast_notMem_of_ne (hlp Q).1.1 (hPr.g_prime i) (fun h => (hlp Q).2 hQ (h ▸ hSg i)) w hw
  have hsu := hSU X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hSg hT hL i w hw
  have heq := fun (Q : rowSG Pr sel mu) (hQ : Q.1 ∉ Pr.vGs) => hEQ X Pr R Ch sel S mu cst L G m2 hL Q w hQ (hlp Q).1 (hq Q hQ)
    fun j hj => (hsu j hj).1 Q fun h => hQ (vG_subset i h)
  have hcd := GlobalTheory.LastSteps.chainDataGuarded X Pr R Ch sel S mu cst m2 hPr hL.cst_ok hm
  rw [show Finset.range R.m = Finset.range (m2 + 2) by rw [hm]]
  refine colCpl_bound (chKerC W Ch sel mu cst L A u m2 b hY P hK).kk hF (fun j hj b => hwt j (by omega) b)
    (lossAt W i u) (chKerC W Ch sel mu cst L A u m2 b hY P hK).cp (hF (m2 + 1) b) (hwt _ (by omega) b)
    (fun j hj al be p p' => ?_) (fun al p₀ p Y hYm => ?_) (fun al p d₁ Y hYm => ?_) (startC hL u φ)
    (fun b' p => GlobalTheory.TestLat.WeylLocal.le_locP w _ (hφ (DecoF.deco p))) d
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u j al p
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (j + 1) be p'
    refine Bd.transfer g g' ((hF j al).del_smul g p) ((hF (j + 1) be).del_smul g' p')
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).equiv g g' p p') ?_
    generalize g • p = p, g' • p' = p' at hg hg' ⊢
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).k p p' =
        matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) j al be p p' := by
      simp only [chKerC, chKer, dif_pos hj]
    rw [e1]
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu j (by omega)).2
      (hdeg j (by omega)) (hrat j (by omega)) (DecoF.deco p) (DecoF.deco p') hg hg' (isFrames_frsF p)
      (isFrames_frsF p') ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (DecoF.deco p').2
      (fun Q x => XiAt Ch sel mu cst j Q (L.h j al Q) (L.h (j + 1) be Q) (inFr (frsF sel mu p Q) (frsF sel mu p' Q) x))
      (fun Q hQ => fnModAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q)
        (hEG X Pr R Ch sel S mu cst L G m2 hL j hj al be Q hQ (hlp Q).1))
      (fun Q hQ => awayAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q) ((heq Q hQ).1 j hj al be))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u m2 al p₀
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    refine Bd.transfer g g' ((hF m2 al).del_smul g p₀) ((hF (m2 + 1) b).del_smul g' p)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv1 g g' p₀ p Y) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g' p Y).2 hYm
    suffices key : ∀ (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) Y',
        StdOver (Pr.g i) (DecoF.deco p₀).1.N → StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N →
        Bd w (lossAt W i u m2) (((chF W sel mu L u m2).mem al).Del p₀) (((chF W sel mu L u (m2 + 1)).mem b).Del p)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y') from key _ _ _ hg hg' hY'
    intro p₀ p Y' hg hg' hY''
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y' =
        cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y' := rfl
    rw [e1, cp1K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu m2 (by omega)).2
      (hdeg m2 (by omega)) (hrat m2 (by omega)) (DecoF.deco p₀) (DecoF.deco p) hg hg' (isFrames_frsF p₀)
      (isFrames_frsF p) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p₀).1 (DecoF.deco p).2 (facPen Ch sel mu cst L m2 al p₀ p Y')
      (fun Q hQ => (hcd Q hQ).2.2.2.1 L al (hL.stabG m2 al Q hQ) u p₀ p Y' hY'')
      (fun Q hQ => awayAt_inFr (isFrames_frsF p₀ Q) (isFrames_frsF p Q) ((heq Q hQ).2 al _))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ d₁.1.N ⟨d₁.2.lat, d₁.2.uni⟩
    refine Bd.transfer (S' := evGSD W Ch sel mu P u) g (γ, 1) ((hF (m2 + 1) b).del_smul g p)
      (evGSD_del_smul W Ch sel mu hPr hsel u hS P γ d₁)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv2 g (γ, 1) p Y d₁) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g p Y).2 hYm
    have hγ' : StdOver (Pr.g i) (((γ, 1) : (evGSD W Ch sel mu P u).G) • d₁).1.N := hγ
    suffices key : ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) Y' (d₂ : RowPt Pr R sel mu),
        StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N → StdOver (Pr.g i) d₂.1.N →
        Bd w (lossAt W i u (m2 + 1)) (((chF W sel mu L u (m2 + 1)).mem b).Del p) ((evGSD W Ch sel mu P u).Del d₂)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂) from key _ _ _ hg hY' hγ'
    intro p Y' d₂ hg hY'' hγ'
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂ =
        cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p Y' d₂ := rfl
    rw [e1, cp2K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (j := m2 + 1) (j' := R.m) (by omega) hm
      (hsu _ (by omega)).2 (hdeg _ (by omega)) (hrat _ (by omega)) (DecoF.deco p) (tilQ sel mu u d₂) hg
      (stdOver_tilH _ (conj_piT_notMem hPr u) (piT_notMem_rowSG sel mu hPr hsel u hS) d₂ hγ') (isFrames_frsF p)
      (isFrames_frsT d₂) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (tilQ sel mu u d₂).2 (facTop Ch sel mu cst m2 p Y' d₂)
      (fun Q hQ => (hcd Q hQ).2.2.2.2 u (piT_notMem_rowSG sel mu hPr hsel u hS) p d₂ Y' hY'')
      (fun Q hQ => hTQ X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL Q w hQ (hlp Q).1 (hq Q hQ) p d₂ Y' hY'')

end GlobalTheory.ColPeriod
