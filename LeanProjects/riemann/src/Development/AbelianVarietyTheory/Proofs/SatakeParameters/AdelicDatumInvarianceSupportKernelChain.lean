import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumInvarianceSupportTransportFramesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorSameCouplingCosetAllBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepresentativeBoundedAtBadPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV.EntrySupportBounds

open GlobalTheory.Mem.Col2 GlobalTheory.TopStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem top_supp (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (x : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hx : XiTop Ch sel mu cst (m2 + 1) p Y p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm] at hx
  unfold xiOver at hx
  refine GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q s l => ?_
  have h := GlobalTheory.GO.locTop_den hL.hm hL.cst_ok (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _)) s
    (Fin.cast (congrArg R.N hm) l)
  simpa [castSp, LinearMap.funLeft_apply] using h

open Classical in
theorem top_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1))
    (hY : ∀ (Q : rowSG Pr sel mu) l, IntAt Q.1 ((qOf Q.1 : X.E) ^ (if Q.1 ∈ Pr.vGs then 1 else cst.M) * (frsF sel mu p Q).symm (repY Y) l))
    (x y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst (m2 + 1) p Y p' (x + y) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm]
  unfold xiOver
  refine congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ => ?_)
  rw [GlobalTheory.inFr_add, LinearMap.comp_add]
  refine GlobalTheory.GO.locTop_add hL.hm hL.cst_ok (hL.depthQ Q) _ (fun s l => ?_) (hY Q)
  simpa [castSp, LinearMap.funLeft_apply] using h2 Q s (Fin.cast (congrArg R.N hm).symm l)

theorem entry_supp (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1)))
    (hx : XiEntry Ch sel mu cst L i al be p p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.xiSupp i hi al be Q _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem entry_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x y : HomE X.E (R.N i) (R.N (i + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + y) = XiEntry Ch sel mu cst L i al be p p' x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg _ (GlobalTheory.inFr_add _ _ x y)).trans (hL.xiInv i hi al be Q _ _ (h2 Q)))

theorem cpl_supp (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hx : XiCpl1 Ch sel mu cst L m2 al p₀ p Y x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.psiSuppX al Q _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem cpl_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x y : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + y) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg (fun t => PsiAt Ch sel mu cst m2 Q _ t _) (GlobalTheory.inFr_add _ _ x y)).trans (hL.psiInvX al Q _ _ _ (h2 Q)))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem transport {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) (Ξ : HomE X.E a b → X.K)
    (hAA : ∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0,
      r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E))
    (h1 : ∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) (h2 : ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) :
    DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))
        (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧
      ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB)
        (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
          ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) :=
  GlobalTheory.T.finiteDatum_invariance_support_transport_frames s cc S N N' f f' cA cB hA hB Ξ hAA h1 h2

theorem cosetNonempty {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) : ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) :=
  GlobalTheory.T.exists_vector_sameCouplingCoset_all_bad_primes sel mu cst fr y0

open Classical in
theorem couplingBaseVector_bound_kernelChain {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) :=
  GlobalTheory.T.intAt_qOf_pow_mul_y0_of_adTie A dtU a H β x Q l

open Classical in
theorem cosetBound {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (x : UA D (t.m2 + 1) hi)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l) := by
  have hy0 : ∀ P, y0At A (t.m2 + 1) hi β P = A.y0 β P := fun P => by simp [y0At]
  obtain ⟨y, hy⟩ := cosetNonempty t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) p P) (fun P => A.y0 β P)
  have hne : repY (cosetOf A (t.m2 + 1) hi β p) ∈ cosetOf A (t.m2 + 1) hi β p := by
    unfold repY
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p) ⟨y, fun P => by rw [hy0]; exact hy P⟩
  have h1 := hne Q l
  rw [hy0] at h1
  have h2 := couplingBaseVector_bound_kernelChain A dtU a H β x Q l
  generalize (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) = v at h1 ⊢
  rw [Pi.sub_apply] at h1
  have hq := GlobalTheory.TopInv.qOf_ne (E := t.X.E) Q.1
  split_ifs at h1 h2 ⊢ with hQ
  · have e : (qOf Q.1 : t.X.E) ^ 1 * v l = (qOf Q.1 : t.X.E) * (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (v l - A.y0 β Q l)) +
        (qOf Q.1 : t.X.E) ^ 1 * A.y0 β Q l := by ring
    rw [e]
    exact ((GlobalTheory.TopStep.intAt_nat _).mul h1).add h2
  · have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf Q.1 : t.X.E) ^ (t.cst μ).M * (qOf Q.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v l - A.y0 β Q l)) + (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 β Q l := by
      field_simp
      ring
    rw [e]
    exact (((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _)).mul h1).add h2

set_option maxHeartbeats 800000 in
theorem sizeLaw_of_tie' : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT hPt i hi β β' x x'
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  have hL := t.idx_ok μ
  have hPr := t.pr_ok
  have hp := (hPt i (Nat.le_of_succ_le hi) β x).choose_spec
  have hp' := (hPt (i + 1) hi β' x').choose_spec
  have hxi : xiAd A a i hi β β' x x' = fun z => t.seam.σ₀ (xiPt A i hi β β' (hPt i (Nat.le_of_succ_le hi) β x).choose
      (hPt (i + 1) hi β' x').choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) :=
    funext fun z => dif_pos ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  generalize (hPt i (Nat.le_of_succ_le hi) β x).choose = p at hp hxi
  generalize (hPt (i + 1) hi β' x').choose = p' at hp' hxi
  have hS : ssRec t u μ = (Sall t.sel (t.tup μ) (t.word u)).map
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).toEmbedding := by
    unfold ssRec
    rw [hSS]
  rw [hxi, hS, hlev, latK_eq_map _ (A.crd i (Nat.le_of_succ_le hi)), latK_eq_map _ (A.crd (i + 1) hi), ← hp.lat, ← hp'.lat]
  unfold levC
  refine transport t.seam t.cc _ _ _ _ _ _ _ GlobalTheory.GO.twDen_pos (GlobalTheory.GO.twMod_pos (hPr.T_prime _).pos) _
    (fun P hP => hT.aa P hP) ?_ ?_
  · intro z hz
    unfold xiPt at hz
    split_ifs at hz with h1 h2
    · exact entry_supp hL h1 _ _ _ _ z hz
    · subst h2
      exact cpl_supp hL _ _ _ _ z hz
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_supp hL _ _ _ z hz
  · intro z y hy
    unfold xiPt
    split_ifs with h1 h2
    · exact entry_add hPr hL h1 _ _ _ _ z y hy
    · subst h2
      exact cpl_add hPr hL _ _ _ _ z y hy
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_add hPr hL _ _ _ (fun Q l => cosetBound A dtU a hT _ β x _ Q l) z y hy

end GlobalTheory.TwV.EntrySupportBounds

theorem GlobalTheory.TwV.sizeLaw_of_tie : GlobalTheory.TwV.UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => GlobalTheory.TwV.PtEx A a → GlobalTheory.TwV.SizeLaw A a) :=
  GlobalTheory.TwV.EntrySupportBounds.sizeLaw_of_tie'
