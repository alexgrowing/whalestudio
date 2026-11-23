import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowerEmbF
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

noncomputable section

namespace GlobalTheory.Mem.Col2.KerRat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep GlobalTheory.GO
open GlobalTheory.LvT.Built (kAt)

theorem sum_cl {E K M : Type} [Field E] [NumberField E] [Field K] [AddCommMonoid M] {n : ℕ} (S : GStep E K n) {i : Fintype S.Cl}
    [∀ b, Fintype (MulAction.orbitRel.Quotient (S.G b) (S.D b))] (g : S.Cl → M) : ∑ c, g c = ∑ b, ∑ q, g ⟨b, q⟩ := by
  rw [← Fintype.sum_sigma]
  congr 1
  congr 1
  exact Subsingleton.elim _ _

theorem csOf_eq {K M : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] (S : GSD K) (h : S.Ok) (s : S.Sec)
    (f : S.D → M) : S.csOf h s f = letI := h.fintypeCl
      ∑ q, ((Nat.card (MulAction.stabilizer S.G (s.rep q)) : ℕ) : K)⁻¹ • f (s.rep q) := by
  unfold GSD.csOf
  simp only [GSD.wt_eq]

theorem sum_step {E K M β : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M]
    {n : ℕ} (S : GStep E K n) {i : Fintype S.Cl} [Fintype β] (e : β ≃ S.β) (T : β → GSD K) (hT : ∀ a, (T a).Ok)
    (π : ∀ a, S.D (e a) → (T a).D) (hs : ∀ a, Function.Surjective (π a))
    (h1 : ∀ a (g : S.G (e a)) d, ∃ g' : (T a).G, π a (g • d) = g' • π a d)
    (h2 : ∀ a (g' : (T a).G) d d', g' • π a d = π a d' → ∃ g : S.G (e a), g • d = d')
    (h3 : ∀ a d, Nat.card (MulAction.stabilizer (S.G (e a)) d) = Nat.card (MulAction.stabilizer (T a).G (π a d)))
    (F : S.Cl → M) (f : ∀ a, (T a).D → M) (hF : ∀ a q, F ⟨e a, q⟩ = f a (π a (S.rp _ q)))
    (hf : ∀ a (g : (T a).G) d, f a (g • d) = f a d) :
    ∑ c, ((Nat.card (S.Stab c) : ℕ) : K)⁻¹ • F c = ∑ a, (T a).csOf (hT a) (T a).outSec (f a) := by
  letI : ∀ b, Fintype (MulAction.orbitRel.Quotient (S.G b) (S.D b)) :=
    fun b => @Fintype.ofFinite _ (Finite.of_injective (@Sigma.mk _ (fun b => MulAction.orbitRel.Quotient (S.G b) (S.D b)) b)
      sigma_mk_injective)
  rw [sum_cl]
  refine (Fintype.sum_equiv e _ _ fun a => ?_).symm
  rw [csOf_eq]
  letI := (hT a).fintypeCl
  refine (sum_cover (π a) (hs a) (h1 a) (h2 a) (h3 a) (S.rp _) (S.rp_spec _) _ (T a).outSec.spec (f a) (hf a)).symm.trans ?_
  exact Finset.sum_congr rfl fun q _ => congrArg _ (hF a q).symm

theorem eqFun_sum {K β : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) [Fintype β] (f : β → S.EqFun) (d : S.D) :
    (∑ a, f a).1 d = ∑ a, (f a).1 d := by
  rw [Submodule.coe_sum, Finset.sum_apply]

theorem csOf_apply₂ {K M M' : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (s : S.Sec) [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module K M'] (B : S.D → (M →ₗ[K] M' →ₗ[K] K)) (x : M) (y : M') :
    S.csOf h s B x y = S.csOf h s fun d => B d x y := by
  simp only [GSD.csOf, LinearMap.sum_apply, LinearMap.smul_apply]

theorem comp_appOf {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}
    (A : CplKer S₀ S S₁ Y) (h₀ : S₀.Ok) (h : S.Ok) (φ : S₀.D → S₀.V) (d₁ : S₁.D) :
    (A.comp h S.outSec).appOf h₀ S₀.outSec φ d₁ =
      (cplKer2 A).appOf (cplGSD_ok Y h) (cplGSD S Y).outSec ((cplKer1 A).appOf h₀ S₀.outSec φ) d₁ := by
  unfold ClsKer.appOf
  simp only [cpl_comp_k, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => ?_
  rw [smul_comm]

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  (A : Amb X) {G : ChGlob X R.m} {m2 : ℕ} (u : Pr.Word)

def idxEquiv {j : ℕ} (h : j < R.m) : L.β j ≃ Idx sel mu L j where
  toFun al := Idx.of al h
  invFun b := b.get h
  left_inv _ := rfl
  right_inv b := Idx.of_get b h h

theorem kAt_mat (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i + 2 < R.m) (al : L.β i) (be : L.β (i + 1))
    (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    kAt W Ch sel mu cst L A u i (Idx.of al (by omega)) (Idx.of be (by omega)) p p' =
      matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) i al be p.1.1 p'.1.1 := by
  rw [matK_eq_xiAt W Ch sel mu cst L _ hi]
  unfold kAt KerT.ker
  rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u i (by omega)]
  rfl

theorem kernelAtPoint_penultimateStep_firstCoupledKernel (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (b' : Idx sel mu L (m2 + 1))
    (p : PtAt R sel mu cst u m2) (p' : PtAt R sel mu cst u (m2 + 1)) :
    kAt W Ch sel mu cst L A u m2 (Idx.of al (by have := hL.hm; omega)) b' p p' =
      cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p.1.1 p'.1.1 p'.1.2 := by
  have hm := hL.hm
  rw [firstCoupledKernel_eq_columnChainDatum W Ch sel mu cst L _ hm.symm al b']
  unfold kAt KerT.ker
  rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u m2 (by omega)]
  rfl

theorem ker_top (hL : L.Ok Ch sel mu cst G m2) (p : PtAt R sel mu cst u (m2 + 1)) (q : ChPt (R := R) sel mu u R.m) :
    KerT.ker W Ch sel mu cst A u (m2 + 1) R.m p.1.1.deco.1.N (frsF sel mu p.1.1) q.deco.1.N (frsF sel mu q)
      (xiOver Ch sel mu cst m2 rfl p.1.1 p.1.2 q) = topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p.1.1 p.1.2 q := by
  have hm := hL.hm
  rw [k2top_eq_xiOver W Ch sel mu cst _ hm.symm]
  unfold KerT.ker
  rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u (m2 + 1) (by omega)]
  rfl

variable {W Ch u} in

theorem k2top_tilF (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hm : R.m = m2 + 2) (hc : cst.Ok) (H : TilOk Pr sel mu u)
    {T : ChTh W sel mu u m2} (hT : TameFr T.top) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (d : XPt Pr R sel mu) :
    topDegreeKTwo W Ch sel mu cst T p Y (tilF sel mu u d) = cp2K W Ch sel mu cst T p Y (toRow sel mu d) := by
  have hQ : ∀ P : QE sel (mu : Chr X.F X.E X.K), Pr.piT u ∉ P.1.asIdeal := fun P => H.2.1 (TopStep.inQ Pr sel mu P)
  have e0 := forgetFr_tilF sel mu hPr u hQ d
  unfold topDegreeKTwo cp2K
  split_ifs with hY
  · have hκ : ∀ P : rowSG Pr sel mu, ∃ κ : GLint X.E (R.N R.m) P.1, redGL _ P.1 κ = 1 ∧
        frsF sel mu (tilF sel mu u d) P = frsT sel mu u (toRow sel mu d) P * κ.1 := fun P => by
      refine exists_of_isLiftFr ?_ (liftFr_spec (tilQ sel mu u (toRow sel mu d)).2 P)
      rw [← e0]
      unfold frsF
      split_ifs with hP
      · have h := liftFr_spec (tilF sel mu u d).deco.2 ⟨P.1, hP⟩
        refine ⟨h.1, fun x hx => ?_⟩
        exact (congrFun (forgetDeco_be_of_mem _ P hP) _).trans (h.2 x hx)
      · exact isLiftFr_forgetFr _ P hP
    choose κ hκ e using hκ
    rw [XiTop_tilF Ch sel mu cst hX hPr hsel hc H hm p hY, funext e, tilF_N sel mu hPr u hQ]
    unfold kerOf
    refine congrArg (latSum _ _) (funext fun x => congrArg _ ?_)
    exact hT _ _ _ _ _ _ κ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u _).2.lat, (tilQ sel mu u _).2.uni⟩ hκ
  · rfl

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

variable (sel mu cst L) in

structure Reps where
  rp : ∀ j b, MulAction.orbitRel.Quotient ((stepAt sel mu cst L Tp u j).G b) (GStep.D (stepAt sel mu cst L Tp u j) b) →
    (stepAt sel mu cst L Tp u j).D b
  spec : ∀ j b q, Quotient.mk (@MulAction.orbitRel _ _ _ ((stepAt sel mu cst L Tp u j).actD b)) (rp j b q) = q

variable {u Tp} (r : Reps sel mu cst L u Tp)

@[reducible] def Reps.step (j : ℕ) : GStep X.E X.K (R.N j) :=
  { stepAt sel mu cst L Tp u j with rp := r.rp j, rp_spec := r.spec j }

theorem sum_low {M : Type} [AddCommGroup M] [Module X.K M] {j : ℕ} (hj : j + 1 < R.m) (hF : (chF W sel mu L u j).Ok)
    {i : Fintype (GStep.Cl (r.step j))} (F : GStep.Cl (r.step j) → M)
    (f : ∀ al : L.β j, ChPt (R := R) sel mu u j → M)
    (e : ∀ al q, F ⟨Idx.of al (Nat.lt_of_succ_lt hj), q⟩ =
      f al (GStep.rep (r.step j) ⟨Idx.of al (Nat.lt_of_succ_lt hj), q⟩).1.1)
    (hf : ∀ al (g : FrmG (L.levG j al) (L.levQ j al)) (d : ChPt (R := R) sel mu u j), f al (g • d) = f al d) :
    ∑ c, ((Nat.card (GStep.Stab (r.step j) c) : ℕ) : X.K)⁻¹ • F c =
      ∑ al, ((chF W sel mu L u j).mem al).csOf (hF al) ((chF W sel mu L u j).mem al).outSec (f al) := by
  have hy := ysAt_ys_of_ne (R := R) sel mu cst hj.ne
  exact sum_step (r.step j) (idxEquiv (Nat.lt_of_succ_lt hj)) (chF W sel mu L u j).mem hF (fun _ p => p.1.1)
    (fun _ q => exists_ptAt sel mu cst q) (fun _ g _ => ⟨g, rfl⟩) (fun _ g d e h => ⟨g, StepZero.pt_ext hy h⟩)
    (fun al d => congrArg (fun H : Subgroup (FrmG (L.levG j al) (L.levQ j al)) => Nat.card H)
      (Subgroup.ext fun g => ⟨fun h => congrArg (fun p : PtAt R sel mu cst u j => p.1.1) h, fun h => StepZero.pt_ext hy h⟩)) F f e hf

theorem sum_mid {M : Type} [AddCommGroup M] [Module X.K M] (hL : L.Ok Ch sel mu cst G m2) (b : L.β (m2 + 1))
    (hY : YbHyp (R := R) sel mu cst L u m2 b) (hC : (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).Ok)
    {i : Fintype (GStep.Cl (r.step (m2 + 1)))} (F : GStep.Cl (r.step (m2 + 1)) → M)
    (f : (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).D → M)
    (e : ∀ c h, F c = f ⟨(GStep.rep (r.step (m2 + 1)) c).1, h⟩)
    (hf : ∀ (g : (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).G) d,
      f (letI := (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).actD; g • d) = f d) :
    ∑ c, ((Nat.card (GStep.Stab (r.step (m2 + 1)) c) : ℕ) : X.K)⁻¹ • F c =
      (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).csOf hC (GSD.outSec _) f := by
  have hm := hL.hm
  have hj : m2 + 1 < R.m := by omega
  let ε : Unit ≃ Idx sel mu L (m2 + 1) := ⟨fun _ => Idx.of b hj, fun _ => (), fun _ => rfl, fun b' => by
    obtain ⟨b₀, h₀⟩ := hL.last_uniq
    show Idx.of b hj = b'
    rw [← Idx.of_get b' hj hj, h₀ (b'.get hj), h₀ b]⟩
  refine (sum_step (r.step (m2 + 1)) ε
    (fun _ => cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)) (fun _ => hC)
    (fun _ p => ⟨p.1, PtAt.mem_ybSet p hm.symm⟩)
    (fun _ q => ⟨⟨q.1, by rw [ysAt_ys_of_eq sel mu cst hm.symm]; exact q.2⟩, rfl⟩)
    (fun _ g _ => ⟨g, rfl⟩) (fun _ g d e h => ⟨g, Subtype.ext (congrArg (fun p : (ybCpl W sel mu cst L u m2 b hY).Pts => p.1) h)⟩)
    (fun _ d => congrArg (fun H : Subgroup (FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)) => Nat.card H)
      (Subgroup.ext fun g => ⟨fun h => Subtype.ext (congrArg (fun p : PtAt R sel mu cst u (m2 + 1) => p.1) h),
        fun h => Subtype.ext (congrArg (fun p : (ybCpl W sel mu cst L u m2 b hY).Pts => p.1) h)⟩))
    F (fun _ => f) (fun _ q => e _ _) fun _ => hf).trans (Fintype.sum_unique _)

theorem sum_row {M : Type} [AddCommGroup M] [Module X.K M] (P : LevFam X.E X.K R.r Pr.vGs)
    (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (hM : (mtildeGSD W Ch sel mu P).Ok)
    {i : Fintype (GStep.Cl (stepX Ch sel mu P))} (f : RowPt Pr R sel mu → M)
    (hf : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D), f (g • d) = f d) :
    ∑ c, ((Nat.card (GStep.Stab (stepX Ch sel mu P) c) : ℕ) : X.K)⁻¹ • f (toRow sel mu (GStep.rep (stepX Ch sel mu P) c).1.1) =
      (mtildeGSD W Ch sel mu P).csOf hM (GSD.outSec _) f := by
  have hy : ∀ N, (Ys.triv X (R.N R.m - 1)).ys N = {∅} := fun _ => rfl
  refine (sum_step (stepX Ch sel mu P) (Equiv.refl Unit) (fun _ => mtildeGSD W Ch sel mu P) (fun _ => hM)
    (fun _ p => toRow sel mu p.1.1) (fun _ q => ?_) (fun _ g d => ⟨toRowG Ch sel mu P g, toRow_smul Ch sel mu P g d.1.1⟩)
    (fun _ g d e h => ?_) (fun _ d => ?_) _ (fun _ => f) (fun _ _ => rfl) fun _ => hf).trans (Fintype.sum_unique _)
  · obtain ⟨p, rfl⟩ := toRow_surjective sel mu q
    exact ⟨trivPt X _ _ _ _ p, rfl⟩
  · obtain ⟨g, -, h⟩ := exists_toRowG_smul Ch sel mu P hd g d.1.1 e.1.1 h
    exact ⟨g, StepZero.pt_ext hy h⟩
  · refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd d.1.1)
    exact congrArg (fun H : Subgroup (FrmG (rowTyG Ch P) (levQX R sel mu)) => Nat.card H)
      (Subgroup.ext fun g => ⟨fun h => congrArg (fun p : (stepX Ch sel mu P).D () => p.1.1) h, fun h => StepZero.pt_ext hy h⟩)

section Col

variable (rho : ∀ i, (r.step i).Cl → ℂ) (rho' : ∀ i, (r.step (i + 1)).Cl → ℂ)
  (jet : ∀ i, (r.step i).Cl → (r.step (i + 1)).Cl → (Pol ℂ X.Tau (R.N i) →ₗ[ℂ] Pol ℂ X.Tau (R.N (i + 1)))) (DG : ℕ)

@[reducible] def Reps.chain : ChainIn X.E X.K X.Tau R := ⟨r.step, rho, rho', jet, DG⟩

variable (hI : (r.chain rho rho' jet DG).Ok)

def kPt : PtKer (r.chain rho rho' jet DG) (W.hc u) := fun i b b' p p' => kAt W Ch sel mu cst L A u i b b' p p'

def colAt (φ : MfV W Ch u) (j : ℕ) (b : Idx sel mu L j) (p : PtAt R sel mu cst u j) : VV X.K (W.lamTrue u j) :=
  colPt hI (kPt W Ch A r rho rho' jet DG) (fun _ p => φ.1 p.1.1.deco) j b p

theorem colAt_succ (φ : MfV W Ch u) (j : ℕ) (b' : Idx sel mu L (j + 1)) (p' : PtAt R sel mu cst u (j + 1)) :
    colAt W Ch A r rho rho' jet DG hI φ (j + 1) b' p' =
      ∑ c ∈ @Finset.univ (GStep.Cl (r.step j)) ((r.chain rho rho' jet DG).clFin hI j),
        ((Nat.card (GStep.Stab (r.step j) c) : ℕ) : X.K)⁻¹ •
          kAt W Ch sel mu cst L A u j c.1 b' (GStep.rep _ c) p' (colAt W Ch A r rho rho' jet DG hI φ j c.1 (GStep.rep _ c)) := rfl

variable {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hL : L.Ok Ch sel mu cst G m2)
  (φ : MfV W Ch u)

theorem colAt_low {j : ℕ} (hj : j ≤ m2) (al : L.β j) (p : PtAt R sel mu cst u j) :
    colAt W Ch A r rho rho' jet DG hI φ j (Idx.of al (by have := hL.hm; omega)) p =
      ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF j (startC hL u φ) al).1 p.1.1 := by
  have hm := hL.hm
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j < m2 := hj
    rw [colAt_succ]
    refine (sum_low (M := VV X.K (W.lamTrue u (j + 1))) W r (by omega) (hF j)
      (fun c => kAt W Ch sel mu cst L A u j c.1 _ (GStep.rep _ c) p (colAt W Ch A r rho rho' jet DG hI φ j c.1 (GStep.rep _ c)))
      (fun a d => ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j a al).k d p.1.1
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF j (startC hL u φ) a).1 d)) (fun a q => ?_)
      fun a g d => ClsKer.term_smul ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j a al)
        ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF j (startC hL u φ) a) g d p.1.1).trans ?_
    · rw [← ih hj'.le]
      refine LinearMap.congr_fun ((kAt_mat W Ch A u hL (by omega) a al _ p).trans ?_) _
      have e : (chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j a al = ⟨_, hK.1 j hj' a al⟩ := dif_pos hj'
      rw [e]
    · show _ = ((∑ a, (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j a al).opOf (hF j a) _) ∘ₗ (LinearMap.proj a))
        ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF j (startC hL u φ))).1 p.1.1
      rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      rfl

def midForm : (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)).EqFun :=
  ∑ al, (cplKer1 ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al)).op (hF m2 al)
    ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF m2 (startC hL u φ) al)

theorem colAt_mid (b' : Idx sel mu L (m2 + 1)) (p : PtAt R sel mu cst u (m2 + 1)) (h) :
    colAt W Ch A r rho rho' jet DG hI φ (m2 + 1) b' p = (midForm W Ch A hK hF hL φ).1 ⟨p.1, h⟩ := by
  have hm := hL.hm
  rw [colAt_succ]
  refine (sum_low (M := VV X.K (W.lamTrue u (m2 + 1))) W r (by omega) (hF m2)
    (fun c => kAt W Ch sel mu cst L A u m2 c.1 b' (GStep.rep _ c) p (colAt W Ch A r rho rho' jet DG hI φ m2 c.1 (GStep.rep _ c)))
    (fun a d => (cplKer1 ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp a)).k d ⟨p.1, h⟩
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF m2 (startC hL u φ) a).1 d)) (fun a q => ?_)
      fun a g d => ClsKer.term_smul (cplKer1 ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp a))
        ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF m2 (startC hL u φ) a) g d ⟨p.1, h⟩).trans ?_
  · rw [← colAt_low W Ch A r rho rho' jet DG hI hK hF hL φ le_rfl]
    exact LinearMap.congr_fun (kernelAtPoint_penultimateStep_firstCoupledKernel W Ch A u hL a b' _ p) _
  · refine Eq.trans ?_ (eqFun_sum (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)) _ _).symm
    rfl

theorem colAt_last {j : ℕ} (e : j = m2 + 1 + 1) (h : j = R.m) (b' : Idx sel mu L j) (p' : PtAt R sel mu cst u j) :
    colAt W Ch A r rho rho' jet DG hI φ j b' p' =
      ∑ c ∈ @Finset.univ (GStep.Cl (r.step (m2 + 1))) ((r.chain rho rho' jet DG).clFin hI (m2 + 1)),
        ((Nat.card (GStep.Stab (r.step (m2 + 1)) c) : ℕ) : X.K)⁻¹ •
          KerT.ker W Ch sel mu cst A u (m2 + 1) j (GStep.rep _ c).1.1.deco.1.N (frsF sel mu (GStep.rep _ c).1.1)
            p'.1.1.deco.1.N (frsF sel mu p'.1.1) (xiOver Ch sel mu cst m2 h (GStep.rep _ c).1.1 (GStep.rep _ c).1.2 p'.1.1)
            (colAt W Ch A r rho rho' jet DG hI φ (m2 + 1) c.1 (GStep.rep _ c)) := by
  subst e
  rw [colAt_succ]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  rw [← xiAt_last Ch sel mu cst L (b := c.1) (b' := b') h]
  rfl

theorem colAt_top (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (H : TilOk Pr sel mu u) (b' : Idx sel mu L R.m)
    (d : XPt Pr R sel mu) :
    colAt W Ch A r rho rho' jet DG hI φ R.m b' (topPt sel mu cst u (tilF sel mu u d)) =
      (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 (toRow sel mu d) := by
  have hm := hL.hm
  have hC := cplGSD_ok (ybCpl W sel mu cst L u m2 b hY) (hF (m2 + 1) b)
  let k2 : ClsKer (cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY)) (evGSD W Ch sel mu P u) :=
    ⟨fun q d => cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) q.1.1 q.1.2 d, fun g g₁ q d => hK.2.2 g g₁ q.1.1 q.1.2 d⟩
  rw [colAt_last W Ch A r rho rho' jet DG hI φ hm rfl]
  refine (sum_mid (M := VV X.K (W.lamTrue u R.m)) W Ch r hL b hY hC _ (fun q => k2.k q (toRow sel mu d) ((midForm W Ch A hK hF hL φ).1 q)) (fun c h => ?_)
    fun g q => ClsKer.term_smul _ _ g q _).trans ?_
  · rw [colAt_mid W Ch A r rho rho' jet DG hI hK hF hL φ _ _ h]
    exact LinearMap.congr_fun ((ker_top W Ch A u hL _ _).trans
      (k2top_tilF hX hPr hsel hm hL.cst_ok H (tameFr_chTh W Ch sel mu cst A u m2) _ _ d)) _
  · show (k2.op hC (midForm W Ch A hK hF hL φ)).1 (toRow sel mu d) =
      ((∑ a, ((((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp a).comp (hF (m2 + 1) b) _).opOf (hF m2 a) _) ∘ₗ (LinearMap.proj a))
        ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF m2 (startC hL u φ))).1 (toRow sel mu d)
    rw [midForm, map_sum, LinearMap.sum_apply, Submodule.coe_sum, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (comp_appOf ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp a) (hF m2 a) (hF (m2 + 1) b)
      ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk.colTo hF m2 (startC hL u φ) a).1 (toRow sel mu d)).symm

omit hF hL in

theorem pair_smul (hW : W.Ok) (ψ : (evGSD W Ch sel mu P u).EqFun) (z : (mtildeGSD W Ch sel mu P).EqFun)
    (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D) :
    pairBK W.sgTrue (brC W u (ψ.1 (g • d))) (z.1 (g • d)) = pairBK W.sgTrue (brC W u (ψ.1 d)) (z.1 d) := by
  have h1 : brC W u (ψ.1 (g • d)) = ((((rowTy Ch sel mu P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) •
      rhoVr X.emb W.sgTrue (ufGL X.E _ g.1) (brC W u (ψ.1 d)) :=
    (congrArg (brC W u) (ψ.2 g d)).trans (((brC W u).map_smul _ _).trans (congrArg _ (TilClass.brC_rho W hW g.1 _)))
  have h2 : z.1 (g • d) = (((rowTy Ch sel mu P).inv.chr g.2 : X.Kˣ) : X.K) • rhoV X.emb W.sgTrue (ufGL X.E _ g.1) (z.1 d) := z.2 g d
  rw [h1, h2, map_smul, map_smul, LinearMap.smul_apply, smul_smul, Units.mul_inv, one_smul]
  exact pairingBInvariant_holds X.E X.K X.Tau _ X.emb W.sgTrue (ufGL _ _ g.1) _ _

theorem ptilCol_eq (hX : X.Ok) (hPr : Pr.Ok) (hW : W.Ok) (hsel : IsSel X sel) (H : TilOk Pr sel mu u) (σ : X.K →+* ℂ)
    (h : ∀ i, i < R.m → ReadsAt X.emb σ hI (kPt W Ch A r rho rho' jet DG) i)
    (h' : ∀ i, i < R.m → EqTarget X.emb (kPt W Ch A r rho rho' jet DG) i) (b0 : ((r.chain rho rho' jet DG).S R.m).β)
    (ext : ∀ b, (stepX Ch sel mu P).G b →* ((r.chain rho rho' jet DG).S R.m).G b0)
    (Hr : ∀ b, Subgroup ((stepX Ch sel mu P).G b))
    (hQ : (PeriodOnStep.perOn (I := r.chain rho rho' jet DG) W Ch sel mu P b0
      (fun _ p => topPt sel mu cst u (tilF sel mu u p.1.1)) ext (star ((Pr.piT u : 𝓞 X.E) : X.E)) Hr).Ok)
    (hM : (mtildeGSD W Ch sel mu P).Ok) (z : (mtildeGSD W Ch sel mu P).EqFun) :
    ((PeriodOnStep.perOn (I := r.chain rho rho' jet DG) W Ch sel mu P b0
      (fun _ p => topPt sel mu cst u (tilF sel mu u p.1.1)) ext (star ((Pr.piT u : 𝓞 X.E) : X.E)) Hr).per X.emb σ hI hQ (W.hc u)).PtilCol
        (fun c => ev X.emb σ (W.hc u) 0 (φ.1 (GStep.rep (r.step 0) c).1.1.deco))
        (PeriodOnStep.rowEmb (I := r.chain rho rho' jet DG) W Ch sel mu P b0 _ ext _ Hr H.2.2 σ z) =
      σ (PtilFF W Ch sel mu P hM u (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 z.1) := by
  refine (ptilCol_ev _ hQ h h' (fun _ p => φ.1 p.1.1.deco) _
    (fun c => z.1 (toRow sel mu (GStep.rep (stepX Ch sel mu P) c).1.1)) fun _ => rfl).trans (congrArg σ ?_)
  refine Eq.trans ?_ ((sum_row W Ch P H.2.2 hM (i := PerIn.clFin _ hQ)
    (fun d => pairBK W.sgTrue (brC W u ((colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 d)) (z.1 d))
    (pair_smul W Ch hW _ z)).trans ?_)
  · refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
    rw [← colAt_top W Ch A r rho rho' jet DG hI hK hF hL φ hX hPr hsel H b0]
    rfl
  · refine Eq.trans ?_ (csOf_apply₂ (mtildeGSD W Ch sel mu P) hM _ _ _ _).symm
    rfl

end Col

end GlobalTheory.Mem.Col2.KerRat
