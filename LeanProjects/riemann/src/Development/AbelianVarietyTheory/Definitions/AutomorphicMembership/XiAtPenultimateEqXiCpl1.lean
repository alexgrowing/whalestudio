import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

section Cast

def castSp (E : Type) [Field E] {a b : ℕ} (h : a = b) : Sp E a →ₗ[E] Sp E b := LinearMap.funLeft E E (Fin.cast h.symm)

theorem castSp_apply {E : Type} [Field E] {a b : ℕ} (h : a = b) (x : Sp E a) (i : Fin b) :
    castSp E h x i = x (Fin.cast h.symm i) := rfl

theorem castSp_comp {E : Type} [Field E] {a b : ℕ} (x : HomE E a b) : castSp E rfl ∘ₗ x = x := rfl

def castV {ι : Type} {a b b' : ℕ} (h : b = b') (z : VCx ι a b) : VCx ι a b' := fun τ r c => z τ (Fin.cast h.symm r) c

end Cast

theorem thC_zero {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (θ : VCx ι a b → ℂ) : thC emb δ d sc AA SS N N' c (fun _ => 0) θ = 0 := by
  have h : ∀ v : VCx ι a b, onV emb δ (fun _ => 0) v = 0 := fun v => by
    unfold onV
    split_ifs <;> rfl
  funext z
  simp [thC, xiV, xiL, xiS, hatS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, h]

theorem PhiQ_comp_of_red {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' n : ℕ) (hc : c' = 0) (κ : GLint E n P)
    (hκ : TopStep.redGL n P κ = 1) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' 0 n (κ.1.toLinearMap ∘ₗ x) = LocE.PhiQ (qOf P) ξ k₀ r c' n' 0 n x := by
  have supp : ∀ y : HomE E (n' + c') (n + 0), LocE.PhiQ (qOf P) ξ k₀ r c' n' 0 n y ≠ 0 →
      ∀ s : Fin n', y (Pi.single ⟨s.1, by omega⟩ 1) ∈ stdAt E n P := fun y hy s => by
    refine TopStep.mem_stdAt.2 fun l => ?_
    unfold LocE.PhiQ at hy
    split_ifs at hy with h
    · have := h.1 l.1 s.1 l.2 (by omega)
      rwa [TopStep.entB_zero _ _ _ _ _ hc, dif_pos ⟨l.2, s.2⟩] at this
    · exact absurd rfl hy
  by_cases hy : ∀ s : Fin n', x (Pi.single ⟨s.1, by omega⟩ 1) ∈ stdAt E n P
  · have h : ∀ p p', TopStep.CongQ P (LocE.entB (qOf P) k₀ c' n' 0 n 0 0 (κ.1.toLinearMap ∘ₗ x : HomE E (n' + c') (n + 0)) p p')
        (LocE.entB (qOf P) k₀ c' n' 0 n 0 0 x p p') := fun p p' => by
      rw [TopStep.entB_zero _ _ _ _ _ hc, TopStep.entB_zero _ _ _ _ _ hc]
      split_ifs with h
      · have h1 := TopStep.mem_stdAt.1 (TopStep.glint_mem κ (hy ⟨p', h.2⟩)) ⟨p, h.1⟩
        have h2 := TopStep.mem_stdAt.1 (hy ⟨p', h.2⟩) ⟨p, h.1⟩
        refine ⟨h1, h2, TopStep.intAt_div_of_redP hq (TopStep.intAt_sub h1 h2) ?_⟩
        have h3 := congrFun (TopStep.redV_redGL κ (hy ⟨p', h.2⟩)) ⟨p, h.1⟩
        rw [hκ, Units.val_one, Matrix.one_mulVec] at h3
        exact (TopStep.reduction_sub h1 h2).trans (sub_eq_zero.2 h3)
      · exact TopStep.congQ_zero
    unfold LocE.PhiQ
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
    · simp only [(h _ _).1, (h _ _).2.1, (h _ _).div_iff]
    · exact TopStep.unitV_det_congr _ fun s s' => h s.1 s'.1
  · have h1 : LocE.PhiQ (qOf P) ξ k₀ r c' n' 0 n x = 0 := by
      by_contra h
      exact hy (supp _ h)
    have h2 : LocE.PhiQ (qOf P) ξ k₀ r c' n' 0 n (κ.1.toLinearMap ∘ₗ x) = 0 := by
      by_contra h
      exact hy fun s => (κ.2 _).1 (supp _ h s)
    rw [h1, h2]

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

variable {sel mu L} in

def Idx.get {j : ℕ} (b : Idx sel mu L j) (h : j < R.m) : L.β j := b.1.get (b.2.2 h)

variable {sel mu L} in

def Idx.of {j : ℕ} (al : L.β j) (h : j < R.m) : Idx sel mu L j := ⟨some al, iff_of_true rfl h⟩

def Idx.top {j : ℕ} (h : R.m ≤ j) : Idx sel mu L j := ⟨none, iff_of_false (by simp) (by omega)⟩

variable {sel mu L} in

theorem Idx.some_get {j : ℕ} (b : Idx sel mu L j) (h : j < R.m) : some (b.get h) = b.1 := Option.some_get _

variable {sel mu L} in

theorem Idx.get_eq {j : ℕ} {b : Idx sel mu L j} {al : L.β j} (e : b.1 = some al) (h : j < R.m) : b.get h = al :=
  Option.some_injective _ ((b.some_get h).trans e)

variable {sel mu L} in

theorem Idx.of_get {j : ℕ} (b : Idx sel mu L j) (h h' : j < R.m) : Idx.of (b.get h) h' = b := Subtype.ext (b.some_get h)

variable {sel mu L} in

theorem Idx.eq_top {j : ℕ} (b : Idx sel mu L j) (h : R.m ≤ j) : b = Idx.top sel mu L h := by
  obtain ⟨_ | b, hb⟩ := b
  · rfl
  · exact absurd (hb.1 rfl) (by omega)

variable (R) in

abbrev PtAt (u : Pr.Word) (j : ℕ) : Type :=
  PtY (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) (ysAt R sel mu cst j)

theorem ysAt_ys_of_eq {j : ℕ} (h : j + 1 = R.m) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) :
    (ysAt R sel mu cst j).ys N = ybSet sel mu cst N := by
  rw [ysAt, if_pos h]

theorem ysAt_ys_of_ne {j : ℕ} (h : j + 1 ≠ R.m) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) :
    (ysAt R sel mu cst j).ys N = {∅} := by
  rw [ysAt, if_neg h]
  rfl

variable {sel mu cst} in

theorem PtAt.mem_ybSet {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    p.1.2 ∈ ybSet sel mu cst p.1.1.deco.1.N := ysAt_ys_of_eq sel mu cst h _ ▸ p.2

variable {sel mu cst} in

theorem PtAt.repY_mem {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j) (h : j + 1 = R.m) : repY p.1.2 ∈ p.1.2 := by
  obtain ⟨y, -, hy⟩ := p.mem_ybSet h
  exact Classical.epsilon_spec (p := fun y => y ∈ p.1.2) ⟨y, by rw [hy]; simp⟩

theorem exists_ptAt {u : Pr.Word} {j : ℕ} (q : ChPt (R := R) sel mu u j) : ∃ p : PtAt R sel mu cst u j, p.1.1 = q := by
  by_cases h : j + 1 = R.m
  · obtain ⟨Y, hY⟩ : (ybSet sel mu cst q.deco.1.N).Nonempty := ⟨_, 0, zero_mem _, rfl⟩
    exact ⟨⟨(q, Y), by rw [ysAt_ys_of_eq sel mu cst h]; exact hY⟩, rfl⟩
  · exact ⟨⟨(q, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl⟩

def tilAt (u : Pr.Word) {j : ℕ} (h : j = R.m) (d : XPt Pr R sel mu) : ChPt (R := R) sel mu u j :=
  tilFr (N_succ_of_eq h) (Pr.piT u) d

theorem eq_tilAt_iff {u : Pr.Word} {j : ℕ} (h : j = R.m) (p' : ChPt (R := R) sel mu u j) (d : XPt Pr R sel mu) :
    p' = tilAt sel mu u h d ↔ HEq p' (tilF sel mu u d) := by
  subst h
  exact heq_iff_eq.symm

def xiOver {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1))))
    (p' : ChPt (R := R) sel mu u j) (x : HomE X.E (R.N (n + 1)) (R.N j)) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu, TopStep.locTop Ch sel mu cst n P
      (castSp X.E (congrArg R.N h) ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

def xiLast {u : Pr.Word} : ∀ (i : ℕ), i + 1 = R.m → ChPt (R := R) sel mu u i → Set (Sp X.E (R.N i)) →
    ChPt (R := R) sel mu u (i + 1) → HomE X.E (R.N i) (R.N (i + 1)) → X.K
  | 0, h => absurd R.two_le_m (by omega)
  | n + 1, h => xiOver Ch sel mu cst n h

def xiAt (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) : HomE X.E (R.N i) (R.N (i + 1)) → X.K :=
  if h : i + 2 < R.m then XiEntry Ch sel mu cst L i (b.get (by omega)) (b'.get (by omega)) p.1.1 p'.1.1
  else if h : i + 2 = R.m then XiCpl1 Ch sel mu cst L i (b.get (by omega)) p.1.1 p'.1.1 p'.1.2
  else if h : i + 1 = R.m then xiLast Ch sel mu cst i h p.1.1 p.1.2 p'.1.1
  else 0

theorem XiTop_tilF {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hc : cst.Ok) (H : TopStep.TilOk Pr sel mu u) {n : ℕ}
    (hm : R.m = n + 2) (p : ChPt (R := R) sel mu u (n + 1)) {Y : Set (Sp X.E (R.N (n + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N)
    (d : XPt Pr R sel mu) :
    TopStep.XiTop Ch sel mu cst n p Y (tilF sel mu u d) = XiCpl2 Ch sel mu cst n p Y (toRow sel mu d) := by
  classical
  have hQ : ∀ P : QE sel (mu : Chr X.F X.E X.K), Pr.piT u ∉ P.1.asIdeal := fun P => H.2.1 (TopStep.inQ Pr sel mu P)
  have e : (tilF sel mu u d).deco = (TopStep.tilTop H (toRow sel mu d)).deco := by
    rw [← forgetFr_res (tilF sel mu u d), forgetFr_tilF sel mu hPr u hQ]
    rfl
  rw [← TopStep.XiTop_tilTop hX hPr hm hc H p hY]
  funext x
  unfold TopStep.XiTop
  rw [e]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  by_cases hP : P.1 ∈ Pr.vGs
  · have e1 : frsF sel mu (tilF sel mu u d) P = frsF sel mu (TopStep.tilTop H (toRow sel mu d)) P := by
      unfold frsF
      rw [dif_pos hP, dif_pos hP, e]
    rw [e1]
  · obtain ⟨κ, hκ, e2⟩ := TopStep.exists_of_isLiftFr (TopStep.liftFr_spec (toRow sel mu d).2 P) (isLiftFr_toRow sel mu d P hP)
    have e1 : frsF sel mu (tilF sel mu u d) P = TopStep.sumE (N_m_succ R) (d.fr (rightOf P hP)) (TopStep.piU H P) := by
      unfold frsF
      rw [dif_neg hP, tilF_fr sel mu hPr u hQ]
      congr 1
      exact Units.ext (unitOf_val (H.2.1 P))
    rw [e1, TopStep.frsF_tilTop_Q H _ P hP, TopStep.tilFr]
    unfold TopStep.locTop
    refine congrArg₂ (· * ·) ?_ ?_
    · unfold PhiTop
      rw [if_neg hP, ← PhiQ_comp_of_red (ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 _ _ _ _ _ _
        (show cOf R (n + 1) = 0 by unfold cOf; omega) κ hκ (prXp X.E R ∘ₗ inFr _ (TopStep.sumE _ ((toRow sel mu d).1.liftFr P) _) x ∘ₗ _)]
      congr 1
      refine LinearMap.ext fun v => (TopStep.prH_sumE_symm (N_m_succ R) _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg κ.1 (TopStep.prH_sumE_symm (N_m_succ R) _ _ _)).symm
      rw [e2]
      exact (κ.1.apply_symm_apply _).symm
    · congr 1
      refine LinearMap.ext fun v => (TopStep.atNL_last _).trans ((TopStep.sumE_symm_last (N_m_succ R) _ _ _).trans ?_)
      exact ((TopStep.atNL_last _).trans (TopStep.sumE_symm_last (N_m_succ R) _ _ _)).symm

section Over

variable {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))

theorem xiOver_rfl (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u R.m) :
    xiOver Ch sel mu cst n rfl p Y p' = TopStep.XiTop Ch sel mu cst n p Y p' := rfl

end Over

section Unfold

variable {u : Pr.Word} {i : ℕ} {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)}

theorem xiAt_entry (h : i + 2 < R.m) {al : L.β i} {be : L.β (i + 1)} (e : b.1 = some al) (e' : b'.1 = some be)
    (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    xiAt Ch sel mu cst L u i b b' p p' = XiEntry Ch sel mu cst L i al be p.1.1 p'.1.1 := by
  rw [xiAt, dif_pos h, Idx.get_eq e, Idx.get_eq e']

theorem xiAt_penultimate_eq_xiCpl1 (h : i + 2 = R.m) {al : L.β i} (e : b.1 = some al) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) :
    xiAt Ch sel mu cst L u i b b' p p' = XiCpl1 Ch sel mu cst L i al p.1.1 p'.1.1 p'.1.2 := by
  rw [xiAt, dif_neg (by omega), dif_pos h, Idx.get_eq e]

theorem xiAt_of_le (h : R.m ≤ i) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    xiAt Ch sel mu cst L u i b b' p p' = 0 := by
  rw [xiAt, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

end Unfold

section UnfoldLast

variable {u : Pr.Word} {n : ℕ} {b : Idx sel mu L (n + 1)} {b' : Idx sel mu L (n + 1 + 1)} (h : n + 1 + 1 = R.m)
  (p : PtAt R sel mu cst u (n + 1)) (p' : PtAt R sel mu cst u (n + 1 + 1))

theorem xiAt_last : xiAt Ch sel mu cst L u (n + 1) b b' p p' = xiOver Ch sel mu cst n h p.1.1 p.1.2 p'.1.1 := by
  rw [xiAt, dif_neg (by omega), dif_neg (by omega), dif_pos h]
  rfl

end UnfoldLast

theorem phiT_of_xiAt_ne_zero {u : Pr.Word} {i : ℕ}
    {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)} {p : PtAt R sel mu cst u i} {p' : PtAt R sel mu cst u (i + 1)}
    {x : HomE X.E (R.N i) (R.N (i + 1))} (hx : xiAt Ch sel mu cst L u i b b' p p' x ≠ 0) (P : Pr.vT u) :
    ∀ y ∈ p.1.1.deco.1.at P.1, x y ∈ p'.1.1.deco.1.at P.1 ∧ p'.1.1.deco.1.f P (x y) = p.1.1.deco.1.f P y := by
  have key : phiT X.K p.1.1.deco.1 p'.1.1.deco.1 x ≠ 0 := by
    rcases lt_trichotomy (i + 2) R.m with h | h | h
    · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm] at hx
      exact left_ne_zero_of_mul hx
    · rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
      exact left_ne_zero_of_mul hx
    · by_cases h1 : i + 1 = R.m
      · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
        rw [xiAt_last Ch sel mu cst L h1] at hx
        exact left_ne_zero_of_mul hx
      · rw [xiAt_of_le Ch sel mu cst L (by omega)] at hx
        exact absurd rfl hx
  by_contra hn
  exact key (if_neg fun h => hn (h P))

variable (A : Amb X)

def thOf (u : Pr.Word) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) : VCx X.Tau a b → ℂ :=
  thC (X.embC A.σ₀) A.δ A.d A.sc A.AA (Sall sel mu u) N N' (levC sel mu cst u) (fun x => A.σ₀ (Ξ x)) (A.e a b N N')

theorem thOf_zero (u : Pr.Word) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    thOf sel mu cst A u N N' 0 = 0 := by
  simp only [thOf, Pi.zero_apply, map_zero]
  exact thC_zero ..

def thAt (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) : VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  thOf sel mu cst A u p.1.1.deco.1.N p'.1.1.deco.1.N (xiAt Ch sel mu cst L u i b b' p p')

section ThUnfold

variable {u : Pr.Word} {i : ℕ} {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)}

theorem thAt_of_le (h : R.m ≤ i) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    thAt Ch sel mu cst L A u i b b' p p' = 0 := by
  rw [thAt, xiAt_of_le Ch sel mu cst L h, thOf_zero]

end ThUnfold

section ThLast

variable {u : Pr.Word} {n : ℕ} {b : Idx sel mu L (n + 1)} {b' : Idx sel mu L (n + 1 + 1)} (h : n + 1 + 1 = R.m)
  (p : PtAt R sel mu cst u (n + 1)) (p' : PtAt R sel mu cst u (n + 1 + 1))

end ThLast

section Ker

variable {u : Pr.Word} {n : ℕ} (T : ChTh W sel mu u n)

theorem matK_eq_xiAt {i : ℕ} (h : i + 2 < R.m) (al : L.β i) (be : L.β (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) : matK W Ch sel mu cst L T i al be p.1.1 p'.1.1 =
      kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N (frsF sel mu p.1.1) p'.1.1.deco.1.N
        (frsF sel mu p'.1.1) (xiAt Ch sel mu cst L u i (Idx.of al (by omega)) (Idx.of be (by omega)) p p') := by
  rw [xiAt_entry Ch sel mu cst L h rfl rfl]
  rfl

theorem firstCoupledKernel_eq_columnChainDatum (h : n + 2 = R.m) (al : L.β n) (b' : Idx sel mu L (n + 1)) (p : PtAt R sel mu cst u n)
    (p' : PtAt R sel mu cst u (n + 1)) : cp1K W Ch sel mu cst L T al p.1.1 p'.1.1 p'.1.2 =
      kerOf (T.th n) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N (frsF sel mu p.1.1) p'.1.1.deco.1.N
        (frsF sel mu p'.1.1) (xiAt Ch sel mu cst L u n (Idx.of al (by omega)) b' p p') := by
  rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h rfl, cp1K, if_pos (p'.mem_ybSet h)]

theorem k2top_eq_xiOver (h : n + 1 + 1 = R.m) (p : PtAt R sel mu cst u (n + 1)) (q : ChPt (R := R) sel mu u R.m) :
    TopStep.topDegreeKTwo W Ch sel mu cst T p.1.1 p.1.2 q =
      kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N (frsF sel mu p.1.1) q.deco.1.N
        (frsF sel mu q) (xiOver Ch sel mu cst n rfl p.1.1 p.1.2 q) := if_pos (p.mem_ybSet h)

end Ker

example (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) : ChainIn X.E X.K X.Tau R :=
  chainAt sel mu cst L (topLev Ch sel mu cst P) u (fun _ _ _ => 1) (fun _ _ _ => 1) A.cD (thAt Ch sel mu cst L A u)

example (u : Pr.Word) : ∃ (n : ℕ) (h : n + 1 + 1 = R.m) (_ : PtAt R sel mu cst u (n + 1)) (p' : PtAt R sel mu cst u (n + 1 + 1))
    (d : XPt Pr R sel mu), p'.1.1 = tilAt sel mu u h d := by
  have h : R.m - 2 + 1 + 1 = R.m := by have := R.two_le_m; omega
  have : NeZero (R.N (R.m - 2 + 1)) := ⟨by have := R.m_add_three_le_k; unfold Ranks.N; omega⟩
  obtain ⟨p, -⟩ := exists_ptAt (R := R) sel mu cst (u := u) (j := R.m - 2 + 1) (DecoF.base _ _ _ _ _)
  obtain ⟨p', hp'⟩ := exists_ptAt sel mu cst (tilAt sel mu u h (DecoF.base _ _ _ _ _))
  exact ⟨_, h, p, p', _, hp'⟩

example {u : Pr.Word} (P : Pr.vT u) (i : ℕ)
    (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) :
    xiAt Ch sel mu cst L u i b b' p p' 0 = 0 := by
  by_contra hx
  have h := phiT_of_xiAt_ne_zero Ch sel mu cst L hx P
  obtain ⟨y, -, hy⟩ := p.1.1.deco.2.f_ne P
  have h0 := p'.1.1.deco.2.f_add P 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero, left_eq_add] at h0
  exact hy ((h y (by_contra fun hn => hy (p.1.1.deco.2.f_off P y hn))).2.symm.trans h0)

example [IsEmpty (rowSG Pr sel mu)] {u : Pr.Word} {i : ℕ} (h : i < R.m) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1))
    (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    xiAt Ch sel mu cst L u i b b' p p' x = phiT X.K p.1.1.deco.1 p'.1.1.deco.1 x := by
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm, XiEntry, Fintype.prod_empty, mul_one]
  · rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm, XiCpl1, Fintype.prod_empty, mul_one]
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
    rw [xiAt_last Ch sel mu cst L (by omega), xiOver, Fintype.prod_empty, mul_one]

end Chain

end GlobalTheory.Mem.Col2
