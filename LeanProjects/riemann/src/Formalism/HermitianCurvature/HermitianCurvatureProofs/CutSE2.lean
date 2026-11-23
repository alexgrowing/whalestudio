import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfSquareDensity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wirt (b : Bool) (f : ℂ → ℂ) (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f t 1 + (if b then -Complex.I else Complex.I) * fderiv ℝ f t Complex.I)

def WD : List Bool → (ℂ → ℂ) → ℂ → ℂ
  | [], f => f
  | b :: bs, f => wirt b (WD bs f)

def WdExpand : Prop :=
  ∀ (n : ℕ) (f : ℂ → ℂ) (bs : List Bool), bs.length ≤ n → ContDiffOn ℝ n f {t | t ≠ 0} →
    ∃ (K : ℕ) (a : Fin K → ℂ) (v : Fin K → Fin bs.length → ℂ),
      (bs = [] → ∑ i, a i = 1) ∧
      ∀ t, t ≠ 0 → WD bs f t = ∑ i, a i * iteratedFDeriv ℝ bs.length f t (v i)

def LetterDensityExpansion : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      ∃ (K : ℕ) (a : Fin K → ℂ) (bs : Fin K → List Bool) (v : Fin K → Ix S → RadSp P.k P.r z z' π π'),
        (∀ i, (bs i).length ≤ w.length) ∧ (∀ i, InK (herKc S P z z' π π' L st l0 D l.castSucc) (v i)) ∧
        (∀ t, t ≠ 0 → ph L st μ l w x y c t =
          ∑ i, a i * WD (bs i) (Dens μ l (act (RRi L st l.castSucc w) x) (v i) c) t) ∧
        ∑ i, a i * (if bs i = [] then form μ l.castSucc (act (RRi L st l.castSucc w) x) (v i) c else 0) =
          RRform L st μ l.castSucc w x y c

def DecayHyp (Q : ℕ → (ℂ → ℂ) → Prop) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x v : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) v →
      ∀ c ∈ OmX P.r, ∀ n : ℕ, Q n (Dens μ l (act (RRi L st l.castSucc w) x) v c)

def DecayPair1 : Prop :=
  DecayHyp fun _ Dd => Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • Dd t)

def DecayPair2 : Prop :=
  DecayHyp fun _ Dd => ∀ t, t ≠ 0 → ContinuousAt Dd t

def DecayPair3 : Prop :=
  DecayHyp fun n Dd => ∃ C : ℝ, ∀ s, ‖∫ t, fsv s t * Dd t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def DecayPair4 : Prop :=
  DecayHyp fun n Dd => ∃ C : ℝ,
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • Dd t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

theorem decayRest_mono {n : ℕ} {C C' : ℝ} {Dd : ℂ → ℂ} (h : C ≤ C') (hD : DecayRest n C Dd) :
    DecayRest n C' Dd := by
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have hp : ∀ s : ℂ, 0 ≤ (1 + ‖s‖) ^ (-((n : ℝ) + 3)) := fun s => Real.rpow_nonneg (by positivity) _
  exact ⟨h1, h2, fun s => (h3 s).trans (mul_le_mul_of_nonneg_right h (hp s)),
    fun s => (h4 s).trans (mul_le_mul_of_nonneg_right h (hp s))⟩

theorem expansion_L2_of_decay_pairs (hW : WdExpand) (hE : LetterDensityExpansion) (h1 : DecayPair1) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : LevelDensitySquareIntegrable := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  obtain ⟨K, a, bs, v, hlen, hv, hexp, hsum⟩ :=
    hE Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  set u := act (RRi L st l.castSucc w) x with hu
  have hC3 := fun i => h3 Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x (v i) hx (hv i) c hc
    w.length
  have hC4 := fun i => h4 Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x (v i) hx (hv i) c hc
    w.length
  choose C3 hC3 using hC3
  choose C4 hC4 using hC4
  set C : ℝ := ∑ i, (|C3 i| + |C4 i|) with hCdef
  have hle : ∀ i, |C3 i| + |C4 i| ≤ C := fun i =>
    Finset.single_le_sum (f := fun i => |C3 i| + |C4 i|) (fun j _ => by positivity) (Finset.mem_univ i)
  have hrest : ∀ i, DecayRest w.length C (Dens μ l u (v i) c) := by
    intro i
    refine decayRest_mono (C := max (C3 i) (C4 i)) ?_ ⟨?_, ?_, fun s => (hC3 i s).trans ?_, fun s => (hC4 i s).trans ?_⟩
    · exact (max_le ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
        ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))).trans (hle i)
    · exact h1 Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x (v i) hx (hv i) c hc w.length
    · exact h2 Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x (v i) hx (hv i) c hc w.length
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
  have hr : 0 < P.r := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  have hgd := compact_kernel_le_good_domain (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' hr
  have hl2s := compact_kernel_le_L2 (S := S) P z z' π π' μ hD.2.1 L st l0 D hD.1 hz hz' hπ hπ'
  have hx0 : InK (herKc S P z z' π π' L st l0 D 0) x := by rw [← hl0]; exact hx
  have hu2 : ∀ b, u b ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 := by
    intro b
    simp only [hu, act]
    rw [hl0]
    exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1).sum_mem fun b' _ => (hgd (hx0 b')).2 w hw b b'
  have hv2 : ∀ i b, v i b ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 := by
    intro i b
    have := hv i b
    rw [hl0] at this
    exact hl2s this
  have IU : ∀ b, LevelSquareIntegrable μ l.castSucc (u b) c := by
    intro b; rw [hl0]; exact (hu2 b).2 c
  have IV : ∀ i b, LevelSquareIntegrable μ l.castSucc (v i b) c := by
    intro i b; rw [hl0]; exact (hv2 i b).2 c
  have hint : ∀ i, Integrable (Dens μ l u (v i) c) := fun i =>
    (dens_int μ hD.2.1 l u (v i) (fun b => (hu2 b).1) (fun b => (hv2 i b).1) c IU (IV i)).1
  have hcd : ∀ i, ContDiffOn ℝ w.length (Dens μ l u (v i) c) {t | t ≠ 0} := by
    intro i
    obtain ⟨r1, r2, r3, r4⟩ := hrest i
    obtain ⟨D', hD'c, hD'e, -⟩ := Fou.smooth_extension_of_fourier_decay _ w.length C (hint i) r1 r2 r3 r4
    exact hD'c.contDiffOn.congr fun t ht => (hD'e t ht).symm
  have hWi := fun i => hW w.length (Dens μ l u (v i) c) (bs i) (hlen i) (hcd i)
  choose K' a' v' hsum1 hexp' using hWi
  let e := Fintype.equivFin (Σ i : Fin K, Fin (K' i))
  refine ⟨w.length, Fintype.card (Σ i : Fin K, Fin (K' i)), C, fun _ => u, fun m => v (e.symm m).1,
    fun m => (bs (e.symm m).1).length, fun m => v' (e.symm m).1 (e.symm m).2,
    fun m => a (e.symm m).1 * a' (e.symm m).1 (e.symm m).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro m b
    exact ⟨(hu2 b).1, IU b, (hv2 _ b).1, IV _ b⟩
  · intro m; exact hlen _
  · intro m; exact hrest _
  · intro t ht
    rw [hexp t ht]
    rw [e.symm.sum_comp (fun p : (Σ i : Fin K, Fin (K' i)) =>
      a p.1 * a' p.1 p.2 * iteratedFDeriv ℝ (bs p.1).length (Dens μ l u (v p.1) c) t (v' p.1 p.2)),
      Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp' i t ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [← hsum]
    rw [e.symm.sum_comp (fun p : (Σ i : Fin K, Fin (K' i)) =>
      a p.1 * a' p.1 p.2 * (if (bs p.1).length = 0 then form μ l.castSucc u (v p.1) c else 0)),
      Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hb : bs i = []
    · have hb' : (bs i).length = 0 := by simp [hb]
      simp only [hb', if_true]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum1 i hb, mul_one]
      simp [hb]
    · have hb' : (bs i).length ≠ 0 := by simpa using hb
      simp [hb', hb]

section Inv

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [Fintype S] [DecidableEq S]

def ivlet (σ : Site A) (l : Letter K S) : SlopeTestRemainingChoices S A :=
  ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then !![0, -star σ.ci; star σ.c, algebraMap K A (l.pt + 1) + star σ.p]
    else !![0, -σ.ci; σ.c, algebraMap K A (l.pt - 1) + σ.p]))

def ibT (σ : Site A) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: w => ivlet σ l * ibT σ w

end Inv

def IbTInv : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (w : List (Letter K S)),
    IsSite σ → (∀ l ∈ w, star l.pt = l.pt) → ibT σ w * star (bT σ w) = 1

def MirrorLetterDensityExpansion : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      ∃ (K : ℕ) (a : Fin K → ℂ) (bs : Fin K → List Bool) (v : Fin K → Ix S → RadSp P.k P.r z z' π π'),
        (∀ i, (bs i).length ≤ w.length) ∧ (∀ i, InK (herKc S P z z' π π' L st l0 D l.castSucc) (v i)) ∧
        (∀ t, t ≠ 0 → Dens μ l (act (ibT (site L l) w) (act (RRi L st l.castSucc w) x)) (act (bTl L l w) y) c t =
          ∑ i, a i * WD (bs i) (Dens μ l (act (RRi L st l.castSucc w) x) (v i) c) t) ∧
        ∑ i, a i * (if bs i = [] then form μ l.castSucc (act (RRi L st l.castSucc w) x) (v i) c else 0) =
          RRform L st μ l.castSucc w x y c

theorem step_density_expansion_of_mirror (hI : IbTInv) (hC : MirrorLetterDensityExpansion) : LetterDensityExpansion := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  obtain ⟨K, a, bs, v, h1, h2, h3, h4⟩ :=
    hC Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  refine ⟨K, a, bs, v, h1, h2, fun t ht => ?_, h4⟩
  rw [← h3 t ht]
  have hss := siteStep_actual P z z' π π' X μ L st l0 w hD hw l
  have hinv : ibT (site L l) w * star (bTl L l w) = 1 :=
    hI ℂ (Pr (RadSp P.k P.r z z' π π')) S (site L l) w (isSite_actual hD.2.2.1 l)
      (fun le hle => Complex.conj_eq_iff_im.mpr (hw.2.1 le hle).1)
  have key : RRi L st l.succ w * bTl L l w = ibT (site L l) w * RRi L st l.castSucc w := by
    rw [← hss]
    simp only [← mul_assoc, hinv, one_mul]
  simp only [P5.ph, RRform, Dens]
  rw [← act_mul, key, act_mul]

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def OpClos (X : ActualOps k r z z' π π') (l : Fin r) (B : Submodule ℂ (RadSp k r z z' π π')) :
    Submodule ℂ (RadSp k r z z' π π') :=
  Submodule.span ℂ {Φ | ∃ (js : List (Fin 6)) (Ψ : RadSp k r z z' π π'), Ψ ∈ B ∧ Φ = (js.map (X.op l)).prod Ψ}

variable [FiniteDimensional ℂ Wq]

def LocFacts₂ (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

end Cls

section ClsE

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (S : Type) [Fintype S] [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
  (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))

def base0 (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  herKc S P z z' π π' L st l0 D 0 ⊔ Submodule.span ℂ {Φ | ∃ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w ∧
    ∃ (a b : Ix S) (Ψ : RadSp P.k P.r z z' π π'), Ψ ∈ herKc S P z z' π π' L st l0 D 0 ∧ Φ = ((RRi L st 0 w) a b).1 Ψ}

def ClsE (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r) :
    Submodule ℂ (RadSp P.k P.r z z' π π') :=
  OpClos X l (base0 S P z z' π π' L st l0 D)

end ClsE

def ClassSquareIntegrable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ ClsE S P z z' π π' X L st l0 D l →
      Φ ∈ lcSub P.k P.r z z' π π' ∧ ∀ c, LevelSquareIntegrable μ l.castSucc Φ c

def DensSmoothCls : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (u v : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ ClsE S P z z' π π' X L st l0 D l) → (∀ b, v b ∈ ClsE S P z z' π π' X L st l0 D l) →
    ∀ c ∈ OmX P.r, (∀ n : ℕ, ContDiffOn ℝ n (Dens μ l u v c) {t | t ≠ 0}) ∧
      ∀ t, t ≠ 0 → ∀ b, LevelSquareIntegrable μ l.succ (u b) (Function.update c l t) ∧ LevelSquareIntegrable μ l.succ (v b) (Function.update c l t)

def LeibnizCls : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (u v : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ ClsE S P z z' π π' X L st l0 D l) → (∀ b, v b ∈ ClsE S P z z' π π' X L st l0 D l) →
    ∀ c ∈ OmX P.r, ∀ t, t ≠ 0 →
      wirt true (fun t => form μ l.succ u v (Function.update c l t)) t =
        form μ l.succ (fun b => X.op l 2 (X.op l 0 (u b))) v (Function.update c l t) +
          form μ l.succ u (fun b => X.op l 5 (X.op l 3 (v b))) (Function.update c l t) ∧
      wirt false (fun t => form μ l.succ u v (Function.update c l t)) t =
        form μ l.succ (fun b => X.op l 5 (X.op l 3 (u b))) v (Function.update c l t) +
          form μ l.succ u (fun b => X.op l 2 (X.op l 0 (v b))) (Function.update c l t)

def WaveOut : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (u v : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ ClsE S P z z' π π' X L st l0 D l) → (∀ b, v b ∈ ClsE S P z z' π π' X L st l0 D l) →
    ∀ c ∈ OmX P.r, ∀ (s : ℂ) (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), multiplicationOperator Wv (fun c' _ => fsv s (c' l)) →
      ∫ t, fsv s t * Dens μ l u v c t = form μ l.castSucc (fun b => Wv (u b)) v c

def ClsDecay : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (Φ Ψ : RadSp P.k P.r z z' π π'), Φ ∈ ClsE S P z z' π π' X L st l0 D l → Ψ ∈ ClsE S P z z' π π' X L st l0 D l → ∀ c ∈ OmX P.r, ∀ n : ℕ,
    ∃ C : ℝ, ∀ (s : ℂ) (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), multiplicationOperator Wv (fun c' _ => fsv s (c' l)) →
      ‖LocFacts₂ μ l.castSucc (Wv Φ) Ψ c‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def OneLetterDens : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (le : Letter ℂ S), le.pt.im = 0 → ∃ (e : ℂ) (bb : Bool) (i j : Fin 2),
    ∀ (u v : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ ClsE S P z z' π π' X L st l0 D l) → (∀ b, v b ∈ ClsE S P z z' π π' X L st l0 D l) →
    ∀ c ∈ OmX P.r, ∀ t, t ≠ 0 →
      Dens μ l (act (ivlet (site L l) le) u) (act (vlet (site L l) le) v) c t =
        Dens μ l u v c t + e * wirt bb (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one i j : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) v) c) t

def BTCls : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (u : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ ClsE S P z z' π π' X L st l0 D l) →
      (∀ (le : Letter ℂ S) b, act (vlet (site L l) le) u b ∈ ClsE S P z z' π π' X L st l0 D l) ∧
      (∀ (le : Letter ℂ S) b, act (ivlet (site L l) le) u b ∈ ClsE S P z z' π π' X L st l0 D l) ∧
      ∀ (a : S) (i j : Fin 2) b, act (eU a i j : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) u b ∈ ClsE S P z z' π π' X L st l0 D l

def ExpansionByLetterInduction : Prop := DensSmoothCls → OneLetterDens → BTCls → MirrorLetterDensityExpansion

def SiteOperatorsWaveJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (j : Fin 6) (Φ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → X.op l j Φ ∈ waveJ P z z' π π' D l

def RadDecay : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (ε : ℝ) (G H : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε → JC.NiceCoef D ε G → JC.NiceCoef D ε H →
    ∀ (Φ Ψ : RadSp P.k P.r z z' π π'),
      (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
      (∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D H) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ n : ℕ,
    ∃ C : ℝ, ∀ (s : ℂ) (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), multiplicationOperator Wv (fun c' _ => fsv s (c' l)) →
      ‖LocFacts₂ μ l.castSucc (Wv Φ) Ψ c‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def WaveOutJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (u v : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ waveJ P z z' π π' D l) → (∀ b, v b ∈ waveJ P z z' π π' D l) →
    ∀ c ∈ OmX P.r, ∀ (s : ℂ) (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), multiplicationOperator Wv (fun c' _ => fsv s (c' l)) →
      ∫ t, fsv s t * Dens μ l u v c t = form μ l.castSucc (fun b => Wv (u b)) v c

def ClsDecayJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (Φ Ψ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → Ψ ∈ waveJ P z z' π π' D l → ∀ c ∈ OmX P.r, ∀ n : ℕ,
    ∃ C : ℝ, ∀ (s : ℂ) (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), multiplicationOperator Wv (fun c' _ => fsv s (c' l)) →
      ‖LocFacts₂ μ l.castSucc (Wv Φ) Ψ c‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def SiteMulWaveJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → X.op l 1 Φ ∈ waveJ P z z' π π' D l ∧ X.op l 4 Φ ∈ waveJ P z z' π π' D l

end Formalism.FourierDecayAlt.P.CutSE
