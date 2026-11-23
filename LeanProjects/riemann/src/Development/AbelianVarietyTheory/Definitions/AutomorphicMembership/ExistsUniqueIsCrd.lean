import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sameOn_iff {K V : Type} {n : ℕ} (j j' : (Fin n → K) → V) : SameOn j j' ↔ j = j' := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact h x x fun a a' e => by rw [Fin.ext e]
  · rintro rfl
    exact ⟨rfl, fun x x' h => congrArg j (funext fun a => h a a rfl)⟩

theorem exists_sameOn {K V : Type} {n n' : ℕ} (h : n = n') (j' : (Fin n' → K) → V) : ∃ j : (Fin n → K) → V, SameOn j j' := by
  subst h
  exact ⟨j', (sameOn_iff _ _).2 rfl⟩

example : ¬ SameOn (fun _ : Fin 1 → ℚ => (0 : ℚ)) (fun _ : Fin 2 → ℚ => (0 : ℚ)) := fun h => absurd h.1 (by decide)

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)

theorem range_lvl : LinearMap.range ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE
    (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVecLin =
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlPart (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr :=
  (image_idempotent_spec X.K _ _).2.trans (level_part_spec X.K _ _ _ _ _)

theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl

theorem exists_isFormOf (y) : ∃ x, IsFormOf W Ch sel mu hX P x (frm W Ch sel mu hX P y) := by
  let F := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).symm (frm W Ch sel mu hX P y)
  have hF : F.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
    rw [← mem_lvlPartX_iff W Ch sel mu P (mtildeKOk W Ch sel mu hX), ← range_lvl W Ch sel mu hX]
    refine ⟨y, ?_⟩
    symm
    show (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun
      (((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)) F) = _
    rw [LinearEquiv.apply_symm_apply, frm, LinearEquiv.apply_symm_apply]
    rfl
  exact ⟨_, F, hF, heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

theorem isFormOf_onto (x : MtildeV W Ch sel mu P) : ∃ y, IsFormOf W Ch sel mu hX P x (frm W Ch sel mu hX P y) := by
  obtain ⟨hK, -⟩ := (mem_MtildeV_iff W Ch sel mu P x.1).1 x.2
  have h := (mem_lvlPartX_iff W Ch sel mu P (mtildeKOk W Ch sel mu hX) ⟨x.1, hK⟩).2 x.2
  rw [← range_lvl W Ch sel mu hX] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ⟨x.1, hK⟩, x.2, heq_of_eq ?_, rfl⟩
  unfold frm
  rw [LinearEquiv.eq_symm_apply]
  exact hy.symm

end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)

theorem tAll_ixOf (U : Set I.ι) (s : R3.TupU I U) : (tAll I (R3.ixOf I U s)).1 = s.1 := R3.tup_ixOf I s

theorem rDim_eq (U : Set I.ι) (Xg tr) (s : R3.TupU I U) (P ψ) :
    rDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A P ψ (tAll I (R3.ixOf I U s)) = rDim X.toD7 (R3.famR X I hX U Xg tr).A P ψ s := by
  have key : ∀ (t : R3.TupU I Set.univ), t.1 = s.1 →
      rDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A P ψ t = rDim X.toD7 (R3.famR X I hX U Xg tr).A P ψ s := by
    obtain ⟨s, hs⟩ := s
    rintro ⟨t, ht⟩ (rfl : t = s)
    rfl
  exact key _ (tAll_ixOf X I U s)

theorem lDim_eq (U : Set I.ι) (Xg tr) (s : R3.TupU I U) (P ψ) (i) :
    lDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A P ψ i (tAll I (R3.ixOf I U s)) =
      lDim X.toD7 (R3.famR X I hX U Xg tr).A P ψ i s := by
  have key : ∀ (t : R3.TupU I Set.univ), t.1 = s.1 →
      lDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A P ψ i t = lDim X.toD7 (R3.famR X I hX U Xg tr).A P ψ i s := by
    obtain ⟨s, hs⟩ := s
    rintro ⟨t, ht⟩ (rfl : t = s)
    rfl
  exact key _ (tAll_ixOf X I U s)

theorem rowForm_eq (Xg tr) (a : I.ι) (y) :
    R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y =
      frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y := rfl

theorem existsUnique_isCrd (Xg tr) (a : I.ι) {M : Type} [AddCommGroup M] [Module ℂ M] (e : Df.MtCx I a ≃ₗ[ℂ] M) (y) :
    ∃! v, IsCrd I hX a e (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) v := by
  obtain ⟨x, hx⟩ := exists_isFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y
  refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
  rintro v ⟨x', hx', rfl⟩
  rw [isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx' hx]

theorem isCrd_determines (Xg tr) (a : I.ι) {M : Type} [AddCommGroup M] [Module ℂ M] (e e' : Df.MtCx I a ≃ₗ[ℂ] M) (j : _ → M)
    (h : ∀ y, IsCrd I hX a e (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) (j y))
    (h' : ∀ y, IsCrd I hX a e' (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) (j y))
    (F : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) : e (Df.toCx I hX a F) = e' (Df.toCx I hX a F) := by
  obtain ⟨y, hy⟩ := isFormOf_onto (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) F
  obtain ⟨u, hu, q⟩ := h y
  obtain ⟨u', hu', q'⟩ := h' y
  rw [← isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hu hy, ← q,
    isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hu hu', ← q']

end Cols

section Core

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem lawsM (t : RowsT K w Z Wt p0) : Formalism.L2.Pj.LawsM t.r.z.core.toCore := t.r.z.geo.fw.laws.toLawsM

theorem rank_inR (t : RowsT K w Z Wt p0) (j : ℕ) (hj : Formalism.L2.Pj.InR (w.st Z).toD7 j) :
    (t.r.z.core.Q.Dw j).p = (B.R.sigW j).1 ∧ (t.r.z.core.Q.Dw j).q = (B.R.sigW j).2 :=
  let h := (lawsM t).pins.2.2.2 j hj; ⟨h.1, h.2.1⟩

theorem rx_io {t : RowsT K w Z Wt p0} (x : RXs t) (μ) (h : ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ) : p0.s.iota μ = 0 := by
  have hm : 0 < (w.D Z).R.m := t.r.Y.hm
  have : ∀ n, 0 < n → p0.s.downTo μ n = 0 := by
    rintro (_ | n) hn
    · omega
    · rw [RowSide.downTo, (x.io μ n h).2, LinearMap.comp_zero]
  rw [RowSide.iota, this _ hm, LinearMap.zero_comp, LinearMap.comp_zero]

end Core

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links

theorem isWtOfPar_unique {N N' : ℕ} {S : SPar} (hS : ∀ x ∈ S, x.2 = true) {lam : DomWeight N} {lam' : DomWeight N'}
    (h : Bridge.IsWtOfPar lam S) (h' : Bridge.IsWtOfPar lam' S) (i : Fin N) (i' : Fin N') (e : (i : ℕ) = i') :
    lam.w i = lam'.w i' := by
  obtain ⟨hc, c, ha, hm, hw⟩ := h
  obtain ⟨hc', c', ha', hm', hw'⟩ := h'
  obtain rfl : N = N' := hc.symm.trans hc'
  obtain rfl : i = i' := Fin.ext e
  have key : ∀ (d : Fin N → ℚ), StrictAnti d → (∀ i, ∃ s, (d i, s) ∈ S) → Set.range d = {y | (y, true) ∈ S} := by
    intro d hd hmem
    have h1 : (Finset.univ.image fun i => (d i, true)) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨s, hs⟩ := hmem i
        have := hS _ hs
        simp only at this
        exact this ▸ hs
      · rw [Finset.card_image_of_injective _ (fun a b q => hd.injective (Prod.ext_iff.1 q).1), hc]
        simp
    ext y
    simp [← h1]
  have : c = c' := (ha.range_inj ha').1 ((key c ha hm).trans (key c' ha' hm').symm)
  have q := (hw i).trans (this ▸ (hw' i).symm)
  exact_mod_cast q

theorem isWtOfPar_sgTrue (D : D7) (τ : D.what₂.Tau) :
    Bridge.IsWtOfPar (RowPar.of (D.hc τ)).sgTrue ((Ptw D).Dpar D.R.m τ) := by
  have hk := D.R.m_add_three_le_k
  have hr : D.sp.X'.rank = D.R.N D.R.m - 1 := by rw [D.sp.X'_rank, rank_X'_eq]; rfl
  refine ⟨hr ▸ (GlobalTheory.ForcedWeights.lamRForced D τ).1, fun i => (RowPar.of (D.hc τ)).sgHC i.1 - RowPar.sh D.R, ?_, ?_,
    fun i => RowPar.sgTrue_eq _ i⟩
  · intro i j hij
    have h1 := RowPar.sgTrue_eq (D.hc τ) i
    have h2 := RowPar.sgTrue_eq (D.hc τ) j
    have h3 : (((RowPar.of (D.hc τ)).sgTrue.w j : ℤ) : ℚ) ≤ (RowPar.of (D.hc τ)).sgTrue.w i := by
      exact_mod_cast (RowPar.of (D.hc τ)).sgTrue.anti hij.le
    have h4 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hij
    simp only [rhoVec] at h1 h2
    simp only
    linarith
  · intro i
    refine ⟨true, ?_⟩
    rw [GlobalTheory.ForcedWeights.dpar_eq, Finset.mem_image]
    have hi := i.2
    unfold Ranks.N at hi
    by_cases h1 : i.1 < D.R.k - 1
    · exact ⟨.inl ⟨i.1, h1⟩, Finset.mem_univ _, by simp [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, RowPar.of]⟩
    · have hq : (i.1 - (D.R.k - 1)) / (D.R.t + 1) < D.R.m := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      by_cases h2 : (i.1 - (D.R.k - 1)) % (D.R.t + 1) = 0
      · exact ⟨.inr (.inl ⟨_, hq⟩), Finset.mem_univ _, by
          simp [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, h2, RowPar.of, RowPar.bAt, hq]⟩
      · have h3 : (i.1 - (D.R.k - 1)) % (D.R.t + 1) < D.R.t + 1 := Nat.mod_lt _ (by omega)
        refine ⟨.inr (.inr (⟨_, hq⟩, ⟨(i.1 - (D.R.k - 1)) % (D.R.t + 1) - 1, by omega⟩)), Finset.mem_univ _, ?_⟩
        simp only [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, h2, RowPar.of, RowPar.eAt, hq, dite_true, dite_false,
          if_false, Prod.mk.injEq, and_true]
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring

theorem lamRdef_eq (X : Stages) (τ) (i : Fin X.toD7.sp.X'.rank) (i' : Fin (X.B.R.N X.B.R.m - 1)) (e : (i : ℕ) = i') :
    (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w i' := by
  refine isWtOfPar_unique ?_ (GlobalTheory.ForcedWeights.lamRForced X.toD7 τ) (isWtOfPar_sgTrue X.toD7 τ) i i' e
  rw [GlobalTheory.ForcedWeights.dpar_eq]
  intro x hx
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 hx
  rfl

theorem labLL_eq (X : Stages) : labLL X.toD7 = X.B.fields.emb := rfl

theorem exists_matEq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (hG : V.gram = 1) (h : Bridge.Gf V) :
    ∃ x : UAd D.sp.cm n, R3.MatEq (R3.matIn V 1 h) (x : GL (Fin n) _) := by
  obtain ⟨_, g, rfl⟩ := h
  refine ⟨⟨_, GlobalTheory.Mem.ColAd.finN_mem hn hG g⟩, ?_⟩
  subst hn
  refine ⟨rfl, fun i j i' j' a b => ?_⟩
  obtain rfl := Fin.ext a
  obtain rfl := Fin.ext b
  unfold R3.matIn
  rw [mul_one]
  rfl

theorem gram_X' {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) : B.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := w.ok.spaces
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

set_option maxHeartbeats 2000000 in

theorem rx_std_read {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (x : RXs t) :
    ∃ c : VV B.LL B.wts.sgTrue → t.r.z.R.cX.W, ∀ (h : Bridge.Gf (w.st Z).toD7.sp.X'), ∃ y : UAd B.sp.cm (B.R.N B.R.m - 1),
      ∀ (s : R3.TupU w.I (R3.usedOf w.I T Wt)) (φ : (mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1).EqFun),
        t.r.z.R.B.jR s ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1).res (mtildeKOk _ _ _ _ t.hX) φ) h =
          c (φ.1 (decoPt (F := B.fields.F) (E := B.fields.E) B.sp.cm _ ∅ (rowSG (B.primes w.px) w.I.sel s.1) (QuotientGroup.mk y))) := by
  obtain ⟨c, -, hc, -⟩ := x.std.1
  refine ⟨c, fun h => ?_⟩
  have hr : (w.st Z).toD7.sp.X'.rank = B.R.N B.R.m - 1 := by rw [(w.st Z).toD7.sp.X'_rank, rank_X'_eq]; rfl
  obtain ⟨y, hy⟩ := exists_matEq (D := (w.st Z).toD7) _ hr (gram_X' w) h
  refine ⟨y, fun s φ => hc B.sp.cm s (⟨mtildeKOk _ _ _ _ t.hX⟩, φ) h y ?_⟩
  rw [t.r.z.lev.beta.2]
  exact hy

theorem lamLdef_eq (X : Stages) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ X.B.R.m) (τ) (i : Fin (X.toD7.sp.V j).rank) (i' : Fin X.B.R.nV)
    (e : (i : ℕ) = i') : (Bridge.lamLdef (D := X.toD7) (X.toD7.sp.V j).rank j τ).w i = (X.B.wts.lamV j τ).w i' := by
  obtain ⟨hj, W, hk, hm, ht, hjj, he, hv, hb, hw⟩ := GlobalTheory.ForcedWeights.lamLForced X.toD7 j h1 h2 τ
  have hk : W.k = X.B.R.k := hk
  have hm : W.m = X.B.R.m := hm
  have ht : W.t = X.B.R.t := ht
  have he : (W.e : ℚ) = (X.B.hc τ).e ⟨j - 1, hj.2⟩ := he
  have hv : ∀ a : Fin (X.B.R.k - 1), (W.v (a + 2) : ℚ) = (X.B.hc τ).v a := hv
  have hb : ∀ a : Fin X.B.R.m, (W.b (a + 1) : ℚ) = (X.B.hc τ).b a := hb
  have hkm := X.B.R.m_add_three_le_k
  have q := RowPar.lamV_eq (X.B.hc τ) h1 h2 i'
  have hi := i'.2
  have hE : (RowPar.of (X.B.hc τ)).eAt (j - 1) = W.e := by
    rw [he]; exact dif_pos hj.2
  have hB : ∀ n, n < X.B.R.m → (RowPar.of (X.B.hc τ)).bAt n = W.b (n + 1) := fun n hn => by
    rw [hb ⟨n, hn⟩]; exact dif_pos hn
  have key : W.lamPrime (i'.1 + 1) = (RowPar.of (X.B.hc τ)).lamVQ j i' := by
    unfold Ranks.nV Ranks.r at hi
    unfold IndefiniteWeightData.WeightData.lamPrime IndefiniteWeightData.WeightData.thetaWt IndefiniteWeightData.WeightData.dTau IndefiniteWeightData.WeightData.aPlus IndefiniteWeightData.WeightData.aMinus
      IndefiniteWeightData.WeightData.lam IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r IndefiniteWeightData.WeightData.p IndefiniteWeightData.WeightData.q
      RowPar.lamVQ RowPar.aPlus RowPar.aMinusRev RowPar.dV RowPar.vb RowPar.pOf RowPar.qOf
    rw [hk, hm, ht, hjj, hE]
    congr 1
    by_cases a : i'.1 < X.B.R.k + j - 1
    · rw [if_pos a, if_pos (show i'.1 + 1 ≤ _ from a), Nat.add_sub_cancel]
      by_cases b : i'.1 < X.B.R.k - 1
      · rw [dif_pos b, if_pos (show i'.1 + 1 ≤ _ from b), hv ⟨_, b⟩]
        rfl
      · rw [dif_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega), Int.cast_neg,
          show i'.1 + 1 - (X.B.R.k - 1) = i'.1 - (X.B.R.k - 1) + 1 by omega]
        rfl
    · rw [if_neg a, if_neg (show ¬ i'.1 + 1 ≤ _ from a)]
      by_cases b : i'.1 < X.B.R.k + j - 1 + X.B.R.t
      · rw [if_pos b, if_pos (show i'.1 + 1 ≤ _ from b)]
      · rw [if_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega),
          show X.B.R.m - j + 1 - (X.B.R.m - j + 1 - (i'.1 + 1 - (X.B.R.k + j - 1) - X.B.R.t)) =
            i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1 by omega,
          show j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) - 1 + 1 = j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) by omega]
  have := (hw i).trans ((e ▸ key).trans q.symm)
  exact_mod_cast this

theorem gram_V {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    (B.sp.V j).gram = 1 := by
  obtain ⟨hs, -, -, -, -, h5⟩ := w.ok.spaces
  have hn : B.sp.Vneg j = false := B.V_pos j h1 h2
  rw [h5 j]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn, hn]

theorem rank_V {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : ℕ) : (B.sp.V j).rank = B.R.nV := by
  obtain ⟨hs, -, -, -, -, h5⟩ := w.ok.spaces
  rw [h5 j]
  rfl

set_option maxHeartbeats 2000000 in

theorem rx_std_readL {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (x : RXs t) (i : Fin (w.st Z).toD7.R.m) :
    ∃ c : VV B.LL (B.wts.lamV ((i : ℕ) + 1)) → (t.r.z.R.cV i).W, ∀ (h : Bridge.Gf (Vc (w.st Z).toD7 i)), ∃ y : UAd B.sp.cm B.R.nV,
      ∀ (s : R3.TupU w.I (R3.usedOf w.I T Wt))
        (φ : (mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1 ((i : ℕ) + 1)).EqFun),
        t.r.z.R.B.jL i s ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel s.1 ((i : ℕ) + 1)).res (mtKOk _ _ _ _ t.hX _) φ) h =
          c (φ.1 (decoPt (F := B.fields.F) (E := B.fields.E) B.sp.cm _ ∅ (rowSG (B.primes w.px) w.I.sel s.1) (QuotientGroup.mk y))) := by
  obtain ⟨c, -, hc, -⟩ := x.std.2 i
  refine ⟨c, fun h => ?_⟩
  obtain ⟨y, hy⟩ := exists_matEq (D := (w.st Z).toD7) _ (rank_V w _) (gram_V w _ (Nat.succ_pos _) i.2) h
  refine ⟨y, fun s φ => hc B.sp.cm s (⟨mtKOk _ _ _ _ t.hX _⟩, φ) h y ?_⟩
  rw [t.r.z.lev.beta.1 i]
  exact hy

end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
