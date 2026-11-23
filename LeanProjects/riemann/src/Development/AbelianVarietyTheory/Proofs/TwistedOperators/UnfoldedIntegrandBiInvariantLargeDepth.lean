import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnermostIntegrandLeftPeriodInvariantLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowInv

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def mvD (t : T) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) (Φ : SchDown ch.G t) : SchDown ch.G t := fun i =>
  ch.W.om (.mu t D.R.m i) ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) (Φ i)

theorem mulSingle_fin {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) (i : ℕ) :
    (Pi.mulSingle j k : Pts ch.G) i ∈ GfC _ := by
  rcases eq_or_ne i j with rfl | hi
  · rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hi]
    exact one_mem _

theorem om_move (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (i : ℕ) (hi : i < D.R.m)
    (g : GA D (ch.G.V (.grid D.R.m i))) (g' : GA D (ch.G.V (.grid D.R.m (i + 1)))) :
    ch.W.om (.mu t D.R.m i) (g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1))
        (fockD ch.W t Φ P ⟨i, hi⟩) =
      ch.W.om (.mu t D.R.m i) (g, g') (fockD ch.W t (mvD ch t j k Φ) P ⟨i, hi⟩) := by
  have hom := ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, hi⟩
  have hb := mulSingle_fin ch hk i
  have hb' := mulSingle_fin ch hk (i + 1)
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m i)) (ch.G.pT (.mu t D.R.m i))
    (ch.G.chrS (.mu t D.R.m i)) (ch.G.chrT (.mu t D.R.m i)) (ch.W.om (.mu t D.R.m i)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m i)) (ch.G.cartS ch.W.cart (.mu t D.R.m i))
    (ch.G.onS ch.W.onb (.mu t D.R.m i)) (ch.G.onS ch.W.onb (.mu t D.R.m i))
    (ch.G.onT ch.W.cart (.mu t D.R.m i)) (ch.G.onT ch.W.cart (.mu t D.R.m i))
    (ch.G.onT ch.W.onb (.mu t D.R.m i)) (ch.G.onT ch.W.onb (.mu t D.R.m i)) _ _
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) (Φ ⟨i, hi⟩) (hΦ ⟨i, hi⟩) (P ⟨i, hi⟩)
  have e1 : ((g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1)) :
      GA D (ch.G.V (.grid D.R.m i)) × GA D (ch.G.V (.grid D.R.m (i + 1)))) =
      (g, g') * ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) := rfl
  rw [e1, map_mul, Module.End.mul_apply]
  exact congrArg (ch.W.om (.mu t D.R.m i) (g, g')) key.2

theorem lastDat_congr {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g g' : GA D (G.V (.grid D.R.m j)))
    (Φ₁ Φ₁' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (e : Wl.om (.mu t D.R.m j) (g, 1) Φ₁ = Wl.om (.mu t D.R.m j) (g', 1) Φ₁') :
    lastDat Wl hM j hj vN g Φ₁ Φ₂ = lastDat Wl hM j hj vN g' Φ₁' Φ₂ := by
  have e' : (lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁ = (lastAt G Wl t hM j hj vN).s.om (g', 1) Φ₁' := e
  unfold lastDat
  rw [e']

theorem down_theta {t : T} {Φ : ch.G.Datum} {τ : SchRow ch.G × SchDown ch.G t →₀ ℂ} (hτ : IsFlipFin t ch.S.B ch.rm Φ τ)
    {d : SchRow ch.G × SchDown ch.G t} (hd : d ∈ τ.support) (j : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (d.2 j) := by
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vT_is t D.R.m j le_rfl j.2
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).2 j).2 hv.2.theta

theorem fockD_theta (t : T) {Φ : SchDown ch.G t} (hΦ : ∀ j, IsThetaFunO ch.W.ψ _ _ (Φ j)) (P : PolDown ch.G) (j : Fin D.R.m) :
    IsThetaFunO ch.W.ψ _ _ (fockD ch.W t Φ P j) := by
  have hom := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, j.2⟩
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
    (ch.G.chrS (.mu t D.R.m j)) (ch.G.chrT (.mu t D.R.m j)) (ch.W.om (.mu t D.R.m j)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m j)) (ch.G.cartS ch.W.cart (.mu t D.R.m j))
    (ch.G.onS ch.W.onb (.mu t D.R.m j)) (ch.G.onS ch.W.onb (.mu t D.R.m j))
    (ch.G.onT ch.W.cart (.mu t D.R.m j)) (ch.G.onT ch.W.cart (.mu t D.R.m j))
    (ch.G.onT ch.W.onb (.mu t D.R.m j)) (ch.G.onT ch.W.onb (.mu t D.R.m j)) 1 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul]) (Φ j) (hΦ j) (P j)
  exact key.1

theorem mvD_theta (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (i : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (mvD ch t j k Φ i) :=
  (ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩).om_pres _ _ (hΦ i)

theorem update_eq_mul (h : Pts ch.G) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) :
    Function.update h j (h j * k) = h * Pi.mulSingle j k := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem conAt_move (t : T) {M : Vol ch.G} (hM : M.Is t) {j : ℕ} (hj : j ∈ idx D) {k : GA D (ch.G.V (.grid D.R.m j))}
    (hk : k ∈ GfC _) {Φ : SchDown ch.G t} (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (h : Pts ch.G) :
    conAt ch.W hM (fockD ch.W t Φ P) (h * Pi.mulSingle j k) = conAt ch.W hM (fockD ch.W t (mvD ch t j k Φ) P) h := by
  have hjm : j ≤ D.R.m - 2 := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  funext j'
  unfold conAt
  by_cases h0 : j' + 2 * 0 + 2 = D.R.m
  · rw [dif_pos h0, dif_pos h0]
    have hne1 : j' + 1 ≠ j := by omega
    have hne2 : j' + 1 + 1 ≠ j := by omega
    have hmv : mvD ch t j k Φ ⟨j' + 1, by omega⟩ = Φ ⟨j' + 1, by omega⟩ := by
      simp only [mvD, Fin.val_mk, Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hf : fockD ch.W t (mvD ch t j k Φ) P ⟨j' + 1, by omega⟩ = fockD ch.W t Φ P ⟨j' + 1, by omega⟩ := by
      unfold fockD
      rw [hmv]
    rw [hf]
    refine lastDat_congr ch.W hM j' h0 _ _ _ _ _ _ ?_
    have e := om_move ch t hk hΦ P j' (by omega) (h j') 1
    rw [Pi.mulSingle_eq_of_ne hne1, one_mul] at e
    exact e
  rw [dif_neg h0, dif_neg h0]
  by_cases h1 : j' + 2 * ((D.R.m - 4 - j') / 2 + 1) + 2 = D.R.m
  · refine dite_congr rfl (fun h1' => ?_) (fun _ => rfl)
    have e1 := om_move ch t hk hΦ P j' (by omega) (h j') (h (j' + 1))
    have e2 := om_move ch t hk hΦ P (j' + 1) (by omega) (h (j' + 1)) (h (j' + 1 + 1))
    simp only [Pi.mul_apply]
    rw [e1, e2]
  · refine dite_congr rfl (fun h1' => absurd h1' h1) (fun _ => rfl)

theorem inv_of (hB : BasicAt ch) (hC : ConLin ch) (hK : KFix ch) (hR : RInv ch) (hT : TensAt ch) : InvAt ch := by
  intro t a τ hτ M hM P y j hj h
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · unfold tot
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hR t M hM _ d.1 (fockD_theta ch t (down_theta ch hτ hd) P.2)
      (fun i => (hB.2.2.2.2.1 t _ τ hτ M hM d hd P.2 h).2 i) P.1 _ _ (hB.1 a) (hB.2.1 t y) j hj r hr h]
  · have hk' : k ∈ GfC _ := (Subgroup.mem_inf.1 hk).1
    have hmv : ∀ d ∈ τ.support, conAt ch.W hM (fockD ch.W t d.2 P.2) (h * Pi.mulSingle j k) =
        conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h := fun d hd =>
      conAt_move ch t hM hj hk' (down_theta ch hτ hd) P.2 h
    rw [update_eq_mul]
    unfold tot
    simp only [Finsupp.sum]
    refine Eq.trans (Finset.sum_congr rfl fun d hd =>
      congrArg (fun C => τ d * per ch.W M t C d.1 P.1 (colFn ch a) (formTop ch t y)) (hmv d hd)) ?_
    let Φs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchDown ch.G t :=
      Sum.elim (fun d => mvD ch t j k d.2) (fun d => d.2)
    let fs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchRow ch.G := Sum.elim (·.1) (·.1)
    let xs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → ℂ := Sum.elim (fun d => τ d) (fun d => -τ d)
    have hth : ∀ i ∈ τ.support.disjSum τ.support, ∀ n, IsThetaFunO ch.W.ψ _ _ (Φs i n) := by
      rintro (d | d) hd n
      · exact mvD_theta ch t (down_theta ch hτ (Finset.inl_mem_disjSum.1 hd)) n
      · exact down_theta ch hτ (Finset.inr_mem_disjSum.1 hd) n
    have hvan : ∀ (yr : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
        ∑ i ∈ τ.support.disjSum τ.support, xs i * ((∏ n, fs i n (yr n)) * ∏ n, Φs i n (v n)) = 0 := by
      intro yr v
      have hk2 := hK t _ τ hτ j hj k hk yr v
      simp only [Finsupp.sum] at hk2
      rw [Finset.sum_disjSum]
      simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact hk2
    have hgood : ∀ i ∈ τ.support.disjSum τ.support, Good ch.W (conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) (fs i) := by
      rintro (d | d) hd
      · have hd' := Finset.inl_mem_disjSum.1 hd
        show Good ch.W (conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h) d.1
        rw [← hmv d hd']
        exact hB.2.2.2.2.1 t _ τ hτ M hM d hd' P.2 _
      · exact hB.2.2.2.2.1 t _ τ hτ M hM d (Finset.inr_mem_disjSum.1 hd) P.2 h
    have key := hT t M (hB.2.2.1 t M hM) _ _ (hB.1 a) (hB.2.1 t y) _ (τ.support.disjSum τ.support) xs
      (fun i => conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) fs hgood (hC t M hM P.2 h _ _ xs fs Φs hth hvan) P.1
    rw [Finset.sum_disjSum] at key
    simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact key

theorem main : Big fun ch => InvAt ch :=
  big_mono (fun ch h => inv_of ch h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses (Big.and GlobalTheory.T.unfoldedProduct_depends_on_dataProduct (Big.and GlobalTheory.T.flippedFiniteTensorLatticeFixed_largeDepth (Big.and GlobalTheory.T.innermostIntegrand_leftPeriodInvariant_largeDepth GlobalTheory.T.definitePeriod_depends_on_productFunction))))

end GlobalTheory.RowInv
