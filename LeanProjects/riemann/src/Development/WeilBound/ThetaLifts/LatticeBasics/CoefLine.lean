import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem coefLine_of (hS : SWFull) (hX : BoxSec) (hW : DblW) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hR : PairsStable) (hM : MatchEx) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : CoefLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t lam hl y hy Ψ hΨ
  have T := h.triple
  have l1 := T.geo.lt
  have l2 := T.geo.aBig
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ T.base (Or.inl T.geo.hV') (by omega)
  obtain ⟨q1, q2⟩ := (hM F E σ B a a' G X om om' R Rf h).2.2 _ _ hy.1 hy.2
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) _ q1
  have s2 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ q2.1
  have s3 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ hΨ
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega))
  have rp : ∀ s u, IsRapid (comb G om om' s u y) := fun s u =>
    cW.rapid (((c1 _ s1).const_smul s).add ((c2 _ s2).const_smul u)) fun γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_inv G.M (b1 _ s1).2.1 γ hγ, I_inv G.M' (b2 _ s2).2.1 γ hγ]
  have tr : ∀ s u g, (fun h => comb G om om' s u y (h * g)) = comb G om om' s u (om (1, g) y.1, om' (1, g) y.2) := fun s u g =>
    funext fun h => by simp only [comb, Pi.add_apply, Pi.smul_apply, I_right]
  obtain ⟨dd, om₂, S, l, d1, d2, d3, -⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)
  obtain ⟨⟨K, ht, k1, k2, k3, k4⟩, e, ce, he⟩ := hH F E σ B _ G.W _ _ T.base (.inr T.geo.hW)
  obtain ⟨t₀, hi⟩ := hT F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K ht e k1 k2 he μ hμ
  have sec := hX F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inr T.geo.hW) (by omega) cW T.chars.heckeα he ce
    (hK F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K k1) k2 k3 k4 sec.cont sec.law hE hμ hD hi
  have key := An.ident hE.isOpen hE.conn (hol _ (rp s t)) ((hol _ (rp 0 1)).const_mul lam) (fun z hz => ⟨(far z hz).1, by
    simp only [(far z hz).2.2 _ (rp s t), (far z hz).2.2 _ (rp 0 1), tr, ← integral_const_mul,
      fun g => hl _ ((hR F E σ B a a' G X om om' R Rf h hp hq).2 y hy g) y hy]
    exact integral_congr_ae (.of_forall fun g => mul_left_comm _ _ _)⟩) u
  haveI := cW.sc; haveI := cV.sc; haveI := cW.lc; haveI := cV.lc
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cV.fin _ _ T.geo.hM'.haar T.geo.hM'.dom⟩
  have val : ∀ φ, IsRapid φ → kpair X.α e μ D (Ê (((a' : ℂ) - (a + a' : ℕ)) / 2)) φ =
      2 * ((G.M'.μ.real G.M'.dom)⁻¹ : ℝ) * pet G.M'.μ G.M'.dom (th om' μ D φ Ψ) (th om' μ D φ Ψ) := fun φ hφ => by
    have := An.at_value (μ.restrict D) (G.M'.μ.restrict G.M'.dom) ⟨(b2 _ s3).1, cV.bdd₂ cW (b2 _ s3).1 (b2 _ s3).2.1⟩
      ⟨hφ.1, cW.bdd hφ.1 hφ.2.1⟩
    refine Eq.trans ?_ (congrArg _ this)
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, if_neg (show ¬ a + a' < a' by omega), setAverage_eq, Complex.real_smul,
      ← fun g => (((d2 Ψ s3 Ψ s3).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  rw [val _ (rp s t), val _ (rp 0 1), mul_left_comm lam] at key
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (cV.vol_ne T.geo.hM'.haar T.geo.hM'.dom)))) key

end GlobalTheory.ThK.Dbl

end
