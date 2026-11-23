import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaDecompositionAdelicStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped NNReal

namespace GlobalTheory.TruncKer.PlaceAdd

section Abstract

variable {G : Type} [Group G] {P : Subgroup G} {δ : P →* ℝ≥0} {K : Subgroup G} (h : Doubling.IsIwasawa δ K)
  (e : G →* G) (hP : ∀ p ∈ P, e p ∈ P) (hK : ∀ k ∈ K, e k ∈ K) (hc : ∀ a b, Commute (e a) ((e b)⁻¹ * b))
include h hP hK hc

theorem iwAbs_eq_mul (g : G) :
    Doubling.iwAbs δ K g = Doubling.iwAbs δ K (e g) * Doubling.iwAbs δ K ((e g)⁻¹ * g) := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  let q : P := ⟨e p, hP _ p.2⟩
  have e1 : e (p * k) = (q : G) * e k := map_mul _ _ _
  have e2 : (e (p * k))⁻¹ * (p * k) = ((q⁻¹ * p : P) : G) * ((e k)⁻¹ * k) := by
    have := (hc k p).inv_left.eq
    change _ = (e p)⁻¹ * p * ((e k)⁻¹ * k)
    rw [← mul_assoc _ (e k)⁻¹, ← this, map_mul]
    group
  rw [e2, e1, h.iwAbs_mul _ hk, h.iwAbs_mul _ (hK _ hk), h.iwAbs_mul _ (mul_mem (inv_mem (hK _ hk)) hk), ← map_mul,
    mul_inv_cancel_left]

theorem iwAbs_four (w : G) {y z : G} (hy : e y = y) (hz : e z = 1) :
    Doubling.iwAbs δ K (w * (y * z)) * Doubling.iwAbs δ K w =
      Doubling.iwAbs δ K (w * y) * Doubling.iwAbs δ K (w * z) := by
  have c : y⁻¹ * ((e w)⁻¹ * w) = (e w)⁻¹ * w * y⁻¹ := by
    have := (hc y w).inv_left.eq
    rwa [hy] at this
  have a1 : e (w * (y * z)) = e (w * y) := by simp [hz]
  have a2 : e (w * z) = e w := by simp [hz]
  have b2 : (e (w * y))⁻¹ * (w * y) = (e w)⁻¹ * w := by
    rw [map_mul, hy, mul_inv_rev, mul_assoc, ← mul_assoc (e w)⁻¹, ← mul_assoc, c, inv_mul_cancel_right]
  have b1 : (e (w * y))⁻¹ * (w * (y * z)) = (e w)⁻¹ * (w * z) := by
    rw [← mul_assoc w, ← mul_assoc, b2, mul_assoc]
  rw [iwAbs_eq_mul h e hP hK hc (w * (y * z)), iwAbs_eq_mul h e hP hK hc w, iwAbs_eq_mul h e hP hK hc (w * y),
    iwAbs_eq_mul h e hP hK hc (w * z), a1, a2, b1, b2]
  ring

end Abstract

variable {D : D7} {V : HSp D} {Φ : WittFrame V} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
  {a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)}

theorem isIwasawa (hg : Φ.IsGood D.sp.cm L a) (i : Fin (wittIndex V)) :
    Doubling.IsIwasawa (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact Doubling.isIwasawa_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hg.isCompact
    (GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg)

theorem continuous_H0 (hg : Φ.IsGood D.sp.cm L a) : Continuous (H0 Φ (levelAll D.sp.cm.sig V.gram L a)) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact (NNReal.continuous_coe.comp ((isIwasawa hg i).continuous_iwAbs (Φ.flag0.isClosed_par _ _)
    (continuous_absChi i) hg.isCompact)).log fun x => NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'

theorem H0_mul_mul_add_eq_add (hg : Φ.IsGood D.sp.cm L a) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : GA D V) {y z : GA D V}
    (hy : y ∈ atPts D.sp.cm.sig V.gram S) (hz : z ∈ awayPts D.sp.cm.sig V.gram S) (i : Fin (wittIndex V)) :
    H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * (y * z)) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) w i =
      H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * y) i + H0 Φ (levelAll D.sp.cm.sig V.gram L a) (w * z) i := by
  let e : GA D V →* GA D V := (embAt D.sp.cm.sig V.gram S).comp (projAt D.sp.cm.sig V.gram S)
  have hm : ∀ g, e g ∈ atPts D.sp.cm.sig V.gram S := fun g => embAt_mem _ _ S _
  have hA : ∀ g u, projArch D.sp.cm.sig V.gram u (e g) = 1 := fun g =>
    mem_finPts_iff_forall.1 (mem_atPts.1 (hm g)).1
  have hF : ∀ g v, proj D.sp.cm.sig V.gram v (e g) = proj D.sp.cm.sig V.gram v g ∨
      proj D.sp.cm.sig V.gram v (e g) = 1 := fun g v => by
    by_cases hv : v ∈ S
    · exact .inl (proj_embAt _ _ S _ ⟨v, hv⟩)
    · exact .inr ((mem_atPts.1 (hm g)).2 v hv)
  have key := iwAbs_four (isIwasawa hg i) e (fun p hp => IsoFlag.mem_par_adelic.2
      ⟨fun u => by rw [hA]; exact one_mem _, fun v => by
        rcases hF p v with h | h <;> rw [h]
        exacts [(IsoFlag.mem_par_adelic.1 hp).2 v, one_mem _]⟩)
    (fun k hk => mem_levelAll.2 ⟨fun v => by
        rcases hF k v with h | h <;> rw [h]
        exacts [(mem_levelAll.1 hk).1 v, one_mem _], fun u => by rw [hA]; exact one_mem _⟩)
    (fun b c => commute_atPts_awayPts _ _ (hm b) (partAway D.sp.cm.sig V.gram S c).2) w (y := y) (z := z)
    (by
      obtain ⟨x, rfl⟩ := (range_embAt D.sp.cm.sig V.gram S).ge hy
      exact congrArg (embAt D.sp.cm.sig V.gram S) (projAt_embAt _ _ S x))
    (by
      have : projAt D.sp.cm.sig V.gram S z = 1 := funext fun v => mem_awayPts.1 hz v v.2
      exact (congrArg (embAt D.sp.cm.sig V.gram S) this).trans (map_one _))
  have n : ∀ x, ((Doubling.iwAbs (absChi Φ i) (levelAll D.sp.cm.sig V.gram L a) x : ℝ≥0) : ℝ) ≠ 0 := fun x =>
    NNReal.coe_ne_zero.2 (Doubling.iwAbs_pos _ _ x).ne'
  change Real.log _ + Real.log _ = Real.log _ + Real.log _
  rw [← Real.log_mul (n _) (n _), ← Real.log_mul (n _) (n _), ← NNReal.coe_mul, ← NNReal.coe_mul, key]

end GlobalTheory.TruncKer.PlaceAdd

namespace GlobalTheory.TruncKer

open PlaceAdd in

theorem yfam_continuous_add : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  intro D V Φ L a hg Q hQ
  obtain ⟨π, ε, w, -, -, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQ
  refine ⟨fun Tr => ?_, fun S y hy z hz Tr => ?_⟩
  · simp only [hY]
    refine (pr Q).continuous.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_))
    exact continuous_const.mul ((PiLp.continuous_apply 2 _ (π i)).comp
      (continuous_const.sub ((continuous_H0 hg).comp (continuous_const.mul continuous_id))))
  · rw [hY, hY, hY, hY, ← map_sub, ← map_add]
    congr 1
    ext i
    have := H0_mul_mul_add_eq_add hg S (rat V w) hy hz (π i)
    simp only [Ys, inverseChamberMap, PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, mul_one]
    linear_combination (-((ε i : SignType) : ℝ)) * this

end GlobalTheory.TruncKer

end
