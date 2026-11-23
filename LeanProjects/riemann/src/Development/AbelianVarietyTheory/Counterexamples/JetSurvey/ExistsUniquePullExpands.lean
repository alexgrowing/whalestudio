import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionPullbackSourceLevelOne
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullEveryLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_pull_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N))
    (h : IsPullByEnd U f k N s s') :
    ∃ c : ∀ y : (pullback G.hom (jK V) : Scheme.{0}), ((pullback G.hom (jK V) ⟶ G.left) → U.LG.L.ι) →
        (pullback G.hom (jK V) : Scheme.{0}).presheaf.stalk y,
      (∀ y J, Good U.LG.L y J → sval s' (𝟙 _) y J = sval s (endK f) y J * c y J) ∧
      ∀ (m : ℕ) (t : U.SecK (m * k)), ∃ t' : U.SecK (m * k * N), IsPullByEnd U f (m * k) N t t' ∧
        ∀ y J, Good U.LG.L y J → sval t' (𝟙 _) y J = sval t (endK f) y J * c y J ^ m := by
  obtain ⟨u, hu, hc, hr⟩ := h
  have hL := U.LG.isLB
  refine ⟨fun y J => (val u (𝟙 _) y J).val, fun y J hJ => ?_, fun m t => ?_⟩
  · have := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 hr _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · obtain ⟨v, hv, hvv⟩ := exists_gen hL (φ' := ![gK, endK f ≫ gK])
      (ε' := ![((m * k * N : ℕ) : ℤ), -((m * k : ℕ) : ℤ)])
      (fun W _ h => by
        simp [Fin.prod_univ_two, _root_.mul_assoc])
      (GeneratorPullback.powGen U.LG.L _ _ u m) (powGen_isGen_of_isGen u hu m)
    obtain ⟨t', ht'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => ((m * k * N : ℕ) : ℤ))
      (fun W _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
        rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec t (endK f) v hv)
    have key : ∀ y J, Good U.LG.L y J →
        sval t' (𝟙 _) y J = sval t (𝟙 _ ≫ endK f) y J * (val v (𝟙 _) y J).val := fun y J hJ => by
      rw [ht' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ]
    refine ⟨t', ⟨v, hv, ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 key⟩, fun y J hJ => ?_⟩
    · refine corr_of_val hL fun z J hJ => ?_
      have e := val_corr hJ hc (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e
      rw [val_pull hJ, val_pull hJ, val_pow, hvv _ _ z J hJ, val_pow, e, ← pow_mul]
      congr 1
      ring
    · rw [key y J hJ, Category.id_comp, hvv _ _ y J hJ, val_pow, Units.val_pow_eq_pow_val]

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Geo.Tor.Host E}
  {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}

theorem expands_pull_every_level (hLaws : Laws) (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ} (hk : 1 ≤ k)
    (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (hs : P.U.Expands k s F)
    (s' : P.U.SecK (k * N)) (hs' : IsPullByEnd P.U (t.act.act a) k N s s') :
    letI := H.starRing
    ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧
      PullAl P.D (FractionRing V) P.oD a k N F F' := by
  letI := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨F', hF'⟩ := exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
    (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  obtain ⟨s'', hs'', -⟩ := (P.U.expand (k * N) (Nat.mul_pos hk hN0)).2 F'
  obtain ⟨c, hc, hpow⟩ := exists_pull_pow P.U _ k N s s' hs'
  have hint := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ _ _ _
    P.U.toUnifPre).2
  have e : s'' = s' := by
    refine SecOps.sec_ext (sec_ext_val P.U.LG.isLB fun y J hJ => ?_)
    have hm : ∀ m : ℕ, 4 ≤ m → sval s'' (𝟙 _) y J ^ m = sval s' (𝟙 _) y J ^ m := fun m hm => by
      have hmk : 4 ≤ m * k := le_trans hm (Nat.le_mul_of_pos_right m hk)
      obtain ⟨τ, hτ⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ _ _ _ P.U.toUnifPre (m * k) hmk _
        (endK (t.act.act a)) y J hJ
      obtain ⟨τ', hτ', hv⟩ := hpow m τ
      obtain ⟨T, hT, -⟩ := (P.U.expand (m * k) (by omega)).1 τ
      obtain ⟨T', hT', hTT⟩ := GlobalTheory.PullExpansion.expands_pull_of_four_le hLaws V E H t P a N hN hN0 (m * k) hmk
        τ T hT τ' hτ'
      have g := GlobalTheory.GenericCross.main hLaws V E H t P a N hN hN0 k s F s'' F' hs hs'' hF' (m * k) τ T τ' T' hT hT'
        hTT m 1 (by ring) y J hJ
      rw [pow_one, pow_one, hv y J hJ] at g
      refine hτ.mul_right_cancel (g.trans ?_)
      rw [hc y J hJ]
      ring
    exact GlobalTheory.PullLevelOne.eq_of_pow_four_five (hm 4 le_rfl) (hm 5 (by norm_num))
  exact ⟨F', e ▸ hs'', hF'⟩

end

end GlobalTheory.PullEveryLevel
