import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompValuesMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pullData_refines : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (Q' : Data V) (e : Q'.X ≃+ Q.X) (D : DegPre V) (hB : D.TauBimult) (e' : D.X ≃+ Q'.X), PullData Q θ Q' e → Refines Q' (RingHom.id V) D e' → PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D hB) (e'.trans e) := by
  intro R V _ _ _ _ θ Q Q' e D hB e' hP hR
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, ht⟩ := hP
  obtain ⟨β', β'₂, w', hpb', hsq', hw', hc', ht'⟩ := hR
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  letI := D.P.isAb.comm
  obtain ⟨w'', hw'', hv⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ D.P.A Q'.B Q.B D.P.L Q'.M.L Q.M.L
    D.P.isLB Q'.M.isLB Q.M.isLB β'₂ β₂ _ rfl w hw w' hw'
  refine ⟨β' ≫ β, β'₂ ≫ β₂, w'', ?_, ?_, hw'', fun a => ?_, fun a b => ?_⟩
  · exact (hpb'.comp hpb).congr (by rw [hs, Category.id_comp]) rfl
  · refine ⟨?_, ?_⟩
    · erw [Category.assoc, hsq.1, ← Category.assoc, hsq'.1, Category.assoc]
    · erw [Category.assoc, hsq.2, ← Category.assoc, hsq'.2, Category.assoc]
  · have h₁ : (D.c a).left ≫ β' = (Q'.c (e' a)).left := (hc' a).trans (by rw [hs, Category.id_comp])
    show (D.c a).left ≫ β' ≫ β = _
    rw [← Category.assoc, h₁]
    exact hc (e' a)
  · obtain ⟨u, x, y, k, k', hu, hy, hk, hk', h1, h2⟩ := ht (e' a) (e' b)
    refine ⟨u, x, y, k, k', hu, hy, hk, hk', h1, fun z J J' hJ hJ' => ?_⟩
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' Q'.M.isLB z
    have hκ : 𝟙 (TK V).left ≫ jK V = jK V ≫ spMap (RingHom.id V) := by rw [hs, Category.id_comp, Category.comp_id]
    have hca : ∀ a, (D.c a).left ≫ β' = (Q'.c (e' a)).left := fun a => (hc' a).trans (by rw [hs, Category.id_comp])
    have t1 := ht' (𝟙 _) hκ a b z I J' hI hJ'
    have hp : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β'₂ =
        (lift (toUnit (TK V) ≫ Q'.c (e' a)) (toUnit (TK V) ≫ Q'.c (e' b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q'.B Q'.B).left = _ ≫ (fst Q'.B Q'.B).left
        rw [Category.assoc, hsq'.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
      · show _ ≫ (snd Q'.B Q'.B).left = _ ≫ (snd Q'.B Q'.B).left
        rw [Category.assoc, hsq'.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
    have t2 := h2 z J I hJ hI
    have t3 := hv _ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J' I J hJ' hI hJ
    rw [hp] at t3
    have t0 := (Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ'
    show val (Wit.exists_tau D a b).choose (𝟙 _) z J' = _
    rw [t0, t1, t2]
    erw [t3]
    exact (mul_left_comm _ _ _).trans (congrArg _ (_root_.mul_assoc _ _ _).symm)

end GlobalTheory.Mum
