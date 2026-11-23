import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

theorem exists_fibre_pull (laws : Laws) {S S' Z Z' : Scheme.{0}} {j : Z ⟶ S} {j' : Z' ⟶ S'} {f : S' ⟶ S} {ψ : Z' ⟶ Z}
    (sq : ψ ≫ j = j' ≫ f) {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (A : PolAV Z)
    (gen : (Over.pullback j).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom j))) :
    ∃ (A' : PolAV Z') (gen' : (Over.pullback j').obj ((Over.pullback f).obj G) ≅ A'.A),
      IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) ((L.pull (pullback.fst G.hom f)).pull
        (pullback.fst ((Over.pullback f).obj G).hom j')) := by
  obtain ⟨A', g, hg, -, mul, t, ht⟩ := laws.polBaseChange _ _ ψ A
  have pg : IsGrpPullback A'.A A.A ψ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have h₂ := (pg.comp ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G j))).congr
    ((congrArg _ (Category.id_comp _)).trans sq) rfl
  obtain ⟨gen', hgen', e⟩ := grpPullback_iso ((isGrpPullback_pullback _ j').comp
    (isGrpPullback_pullback G f)) h₂
  have hi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, gen.inv_hom_id, Over.id_left]
  refine ⟨A', gen', hgen', LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB g) gen'.hom.left)
    (pull_isLB (pull_isLB hL _) _) ?_ ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm ⟨t, ht⟩)
  · refine LBIso.chartPull (h := gen'.hom.left ≫ g ≫ gen.inv.left)
      (chartPullLinComb A.L g _ (fun _ : PUnit => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb L _ _ (fun _ : PUnit => pullback.fst G.hom j) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hi, Category.comp_id]
    · rw [Category.assoc, Category.assoc]
      exact e.symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_generic_square {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (φ : R →+* V) (hφ : Function.Injective φ) :
    ∃ ψ : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of (FractionRing R)),
      ψ ≫ jK R = jK V ≫ spMap φ := by
  have gen : ∀ (K F : Type) [Field K] [Field F] [Algebra R K] [IsFractionRing R K] (g : R →+* F),
      Function.Injective g → ∃ ψ : K →+* F, ψ.comp (algebraMap R K) = g := fun K F _ _ _ _ g hg =>
    ⟨IsFractionRing.lift hg, RingHom.ext fun x => IsFractionRing.lift_algebraMap hg x⟩
  obtain ⟨ψ, hψ⟩ := gen (FractionRing R) (FractionRing V) ((algebraMap V (FractionRing V)).comp φ)
    ((IsFractionRing.injective V (FractionRing V)).comp hφ)
  exact ⟨spMap ψ, (spMap_comp _ ψ).trans ((congrArg spMap hψ).trans (spMap_comp φ _).symm)⟩

theorem exists_desc_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} (pF : IsGrpPullback G' G f F)
    (Q : TQ G X) {P : CP G} (D : Q.Desc P) {P' : CP G'} {hw w} (k : IsCPMap P' P f F hw w) :
    ∃ (Q' : TQ G' X) (D' : Q'.Desc P') (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f β ∧
      LBIso D'.M.L.L (D.M.L.L.pull β) := by
  obtain ⟨Q₀, hQ⟩ := exists_tq_baseChange _ _ _ X _ _ F pF Q
  obtain ⟨β, eβ, pβ⟩ := TQ.exists_isGrpPullback _ _ _ X _ _ F pF Q Q₀ hQ
  obtain ⟨M₀, v, hv⟩ := exists_pull (hw := pβ.1.w) D.M
    (fun Z x y => Over.OverMorphism.ext (pβ.2 Z x y _ _ rfl rfl).symm)
  obtain ⟨w₄, -, k₄⟩ := D.map.exists_comp k (by rw [Category.assoc, Over.w, hw, Category.comp_id])
  obtain ⟨w₅, k₅⟩ := cpMap_congr ((Category.comp_id _).trans (Category.id_comp _).symm) eβ.symm k₄
    (by rw [Category.assoc, pβ.1.w, Over.w_assoc, Category.id_comp])
  have := Q₀.q_hom
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P' _ _ _ Q₀.q.left (by simp) _ hv).2
    (toBase_mul_of_isMonHom Q₀.q _) w₅ k₅
  exact ⟨Q₀, ⟨M₀, w₆, k₆⟩, β, pβ, v, hv.gen⟩

theorem exists_fourth {S S' Z Z' : Scheme.{0}} {t : Z ⟶ S} {t' : Z' ⟶ S'} {f : S' ⟶ S} {b : Z' ⟶ Z}
    (sq : b ≫ t = t' ≫ f) {G : Over S} {G' : Over S'} {H : Over Z} {H' : Over Z'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    {F : G'.left ⟶ G.left} {c : H.left ⟶ G.left} {c' : H'.left ⟶ G'.left} (pF : IsGrpPullback G' G f F)
    (pc : IsGrpPullback H G t c) (pc' : IsGrpPullback H' G' t' c') {P : CP G} {P' : CP G'} {N : CP H} {N' : CP H'}
    {h₁ w₁ h₂ w₂ h₃ w₃} (k₁ : IsCPMap P' P f F h₁ w₁) (k₂ : IsCPMap N P t c h₂ w₂) (k₃ : IsCPMap N' P' t' c' h₃ w₃) :
    ∃ (E : H'.left ⟶ H.left) (pE : IsGrpPullback H' H b E) (w : _), IsCPMap N' N b E pE.1.w w := by
  have p := pc'.comp pF
  have w : (c' ≫ F) ≫ G.hom = (H'.hom ≫ b) ≫ t := p.1.w.trans (by rw [Category.assoc, sq])
  have e₁ := pc.1.lift_fst _ _ w
  have e₂ := pc.1.lift_snd _ _ w
  have p' := p.congr sq.symm e₁.symm
  have pE := pc.cancel p' e₂
  obtain ⟨w₄, -, k₄⟩ := k₁.exists_comp k₃ p.1.w
  obtain ⟨w₅, k₅⟩ := cpMap_congr sq.symm e₁.symm k₄ p'.1.w
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ N' _ _ _ _ e₂ _ k₂).2
    (fun Z x y => Over.OverMorphism.ext (pE.2 Z x y _ _ rfl rfl).symm) w₅ k₅
  exact ⟨_, pE, w₆, k₆⟩

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) {k : Type}
    [Field k] (a : R ⧸ I ^ (0 + 1) →+* k) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V)
      (b : R ⧸ I ^ (0 + 1) →+* V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), CDVR V ∧ Function.Injective φ ∧
      RingHom.ker a = RingHom.ker b ∧ spMap b ≫ thick R I 0 = thick V _ 0 ≫ spMap φ := by
  have := RingHom.ker_isPrime a
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := exists_cdvr R ((RingHom.ker a).comap (Ideal.Quotient.mk _))
  have hm' : (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ = (RingHom.ker a).comap (Ideal.Quotient.mk _) := by
    rw [← hm, zero_add, pow_one]
  have le : I ^ (0 + 1) ≤ (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ := fun r hr => by
    rw [hm', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact zero_mem _
  refine ⟨V, _, ‹_›, ‹_›, φ, Ideal.quotientMap (IsLocalRing.maximalIdeal V ^ (0 + 1)) φ le, hV, hφ,
    Ideal.ext fun y => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.mem_comap, ← hm', RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]

set_option maxHeartbeats 800000 in

theorem main : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  intro laws _ _ hU R _ _ _ I ⟨⟨hN, _⟩, _, hc, _⟩ G _ _ P hG ⟨w, _, hw, _, _, prim, _⟩ A gen hgen hA X _ _ _ T k _ x
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := exists_trait R I a
  obtain ⟨ψ, sq'⟩ := exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  have prim' := prim_pull (spMap φ) prim
  rw [← hP'] at hA' prim'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' := IsSemiAbelian.pullback (spMap φ) G hG
  have ev := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A' _ hG' gen' hgen' P' ((Over.pullback (spMap φ)).map w) inferInstance
    prim' X Q₀ P₀ ⟨w₀, H₀⟩
  obtain ⟨wA, hwA⟩ := hA'
  have pol := pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

end GlobalTheory.ClosedPol

end
