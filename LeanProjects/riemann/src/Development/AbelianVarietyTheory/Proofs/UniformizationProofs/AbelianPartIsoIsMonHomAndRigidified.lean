import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianPartIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem isMonHom_of_comp {S : Scheme.{0}} {G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q' : G ⟶ B') (q : G ⟶ B) (β : B' ⟶ B) [IsMonHom q'] [IsMonHom q] [Flat q'.left]
    [Surjective q'.left] (hβ : q' ≫ β = q) : IsMonHom β := by
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom q', Category.assoc, hβ, IsMonHom.one_hom]
  · have := FlatQuotient.epi_tensorHom q' q'
    rw [← cancel_epi (q' ⊗ₘ q'), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc, hβ,
      IsMonHom.mul_hom]

theorem hom_eq_of_map_eq {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom]
    (f g : H ⟶ Y)
    (h : ∀ n, (Over.pullback (thick R I n)).map f = (Over.pullback (thick R I n)).map g) : f = g := by
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 Y f g fun n => ?_
  have k : ∀ f : H ⟶ Y, ((Over.pullback (thick R I n)).map f).left ≫ pullback.fst Y.hom (thick R I n) =
      pullback.fst H.hom (thick R I n) ≫ f.left := fun f => pullback.lift_fst _ _ _
  exact (k f).symm.trans ((congrArg (fun φ => φ.left ≫ pullback.fst Y.hom (thick R I n)) (h n)).trans (k g))

theorem isMonHom_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {B B' : Over (Spec (CommRingCat.of R))} [GrpObj B] [GrpObj B']
    (hB : IsAbelianScheme B) (hB' : IsAbelianScheme B') (f : B' ⟶ B)
    (h : ∀ n, IsMonHom ((Over.pullback (thick R I n)).map f)) : IsMonHom f := by
  have := hB.proper
  have := hB'.smooth
  have := hB'.geomConnected
  refine ⟨?_, ?_⟩
  · have : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
    have : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (GeometricallyConnected (𝟙 _))
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : Smooth (B' ⊗ B').hom := inferInstanceAs (Smooth (pullback.fst B'.hom B'.hom ≫ B'.hom))
    have : GeometricallyConnected (B' ⊗ B').hom := by
      change GeometricallyConnected (pullback.fst B'.hom B'.hom ≫ B'.hom)
      exact GeometricallyConnected.comp _ _
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

theorem fn_eq_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ (e : ℕ) (z), gs (thick R I e) z W a = gs (thick R I e) z W b) : a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick R I e).app ⊤).hom a = ((thick R I e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

theorem pmaps_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (s' : Spec (CommRingCat.of R) ⟶ X') (s : Spec (CommRingCat.of R) ⟶ X) (hs : s' ≫ F = s)
    (a : LB.Gen (L'.pull s')) (ha : a.IsGen) (t : LB.Gen (L.pull s)) (ht : t.IsGen)
    (h : ∀ (e : ℕ) (z) (p : L.ι) (q : L'.ι), (thick R I e ≫ s) z ∈ L.U p →
      (thick R I e ≫ s') z ∈ L'.U q →
      gm (thick R I e) z ((L.pull s).U (fun _ => p)) (t.s (fun _ => p)) =
        gw w (thick R I e ≫ s') z p q *
          gm (thick R I e) z ((L'.pull s').U (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => s') (fun _ => s) (fun _ => 1) a t (𝟙 _) := by
  subst hs
  obtain ⟨p₀, hp₀⟩ := exists_chart hL ((s' ≫ F) (IsLocalRing.closedPoint R))
  obtain ⟨q₀, hq₀⟩ := exists_chart hL' (s' (IsLocalRing.closedPoint R))
  have hp : ∀ x, (s' ≫ F) x ∈ L.U p₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map (s' ≫ F).continuous).mem_open
      (L.U p₀).isOpen hp₀
  have hq : ∀ x, s' x ∈ L'.U q₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map s'.continuous).mem_open
      (L'.U q₀).isOpen hq₀
  have l₁ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L.pull (s' ≫ F)).U (fun _ => p₀) :=
    fun x _ => mem_pull.2 (hp x)
  have l₂ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L'.pull s').U (fun _ => q₀) :=
    fun x _ => mem_pull.2 (hq x)
  have l₃ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      s' ⁻¹ᵁ ((L.pull F).U (fun _ => p₀) ⊓ L'.U q₀) :=
    fun x _ => ⟨mem_pull.2 (hp x), hq x⟩
  have ev₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₁ (t.s (fun _ => p₀))) =
        gm r z ((L.pull (s' ≫ F)).U (fun _ => p₀)) (t.s (fun _ => p₀)) :=
    fun Z r z => gm_res r z l₁ trivial _
  have ev₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀))) =
        gw w (r ≫ s') z p₀ q₀ * gm r z ((L'.pull s').U (fun _ => q₀)) (a.s (fun _ => q₀)) :=
    fun Z r z => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l₃ trivial _).trans (gm_pull r s' z _ (l₃ (Set.mem_univ (r z))) _))
      (gm_res r z l₂ trivial _))
  have key : res l₁ (t.s (fun _ => p₀)) =
      res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀)) := by
    refine Units.ext (fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, ev₁, ev₂, h e z p₀ q₀ (hp _) (hq _)]
  intro Z r z p q hpz hqz
  have E := (ev₁ Z r z).symm.trans ((congrArg (gm r z ⊤) key).trans (ev₂ Z r z))
  have a₁ := gen_trans ht r z (j := p) (j' := fun _ => p₀) (Set.mem_iInter.2 hpz) (l₁ (Set.mem_univ _))
  have a₂ := gen_trans ha r z (j := q) (j' := fun _ => q₀) (Set.mem_iInter.2 hqz) (l₂ (Set.mem_univ _))
  have a₃ := (isGen_iff w).1 hw Z (r ≫ s') z (p PUnit.unit) p₀ (q PUnit.unit) q₀ (hpz _) (hp _)
    (hqz _) (hq _)
  rw [Category.comp_id, a₁, a₂, Fintype.prod_unique, zpow_one, a₃]
  refine (congrArg _ E).trans ?_
  simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, PUnit.default_eq_unit]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end AbelianPartIso

open AbelianPartIso ReciprocityTheory.ChartRestriction.G.DVR in

theorem abelianPartIso_isMonHom_and_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' wL he hwL hrig Φ w ⟨hw, H⟩
  obtain ⟨_, -, -, _⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hI' : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h.ge.trans (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).le)))
  have hΦ : IsMonHom Φ.hom := by
    refine isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R I e) =
          pullback.fst D'.toPre.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (H e).1))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨hΦ, pmaps_of_thickenings hI' D.toPre.P.isLB D'.toPre.P.isLB w hw _ _
    (congrArg Over.Hom.left hΦ.one_hom) _ D'.toPre.rig_gen _ D.toPre.rig_gen
    fun e z p q hp hq => ?_⟩
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart U.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  obtain ⟨j', hj'⟩ := Geo.Tor.exists_chart U'.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  have e₁ := UnitValue.wv_rig U e z p j hp hj
  have e₂ := UnitValue.wv_rig U' e z q j' hq hj'
  have e₃ := (Geo.Tor.maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (𝟙 _) _
    (rigPull_le (𝟙 G.left) (𝟙 _) he U.LG.L) (fun _ => rfl)).1 hrig _ (UnitValue.thU R I e) z
    (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')
  have e₄ := (H e).2 _ (eSec (thickObj R I e G)) z p q j j'
    ((congrArg (fun g => g z ∈ D.toPre.P.L.U p) (UnitValue.eSec_pGl U e)).mpr hp)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U q) (UnitValue.eSec_pGl U' e)).mpr hq)
    ((congrArg (fun g => g z ∈ U.LG.L.U j) (UnitValue.eSec_fGl (G := G) e)).mpr hj)
    ((congrArg (fun g => g z ∈ U'.LG.L.U j') (UnitValue.eSec_fGl (G := G) e)).mpr hj')
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G) e] at e₄
  rw [Category.comp_id, Fintype.prod_unique, zpow_one] at e₃
  refine e₁.symm.trans ((congrArg _ e₃).trans ((mul_assoc _ _ _).symm.trans ?_))
  exact (congrArg (· * _) e₄.symm).trans ((mul_assoc _ _ _).trans (congrArg _ e₂))

end GlobalTheory
