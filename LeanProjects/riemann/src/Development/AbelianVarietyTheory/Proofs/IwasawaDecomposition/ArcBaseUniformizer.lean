import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcValuation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparisonStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolArcSpec

open MonoidalCategory CartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_sabMap_congr {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (h : f = f')
    (m : SABMap t' t f) : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem comp_m_of_comp_m {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c.F}
    {Z : Model Xo c β} {Y : Model Xo c β₂} {S : Scheme.{0}} {χZ : S ⟶ Z.X} {χY : S ⟶ Y.X} {t : SAB H S}
    (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    {T : Scheme.{0}} (g : T ⟶ t.G.left) (gg : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (r : T ⟶ S) (hb : g ≫ t.G.hom = r) (hw : gg ≫ Z.oF.t.G.hom ≫ Z.j = r ≫ χZ)
    (h : g ≫ m₂.φ = g₂ ≫ Y.m.φ) : g ≫ m₁.φ = gg ≫ Z.m.φ := by
  have w : (gg ≫ Z.m.φ) ≫ Z.t.G.hom = r ≫ χZ := by
    rw [Category.assoc, Z.m.cart.1.w, ← hw]; rfl
  have e₁ := m₁.cart.1.lift_fst _ _ w
  have e₂ := m₁.cart.1.lift_snd _ _ w
  have : g = m₁.cart.1.lift _ _ w := m₂.cart.1.hom_ext (h.trans (hc T _ gg g₂ e₁ h₀ h₁).symm) (hb.trans e₂.symm)
  rw [this]; exact e₁

theorem hasArcData_moveV_of_triple (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    {O' : Type} [CommRing O'] [IsDomain O'] (b' : c.V W →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV))
    {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f₀ : O' →+* R) (u : R) (χZ : Sp R ⟶ Z.X) (χY : Sp R ⟶ Y.X)
    (y : Sp (FractionRing R) ⟶ Xo.XF c) (hZ : Out.jK R ≫ χZ = y ≫ Z.j) (hY : Out.jK R ≫ χY = y ≫ Y.j)
    (t : SAB H (Sp R)) (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (hd : Z.HasArcData a I f₀ u χZ) : Y.HasArcData (GlobalTheory.PolArc.moveV bV hbV b' a) I f₀ u χY := by
  have hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  obtain ⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := hd
  obtain ⟨m0, hm0⟩ := exists_sabMap_congr (Category.id_comp χZ).symm m
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₁ m0
  obtain ⟨m1, hm1⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ n
  obtain ⟨m', hm'⟩ := exists_sabMap_congr (Category.id_comp χY) m1
  refine ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
    ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
  have hyZ : yF ≫ Z.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χZ := by
    have h1 : yF ≫ Y.j = (Out.jFK (R := R) F ≫ y) ≫ Y.j := by rw [hyF, hY, Category.assoc]
    rw [(cancel_mono Y.j).1 h1, Category.assoc, hZ]
  have hbase : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom =
      Out.jFK (R := R) F ≫ Out.jK R := by
    have a₁ : P.U.gen.inv.left ≫ pullback.snd t'.G.hom (Out.jK R) = P.A.A.hom := Over.w P.U.gen.inv
    have a₂ : x.left ≫ P.A.A.hom = Out.jFK (R := R) F := Over.w x
    have a₃ : n.φ ≫ t.G.hom = t'.G.hom ≫ 𝟙 _ := n.cart.1.w
    rw [Category.comp_id] at a₃
    simp only [Category.assoc]
    rw [a₃, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁, ← Category.assoc, a₂]
  have go : ∀ σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G, σZ.left ≫ Z.m0.toSABMap.φ = σ.left ≫ Y.m0.toSABMap.φ →
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m.φ = yF ≫ σZ.left ≫ Z.m.φ := by
    intro σZ h0
    have b₁ : σZ.left ≫ Z.oF.t.G.hom = 𝟙 _ := Over.w σZ
    have b₂ : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    have := comp_m_of_comp_m m₁ m₂ hc (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ)
      (yF ≫ σZ.left) (yF ≫ σ.left) (by rw [Category.assoc, h0, Category.assoc])
      (by rw [Category.assoc, b₁, Category.assoc, b₂]) _ hbase
      (by rw [Category.assoc, ← Category.assoc σZ.left, b₁, Category.id_comp, hyZ, Category.assoc])
      (by rw [hm', hm1] at e4; simpa only [Category.assoc] using e4)
    rw [← hm0, hn]; simpa only [Category.assoc] using this
  rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
  · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
  · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] (f : A →+* B) (g : B →+* D)
    (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') : spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  rw [← spMap_comp, ← spMap_comp, h]

theorem jK_eq (R : Type) [CommRing R] : Out.jK R = spMap (algebraMap R (FractionRing R)) := rfl

theorem ext_of_generic {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O)
    [IsSeparated s] (f g : Sp R ⟶ X) (h : Out.jK R ≫ f = Out.jK R ≫ g) : f = g := by
  have hs : f ≫ s = g ≫ s :=
    ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK R)
      (by rw [← Category.assoc, h, Category.assoc])
  exact ext_of_isDominant_of_isSeparated s hs (Out.jK R) h

theorem exists_generic (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    (b' : c.V W →+* O') (y' : Sp O' ⟶ Z.X) (hs : y' ≫ Z.s = spMap (b'.comp bV))
    (hr : Set.range (Out.jK O' ≫ y') ⊆ Set.range Z.j) :
    ∃ y₀ : Sp (FractionRing O') ⟶ Xo.XF c, Out.jK O' ≫ y' = y₀ ≫ Z.j := by
  have hb' := GlobalTheory.PolArc.injective_of_charZero c W b'
  have hinj : Function.Injective ((algebraMap O' (FractionRing O')).comp b') :=
    (IsFractionRing.injective O' (FractionRing O')).comp hb'
  obtain ⟨g, hg⟩ : ∃ g : c.F →+* FractionRing O', g.comp (c.V W).subtype = (algebraMap O' (FractionRing O')).comp b' := by
    refine ⟨IsFractionRing.lift (A := c.V W) (K := c.F) hinj, RingHom.ext fun v => ?_⟩
    have key := IsFractionRing.lift_algebraMap (A := c.V W) (K := c.F) hinj v
    rw [RingHom.comp_apply]
    exact key
  have hring : (algebraMap O' (FractionRing O')).comp (b'.comp bV) = g.comp (algebraMap (𝓞 c.F) c.F) := by
    refine RingHom.ext fun x => ?_
    have := congrArg (fun φ => φ (bV x)) hg
    simp only [RingHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    exact hbV x
  have hsq : (Out.jK O' ≫ y') ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hs, jK_eq]
    exact spMap_comp_eq _ _ _ _ hring
  let q := pullback.lift (Out.jK O' ≫ y') (spMap g) hsq
  have hrange : Set.range q ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨z, hz⟩ := hr ⟨p, rfl⟩
    rw [← hz]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Z z
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ q hrange, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem exists_lift_F (W : ValuationSubring ℂ) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    [IsDiscreteValuationRing O'] (b' : c.V W →+* O') (ϖ : O') (hϖ : Irreducible ϖ) {A : Type} [CommRing A] (ι : O' →+* A)
    (huϖ : IsUnit (ι ϖ)) : ∃ φF : c.F →+* A, φF.comp (c.V W).subtype = ι.comp b' := by
  have hb' := GlobalTheory.PolArc.injective_of_charZero c W b'
  have hV : ∀ y : nonZeroDivisors (c.V W), IsUnit ((ι.comp b') y) := by
    intro y
    have hy : b' y ≠ 0 := fun h => nonZeroDivisors.ne_zero y.2 (hb' (h.trans (map_zero _).symm))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [RingHom.comp_apply, hu, map_mul, map_pow]
    exact (u.isUnit.map _).mul (huϖ.pow n)
  exact ⟨IsLocalization.lift (M := nonZeroDivisors (c.V W)) (S := c.F) hV,
    RingHom.ext fun v => IsLocalization.lift_eq (M := nonZeroDivisors (c.V W)) (S := c.F) hV v⟩

theorem exists_generic_map {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] (ι : R →+* A)
    (hι : Function.Injective ι) :
    ∃ γ : FractionRing R →+* FractionRing A, Out.jK A ≫ spMap ι = spMap γ ≫ Out.jK R := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ι) :=
    (IsFractionRing.injective A (FractionRing A)).comp hι
  refine ⟨IsFractionRing.lift (A := R) (K := FractionRing R) hinj, ?_⟩
  have h : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) hinj (algebraMap R (FractionRing R) r) =
      algebraMap A (FractionRing A) (ι r) :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => (h r).symm)

theorem eval_generic (W : ValuationSubring ℂ) {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (Y : Model Xo c (c.V W).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] [IsDiscreteValuationRing O']
    (b' : c.V W →+* O') (ϖ : O') (hϖ : Irreducible ϖ) (χ₀ : Sp (PowerSeries O') ⟶ Y.X)
    (hχ₀s : χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b')
    (hχ₀ab : ∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal)
    (x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (hx₀ : Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j)
    (χ : Sp (PowerSeries O') ⟶ Z.X) (hχ : Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j)
    (ev : PowerSeries O' →+* O') (hevC : ∀ x, ev (PowerSeries.C x) = x) (hevX : ev PowerSeries.X = ϖ)
    (y₀ : Sp (FractionRing O') ⟶ Xo.XF c) (h0 : Out.jK O' ≫ spMap ev ≫ χ₀ = y₀ ≫ Y.j) :
    Out.jK O' ≫ spMap ev ≫ χ = y₀ ≫ Z.j := by
  haveI := isProper_toroidalModel_structureMap Z
  have hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hb' := GlobalTheory.PolArc.injective_of_charZero c W b'
  let s : PowerSeries O' := PowerSeries.C ϖ * PowerSeries.X
  have hs0 : s ≠ 0 := mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm)))
    PowerSeries.X_ne_zero
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hs0
  let A := Localization.Away s
  haveI : IsDomain A := IsLocalization.isDomain_localization hle
  let ι : PowerSeries O' →+* A := algebraMap (PowerSeries O') A
  have hιinj : Function.Injective ι := IsLocalization.injective A hle
  have hus : IsUnit (ι s) := IsLocalization.Away.algebraMap_isUnit s
  have huϖ : IsUnit (ι (PowerSeries.C ϖ)) := by
    have : ι s = ι (PowerSeries.C ϖ) * ι PowerSeries.X := map_mul _ _ _
    rw [this] at hus
    exact isUnit_of_mul_isUnit_left hus
  obtain ⟨φF, hφF₀⟩ := exists_lift_F W b' ϖ hϖ (ι.comp (PowerSeries.C (R := O'))) huϖ
  have hφF : φF.comp (c.V W).subtype = ι.comp ((PowerSeries.C (R := O')).comp b') := hφF₀
  have hsq : (spMap ι ≫ χ₀) ≫ Y.s = spMap φF ≫ spMap (c.V W).subtype := by
    rw [Category.assoc, hχ₀s, ← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, hφF]
  let q := pullback.lift (spMap ι ≫ χ₀) (spMap φF) hsq
  have hrange : Set.range q ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hχ₀ab]
    intro hX
    have h2 : ι PowerSeries.X ∈ p.asIdeal := hX
    have h3 : ι s ∈ p.asIdeal := by
      have : ι s = ι (PowerSeries.C ϖ) * ι PowerSeries.X := map_mul _ _ _
      rw [this]; exact p.asIdeal.mul_mem_left _ h2
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 hus)
  haveI := Y.jQ_open
  let g : Sp A ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ q hrange
  have hg : g ≫ Y.j = spMap ι ≫ χ₀ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

  obtain ⟨γ, hjγ⟩ := exists_generic_map ι hιinj
  have hgen : Out.jK A ≫ g = spMap γ ≫ x₀ := by
    rw [← cancel_mono Y.j, Category.assoc, hg, ← Category.assoc, hjγ, Category.assoc, hx₀, Category.assoc]
  have hχA : spMap ι ≫ χ = g ≫ Z.j := by
    refine ext_of_generic Z.s _ _ ?_
    rw [← Category.assoc, hjγ, Category.assoc, hχ, ← Category.assoc, ← hgen, Category.assoc]

  have hev : IsUnit (((algebraMap O' (FractionRing O')).comp ev) s) := by
    refine isUnit_iff_ne_zero.2 ?_
    simp only [RingHom.comp_apply, s, map_mul, hevC, hevX]
    rw [← map_mul]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O' (FractionRing O'))).2 (mul_ne_zero hϖ.ne_zero hϖ.ne_zero)
  let eA : A →+* FractionRing O' := IsLocalization.Away.lift s hev
  have heA : eA.comp ι = (algebraMap O' (FractionRing O')).comp ev := IsLocalization.lift_comp _
  have hjev : Out.jK O' ≫ spMap ev = spMap eA ≫ spMap ι := by
    rw [jK_eq]; exact spMap_comp_eq _ _ _ _ heA.symm
  have hy : spMap eA ≫ g = y₀ := by
    rw [← cancel_mono Y.j, ← h0, Category.assoc, hg, ← Category.assoc, ← hjev, Category.assoc]
  rw [← Category.assoc, hjev, Category.assoc, hχA, ← Category.assoc, hy]

theorem chart_specialises : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
    (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
    (Irreducible ϖ → ∀ (y' : Sp O' ⟶ Y.X) (ev : PowerSeries O' →+* O'), y' ≫ Y.s = spMap b' →
      Set.range (Out.jK O' ≫ y') ⊆ Set.range Y.j →
      Y.HasArcData (GlobalTheory.PolArc.moveV bV hbV b' a) (Ideal.span {ϖ}) (RingHom.id O') ϖ y' →
      (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → spMap ev ≫ χ₀ = y') →
    ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
    ∀ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j → Irreducible ϖ →
      ∀ (y' : Sp O' ⟶ Z.X) (ev : PowerSeries O' →+* O'), y' ≫ Z.s = spMap (b'.comp bV) →
        Set.range (Out.jK O' ≫ y') ⊆ Set.range Z.j → Z.HasArcData a (Ideal.span {ϖ}) (RingHom.id O') ϖ y' →
        (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → spMap ev ≫ χ = y' := by
  intro E _ _ _ H D l Xo c W Z Y bV hbV O' _ _ _ b' ϖ a χ₀ hO hχ₀ hspec x₀ hx₀ χ hχ hϖ y' ev hy's hy'r hy'd hevC hevX
  haveI : IsDiscreteValuationRing O' := by
    rcases hO with ⟨-, rfl⟩ | ⟨hd, -, -⟩
    · exact absurd hϖ not_irreducible_one
    · exact hd
  haveI := isProper_toroidalModel_structureMap Y
  haveI := isProper_toroidalModel_structureMap Z
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.PolArcSpec.exists_generic W Z bV hbV b' y' hy's hy'r
  have hYs : (y₀ ≫ Y.j) ≫ Y.s = Out.jK O' ≫ spMap b' := by
    haveI := GlobalTheory.PolArcData.mono_spMap_incl bV hbV
    rw [← cancel_mono (spMap bV)]
    simp only [Category.assoc]
    have e1 : Y.j ≫ Y.s ≫ spMap bV = Z.j ≫ Z.s := by
      rw [← Category.assoc, GlobalTheory.ThetaShiftProofs.j_over Y, GlobalTheory.ThetaShiftProofs.j_over Z, GlobalTheory.PolArcData.spMap_algebraMap_eq bV hbV,
        Category.assoc]
    rw [e1, ← Category.assoc, ← hy₀, Category.assoc, hy's, spMap_comp]
  obtain ⟨y'Y, hyY1, hyY2⟩ := val_exists Y.s (y₀ ≫ Y.j) (spMap b') hYs
  obtain ⟨t, m₁, m₂, hc⟩ := GlobalTheory.T.integral_point_pullback_comparison E H D l Xo c W Z Y bV hbV O' y' y'Y y₀ hy₀ hyY1
  have hdY := GlobalTheory.PolArcSpec.hasArcData_moveV_of_triple W Z Y bV hbV b' a (Ideal.span {ϖ}) (RingHom.id O') ϖ y' y'Y y₀
    hy₀ hyY1 t m₁ m₂ hc hy'd
  have hrY : Set.range (Out.jK O' ≫ y'Y) ⊆ Set.range Y.j := by
    rw [hyY1]
    rintro _ ⟨p, rfl⟩
    exact ⟨y₀ p, by rw [Scheme.Hom.comp_apply]⟩
  have hsp := hspec hϖ y'Y ev hyY2 hrY hdY hevC hevX
  have h0 : Out.jK O' ≫ spMap ev ≫ χ₀ = y₀ ≫ Y.j := by rw [hsp, hyY1]
  have hgen := GlobalTheory.PolArcSpec.eval_generic W Z Y b' ϖ hϖ χ₀ hχ₀.1 hχ₀.2.1 x₀ hx₀ χ hχ ev hevC hevX y₀ h0
  exact GlobalTheory.PolArcSpec.ext_of_generic Z.s _ _ (by rw [hgen, hy₀])

end GlobalTheory.PolArcSpec
