import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFramesEL
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.FrameN
open GlobalTheory.BoxFamily

section General

variable {X X' Y Y₀ Y₁ Y₂ Z : Scheme.{0}} {M : LB X} {M' : LB X'} {n : ℕ} {pr : Fin n → (X' ⟶ X)}

theorem val_along (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y₁ ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y₂ ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb M φ ε)) (t' : LB.Gen (LB.LinComb M φ' ε'))
    (ρ : Y ⟶ Y₁) (ρ' : Y ⟶ Y₂) (h : ∀ y J, Good M y J → val t ρ y J = val t' ρ' y J)
    (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) : val t (r ≫ ρ) z J = val t' (r ≫ ρ') z J := by
  have c : LB.Gen.Corr M _ _ _ _ (LB.pullGen M φ ε t ρ) (LB.pullGen M φ' ε' t' ρ') :=
    corr_of_val hM fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]; exact h y J hJ
  have := val_corr hJ c r
  rwa [val_pull hJ, val_pull hJ] at this

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen M φ ε t).IsGen := by
  intro (j : I × K → M.ι) (j' : I × K → M.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → M.ι, y ∈ LB.wchart M (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart M (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen M φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart M (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb M _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem mapsAt_of_val (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    (p : Y ⟶ X') (q : ℤ) (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => q)))
    (b : LB.Gen (LB.LinComb M (K := Fin n) (fun i => p ≫ pr i) (fun _ => q))) (hb : b.IsGen)
    (H : ∀ y J J', Good M y J → Good M' y J' → val b (𝟙 Y) y J = om w y J J' (𝟙 Y ≫ p) ^ q * val a (𝟙 Y) y J') :
    GeneratorPullback.MapsAt M M' pr w p q a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := exists_good_at hM y
  obtain ⟨J', hJ', e⟩ := exists_good M' hM' y (fun _ : PUnit => 𝟙 Y ≫ p) (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hy.2)
  have e' : J' (𝟙 Y ≫ p) = jL := e PUnit.unit
  have h := H y J J' hJ hJ'
  rw [val_of a _ y J' (fun _ => jL) (fun _ => e'),
    val_of b _ y J (fun i => J ((𝟙 Y ≫ p) ≫ pr i)) (fun i => by rw [Category.assoc]), om, e'] at h
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart M (fun i => p ≫ pr i) jN := GeneratorPullback.mapsAt_le_b M M' pr p jN jL hy
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart M (fun i => p ≫ pr i) (fun i => J ((𝟙 Y ≫ p) ≫ pr i)) :=
    Set.mem_iInter.2 fun i => hJ ((𝟙 Y ≫ p) ≫ pr i)
  have m₃ : (𝟙 Y ≫ p) y ∈ LB.wchart M pr jN := hy.1
  have m₄ : (𝟙 Y ≫ p) y ∈ LB.wchart M pr (fun i => J ((𝟙 Y ≫ p) ≫ pr i)) :=
    Set.mem_iInter.2 fun i => hJ ((𝟙 Y ≫ p) ≫ pr i)
  have m₅ : (𝟙 Y ≫ p) y ∈ M'.U jL := hy.2
  have g := gm_isGen hw (𝟙 Y ≫ p) y jN (fun i => J ((𝟙 Y ≫ p) ≫ pr i)) jL jL m₃ m₄ m₅ m₅
  rw [gm_self hM' _ y m₅, inv_one, _root_.mul_one] at g
  have g' := g.trans (congrArg₂ (· * ·) (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ p) y _ _ m₃ m₄) rfl)
  refine ((gm_res _ y _ hy _).trans (gen_trans hb _ y m₁ m₂)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ q) ((gm_pull (𝟙 Y) p y _ hy _).trans g')))
      (gm_res _ y _ hy _))).symm)
  rw [h, mul_zpow, ← _root_.mul_assoc, ← Finset.prod_zpow]
  simp only [trF, zpow_one, Category.assoc]
  rfl

theorem clause_iff (hM' : M'.IsLB) (g : Y₁ ⟶ X') (z : Y ⟶ Y₁) (q : ℤ)
    (σ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => g) (fun _ => q))) (a : Γ(Y, ⊤))
    (τ : LB.Gen (LB.LinComb M' (K := PUnit.{1}) (fun _ => z ≫ g) (fun _ => q))) :
    (∀ j : Fin 1 → M'.ι, (Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j)) =
      (Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) ↔
    ∀ y J, Good M' y J → sval σ z y J = gs (𝟙 Y) y ⊤ a * (val τ (𝟙 Y) y J).val := by
  have key : ∀ (j : Fin 1 → M'.ι) (y : Y) (hy : y ∈ LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0)),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j))) =
        gs z y (LB.wchart M' (fun _ : Fin 1 => g) j) (σ.f j) ∧
      gs (𝟙 Y) y (LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0))
        ((Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) =
        gs (𝟙 Y) y ⊤ a * (gm (𝟙 Y) y (LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0)) (τ.s (fun _ => j 0))).val :=
    fun j y hy => ⟨(gs_res _ y _ hy _).trans ((gs_pull (𝟙 Y) z y _ (ExpBijectiveUniformisation.wchart_comp_le M' g z j hy) _).trans
      (by rw [Category.id_comp])),
      (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))⟩
  constructor
  · intro H y J hJ
    obtain ⟨k₁, k₂⟩ := key (fun _ => J (z ≫ g)) y (Set.mem_iInter.2 fun _ => hJ (z ≫ g))
    rw [val_of τ _ y J (fun _ => J (z ≫ g)) (fun _ => by rw [Category.id_comp])]
    have e := congrArg (gs (𝟙 Y) y _) (H (fun _ => J (z ≫ g)))
    rw [sval_of σ z y J (fun _ => J (z ≫ g)) (fun _ => rfl)]
    exact k₁.symm.trans (e.trans k₂)
  · intro H j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good M' hM' y (fun _ : PUnit => z ≫ g) (fun _ => j 0) (fun _ _ _ => rfl)
      (fun k => Set.mem_iInter.1 hy k)
    have h := H y J hJ
    rw [sval_of σ z y J j (fun k => by rw [Fin.fin_one_eq_zero k]; exact e PUnit.unit),
      val_of τ _ y J (fun _ => j 0) (fun _ => by rw [Category.id_comp]; exact e PUnit.unit)] at h
    obtain ⟨k₁, k₂⟩ := key j y hy
    exact k₁.trans (h.trans k₂.symm)

theorem core_iff (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {x : Y₀ ⟶ X} (τ₁ : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => x) (fun _ => 1))) (h₁ : τ₁.IsGen)
    (cp : Fin n → (Y₂ ⟶ Y₀)) {zv : Y₂ ⟶ X'} (hz : ∀ i, zv ≫ pr i = cp i ≫ x)
    (τ₂ : LB.Gen (LB.LinComb M' (K := Fin 1) (fun _ => zv) (fun _ => 1))) (h₂ : τ₂.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (y : Z) (J J'), Good M y J → Good M' y J' →
      om w y J J' (r ≫ zv) * val τ₂ r y J' = ∏ i, val τ₁ (r ≫ cp i) y J)
    (s : Y ⟶ Y₂) (g : Y₁ ⟶ X') (z : Y ⟶ Y₁) (hzg : z ≫ g = s ≫ zv) (q : ℕ)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb M φ ε))
    (hc : ∀ y J, Good M y J → val c (𝟙 Y) y J = ∏ i, val τ₁ (s ≫ cp i) y J ^ q)
    (σ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => g) (fun _ => (q : ℤ)))) (a : Γ(Y, ⊤)) :
    (∃ (τ : LB.Gen (LB.LinComb M' (K := PUnit.{1}) (fun _ => z ≫ g) (fun _ => (q : ℤ))))
      (b : LB.Gen (LB.LinComb M (K := Fin n) (fun i => (z ≫ g) ≫ pr i) (fun _ => (q : ℤ)))),
      GeneratorPullback.MapsAt M M' pr w (z ≫ g) q τ b ∧ LB.Gen.Corr M _ _ _ _ b c ∧
      ∀ j : Fin 1 → M'.ι, (Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j)) =
        (Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) ↔
    ∀ y J, Good M' y J → sval σ z y J = gs (𝟙 Y) y ⊤ a * (val τ₂ s y J ^ q).val := by
  have hp : ∀ y J J', Good M y J → Good M' y J' → ∏ i, val τ₁ (s ≫ cp i) y J ^ q =
      om w y J J' (𝟙 Y ≫ z ≫ g) ^ (q : ℤ) * val τ₂ s y J' ^ q := fun y J J' hJ hJ' => by
    rw [Finset.prod_pow, ← hv _ s y J J' hJ hJ', Category.id_comp, hzg, zpow_natCast, mul_pow]
  constructor
  · rintro ⟨τ, b, m, cr, cl⟩ y J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have e := (mapsAt_val w _ _ τ b m (𝟙 Y) y hJ hJ').symm.trans ((val_corr hJ cr (𝟙 Y)).trans
      ((hc y J hJ).trans (hp y J J' hJ hJ')))
    rw [(clause_iff hM' g z q σ a τ).1 cl y J' hJ', mul_left_cancel e]
  · intro H
    obtain ⟨τ, -, hτ⟩ := exists_gen hM' (K' := PUnit.{1}) (φ' := fun _ => z ≫ g) (ε' := fun _ => (q : ℤ)) (by
        intro U _ h
        simp [hzg]) _
      (DVR.powGen_isGen M' _ _ _ (DVR.pullGen_isGen M' _ _ _ h₂ s) q)
    obtain ⟨b, hb, hbv⟩ := exists_gen hM (K' := Fin n) (φ' := fun i => (z ≫ g) ≫ pr i) (ε' := fun _ => (q : ℤ)) (by
        intro U _ h
        simp [hzg, hz, Fintype.prod_prod_type]) _
      (finProd_isGen (I := Fin n) _ _ _ fun i =>
        DVR.powGen_isGen M _ _ _ (DVR.pullGen_isGen M _ _ _ h₁ (s ≫ cp i)) q)
    have τv : ∀ y J', Good M' y J' → val τ (𝟙 Y) y J' = val τ₂ s y J' ^ q := fun y J' hJ' => by
      rw [hτ _ _ y J' hJ', val_powGen, val_pull hJ', Category.id_comp]
    have bv : ∀ y J, Good M y J → val b (𝟙 Y) y J = ∏ i, val τ₁ (s ≫ cp i) y J ^ q := fun y J hJ => by
      rw [hbv _ _ y J hJ, val_finProd _ _ _ _ _ hJ]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [val_powGen, val_pull hJ, Category.id_comp]
    refine ⟨τ, b, mapsAt_of_val hM hM' w hw _ _ τ b hb fun y J J' hJ hJ' => ?_,
      corr_of_val hM fun y J hJ => (bv y J hJ).trans (hc y J hJ).symm,
      (clause_iff hM' g z q σ a τ).2 fun y J' hJ' => ?_⟩
    · rw [bv y J hJ, τv y J' hJ', hp y J J' hJ hJ']
    · rw [τv y J' hJ', H y J' hJ']

theorem corr_genCast {L L' : LB X} (h : L = L') {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (b : LB.Gen (LB.LinComb L φ ε)) (c : LB.Gen (LB.LinComb L' φ' ε')) :
    LB.Gen.Corr L' _ _ _ _ (genCast h _ _ b) c ↔ LB.Gen.Corr L _ _ _ _ b (genCast h.symm _ _ c) := by
  subst h; rfl

end General

section Jets

variable {V : Type} [CommRing V] {n d : ℕ}

abbrev cpy (V : Type) [CommRing V] (n d m : ℕ) (i : Fin n) : Sp (Jet V (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
    Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m)

theorem zV_pr {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G)
    (m : ℕ) (i : Fin n) : (zV pG xT m).left ≫ (pG.pr i).left = cpy V n d m i ≫ (xT m).left :=
  congrArg (fun q => q.left) (pG.lim.fac (Fan.mk _ fun i => Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m) ⟨i⟩)

theorem coef_cpy (F : Type) [Field F] [Algebra V F] (m : ℕ) (i : Fin n) :
    spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ cpy V n d m i = jcN V F d n m i := by
  rw [jcN, ← JetTr.jetCoef_copy]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem trunc_cpy (m : ℕ) (i : Fin n) :
    spMap ((jetTrunc : Jet V (Fin n × Fin d) (m + 1) →ₐ[V] Jet V (Fin n × Fin d) m) :
        Jet V (Fin n × Fin d) (m + 1) →+* Jet V (Fin n × Fin d) m) ≫ cpy V n d (m + 1) i =
      cpy V n d m i ≫ spMap ((jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) :
        Jet V (Fin 1 × Fin d) (m + 1) →+* Jet V (Fin 1 × Fin d) m) := by
  have hc : (jetTrunc : Jet V (Fin n × Fin d) (m + 1) →ₐ[V] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] _) := by
    apply GermD.jet_hom_ext
    intro p
    rfl
  have e := (GermD.homAt_comp (𝟙 (Sp V)) _ _).trans ((congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V))) hc).trans
    (GermD.homAt_comp (𝟙 (Sp V)) _ _).symm)
  exact congrArg (fun q => q.left) e

theorem pow_ext {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] (pG : IsPowGrp G' G n) {Y : Scheme.{0}}
    (a b : Y ⟶ G'.left) (h₀ : a ≫ G'.hom = b ≫ G'.hom) (h : ∀ i, a ≫ (pG.pr i).left = b ≫ (pG.pr i).left) : a = b := by
  have e : (Over.homMk a rfl : Over.mk (a ≫ G'.hom) ⟶ G') = Over.homMk b h₀.symm :=
    pG.lim.hom_ext fun i => Over.OverMorphism.ext (h i.as)
  exact congrArg (fun q => q.left) e

theorem val_cast_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (L : LB t.G.left) (h : t.PP.L = L) {Y Y₀ : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y₀ ⟶ t.G.left)) (ε : K → ℤ)
    (e : LB.Gen (LB.LinComb t.PP.L φ ε)) (q : ℕ) (r : Fin n → (Y ⟶ Y₀)) (y : Y) (J) (hJ : Good L y J) :
    val (genCast h _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i))) (𝟙 Y) y J = ∏ i, val (genCast h _ _ e) (r i) y J ^ q := by
  subst h
  show val (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i)) (𝟙 Y) y J = ∏ i, val e (r i) y J ^ q
  rw [val_finProd _ _ _ _ _ hJ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [val_pull hJ, GermD.val_genPowG, Category.id_comp]

end Jets

end GlobalTheory.PowGerm.FrameN

namespace GlobalTheory.PowGerm
open GlobalTheory.BoxFamily FrameN

theorem frameNSt_holds : FrameNSt := by
  intro E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr n D' A' G' _ _ pD pA pG U' PU
  obtain ⟨τ₁, g₁, el, tr⟩ := frame1St_holds E H V t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr
  have hM : P.U.LG.L.IsLB := P.U.LG.isLB
  have hM' : U'.LG.L.IsLB := U'.LG.isLB
  have ex : ∀ m, ∃ τ : LB.Gen (LB.LinComb U'.LG.L (Y := Sp (Jet V (Fin n × Fin d) m)) (K := Fin 1)
      (fun _ => (zV pG xT m).left) (fun _ => (1 : ℤ))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J → Good U'.LG.L y J' →
        om PU.wL y J J' (r ≫ (zV pG xT m).left) * val τ r y J' = ∏ i, val (τ₁ m) (r ≫ cpy V n d m i) y J := by
    intro m
    obtain ⟨τ, hτ, hv⟩ := exists_boxPull_gen (pr := fun i => (pG.pr i).left) PU.wL PU.wL_gen hM hM' (K := Fin 1)
      (φ' := fun _ => (zV pG xT m).left) (φ := fun _ _ => (xT m).left) (ε := fun _ => 1) (cpy V n d m)
      (fun i _ => zV_pr pG xT m i) (fun _ => τ₁ m) (fun _ => g₁ m)
    refine ⟨τ, hτ, fun Z r y J J' hJ hJ' => ?_⟩
    have := hv Z r y J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one] at this
  choose τ hτ hv using ex
  refine ⟨τ, hτ, fun htr m y J' hJ' => ?_, fun F _ _ _ _ q σ' f => forall_congr' fun m => exists_congr fun z => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_at hM y
    have c : ∀ i, val (τ₁ (m + 1)) (spMap ((jetTrunc : Jet V (Fin n × Fin d) (m + 1) →ₐ[V] Jet V (Fin n × Fin d) m) :
        Jet V (Fin n × Fin d) (m + 1) →+* Jet V (Fin n × Fin d) m) ≫ cpy V n d (m + 1) i) y J =
        val (τ₁ m) (𝟙 _ ≫ cpy V n d m i) y J := fun i => by
      rw [trunc_cpy, Category.id_comp]
      exact (val_along hM _ _ _ _ (tr htr m) _ y J hJ).trans (by rw [Category.comp_id])
    have ez : spMap ((jetTrunc : Jet V (Fin n × Fin d) (m + 1) →ₐ[V] Jet V (Fin n × Fin d) m) :
        Jet V (Fin n × Fin d) (m + 1) →+* Jet V (Fin n × Fin d) m) ≫ (zV pG xT (m + 1)).left = 𝟙 _ ≫ (zV pG xT m).left := by
      refine pow_ext pG _ _ ?_ fun i => ?_
      · rw [Category.id_comp, Category.assoc, Over.w, Over.w]
        exact Over.w (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin n × Fin d) (m + 1) →ₐ[V] Jet V (Fin n × Fin d) m))
      · rw [Category.id_comp, Category.assoc, zV_pr, zV_pr, ← Category.assoc, trunc_cpy, Category.assoc]
        exact congrArg (fun q => cpy V n d m i ≫ q.left) (hch.trunc m)
    have e := (hv (m + 1) _ _ y J J' hJ hJ').trans ((Finset.prod_congr rfl fun i _ => c i).trans
      (hv m _ _ y J J' hJ hJ').symm)
    rw [ez] at e
    exact mul_left_cancel e
  · have pts : z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
        spMap (algebraMap F (Jet F (Fin n × Fin d) m)) →
        ((∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ↔
          z ≫ UnifPre.gFK (R := V) (G := G') F =
            spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left) := by
      intro h₀
      have hp : ∀ i, (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left) ≫ (pG.pr i).left =
          jptN xT F n m i := fun i => by
        rw [Category.assoc, zV_pr, ← Category.assoc, coef_cpy, jptN]
      refine ⟨fun h => pow_ext pG _ _ ?_ fun i => ?_, fun h i => ?_⟩
      · have hg : UnifPre.gFK (R := V) (G := G') F ≫ G'.hom =
            (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left ≫
              (TFK (R := V) F).hom ≫ jK V := by
          rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, Over.w]
          exact congrArg (· ≫ jK V) (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G')))
        rw [Category.assoc, hg, ← Category.assoc, h₀, Category.assoc _ (zV pG xT m).left, Over.w (zV pG xT m)]
        show spMap _ ≫ spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)) =
          spMap _ ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) ≫ 𝟙 _
        simp only [spMap, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rw [JetTr.jetCoef_alg, ← IsScalarTower.algebraMap_eq]
      · rw [hp, Category.assoc, h]
      · rw [← Category.assoc, h, hp]
    have core := fun hzg => core_iff (pr := fun i => (pG.pr i).left) hM hM' PU.wL PU.wL_gen (τ₁ m) (g₁ m) (cpy V n d m)
      (zV_pr pG xT m) (τ m) (hτ m) (hv m) (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m))
      (UnifPre.gFK (R := V) (G := G') F) z hzg q
      (genCast (congrArg RigLB.L P.bundle).symm _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)))
      (fun y J hJ => (val_cast_prod t _ _ _ _ _ q _ y J hJ).trans (Finset.prod_congr rfl fun i _ => by
        rw [coef_cpy]
        have := val_along hM _ _ _ _ (el m) (jcN V F d n m i) y J hJ
        rw [Category.comp_id] at this
        exact congrArg (· ^ q) this.symm)) σ' (toΓ _ (psJet m f))
    constructor
    · rintro ⟨a, b, h₀, h₁, h₂, h₃, h₄⟩
      have hzg := (pts h₀).1 h₁
      exact ⟨h₀, hzg, (core hzg).1 ⟨a, b, h₂, (corr_genCast _ _ _).1 h₃, h₄⟩⟩
    · rintro ⟨h₀, hzg, h⟩
      obtain ⟨a, b, h₂, h₃, h₄⟩ := (core hzg).2 h
      exact ⟨a, b, h₀, (pts h₀).2 hzg, h₂, (corr_genCast _ _ _).2 h₃, h₄⟩

end GlobalTheory.PowGerm
