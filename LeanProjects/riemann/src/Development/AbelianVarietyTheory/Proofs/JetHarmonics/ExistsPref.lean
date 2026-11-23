import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameBiextId

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkRel

section Pref
variable {X Y Z : Scheme.{0}} (L : LB X) (j : L.ι)

def Pref (z : Z) (J : (Z ⟶ X) → L.ι) : Prop := Good L z J ∧ ∀ ψ : Z ⟶ X, ψ z ∈ L.U j → J ψ = j

theorem exists_pref (hL : L.IsLB) (z : Z) : ∃ J, Pref L j z J := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := {ψ : Z ⟶ X // ψ z ∈ L.U j}) (fun ψ => ψ.1) (fun _ => j)
    (fun _ _ _ => rfl) (fun ψ => ψ.2)
  exact ⟨J, hJ, fun ψ h => e ⟨ψ, h⟩⟩

variable {L j}

theorem val_pref {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Pref L j z J) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (h : r z ∈ LB.wchart L φ (fun _ => j)) :
    (val t r z J).val = gs r z (LB.wchart L φ (fun _ => j)) (t.s (fun _ => j)).val := by
  rw [val_of t r z J (fun _ => j) (fun k => hJ.2 _ (Set.mem_iInter.1 h k))]
  exact (gs_unit r z _ h _).symm

theorem val_fnVal {A : Type} [CommRing A] {z : Sp A} {J : (Sp A ⟶ X) → L.ι} (hJ : Pref L j z J) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp A ⟶ Y)
    (h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j)) :
    (val t r z J).val = cst (𝟙 _) z (JetSer.fnVal r (LB.wchart L φ (fun _ => j)) (t.s (fun _ => j)).val) :=
  (val_pref hJ t r (h trivial)).trans ((JetSer.valSer_germ_fnVal r _ h z _).symm.trans
    (gs_eq (𝟙 _) z ⊤ trivial _).symm)

end Pref

variable {V : Type} [CommRing V]

theorem aug_surj {κ : Type} (m : ℕ) (y : Sp (Jet V κ m)) :
    ∃ y₀ : Sp V, spMap ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) y₀ = y := by
  have hs : Function.Surjective ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) :=
    fun a => ⟨algebraMap V _ a, (jetAug : Jet V κ m →ₐ[V] V).commutes a⟩
  have hy : (y : PrimeSpectrum (Jet V κ m)) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) : Set (Jet V κ m)) := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.aeval (fun _ => (0 : V)) P = 0 := ha
    have h1 : P ∈ orig V κ := FBIdPh.mem_orig_of_cc P (by simpa using h0)
    refine PrimeSpectrum.isPrime y |>.mem_of_pow_mem (m + 1) ?_
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h1 _)]
    exact Ideal.zero_mem _
  rw [← range_comap_of_surjective _ _ hs] at hy
  exact hy

theorem mem_of_aug {G : Over (Sp V)} [GrpObj G] {κ : Type} {m : ℕ} (p : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (hp : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V κ m →ₐ[V] V) ≫ p = 1) (U : G.left.Opens)
    (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) (y : Sp (Jet V κ m)) : p.left y ∈ U := by
  obtain ⟨y₀, rfl⟩ := aug_surj m y
  have e : spMap ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) ≫ p.left =
      (toUnit (overAt (𝟙 (Sp V)) V)).left ≫ η[G].left := congrArg (fun q => q.left) hp
  have h : ((toUnit (overAt (𝟙 (Sp V)) V)).left ≫ η[G].left) y₀ ∈ U := hU trivial
  rw [← e] at h
  exact h

theorem comp_psum {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (ρ : T' ⟶ T)
    (xs : Fin n → (T ⟶ G)) (h : ∀ i, ρ ≫ xs i = 1) (I : Finset (Fin n)) : ρ ≫ psum G xs I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one ρ
  | cons a l ih =>
    refine (MonObj.comp_mul _ _ _).trans ?_
    rw [h a, _root_.one_mul]
    exact ih

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)} {d : ℕ}
  {xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {j : t.PP.L.ι}

theorem mem_frame (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xT m = 1)
    (hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j) (m : ℕ) (y : Sp (Jet V (Fin 2 × Fin d) m)) :
    y ∈ LB.wchart t.PP.L (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)])
      (fun _ => j) := by
  have h : ∀ i : Fin 2, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 2 × Fin d) m →ₐ[V] V) ≫
      jptG t (𝟙 (Sp V)) d xT m i = 1 := by
    intro i
    have e : (jetAug : Jet V (Fin 2 × Fin d) m →ₐ[V] V).comp (jetCopy d m i) = jetAug := by
      apply jet_hom_ext
      rintro ⟨i0, l⟩
      simp only [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, jetAug, liftJet,
        Ideal.Quotient.liftₐ_apply]
      simp
    rw [jptG, ← Category.assoc, homAt_comp, e, hz]
  refine Set.mem_iInter.2 fun I => ?_
  exact mem_of_aug _ (comp_psum _ _ (fun i => by fin_cases i; exacts [h 0, h 1]) I.down) _ hj y

theorem ee_eps (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xT m = 1)
    (hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j) {eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m} {ε : PS V 2 d}
    (hε : IsEps t xT eT j ε) {n m : ℕ} {y : (jOG (𝟙 (Sp V)) d m n).left} {J} (hJ : Pref t.PP.L j y J)
    (u v : Q V d n) : VV m y (E2 ε u v) = (ee xT eT y J u v).val := by
  have hfun : ((eT m).s (fun _ => j)).val = ((Sp (Jet V (Fin 2 × Fin d) m)).presheaf.map (homOfLE (le_top :
      LB.wchart t.PP.L (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)])
      (fun _ => j) ≤ ⊤)).op).hom (toΓ _ (psJet m ε)) := by
    refine fn_ext fun w hw => ?_
    obtain ⟨I, hI⟩ := exists_pref t.PP.L j t.PP.isLB (Z := Sp (Jet V (Fin 2 × Fin d) m)) w
    exact (val_pref hI (eT m) (𝟙 _) hw).symm.trans ((hε m w I hI.1
      (fun k => hI.2 _ (Set.mem_iInter.1 hw k))).trans (gs_res (𝟙 _) w le_top hw _).symm)
  have hm := mem_frame hz hj m ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u, v])).left y)
  refine Eq.symm ((val_pref hJ (eT m) _ hm).trans ((congrArg _ hfun).trans ((gs_res _ y le_top hm _).trans ?_)))
  rw [VV, E2, ← jQ_psJet]
  refine Eq.trans ?_ (cst_comp (𝟙 _) (jQ m ![u, v] : Jet V (Fin 2 × Fin d) m →+* Jet V (Fin n × Fin d) m) y _)
  rw [Category.id_comp]; rfl

theorem psJet_eq {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    psJet m f = JetSer.toJet m f := congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)

theorem rep_PP {x : JetSer.Fam t.G (Fin d)} (hM : Match (oneCol d) xT x) {n : ℕ} (u : Q V d n) :
    JetSer.Rep x u.1 (fun m => LinkLaw.toAt _ ≫ PP m xT u) := by
  refine ⟨u.2, fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  refine ⟨(AlgHom.id V _).comp ((jQ m ![u]).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)),
    fun l => ?_, ?_⟩
  · show jQ m ![u] (e (Chart.zR m l)) = _
    rw [he1, jQ_X]
    exact psJet_eq m _
  · have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin n × Fin d) m)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact Spec.map_id _
    have := LinkLaw.read_match (xT m) (x m) e he2 (jQ m ![u]) (AlgHom.id V _)
    rw [hid, Category.comp_id] at this
    exact this

theorem cub_ser {x : JetSer.Fam t.G (Fin d)} (hM : Match (oneCol d) xT x) {f : PS V 3 d}
    (hf : JetSer.IsSer3 x _ (t.cub.t.s (fun _ => j)).val f) {n m : ℕ} {y : (jOG (𝟙 (Sp V)) d m n).left} {J}
    (hJ : Pref t.PP.L j y J) (u v w : Q V d n) :
    VV m y (E3 f u v w) = (cubV t.cub y J (PP m xT u) (PP m xT v) (PP m xT w)).val := by
  have h := hf n _ _ _ _ _ _ (rep_PP hM u) (rep_PP hM v) (rep_PP hM w) m
  have e : (lift (LinkLaw.toAt _ ≫ PP m xT u) (lift (LinkLaw.toAt _ ≫ PP m xT v) (LinkLaw.toAt _ ≫ PP m xT w))).left =
      (lift (PP m xT u) (lift (PP m xT v) (PP m xT w))).left := by
    rw [← comp_lift, ← comp_lift]
    exact Category.id_comp _
  replace h := (congrArg (fun r : Sp (Jet V (Fin n × Fin d) m) ⟶ _ =>
    ⊤ ≤ r ⁻¹ᵁ _ ∧ JetSer.fnVal r _ _ = JetSer.toJet m _) e).mp h
  refine Eq.trans ?_ (val_fnVal (φ := thφ t.G (x3 t.G)) (ε := thε) hJ t.cub.t _ h.1).symm
  rw [VV, formalSeriesValueAtThreePoints_eq_ev, psJet_eq]
  exact congrArg _ h.2.symm

theorem two_ser {x : JetSer.Fam t.G (Fin d)} (hM : Match (oneCol d) xT x) {K : Type} [Fintype K]
    {φ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ} (g : LB.Gen (LB.LinComb t.PP.L φ ε)) {f : PS V 2 d}
    (hf : JetSer.IsSer2 x _ (g.s (fun _ => j))⁻¹.val f) {n m : ℕ} {y : (jOG (𝟙 (Sp V)) d m n).left} {J}
    (hJ : Pref t.PP.L j y J) (u v : Q V d n) :
    VV m y (E2 f u v) = (val₂ g y J (PP m xT u) (PP m xT v))⁻¹.val := by
  have h := hf n _ _ _ _ (rep_PP hM u) (rep_PP hM v) m
  have e : (lift (LinkLaw.toAt _ ≫ PP m xT u) (LinkLaw.toAt _ ≫ PP m xT v)).left =
      (lift (PP m xT u) (PP m xT v)).left := by
    rw [← comp_lift]
    exact Category.id_comp _
  replace h := (congrArg (fun r : Sp (Jet V (Fin n × Fin d) m) ⟶ _ =>
    ⊤ ≤ r ⁻¹ᵁ _ ∧ JetSer.fnVal r _ _ = JetSer.toJet m _) e).mp h
  refine Eq.trans ?_ ((val_fnVal hJ (LB.invGen t.PP.L φ ε g) _ h.1).symm.trans (congrArg Units.val (val_inv _ _)))
  rw [VV, formalSeriesValueAtTwoPoints_eq_ev, psJet_eq]
  exact congrArg _ h.2.symm

theorem VV_ext_pref (j : t.PP.L.ι) {n : ℕ} {f g : PS V n d}
    (h : ∀ m (y : (jOG (𝟙 (Sp V)) d m n).left) J, Pref t.PP.L j y J → VV m y f = VV m y g) : f = g :=
  ps_ext fun m => cst_ext fun y => by
    obtain ⟨J, hJ⟩ := exists_pref t.PP.L j t.PP.isLB (Z := (jOG (𝟙 (Sp V)) d m n).left) y
    exact h m y J hJ

theorem prod_ad (a : 𝓞 E) (U : Type) [CommGroup U] (h : ((t.G ⊗ t.G).left ⟶ t.G.left) → U) :
    ∏ i, h (Sum.elim (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
        (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) i) ^
      Sum.elim (Sum.elim (cε 2) (fun I => -cε 2 I)) rosatiε i = 1 := by
  have r := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) h
  rw [lift_fst_snd] at r
  have r' : ∏ i, h (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a)) i) ^ rosatiε i = _ :=
    (Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ rosatiε i) (Category.id_comp _).symm).trans r
  have c₁ := prod_cube₂ (fst t.G t.G) (snd t.G t.G ≫ t.act.act (H.bar a)) h
  have c₂ := prod_neg _ _ (prod_cube₂ (fst t.G t.G ≫ t.act.act a) (snd t.G t.G) h)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) c₁ c₂) r').trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem linkRel : LinkRelSt := by
  intro E _ _ _ H V _ _ t hs d BT tg xT eT wPT hc hf hP x hx hM j hj u hu B hB ε hε
  letI := H.starRing
  obtain ⟨hlaw, hact⟩ := LinkLaw.linkLaw E H V t d BT tg xT eT wPT hc hf hP x hx hM
  obtain ⟨-, -, hL, hMp, -⟩ := JetRoad.jetRoad
  have R := JetSer.Related.refl B
  have eF : BT.G.F = B.G.F := (hL V t.G d x hx).2 _ _ hlaw hB.law
  have eA : ∀ a, BT.A.act a = B.A.act a := fun a => by
    have := t.act.hom a
    exact (hMp V t.G t.G d x x hx hx (t.act.act a) (IsMonHom.one_hom _)).unique (hact a) (hB.map a)
  have c : ∀ {n : ℕ} (i : Fin n), comp1 (pt V (n := 1) d 0) (pt V (n := n) d i) = pt V d i :=
    fun i => TB.WickVanishing.gt_comp1_pt _ (TB.WickVanishing.gp_pt i)
  have hE : ∀ {n m : ℕ} {y : (jOG (𝟙 (Sp V)) d m n).left} {J}, Pref t.PP.L j y J → ∀ p q : Q V d n,
      VV m y (E2 ε p q) = (ee xT eT y J p q).val := fun hJ p q => ee_eps hc.zero hj hε hJ p q
  have g2 : ∀ f : PS V 2 d, ev (n := 2) ![pt V d 0, pt V d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  have g3 : ∀ f : PS V 3 d, ev (n := 3) ![pt V d 0, pt V d 1, pt V d 2] f = f := fun f =>
    (formalSeriesValueAtThreePoints_eq_ev f (gen 0) (gen 1) (gen 2)).symm.trans (formalSeriesValueAtThreePoints_genericPoints f)
  have z2 : ∀ {n : ℕ} (f : PS V 2 d), ev (n := 1) ![0, pt V d 0] f = 1 → E2 f (0 : Q V d n) 0 = 1 := by
    intro n f h
    have := congrArg (sb (![0] : Fin 1 → Q V d n)) ((formalSeriesValueAtTwoPoints_eq_ev f 0 (gen 0)).trans h)
    rwa [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, sq_gen, map_one] at this
  refine ⟨R.inv, ?_, ?_, fun i => (congrFun eF i).trans (R.law i), fun a => (eA a).trans (R.act a), ?_, ?_, ?_,
    fun a => ?_⟩
  · have z : E3 BT.ph1 (0 : Q V d 1) 0 (gen 0) = 1 := by
      have := congrArg (sb (![0, gen 0] : Fin 2 → Q V d 1)) ((formalSeriesValueAtThreePoints_eq_ev BT.ph1 0 (gen 0) (gen 1)).trans BT.cocycleLeft_zero_fst)
      rwa [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, sq_gen, sq_gen, map_one] at this
    refine (formalSeriesValueAtTwoPoints_eq_ev ε 0 (gen 0)).symm.trans (VV_ext_pref j fun m y J hJ => ?_)
    have k := frame_biext_dictionary_first_partial_law hJ.1 hf (0 : Q V d 1) 0 (gen 0)
    rw [z, op0, PP_zero hc, (isCub_cubV t.cub hJ.1).face, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at k
    rw [hE hJ, k]
  · have z : E3 BT.ph2 (gen 0 : Q V d 1) 0 0 = 1 := by
      have := congrArg (sb (![gen 0, 0] : Fin 2 → Q V d 1)) ((formalSeriesValueAtThreePoints_eq_ev BT.ph2 (gen 0) 0 (gen 1)).trans BT.cocycleRight_zero_snd)
      rwa [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, sq_gen, sq_gen, map_one] at this
    refine (formalSeriesValueAtTwoPoints_eq_ev ε (gen 0) 0).symm.trans (VV_ext_pref j fun m y J hJ => ?_)
    have k := frame_biext_dictionary_second_partial_law hJ.1 hf (gen 0 : Q V d 1) 0 0
    rw [z, op0, PP_zero hc, (isCub_cubV t.cub hJ.1).face₂, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at k
    rw [hE hJ, k]
  · have : E3 BT.ph1 (gen 0 : Q V d 3) (gen 1) (gen 2) * E2 ε (op (FQ BT.G) (gen 0) (gen 1)) (gen 2) =
        E3 B.ph1 (gen 0) (gen 1) (gen 2) * (E2 ε (gen 0) (gen 2) * E2 ε (gen 1) (gen 2)) :=
      VV_ext_pref j fun m y J hJ => by
        simp only [VV_mul, frame_biext_dictionary_first_partial_law hJ.1 hf, hE hJ, cub_ser hM hB.ph1 hJ, ← Units.val_mul]
        refine congrArg Units.val (Additive.ofMul.injective ?_)
        simp only [ofMul_mul, ofMul_inv]
        abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, gen_val, c, g3] using this
  · have : E3 BT.ph2 (gen 0 : Q V d 3) (gen 1) (gen 2) * E2 ε (gen 0) (op (FQ BT.G) (gen 1) (gen 2)) =
        E3 B.ph1 (gen 0) (gen 1) (gen 2) * (E2 ε (gen 0) (gen 1) * E2 ε (gen 0) (gen 2)) :=
      VV_ext_pref j fun m y J hJ => by
        simp only [VV_mul, frame_biext_dictionary_second_partial_law hJ.1 hf, hE hJ, cub_ser hM hB.ph1 hJ, ← Units.val_mul]
        refine congrArg Units.val (Additive.ofMul.injective ?_)
        simp only [ofMul_mul, ofMul_inv]
        abel
    rw [hB.ph2]
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, gen_val, c, g3] using this
  · have : E2 BT.sy (gen 0 : Q V d 2) (gen 1) * E2 ε (gen 0) (gen 1) = E2 ε (gen 1) (gen 0) :=
      VV_ext_pref j fun m y J hJ => by
        simp only [VV_mul, dict_sy hJ.1 hf, hE hJ, ← Units.val_mul, inv_mul_cancel_right]
    rw [hB.sy, ev_one, _root_.one_mul]
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, gen_val, g2] using this
  · obtain ⟨wL, hw, hU⟩ := hf.ad a
    obtain ⟨c₀, hc₀⟩ := exists_const t.PP.L t.PP.isLB (t.G ⊗ t.G).hom hs
      (LB.mulGen t.PP.L _ _ _ _ wL (u a)) (mulGen_isGen _ _ _ _ _ _ _ hw (hu a).1) (prod_ad a)
    have : E2 (BT.ad a) (gen 0 : Q V d 2) (gen 1) * E2 ε (gen 0) (ac (AQ BT.A (star a)) (gen 1)) =
        E2 (B.ad a) (gen 0) (gen 1) * E2 ε (ac (AQ BT.A a) (gen 0)) (gen 1) :=
      VV_ext_pref j fun m y J hJ => by
        obtain ⟨U, h₁, h₂⟩ := hU m
        have dA : ∀ p q : Q V d 2, VV m y (E2 (BT.ad a) p q) = (val₂ wL y J (PP m xT p) (PP m xT q) *
            ee xT eT y J (ac (AQ BT.A a) p) q * (ee xT eT y J p (ac (AQ BT.A (star a)) q))⁻¹).val :=
          dict_ad hJ.1 a wL U h₁ h₂
        have dB := two_ser hM (u a) (hB.ad a) hJ
        have k : ∀ p q : jOG (𝟙 (Sp V)) d m 2 ⟶ t.G, (val₂ wL y J p q * val₂ (u a) y J p q).val =
            gs (jOG (𝟙 (Sp V)) d m 2).hom y ⊤ c₀ := fun p q => by
          have := hc₀ _ (lift p q).left y J hJ.1
          rw [val_mul hJ.1, Over.w] at this
          exact this
        have a₀ := dA 0 0
        have b₀ := dB 0 0
        rw [z2 _ (BT.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right] at a₀
        rw [z2 _ (B.adjoint_zero_fst a), VV_one] at b₀
        have k₁ := Units.ext ((k (PP m xT (gen 0)) (PP m xT (gen 1))).trans (k (PP m xT 0) (PP m xT 0)).symm)
        rw [Units.ext a₀.symm (v := 1), inv_eq_one.1 (Units.ext b₀.symm (v := 1)), _root_.mul_one] at k₁
        simp only [VV_mul, dA, dB, hE hJ, ← Units.val_mul, inv_mul_cancel_right, eq_inv_of_mul_eq_one_left k₁]
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val, c, g2] using this

end GlobalTheory.LinkRel
