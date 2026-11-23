import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup

noncomputable section

namespace GlobalTheory.ArcBasisIndep

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ConstLie GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

section Transport

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstFam

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {f : R₀ →+* R} {φ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {e : D₀.X → D.X}

theorem isZero_iff {T : Over (Sp R)} (g : GtPt D T) :
    g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem gtComb_unique {m : ℕ} {cf : Fin m → R} {u : Fin m → GtPt D (epsR R)} {ν ν' : GtPt D (epsR R)}
    (h : GtComb cf u ν) (h' : GtComb cf u ν') : ν = ν' := by
  obtain ⟨s, p, hs, p0, ps, rfl⟩ := h
  obtain ⟨s', p', hs', p0', ps', rfl⟩ := h'
  obtain rfl : s = s' := funext fun i => isPull_unique (T := epsR R) (T' := epsR R)
    (k := Over.homMk (spMap (epsScaleR (cf i))) (LieCombBaseChange.epsScale_over _)) (hs i) (hs' i)
  have : ∀ i, p i = p' i := fun i => by
    induction i using Fin.induction with
    | zero =>
      obtain ⟨a, b⟩ := (isZero_iff _).1 p0
      obtain ⟨a', b'⟩ := (isZero_iff _).1 p0'
      exact pt_ext (a.trans a'.symm) fun χ y J hJ => (b χ y J hJ).trans (b' χ y J hJ).symm
    | succ i ih => exact isAdd_unique (ps i) (ih ▸ ps' i)
  exact this _

section
variable {T : Over (Sp R)} {T₀ : Over (Sp R₀)} {h : T.left ⟶ T₀.left}

theorem tr_isZero (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (he : Function.Surjective e)
    (hh : h ≫ T₀.hom = T.hom ≫ spMap f) {g : GtPt D T} {g₀ : GtPt D₀ T₀} (r : Tr w e h g g₀) (h₀ : g₀.IsZero) :
    g.IsZero := by
  let ρ : Over.mk (T.hom ≫ spMap f) ⟶ T₀ := Over.homMk h hh
  have r₁ : pushHom gp T g.b = ρ ≫ g₀.b := Over.OverMorphism.ext ((r 0).1 2)
  have hb : g.b = 1 := ConstGrp.push_injective gp T (by
    rw [r₁, map_one, ((isZero_iff _).1 h₀).1, MonObj.comp_one])
  refine (isZero_iff _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := exists_good' D₀.P.isLB z
  have b := (r x).2 _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at b
  rw [prod_pt _ _ (wVal w z J J'), (val_corr hJ (h₀.2 x) h).trans (val_one _)] at b
  simp only [cv]
  generalize val (g.s (e x)) (𝟙 _) z J' = s at b ⊢
  rw [hb, _root_.mul_one] at b
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul b
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) -k

theorem tr_isAdd (hG : GlobalFnsSt) (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (hw : w.IsGen)
    (he : Function.Surjective e) (hh : h ≫ T₀.hom = T.hom ≫ spMap f) {g g' g'' : GtPt D T}
    {g₀ g₀' g₀'' : GtPt D₀ T₀} (r : Tr w e h g g₀) (r' : Tr w e h g' g₀') (r'' : Tr w e h g'' g₀'')
    (h₀ : g₀.IsAdd g₀' g₀'') : g.IsAdd g' g'' := by
  let ρ : Over.mk (T.hom ≫ spMap f) ⟶ T₀ := Over.homMk h hh
  have r₁ : pushHom gp T g.b = ρ ≫ g₀.b := Over.OverMorphism.ext ((r 0).1 2)
  have r₁' : pushHom gp T g'.b = ρ ≫ g₀'.b := Over.OverMorphism.ext ((r' 0).1 2)
  have r₁'' : pushHom gp T g''.b = ρ ≫ g₀''.b := Over.OverMorphism.ext ((r'' 0).1 2)
  have hc : ∀ x, pushHom gp T (cP D T (e x)) = ρ ≫ cP D₀ _ x := fun x => Over.OverMorphism.ext ((r x).1 1)
  have hb : g''.b = g.b * g'.b := ConstGrp.push_injective gp T (by
    rw [map_mul, r₁, r₁', r₁'', h₀.1]; exact MonObj.comp_mul _ _ _)
  refine (TorusModel.isAdd_iff _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := exists_good' D₀.P.isLB z
  have a := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub ρ hJ _ _ _))).symm.trans
    ((val_corr hJ (h₀.2 x) ρ.left).trans (val_mul hJ _ _ _))
  have c := ConstGrp.cubV_push gp hG D.P.isAb D₀.cub D.cub ((isGen_iff w).1 hw) (cP D T (e x)) g.b g'.b hJ hJ'
    (wVal w z J J') (fun _ => rfl)
  rw [hc, r₁, r₁'] at c
  have b := (r x).2 _ (𝟙 _) z J J' hJ hJ'
  have b' := (r' x).2 _ (𝟙 _) z J J' hJ hJ'
  have b'' := (r'' x).2 _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at b b' b''
  rw [prod_pt _ _ (wVal w z J J')] at b b' b''
  have a' := (congrArg₂ (fun a b : (T.left.presheaf.stalk z)ˣ => a * b) b'' c).symm.trans
    (a.trans (congrArg₂ (fun a b : (T.left.presheaf.stalk z)ˣ => a * b) b b'))
  beta_reduce at a'
  simp only [cv, th]
  generalize val (g''.s (e x)) (𝟙 _) z J' = s'' at a' ⊢
  rw [hb, ← _root_.mul_assoc (cP D T (e x))] at a'
  apply Additive.ofMul.injective
  have a'' := congrArg Additive.ofMul a'
  simp only [ofMul_mul, ofMul_inv] at a'' ⊢
  linear_combination (norm := abel) a''

theorem tr_of_isPull {T₁ : Over (Sp R₀)} {k : T₀.left ⟶ T₁.left} {g : GtPt D T} {g₀ : GtPt D₀ T₀}
    {g₁ : GtPt D₀ T₁} (r : Tr w e h g g₀) (h₀ : GtPt.IsPull k g₁ g₀) : Tr w e (h ≫ k) g g₁ := fun x =>
  ⟨fun i => by
    have := (TorusCoord.comp_eq_of_left g₁.b g₀.b k (𝟙 _) (h₀.1.symm.trans (Category.id_comp _).symm)).1 x i
    rw [Category.assoc, this, Category.id_comp, ← TorusCoord.gtφT_eq]
    exact (r x).1 i,
  fun Z s z J J' hJ hJ' => by
    rw [← Category.assoc, ← val_pull hJ, ← val_corr hJ (h₀.2 x)]
    exact (r x).2 Z s z J J' hJ hJ'⟩

end

end Transport

section Same

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstFam Formalism.L2.Pj

variable {A : Type} [CommRing A] [IsDomain A] {D₀ D₁ : DegPre A} (p : IsPullDeg (RingHom.id A) D₀ D₁)

def Cor (ν' : GtPt D₁ (epsR A)) (ν : GtPt D₀ (epsR A)) : Prop := Tr p.w p.xe.symm (𝟙 (epsR A).left) ν' ν

theorem grp : IsGrpPullback D₁.P.A D₀.P.A (spMap (RingHom.id A)) (prj p) :=
  have := p.e_hom
  ((isGrpPullback_of_iso p.e).comp (isGrpPullback_pullback D₀.P.A (specOf (RingHom.id A)))).congr
    (Category.id_comp _) rfl

omit [IsDomain A] in
theorem over_id : 𝟙 (epsR A).left ≫ (epsR A).hom = (epsR A).hom ≫ spMap (RingHom.id A) :=
  (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))

variable {p}

theorem cor_of_letBC {ν' : GtPt D₁ (epsR A)} {ν : GtPt D₀ (epsR A)} (h : LetBC p ν ν') : Cor p ν' ν := by
  have e : spMap (dualMap (RingHom.id A)) = 𝟙 (epsR A).left := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun x => ?_)) (Spec.map_id _)
    ext <;> simp [dualMap]
  unfold Cor
  rw [← e]
  intro x
  obtain ⟨χ, rfl⟩ := p.xe.surjective x
  rw [p.xe.symm_apply_apply]
  obtain ⟨hψ, H⟩ := h.2 χ
  exact ⟨hψ, fun Z r z J J' hJ hJ' =>
    CubTransport.val_pmaps hψ ((maps_iff _ _ _ _ _ _ _ _ _ (fun _ => rfl)).1 H) r hJ hJ'⟩

variable (p) in
theorem exists_cor_left (hG : GlobalFnsSt) (ν : GtPt D₀ (epsR A)) : ∃ ν', Cor p ν' ν :=
  exists_tr_down hG (grp p) p.w_gen p.xe.symm
    (fun y => by have := p.c_pr (p.xe.symm y); rwa [p.xe.apply_symm_apply] at this) _ over_id ν

variable (p) in
theorem exists_cor_right (hG : GlobalFnsSt) (ν' : GtPt D₁ (epsR A)) : ∃ ν, Cor p ν' ν :=
  exists_tr_up hG (grp p) p.w_gen p.xe.symm
    (fun y => by have := p.c_pr (p.xe.symm y); rwa [p.xe.apply_symm_apply] at this) (T := epsR A) _
    ((Category.id_comp _).symm.trans over_id) ν'

theorem Cor.left_unique {ν' ξ' : GtPt D₁ (epsR A)} {ν : GtPt D₀ (epsR A)} (h : Cor p ν' ν) (h' : Cor p ξ' ν) :
    ν' = ξ' :=
  (isPull_unique (k := 𝟙 (epsR A)) (Tr.cancel (grp p) p.xe.symm.surjective h h (𝟙 _) (Category.id_comp _))
    (Tr.cancel (grp p) p.xe.symm.surjective h h' (𝟙 _) (Category.id_comp _)))

theorem Cor.right_unique {ν' : GtPt D₁ (epsR A)} {ν ξ : GtPt D₀ (epsR A)} (h : Cor p ν' ν) (h' : Cor p ν' ξ) :
    ν = ξ :=
  Tr.inj h h' (𝟙 _) (Category.id_comp _) rfl fun _ _ _ _ => rfl

theorem Cor.gtComb_iff (hG : GlobalFnsSt) {m : ℕ} (cf : Fin m → A) {u' : Fin m → GtPt D₁ (epsR A)}
    {u : Fin m → GtPt D₀ (epsR A)} {ν' : GtPt D₁ (epsR A)} {ν : GtPt D₀ (epsR A)} (hu : ∀ i, Cor p (u' i) (u i))
    (h : Cor p ν' ν) : GtComb cf u' ν' ↔ GtComb cf u ν := by
  choose Φ hΦ using exists_cor_left p hG
  have key : ∀ ξ, GtComb cf u ξ → GtComb cf u' (Φ ξ) := by
    rintro _ ⟨s, q, hs, q0, qs, rfl⟩
    refine ⟨fun i => Φ (s i), fun i => Φ (q i), fun i => ?_,
      tr_isZero (grp p) p.xe.symm.surjective over_id (hΦ _) q0,
      fun i => tr_isAdd hG (grp p) p.w_gen p.xe.symm.surjective over_id (hΦ _) (hΦ _) (hΦ _) (qs i), rfl⟩
    exact Tr.cancel (grp p) p.xe.symm.surjective (hu i) (tr_of_isPull (hΦ (s i)) (hs i))
      (Over.homMk (spMap (epsScaleR (cf i))) (LieCombBaseChange.epsScale_over _))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨fun H => ?_, fun H => (hΦ ν).left_unique h ▸ key ν H⟩
  obtain ⟨ξ, hξ⟩ := exists_gtComb cf u
  have e := gtComb_unique (key ξ hξ) H
  exact (e ▸ hΦ ξ : Cor p ν' ξ).right_unique h ▸ hξ

theorem Cor.smulPt (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O] [Module O D₁.X] [Module O D₀.X]
    (oa₁ : D₁.OAct O) (oa₀ : D₀.OAct O) (hl : ∀ (a : O) x, p.xe (a • x) = a • p.xe x)
    (ho : ∀ a, (oa₁.onB.act a).left ≫ prj p = prj p ≫ (oa₀.onB.act a).left) (a : O)
    {ν' : GtPt D₁ (epsR A)} {ν : GtPt D₀ (epsR A)} (h : Cor p ν' ν) :
    Cor p (smulPt hG oa₁ a ν') (smulPt hG oa₀ a ν) := by
  obtain ⟨ξ', hξ⟩ := exists_cor_left p hG (TorusModel.smulPt hG oa₀ a ν)
  have s := Tr.smul hG (grp p) p.w_gen p.xe.symm.surjective oa₁ oa₀
    (fun a x => p.xe.injective (by rw [hl, p.xe.apply_symm_apply, p.xe.apply_symm_apply])) ho a over_id h hξ
    (isSmulPt_smulPt hG oa₀ a ν)
  obtain ⟨b, v⟩ := (isSmulPt_iff hG oa₁ _ _ _).1 s
  obtain rfl : ξ' = TorusModel.smulPt hG oa₁ a ν' :=
    pt_ext (b.trans (smulPt_b hG oa₁ a ν').symm) fun χ y J hJ => (v χ y J hJ).trans (smulPt_val hG oa₁ a ν' χ hJ).symm
  exact hξ

end Same

section Algebra

open Matrix

variable {A : Type} [CommRing A] {g m : ℕ}

theorem coeff_vecMul (N : Matrix (Fin g) (Fin g) A) (w : Fin g → PowerSeries A) (n : ℕ) :
    (fun j => PowerSeries.coeff n ((w ᵥ* N.map (PowerSeries.C (R := A))) j)) =
      (fun j => PowerSeries.coeff n (w j)) ᵥ* N := by
  funext j
  simp [vecMul, dotProduct]

theorem coeff_comb (U : Fin m → Fin g → A) (cf : Fin m → PowerSeries A) (n : ℕ) :
    (fun j => PowerSeries.coeff n ((∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j)) j)) =
      ∑ k, PowerSeries.coeff n (cf k) • U k := by
  funext j
  simp

theorem eig_iff_coeff (N : Matrix (Fin g) (Fin g) A) (r : A) (w : Fin g → PowerSeries A) :
    w ᵥ* N.map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) r • w ↔
      ∀ n, (fun j => PowerSeries.coeff n (w j)) ᵥ* N = r • fun j => PowerSeries.coeff n (w j) := by
  simp only [← coeff_vecMul, funext_iff, PowerSeries.ext_iff, Pi.smul_apply, smul_eq_mul, PowerSeries.coeff_C_mul]
  exact forall_comm

theorem comb_iff_coeff (U : Fin m → Fin g → A) (cf : Fin m → PowerSeries A) (w : Fin g → PowerSeries A) :
    (w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j)) ↔
      ∀ n, (fun j => PowerSeries.coeff n (w j)) = ∑ k, PowerSeries.coeff n (cf k) • U k := by
  simp only [← coeff_comb, funext_iff, PowerSeries.ext_iff]
  exact forall_comm

theorem eig_const_iff (N : Matrix (Fin g) (Fin g) A) (r : A) (z : Fin g → A) :
    (fun j => PowerSeries.C (R := A) (z j)) ᵥ* N.map (PowerSeries.C (R := A)) =
      PowerSeries.C (R := A) r • (fun j => PowerSeries.C (R := A) (z j)) ↔ z ᵥ* N = r • z := by
  simp only [funext_iff, vecMul, dotProduct, map_apply, Pi.smul_apply, smul_eq_mul, ← map_mul, ← map_sum,
    PowerSeries.C_injective.eq_iff]

theorem comb_const_iff (U : Fin m → Fin g → A) (cf : Fin m → A) (z : Fin g → A) :
    ((fun j => PowerSeries.C (R := A) (z j)) =
      ∑ k, PowerSeries.C (R := A) (cf k) • fun j => PowerSeries.C (R := A) (U k j)) ↔ z = ∑ k, cf k • U k := by
  simp only [funext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← map_mul, ← map_sum,
    PowerSeries.C_injective.eq_iff]

theorem eigBasis_powerSeries_iff {I : Type} (M : I → Matrix (Fin g) (Fin g) A) (r : I → A) (U : Fin m → Fin g → A) :
    (∀ w : Fin g → PowerSeries A, (∀ x, w ᵥ* (M x).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (r x) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j)) ↔
    ∀ z : Fin g → A, (∀ x, z ᵥ* M x = r x • z) → ∃! cf : Fin m → A, z = ∑ k, cf k • U k := by
  refine ⟨fun H z hz => ?_, fun H w hw => ?_⟩
  · obtain ⟨cf, h, hu⟩ := H _ fun x => (eig_const_iff _ _ z).2 (hz x)
    refine ⟨fun k => PowerSeries.coeff 0 (cf k), ?_, fun c hc => funext fun k => ?_⟩
    · simpa using (comb_iff_coeff U cf _).1 h 0
    · rw [← hu _ ((comb_const_iff U c z).2 hc)]
      simp
  · choose c hc hu using fun n => H _ fun x => (eig_iff_coeff _ _ w).1 (hw x) n
    refine ⟨fun k => PowerSeries.mk fun n => c n k, (comb_iff_coeff U _ w).2 fun n => ?_,
      fun cf h => funext fun k => PowerSeries.ext fun n => ?_⟩
    · simpa only [PowerSeries.coeff_mk] using hc n
    · rw [PowerSeries.coeff_mk, ← hu n _ ((comb_iff_coeff U cf w).1 h n)]

end Algebra

section Lie

open ReciprocityTheory.ChartRestriction.G.Chart hiding spMap spMap_comp
open Matrix

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_comp (f : G ⟶ G) [IsMonHom f] {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => by rw [Over.comp_left, hu, Over.comp_left, Category.assoc], ?_⟩
  exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) _).trans (by rw [List.map_ofFn]; rfl)

theorem scale_iff (r : R) (w w' : epsR R ⟶ G) :
    w'.left = spMap (epsScaleR r) ≫ w.left ↔ IsLieComb (fun _ : Fin 1 => r) (fun _ => w) w' :=
  ⟨fun h => ⟨fun _ => w', fun _ => h, by simp⟩, fun ⟨u, hu, h⟩ => by rw [h, ← hu 0]; simp⟩

variable [IsLocalRing R] [Smooth G.hom] {g : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
include hv

theorem isTangent_prodPts (z : Fin g → R) : IsTangent (G := G) (prodPts z v) := by
  obtain ⟨n, y, hy⟩ := univChartLoc G
  exact (isTan_iff _).1 (prodPts_tan hy z v fun i => (isTan_iff _).2 (hv.1 i)).1

theorem comb_prodPts_iff {m : ℕ} (a : Fin m → R) (U : Fin m → Fin g → R) (z : Fin g → R) :
    IsLieComb (G := G) a (fun k => prodPts (U k) v) (prodPts z v) ↔ z = ∑ k, a k • U k := by
  obtain ⟨n, y, hy⟩ := univChartLoc G
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  choose tp hp using fun z => prodPts_tan hy z v tv
  have e : ∑ k, a k • tcoord hy (prodPts (U k) v) (tp _) = ∑ j, (∑ k, a k • U k) j • tcoord hy (v j) (tv j) := by
    simp only [hp, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, smul_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_comm
  have hz : IsLieComb z v (prodPts z v) := (isLieComb_iff _ _ _).2 rfl
  refine (comb_iff_coord hy a (fun k => tp (U k)) (tp z)).trans ?_
  rw [e]
  refine (comb_iff_coord hy _ tv (tp z)).symm.trans ?_
  exact ⟨fun q => (hv.2 _ (isTangent_prodPts hv z)).unique hz q, fun q => q ▸ hz⟩

theorem eig_prodPts_iff (f : G ⟶ G) [IsMonHom f] (N : Matrix (Fin g) (Fin g) R)
    (hN : ∀ i, IsLieComb (N i) v (v i ≫ f)) (r : R) (z : Fin g → R) :
    ((prodPts z v : epsR R ⟶ G) ≫ f).left = spMap (epsScaleR r) ≫ (prodPts z v : epsR R ⟶ G).left ↔
      z ᵥ* N = r • z := by
  have h₁ := isLieComb_comp f ((isLieComb_iff z v _).2 rfl)
  simp only [fun i => (isLieComb_iff _ _ _).1 (hN i)] at h₁
  have h₂ := (comb_prodPts_iff hv z N _).2 (Matrix.vecMul_eq_sum z N)
  have e : (prodPts z v : epsR R ⟶ G) ≫ f = prodPts (z ᵥ* N) v :=
    ((isLieComb_iff _ _ _).1 h₁).trans ((isLieComb_iff _ _ _).1 h₂).symm
  refine (scale_iff r _ _).trans ?_
  rw [e]
  exact (comb_prodPts_iff hv (fun _ : Fin 1 => r) (fun _ => z) _).trans (by simp)

end Lie

section ThetaShiftProofs

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.TorusModel Formalism.L2.Pj Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts isLieComb_iff)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] {b : O →+* A} (hG : GlobalFnsSt) {a : ArcIn Dw l β A b}

def IsEig (r : 𝓞 E →+* A) (ν : GtPt a.D₀ (epsR A)) : Prop :=
  letI := H.starRing
  ∀ x : 𝓞 E, GtComb (fun _ : Fin 1 => r x) (fun _ => ν) (smulPt hG a.oa x ν)

def IsEigBasis (r : 𝓞 E →+* A) {m : ℕ} (u : Fin m → GtPt a.D₀ (epsR A)) : Prop :=
  (∀ k, GtTanR (u k) ∧ IsEig hG r (u k)) ∧ ∀ ν, GtTanR ν → IsEig hG r ν → ∃! cf : Fin m → A, GtComb cf u ν

variable [IsLocalRing A] [IsNoetherianRing A] {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
include hG

theorem lieImg_smulPt {ν : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E) :
    letI := H.starRing
    LieImg W (smulPt hG a.oa x ν) (v ≫ W.t.act.act x) := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) (smulPt hG a.oa x ν)
  have s := Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' (isSmulPt_smulPt hG a.oa x ν)
  exact lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)

theorem gtComb_iff_isLieComb {m : ℕ} (cf : Fin m → A) {u : Fin m → GtPt a.D₀ (epsR A)} {ν : GtPt a.D₀ (epsR A)}
    {v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)} {w : epsR (PowerSeries A) ⟶ W.t.G} (hu : ∀ i, LieImg W (u i) (v i))
    (h : LieImg W ν w) : GtComb cf u ν ↔ IsLieComb (fun i => PowerSeries.C (R := A) (cf i)) v w := by
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W m cf u
  refine ⟨fun H => (lin ν v w hu H).1 h, fun H => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_gtComb cf u
  exact eq_of_red W hG ((lin ξ v w hu hξ).2 H) h rfl ▸ hξ

theorem isEig_iff (r : 𝓞 E →+* A) {ν : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) :
    IsEig hG r ν ↔ ∀ x : 𝓞 E,
      (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (r x))) ≫ v.left :=
  forall_congr' fun x => (gtComb_iff_isLieComb hG W _ (fun _ => hv) (lieImg_smulPt hG W hv x)).trans
    (scale_iff _ _ _).symm

include W in
theorem gtTanR_iff (ν : GtPt a.D₀ (epsR A)) {o : GtPt a.D₀ (epsR A)} (ho : GtComb (m := 0) Fin.elim0 Fin.elim0 o) :
    GtTanR ν ↔ GtComb (fun _ : Fin 1 => 0) (fun _ => ν) o := by
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W
  obtain ⟨v, hv, -⟩ := (ex ν).1
  have h₀ := (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W 0 _ _ o Fin.elim0 1 (fun j => j.elim0) ho).2
    ⟨Fin.elim0, fun j => j.elim0, by simp⟩
  rw [(ex ν).2 v hv, isTangent_iff_comb, gtComb_iff_isLieComb hG W _ (fun _ => hv) h₀]
  simp only [map_zero]

theorem isEigBasis_iff (r : 𝓞 E →+* A) {m : ℕ} {u : Fin m → GtPt a.D₀ (epsR A)}
    {v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)} (hu : ∀ i, LieImg W (u i) (v i)) :
    IsEigBasis hG r u ↔ (∀ k, IsTangent (v k) ∧ ∀ x : 𝓞 E,
        (v k ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (r x))) ≫ (v k).left) ∧
      ∀ w, IsTangent w → (∀ x : 𝓞 E,
        (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (r x))) ≫ w.left) →
        ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w := by
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W
  refine (and_congr_left' (forall_congr' fun k =>
    and_congr ((ex _).2 _ (hu k)) (isEig_iff hG W r (hu k)))).trans (and_congr_right fun h => ?_)
  have := W.P.U.smooth
  obtain ⟨g, s, t, M, hs, ht, hc, hM⟩ := exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
  have img : ∀ z ν, GtComb z s ν → LieImg W ν (prodPts (fun j => PowerSeries.C (R := A) (z j)) t) := fun z ν H =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E _ Dw l Xo c O β Y A b a χ W g z s ν t _ (fun i => (hs i).2) H).2 ((isLieComb_iff _ _ _).2 rfl)
  have eig : ∀ (z : Fin g → PowerSeries A) x, ((prodPts z t : epsR _ ⟶ W.t.G) ≫ W.t.act.act x).left =
      spMap (epsScaleR (PowerSeries.C (R := A) (r x))) ≫ (prodPts z t : epsR _ ⟶ W.t.G).left ↔
      z ᵥ* (M x).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (r x) • z := fun z x =>
    have := W.t.act.hom x
    eig_prodPts_iff ht _ ((M x).map (PowerSeries.C (R := A))) (hM x) _ z
  choose U hU using fun k => (hc (u k) (((ex _).2 _ (hu k)).2 (h k).1)).exists
  obtain rfl : v = fun k => prodPts (fun j => PowerSeries.C (R := A) (U k j)) t :=
    funext fun k => (ex _).1.unique (hu k) (img _ _ (hU k))
  refine Iff.trans ?_ ((eigBasis_powerSeries_iff M r U).symm.trans ?_)
  · have key : ∀ z ν, GtComb z s ν → (IsEig hG r ν ↔ ∀ x, z ᵥ* M x = r x • z) ∧
        ∀ cf, GtComb cf u ν ↔ z = ∑ k, cf k • U k := fun z ν H =>
      ⟨(isEig_iff hG W r (img z ν H)).trans (forall_congr' fun x => (eig _ x).trans (eig_const_iff _ _ _)),
        fun cf => (gtComb_iff_isLieComb hG W cf hu (img z ν H)).trans
          ((comb_prodPts_iff ht _ _ _).trans (comb_const_iff U cf z))⟩
    refine ⟨fun H z hz => ?_, fun H ν hν he => ?_⟩
    · obtain ⟨ν, hν⟩ := exists_gtComb z s
      simpa only [(key z ν hν).2] using
        H ν (((ex _).2 _ (img z ν hν)).2 (isTangent_prodPts ht _)) ((key z ν hν).1.2 hz)
    · obtain ⟨z, hz, -⟩ := hc ν hν
      simpa only [(key z ν hz).2] using H z ((key z ν hz).1.1 he)
  · refine ⟨fun H w hw he => ?_, fun H z hz => ?_⟩
    · obtain ⟨z, hz, -⟩ := ht.2 w hw
      obtain rfl := (isLieComb_iff _ _ _).1 hz
      exact (existsUnique_congr fun cf => comb_prodPts_iff ht cf _ z).2 (H z fun x => (eig z x).1 (he x))
    · exact (existsUnique_congr fun cf => comb_prodPts_iff ht cf _ z).1
        (H _ (isTangent_prodPts ht z) fun x => (eig z x).2 (hz x))

theorem arcBasis_iff (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → GtPt a.D₀ (epsR A)) :
    ArcBasis W ρ e ↔ ∀ τ, IsEigBasis hG (ρ τ) (e τ) := by
  refine ⟨fun ⟨v, hv, h⟩ τ => (isEigBasis_iff hG W _ (hv τ)).2 (h τ), fun h => ?_⟩
  choose v hv using fun ν => (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W ν).1.exists
  exact ⟨fun τ k => v (e τ k), fun τ k => hv _, fun τ => (isEigBasis_iff hG W _ fun k => hv _).1 (h τ)⟩

include W in

theorem IsEigBasis.of_cor {O' : Type} [CommRing O'] {β' : O' →+* c.F} {Y' : Model Xo c β'} {b' : O' →+* A}
    {a' : ArcIn Dw l β' A b'} {χ' : Sp (PowerSeries A) ⟶ Y'.X} (W' : Wit Y' a' χ')
    {p : IsPullDeg (RingHom.id A) a.D₀ a'.D₀} (hl : ∀ (x : 𝓞 E) y, p.xe (x • y) = x • p.xe y)
    (ho : letI := H.starRing; ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (a.oa.onB.act x).left)
    {r : 𝓞 E →+* A} {m : ℕ} {u : Fin m → GtPt a.D₀ (epsR A)} {u' : Fin m → GtPt a'.D₀ (epsR A)}
    (hu : ∀ k, Cor p (u' k) (u k)) (h : IsEigBasis hG r u) : IsEigBasis hG r u' := by
  letI := H.starRing
  obtain ⟨o, ho₀⟩ := exists_gtComb (D := a.D₀) (m := 0) Fin.elim0 Fin.elim0
  obtain ⟨o', ho'⟩ := exists_cor_left p hG o
  have ho₁ : GtComb (m := 0) Fin.elim0 Fin.elim0 o' := (Cor.gtComb_iff hG _ (fun i => i.elim0) ho').2 ho₀
  have tan : ∀ ν' ν, Cor p ν' ν → (GtTanR ν' ↔ GtTanR ν) := fun ν' ν q =>
    (gtTanR_iff hG W' ν' ho₁).trans ((Cor.gtComb_iff hG _ (fun _ => q) ho').trans (gtTanR_iff hG W ν ho₀).symm)
  have eig : ∀ ν' ν, Cor p ν' ν → (IsEig hG r ν' ↔ IsEig hG r ν) := fun ν' ν q =>
    forall_congr' fun x => Cor.gtComb_iff hG _ (fun _ => q) (q.smulPt hG a'.oa a.oa hl ho x)
  refine ⟨fun k => ⟨(tan _ _ (hu k)).2 (h.1 k).1, (eig _ _ (hu k)).2 (h.1 k).2⟩, fun ν' ht he => ?_⟩
  obtain ⟨ν, q⟩ := exists_cor_right p hG ν'
  exact (existsUnique_congr fun cf => Cor.gtComb_iff hG cf hu q).2 (h.2 ν ((tan _ _ q).1 ht) ((eig _ _ q).1 he))

end ThetaShiftProofs

end GlobalTheory.ArcBasisIndep

namespace GlobalTheory.ArcBasisIndep

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem arcBasis_indep : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → (∀ (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (b' : O' →+* A) (a' : ArcIn Dw l β' A b') (χ' : Sp (PowerSeries A) ⟶ Y'.X) (W' : Wit Y' a' χ') (p : Out.IsPullDeg (RingHom.id A) a.D₀ a'.D₀) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A)), (∀ (x : 𝓞 E) y, p.xe (x • y) = x • p.xe y) → (letI := H.starRing; ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (a.oa.onB.act x).left) → (∀ τ k, LetBC p (e τ k) (e' τ k)) → ArcBasis W' ρ e') ∧ (∀ (χ' : Sp (PowerSeries A) ⟶ Y.X) (W' : Wit Y a χ'), ArcBasis W' ρ e) ∧ ∀ τ ν (v : epsR (PowerSeries A) ⟶ W.t.G), GtTanR ν → LieImg W ν v → (∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (ρ τ x))) ≫ v.left) → ∃! cf : Fin (Dw.mult τ) → A, GtComb cf (e τ) ν := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e h
  have h' := (arcBasis_iff hG W ρ e).1 h
  exact ⟨fun O' _ β' Y' b' a' χ' W' p e' hl ho hp => (arcBasis_iff hG W' ρ e').2 fun τ =>
      IsEigBasis.of_cor hG W W' hl ho (fun k => cor_of_letBC (hp τ k)) (h' τ),
    fun χ' W' => (arcBasis_iff hG W' ρ e).2 h',
    fun τ ν v hν hv he => (h' τ).2 ν hν ((isEig_iff hG W _ hv).2 he)⟩

end GlobalTheory.ArcBasisIndep
