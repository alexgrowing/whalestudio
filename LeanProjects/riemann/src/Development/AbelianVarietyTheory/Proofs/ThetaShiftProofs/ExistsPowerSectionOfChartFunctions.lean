import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaUnit

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection

def IsPullTerm {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {B₀ : Scheme.{0}} {M₀ : LB B₀}
    (φ : D.P.A.left ⟶ B₀) (w : LB.Iso D.P.L (M₀.pull φ)) (th : M₀.Sec) (t : D.SecB 1 0) : Prop :=
  ∀ (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι) (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB 0) j)
    (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ φ ⁻¹ᵁ M₀.U j₀),
    LB.Coh D.P.L (D.famφB 0) j →
    (φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (t.f j)

def PullsToMul {R : Type} [CommRing R] {X X' : Scheme.{0}} (p : X' ⟶ Sp R) {L : LB X} {L' : LB X'} (F : X' ⟶ X)
    (w : LB.Iso L' (L.pull F)) (V : X.Opens) (s : ∀ j, Γ(X, V ⊓ L.U j)) (r : R) (σ : H0 L' 1) : Prop :=
  ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (V ⊓ L.U j))
    (h₂ : W ≤ (LB.div (L.pull F) L').U (fun _ => j, k))
    (h₃ : W ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)),
    (F.appLE _ _ h₁).hom (s j) = resG _ h₂ (w.s (fun _ => j, k)).val * constFn p W r * resG _ h₃ (σ.f (fun _ => k))

def IsPushGen {X : Scheme.{0}} (G : Over X) (L : LB G.left) (V : X.Opens)
    (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop :=
  θ ∈ secOn L (G.hom ⁻¹ᵁ V) ∧ ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
    s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
      resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)

section General

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem mem_chart_one {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {k : L.ι} (h : r z ∈ L.U k) :
    r z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := Set.mem_iInter.2 fun _ => h

theorem exists_powerSection_of_chartFunctions (s : L.Sec) : ∃ t : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : L.ι), r z ∈ L.U k →
    gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (t.f fun _ => k) = gs r z (L.U k) (s.f k) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => resG X (le j) (s.f (j 0)), fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩,
    fun Z r z k h => gs_res r z (le fun _ => k) (mem_chart_one r z h) _⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((gs_compat s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp [Geo.Tor.trF]

theorem mem_basicOpen_iff_gs {U : X.Opens} (f : Γ(X, U)) {x : X} (hx : x ∈ U) :
    x ∈ X.basicOpen f ↔ IsUnit (gs (𝟙 X) x U f) := by
  rw [gs_eq (𝟙 X) x U hx]
  exact X.mem_basicOpen f x hx

theorem gs_secOn {V : X.Opens} {s : ∀ j, Γ(X, V ⊓ L.U j)} (hs : s ∈ secOn L V) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    {j j' : L.ι} (hV : r z ∈ V) (h : r z ∈ L.U j) (h' : r z ∈ L.U j') :
    gs r z _ (s j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z _ (s j') := by
  have hm : r z ∈ V ⊓ L.U j ⊓ L.U j' := ⟨⟨hV, h⟩, h'⟩
  have e := congrArg (gs r z _) (hs j j')
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm,
    gs_unit _ z (L.U j ⊓ L.U j') ⟨h, h'⟩] at e

theorem res_mem_secOn {V W : X.Opens} (hW : W ≤ V) {s : ∀ j, Γ(X, V ⊓ L.U j)} (hs : s ∈ secOn L V) :
    (fun j => resG X (inf_le_inf_right _ hW) (s j)) ∈ secOn L W := fun j j' => fn_ext fun y hy => by
  have h₁ : (𝟙 X : X ⟶ X) y ∈ W ⊓ L.U j := hy.1
  have h₂ : (𝟙 X : X ⟶ X) y ∈ W ⊓ L.U j' := ⟨hy.1.1, hy.2⟩
  exact ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ h₁ _)).trans
    ((gs_secOn hs (𝟙 X) y (hW hy.1.1) hy.1.2 hy.2).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y (L.U j ⊓ L.U j') ⟨hy.1.2, hy.2⟩ _))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ h₂ _))))))

theorem exists_pull_secOn {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {V : X.Opens}
    (hV : ∀ y, F y ∈ V) {s : ∀ j, Γ(X, V ⊓ L.U j)} (hs : s ∈ secOn L V) : ∃ t : H0 L' 1,
    (∀ y, y ∈ nonzeroLocus t ↔ ∃ j, F y ∈ X.basicOpen (s j)) ∧
    ∀ (R : Type) [CommRing R] (p : X' ⟶ Sp R) (r : R) (σ : H0 L' 1), PullsToMul p F w V s r σ ↔ SecIsMul p r t σ := by
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun j x hx => ⟨hV x, hx⟩
  have ev : ∀ y j, F y ∈ L.U j → gs (𝟙 _) y _ ((F.appLE _ _ (le j)).hom (s j)) = gs F y _ (s j) :=
    fun y j h => (gs_appLE F _ _ (le j) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  obtain ⟨t₀, ht₀⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (s j))
    fun y j j' h h' => (ev y j h).trans ((gs_secOn hs F y (hV y) h h').trans (congrArg _ (ev y j' h').symm))
  obtain ⟨t, ht⟩ := exists_powerSection_of_chartFunctions t₀
  have key : ∀ y j k, F y ∈ L.U j → y ∈ L'.U k → gs F y _ (s j) = (Geo.Tor.gw w (𝟙 _) y j k).val *
      gs (𝟙 X') y (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f fun _ => k) := fun y j k hj hk =>
    (ev y j hj).symm.trans ((ht₀ _ (𝟙 _) y j k hj hk).trans (congrArg _ (ht _ (𝟙 _) y k hk).symm))
  have ev₂ : ∀ (R : Type) [CommRing R] (p : X' ⟶ Sp R) (r : R) (σ : H0 L' 1) (j : L.ι) (k : L'.ι) (W : X'.Opens)
      (h₁ : W ≤ F ⁻¹ᵁ (V ⊓ L.U j)) (h₂ : W ≤ (LB.div (L.pull F) L').U (fun _ => j, k))
      (h₃ : W ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (y : X'), y ∈ W →
      gs (𝟙 _) y W ((F.appLE _ _ h₁).hom (s j)) = gs F y _ (s j) ∧
      gs (𝟙 _) y W (resG _ h₂ (w.s (fun _ => j, k)).val * constFn p W r * resG _ h₃ (σ.f (fun _ => k))) =
        (Geo.Tor.gw w (𝟙 _) y j k).val * (cst (𝟙 _ ≫ p) y r *
          gs (𝟙 X') y (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (σ.f fun _ => k)) :=
    fun R _ p r σ j k W h₁ h₂ h₃ y hy => ⟨(gs_appLE F _ _ h₁ (𝟙 _) y hy _).trans (by rw [Category.id_comp]),
      ((gs_mul (𝟙 _) y W hy _ _).trans (congrArg₂ (· * ·) ((gs_mul (𝟙 _) y W hy _ _).trans (congrArg₂ (· * ·)
        ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)) (gs_constFn p W (𝟙 _) y hy r)))
        (gs_res (𝟙 _) y h₃ hy _))).trans (_root_.mul_assoc _ _ _)⟩
  refine ⟨t, fun y => ⟨fun h => ?_, fun ⟨j, h⟩ => ?_⟩, fun R _ p r σ => ⟨fun h k => ?_, fun h j k W h₁ h₂ h₃ => ?_⟩⟩
  · obtain ⟨k, hk, hu⟩ := (SectionBaseChange.mem_nonzeroLocus t _).1 h
    obtain ⟨k, rfl⟩ : ∃ k', k = fun _ => k' := ⟨k 0, funext fun i => congrArg k (Subsingleton.elim i 0)⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have hj' : F y ∈ V ⊓ L.U j := ⟨hV y, hj⟩
    refine ⟨j, (mem_basicOpen_iff_gs _ hj').2 ((isUnit_gs_iff F y _ hj' _).1 ?_)⟩
    rw [key y j k hj (Set.mem_iInter.1 hk 0)]
    exact (Units.isUnit _).mul hu
  · have hj : F y ∈ V ⊓ L.U j := X.basicOpen_le _ h
    obtain ⟨k, hk⟩ := exists_chart hL' y
    have hu := (isUnit_gs_iff F y _ hj _).2 ((mem_basicOpen_iff_gs _ hj).1 h)
    rw [key y j k hj.2 hk] at hu
    exact (SectionBaseChange.mem_nonzeroLocus t _).2 ⟨fun _ => k, mem_chart_one (𝟙 _) y hk,
      isUnit_of_mul_isUnit_right hu⟩
  · obtain ⟨k, rfl⟩ : ∃ k', k = fun _ => k' := ⟨k 0, funext fun i => congrArg k (Subsingleton.elim i 0)⟩
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have hk : y ∈ L'.U k := Set.mem_iInter.1 hy 0
    obtain ⟨a₁, a₂⟩ := ev₂ R p r σ j k ((L.pull F).U (fun _ => j) ⊓ L'.U k) (fun z hz => ⟨hV z, mem_pull.1 hz.1⟩) le_rfl
      (fun z hz => mem_chart_one (𝟙 _) z hz.2) y ⟨mem_pull.2 hj, hk⟩
    have e := (key y j k hj hk).symm.trans (a₁.symm.trans ((congrArg _ (h j k _ _ _ _)).trans a₂))
    exact ((Units.mul_right_inj _).1 e).trans (Eq.symm ((gs_mul (𝟙 X') y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ (𝟙 X') y hy r) rfl)))
  · refine fn_ext fun y hy => ?_
    obtain ⟨a₁, a₂⟩ := ev₂ R p r σ j k W h₁ h₂ h₃ y hy
    exact a₁.trans ((key y j k (h₁ hy).2 (h₂ hy).2).trans
      ((congrArg _ (secIsMul_gs h (𝟙 X') y _ (h₃ hy))).trans a₂.symm))

theorem IsPushGen.exists_mem_basicOpen {G : Over X} {L : LB G.left} (hP : PushInvertible G L) {V : X.Opens}
    {θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)} (h : IsPushGen G L V θ) {x : X} (hx : x ∈ V) :
    ∃ (g : G.left) (i : L.ι), G.hom g = x ∧ g ∈ G.left.basicOpen (θ i) := by
  obtain ⟨V₀, hV₀, θ₀, hθ₀, -, nz⟩ := hP x
  obtain ⟨g, i, rfl, hb⟩ := nz x hV₀
  obtain ⟨a, ha, -⟩ := h.2 (V ⊓ V₀) inf_le_left _ (res_mem_secOn (G.hom.preimage_mono inf_le_right) hθ₀)
  have h₀ : g ∈ G.hom ⁻¹ᵁ V₀ ⊓ L.U i := G.left.basicOpen_le _ hb
  have hm : (𝟙 G.left : _ ⟶ _) g ∈ G.hom ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U i := ⟨⟨hx, hV₀⟩, h₀.2⟩
  have e := congrArg (gs (𝟙 _) g _) (ha i)
  rw [gs_res _ g _ hm, gs_mul _ g _ hm, gs_res _ g _ hm] at e
  exact ⟨g, i, rfl, (mem_basicOpen_iff_gs _ (show g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i from ⟨hx, h₀.2⟩)).2
    (isUnit_of_mul_isUnit_right (e ▸ (mem_basicOpen_iff_gs _ h₀).1 hb))⟩

end General

section Term

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {B₀ : Scheme.{0}} {M₀ : LB B₀} {φ : D.P.A.left ⟶ B₀}
  {w : LB.Iso D.P.L (M₀.pull φ)} {th : M₀.Sec}

theorem famφB_zero_one : D.famφB 0 1 = 𝟙 D.P.A.left := by
  show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = (𝟙 D.P.A : _ ⟶ _).left
  congr 1
  exact (congrArg (𝟙 D.P.A * ·) (cPoint_zero (D := D) D.P.A)).trans (_root_.mul_one _)

theorem isPullTerm_iff {t : D.SecB 1 0} : IsPullTerm D φ w th t ↔ ∀ (y : D.P.A.left) J j₀, Good D.P.L y J →
    φ y ∈ M₀.U j₀ → gs φ y _ (th.f j₀) = (Geo.Tor.gw w (𝟙 _) y j₀ (J (𝟙 _))).val * sval t (𝟙 _) y J := by
  have ev : ∀ (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι) (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB 0) j)
      (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ φ ⁻¹ᵁ M₀.U j₀) (y : D.P.A.left), y ∈ V →
      gs (𝟙 _) y V ((φ.appLE _ _ h₃).hom (th.f j₀)) = gs φ y _ (th.f j₀) ∧
      gs (𝟙 _) y V (resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (t.f j)) =
        (Geo.Tor.gw w (𝟙 _) y j₀ (j 1)).val * gs (𝟙 _) y (LB.wchart D.P.L (D.famφB 0) j) (t.f j) :=
    fun j j₀ V h₁ h₂ h₃ y hy => ⟨(gs_appLE φ _ _ h₃ (𝟙 _) y hy _).trans (by rw [Category.id_comp]),
      (gs_mul (𝟙 _) y V hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans
        (gs_unit (𝟙 _) y _ (h₂ hy) _)) (gs_res (𝟙 _) y h₁ hy _))⟩
  have e₁ : 𝟙 _ ≫ D.famφB 0 1 = 𝟙 D.P.A.left := (Category.id_comp _).trans famφB_zero_one
  refine ⟨fun h y J j₀ hJ hy => ?_, fun h j j₀ V h₁ h₂ h₃ hc => fn_ext fun y hy => ?_⟩
  · let j : Fin 4 → D.P.L.ι := fun k => J (𝟙 _ ≫ D.famφB 0 k)
    have hj : j 1 = J (𝟙 _) := congrArg J e₁
    let V := LB.wchart D.P.L (D.famφB 0) j ⊓ ((M₀.pull φ).U (fun _ => j₀) ⊓ D.P.L.U (j 1))
    have hm : y ∈ V := ⟨hJ.mem _ (𝟙 _), mem_pull.2 hy, hj ▸ hJ (𝟙 _)⟩
    obtain ⟨a₁, a₂⟩ := ev j j₀ V inf_le_left inf_le_right (fun z hz => mem_pull.1 hz.2.1) y hm
    refine a₁.symm.trans ((congrArg _ (h j j₀ V _ _ _ fun k k' e => congrArg (fun q => J (𝟙 _ ≫ q)) e)).trans
      (a₂.trans ?_))
    rw [hj]
    rfl
  · obtain ⟨a₁, a₂⟩ := ev j j₀ V h₁ h₂ h₃ y hy
    obtain ⟨J, hJ, hj⟩ := exists_good D.P.L D.P.isLB y (fun k => 𝟙 _ ≫ D.famφB 0 k) j
      (fun k k' e => hc k k' (by simpa using e)) (fun k => Set.mem_iInter.1 (h₁ hy) k)
    rw [a₁, a₂, h y J j₀ hJ (h₃ hy), sval_of t _ y J j hj, ← hj 1, e₁]

theorem exists_isPullTerm (hw : w.IsGen) (hM : M₀.IsLB) (th : M₀.Sec) : ∃ t, IsPullTerm D φ w th t := by
  obtain ⟨s, hs⟩ := sec_pull_down ((isGen_iff w).1 hw) hM D.P.isLB th
  obtain ⟨s', hs'⟩ := exists_powerSection_of_chartFunctions s
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := D.famφB 0) (ε' := DegPre.famε 1)
    (fun U _ h => by rw [prod_fam_zero]; simp) s'
  refine ⟨t, isPullTerm_iff.2 fun y J j₀ hJ hy => ?_⟩
  have e := hs _ (𝟙 _) y j₀ _ hy (hJ (𝟙 _))
  rw [Category.id_comp] at e
  rw [e, ht _ _ y J hJ, sval_of s' _ y J (fun _ => J (𝟙 _)) (fun _ => by rw [Category.id_comp]),
    hs' _ _ y _ (hJ (𝟙 _))]

theorem IsPullTerm.unique (hM : M₀.IsLB) {t t' : D.SecB 1 0} (h : IsPullTerm D φ w th t)
    (h' : IsPullTerm D φ w th t') : t = t' := sec_ext' D.P.isLB fun y J hJ => by
  obtain ⟨j₀, hy⟩ := exists_chart hM (φ y)
  exact (Units.mul_right_inj _).1 ((isPullTerm_iff.1 h y J j₀ hJ hy).symm.trans (isPullTerm_iff.1 h' y J j₀ hJ hy))

theorem IsPullTerm.mem_nonzeroLocus {t : D.SecB 1 0} (h : IsPullTerm D φ w th t) {y : D.P.A.left}
    (hy : φ y ∈ nonzeroLocus th) : y ∈ nonzeroLocus t := by
  obtain ⟨j₀, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus th _).1 hy
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have hu' := (isUnit_gs_iff φ y _ hj _).2 hu
  rw [isPullTerm_iff.1 h y J j₀ hJ hj] at hu'
  exact (SectionBaseChange.mem_nonzeroLocus t _).2 ⟨_, hJ.mem _ (𝟙 _), isUnit_of_mul_isUnit_right hu'⟩

end Term

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_theta_arc (hG : GlobalFnsSt) (hS : SecBaseChangeSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W : ArcWit Y a I f u χ) (th : W.P.D.toPre.SecB 1 0)
    (hth : ∃ x, W.P.D.toPre.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus th) :
    ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ α, W.P.D.toPre.SecB 1 α), fam 0 = th ∧
      (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      (∀ α, α ≠ 0 → ∃ r ∈ I, ∃ g : W.P.D.toPre.SecB 1 α,
        SecIsMul W.P.D.toPre.P.A.hom r (fam α) g) ∧
      (∀ (σ' : H0 W.P.U.LG.L 1) (fam' : ∀ α, W.P.D.toPre.SecB 1 α), fam' 0 = th →
        (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ' fam') → σ' = σ) ∧
      (∀ s : H0 W.P.U.LG.L 1, ∃! r : R, SecIsMul W.t.G.hom r s σ) ∧
      (∀ (s : H0 W.P.U.LG.L 1) (r : R), SecIsMul W.t.G.hom r s σ →
        (IsUnit r ↔ NonzeroOnSpecial W.P.U s)) ∧
      (∃ w₂, IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) ∧
      ∀ w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ), w₂.IsGen →
        (∀ (V : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j)), ⊤ ≤ χ ⁻¹ᵁ V →
          s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V) →
          (∃! r : R, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ) ∧
          ∀ r : R, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ →
            (IsUnit r ↔ ∃ g j, Y.t.G.hom g = χ (closedPoint R) ∧
              g ∈ Y.t.G.left.basicOpen (s j))) ∧
        (PushInvertible Y.t.G Y.t.PP.L → (∃ V θ, ⊤ ≤ χ ⁻¹ᵁ V ∧ IsPushGen Y.t.G Y.t.PP.L V θ) ∧
          ∀ V θ, ⊤ ≤ χ ⁻¹ᵁ V → IsPushGen Y.t.G Y.t.PP.L V θ →
            ∃ r : Rˣ, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) θ r.val σ) := by
  have := W.t.semi.geomConnected
  obtain ⟨σ, fam, h₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_theta hG hS hI W.P.U th hth
  refine ⟨σ, fam, h₀, h₁, h₂, h₃, h₄, fun s r h => (h₅ s r h).1, ?_, fun w₂ hw₂ => ?_⟩
  · rw [W.P.bundle]
    obtain ⟨w₂, h, h', -⟩ := W.m.lin
    exact ⟨w₂, h, h'⟩
  have main : ∀ (V : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j)), ⊤ ≤ χ ⁻¹ᵁ V →
      s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V) →
      (∃! r : R, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ) ∧
      ∀ r : R, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ →
        (IsUnit r ↔ ∃ g j, Y.t.G.hom g = χ (closedPoint R) ∧ g ∈ Y.t.G.left.basicOpen (s j)) := fun V s hV hs => by
    obtain ⟨s', hz, hp⟩ := exists_pull_secOn hw₂ Y.t.PP.isLB W.P.U.LG.isLB (V := Y.t.G.hom ⁻¹ᵁ V)
      (fun y => (congrArg (fun q => q y ∈ V) W.m.cart.1.w).mpr (hV (x := W.t.G.hom y) trivial)) hs
    refine ⟨by simpa only [hp] using h₄ s', fun r hr => (h₅ s' r ((hp _ _ _ _).1 hr)).2.trans
      ⟨fun ⟨g, hg, hn⟩ => ?_, fun ⟨g, j, hg, hn⟩ => ?_⟩⟩
    · obtain ⟨j, hj⟩ := (hz g).1 hn
      exact ⟨_, j, (congrArg (fun q => q g) W.m.cart.1.w).trans (congrArg χ hg), hj⟩
    · obtain ⟨g', rfl, hg'⟩ := Scheme.exists_preimage_of_isPullback W.m.cart.1 g (closedPoint R) hg
      exact ⟨g', hg', (hz g').2 ⟨j, hn⟩⟩
  refine ⟨main, fun hP => ⟨?_, fun V θ hV hθ => ?_⟩⟩
  · obtain ⟨V, hV, θ, hθ, hg, -⟩ := hP (χ (closedPoint R))
    exact ⟨V, θ, (Scheme.preimage_eq_top_of_closedPoint_mem χ hV).ge, hθ, hg⟩
  · obtain ⟨⟨r, hr, -⟩, hu⟩ := main V θ hV hθ.1
    obtain ⟨v, rfl⟩ := (hu r hr).2 (hθ.exists_mem_basicOpen hP (hV (x := closedPoint R) trivial))
    exact ⟨v, hr⟩

theorem existsUnique_pullTerm {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (th₀ : a.D₀.P.L.Sec) :
    (∃! th, IsPullTerm W.P.D.toPre W.φ W.w th₀ th) ∧
      ∀ th, IsPullTerm W.P.D.toPre W.φ W.w th₀ th → (∀ y, ∃ x, a.D₀.P.A.hom x = y ∧ x ∈ nonzeroLocus th₀) →
        ∀ y, ∃ x, W.P.D.toPre.P.A.hom x = y ∧ x ∈ nonzeroLocus th := by
  obtain ⟨t, ht⟩ := exists_isPullTerm W.spec.2.1 a.D₀.P.isLB th₀
  refine ⟨⟨t, ht, fun t' h => h.unique a.D₀.P.isLB ht⟩, fun th h hn y => ?_⟩
  obtain ⟨x₀, hx₀, hn₀⟩ := hn (spMap f y)
  obtain ⟨x, rfl, hx⟩ := Scheme.exists_preimage_of_isPullback W.spec.1.1 x₀ y hx₀
  exact ⟨x, hx, h.mem_nonzeroLocus hn₀⟩

end GlobalTheory.ThetaUnit

namespace GlobalTheory

open GlobalTheory.ThetaUnit

theorem theta_generates_along_arc (hG : GlobalFnsSt) (hS : SecBaseChangeSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O']
    [IsLocalRing O'] [IsNoetherianRing O'] {b : O →+* O'} (a : ArcIn D l β O' b) (χ : Sp (PowerSeries O') ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ) :
    (∀ th : W.P.D.toPre.SecB 1 0,
      (∃ x, W.P.D.toPre.P.A.hom x = closedPoint (PowerSeries O') ∧ x ∈ nonzeroLocus th) →
      ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ α, W.P.D.toPre.SecB 1 α), fam 0 = th ∧
        (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
        (∀ α, α ≠ 0 → ∃ r ∈ Ideal.span {(PowerSeries.X : PowerSeries O')}, ∃ g : W.P.D.toPre.SecB 1 α,
          SecIsMul W.P.D.toPre.P.A.hom r (fam α) g) ∧
        (∀ (σ' : H0 W.P.U.LG.L 1) (fam' : ∀ α, W.P.D.toPre.SecB 1 α), fam' 0 = th →
          (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ' fam') → σ' = σ) ∧
        (∀ s : H0 W.P.U.LG.L 1, ∃! r : PowerSeries O', SecIsMul W.t.G.hom r s σ) ∧
        (∀ (s : H0 W.P.U.LG.L 1) (r : PowerSeries O'), SecIsMul W.t.G.hom r s σ →
          (IsUnit r ↔ NonzeroOnSpecial W.P.U s)) ∧
        (∃ w₂, IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) ∧
        ∀ w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ), w₂.IsGen →
          (∀ (V : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j)), ⊤ ≤ χ ⁻¹ᵁ V →
            s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V) →
            (∃! r : PowerSeries O', PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ) ∧
            ∀ r : PowerSeries O', PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s r σ →
              (IsUnit r ↔ ∃ g j, Y.t.G.hom g = χ (closedPoint (PowerSeries O')) ∧
                g ∈ Y.t.G.left.basicOpen (s j))) ∧
          (PushInvertible Y.t.G Y.t.PP.L → (∃ V θ, ⊤ ≤ χ ⁻¹ᵁ V ∧ IsPushGen Y.t.G Y.t.PP.L V θ) ∧
            ∀ V θ, ⊤ ≤ χ ⁻¹ᵁ V → IsPushGen Y.t.G Y.t.PP.L V θ →
              ∃ r : (PowerSeries O')ˣ, PullsToMul W.t.G.hom W.m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) θ r.val σ)) ∧
    ∀ th₀ : a.D₀.P.L.Sec, (∃! th, IsPullTerm W.P.D.toPre W.φ W.w th₀ th) ∧
      ∀ th, IsPullTerm W.P.D.toPre W.φ W.w th₀ th → (∀ y, ∃ x, a.D₀.P.A.hom x = y ∧ x ∈ nonzeroLocus th₀) →
        ∀ y, ∃ x, W.P.D.toPre.P.A.hom x = y ∧ x ∈ nonzeroLocus th := by
  refine ⟨exists_theta_arc hG hS ?_ W, existsUnique_pullTerm W⟩
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
    PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
  exact not_isUnit_zero

end GlobalTheory
