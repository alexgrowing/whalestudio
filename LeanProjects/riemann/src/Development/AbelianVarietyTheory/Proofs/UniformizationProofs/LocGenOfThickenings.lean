import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosatiCubicalAdditive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EndRosati

open GlobalTheory.CechPic

theorem gen_iff_sum {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∑ k, ε k • pull (φ k) (cls L hL) = 0 := by
  rw [← cls_linComb hL φ ε (LB.isLB_linComb hL φ ε), cls_eq_zero_iff]

section Points

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem ros_comp (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A) (k : Fin 6) :
    (lift x y).left ≫ rosatiφ A f g k =
      ((![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] : Fin 6 → (T ⟶ A)) k).left := by
  have e₀ : lift x y ≫ padd A (fst A A ≫ f) (snd A A) = (x ≫ f) * y := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₃ : lift x y ≫ padd A (fst A A) (snd A A ≫ g) = x * (y ≫ g) := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₁ : lift x y ≫ fst A A ≫ f = x ≫ f := by simp
  have e₅ : lift x y ≫ snd A A ≫ g = y ≫ g := by simp
  fin_cases k
  exacts [congrArg (·.left) e₀, congrArg (·.left) e₁, congrArg (·.left) (lift_snd x y), congrArg (·.left) e₃,
    congrArg (·.left) (lift_fst x y), congrArg (·.left) e₅]

variable {S' : Scheme.{0}} {j : S' ⟶ S} {E : Over S'} [GrpObj E] [IsCommMonObj E] (p : (Over.map j).obj E ⟶ A)

abbrev push {T : Over S'} (x : T ⟶ E) : (Over.map j).obj T ⟶ A := (Over.map j).map x ≫ p

omit [IsCommMonObj A] [IsCommMonObj E] in
theorem push_mul (q : E ⟶ (Over.pullback j).obj A) [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst A.hom j)
    {T : Over S'} (x y : T ⟶ E) : push p (x * y) = push p x * push p y := by
  have key : ∀ y : T ⟶ E, push p y = pushHom (isGrpPullback_pullback A j) T (y ≫ q) := fun y =>
    Over.OverMorphism.ext ((congrArg (y.left ≫ ·) hp).trans (Category.assoc _ _ _).symm)
  rw [key, key, key, MonObj.mul_comp]
  exact map_mul _ _ _

omit [GrpObj A] [GrpObj E] [IsCommMonObj A] [IsCommMonObj E] in
theorem push_comp {f' : E ⟶ E} {f : A ⟶ A} (hf : push p f' = p ≫ f) {T : Over S'} (x : T ⟶ E) :
    push p (x ≫ f') = push p x ≫ f := by
  rw [push, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg _ hf

theorem ros_push (hm : ∀ {T : Over S'} (x y : T ⟶ E), push p (x * y) = push p x * push p y)
    {f' g' : E ⟶ E} {f g : A ⟶ A} (hf : push p f' = p ≫ f) (hg : push p g' = p ≫ g) {T : Over S'} (x y : T ⟶ E)
    (k : Fin 6) : (lift (push p x) (push p y)).left ≫ rosatiφ A f g k =
      (lift x y).left ≫ rosatiφ E f' g' k ≫ p.left := by
  rw [← Category.assoc, ros_comp, ros_comp, ← push_comp p hf, ← push_comp p hg, ← hm, ← hm]
  fin_cases k <;> rfl

theorem ros_push' (hm : ∀ {T : Over S'} (x y : T ⟶ E), push p (x * y) = push p x * push p y)
    {f' g' : E ⟶ E} {f g : A ⟶ A} (hf : push p f' = p ≫ f) (hg : push p g' = p ≫ g) (k : Fin 6) :
    (lift (push p (fst E E)) (push p (snd E E))).left ≫ rosatiφ A f g k = rosatiφ E f' g' k ≫ p.left := by
  rw [ros_push p hm hf hg, lift_fst_snd]
  exact Category.id_comp _

omit [GrpObj A] [GrpObj E] [IsCommMonObj A] [IsCommMonObj E] in
theorem lift_push {T : Over S'} (x y : T ⟶ E) :
    (lift x y).left ≫ (lift (push p (fst E E)) (push p (snd E E))).left = (lift (push p x) (push p y)).left := by
  have : (Over.map j).map (lift x y) ≫ lift (push p (fst E E)) (push p (snd E E)) = lift (push p x) (push p y) := by
    rw [comp_lift, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, lift_fst, lift_snd]
  exact congrArg (·.left) this

end Points

theorem eq_of_translate_cls {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
    [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L)
    (a b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A)
    (H : pull (𝟙 A * (toUnit A ≫ b)).left (cls L hL) - pull (toUnit A ≫ b).left (cls L hL) =
      pull (𝟙 A * (toUnit A ≫ a)).left (cls L hL) - pull (toUnit A ≫ a).left (cls L hL)) : b = a := by
  let O : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  let x : O ⟶ A := b * a⁻¹
  let m : O ⊗ A ⟶ A := snd _ _ * (toUnit _ ≫ a)⁻¹
  have hf : fst O A = toUnit _ := toUnit_unique _ _
  have hx : lift (fst O A ≫ x) (snd O A) ≫ μ[A] = m * (toUnit _ ≫ b) := by
    rw [← Hom.mul_def, hf]
    simp only [x, m, MonObj.comp_mul, GrpObj.comp_inv]
    rw [mul_comm, _root_.mul_assoc, mul_comm (toUnit _ ≫ b)]
  have hy : m * (toUnit _ ≫ a) = snd O A := inv_mul_cancel_right _ _
  have H' := congrArg (pull m.left) H
  simp only [map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc] at H'
  rw [hy, ← hx] at H'
  have h1 : x = 1 := hK R (𝟙 _) x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R)).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : O ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst O A).left ⁻¹ᵁ V).ι (pull (toUnit (O ⊗ A) ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp, ← hf]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst O A ≫ x) (snd O A) ≫ μ[A]).left,
        (snd O A).left] : Fin 2 → _) k) (cls L hL) =
        pull (toUnit (O ⊗ A) ≫ b).left (cls L hL) - pull (toUnit (O ⊗ A) ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H'
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

theorem loc_gen_of_thickenings (hG : GlobalFnsSt) {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (hp : AbLaw.IsProjBy B.hom)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (B.left ⟶ X)) (ε : K → ℤ)
    (h : ∀ e, ∃ t : LB.Gen (LB.LinComb L (fun k => pullback.fst B.hom (thick R I e) ≫ φ k) ε), t.IsGen)
    (s : Spec (CommRingCat.of R)) : ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (B.hom ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen := by
  have hF := LB.isLB_linComb hL φ ε
  have key : ∀ {Y Z : Scheme.{0}} (π : Y ⟶ B.left) (κ : Z ⟶ Y),
      AbLaw.Triv (((LB.LinComb L φ ε).pull π).pull κ) ↔
        pull κ (∑ k, ε k • pull (π ≫ φ k) (cls L hL)) = 0 := fun π κ => by
    refine (cls_eq_zero_iff (LB.isLB_pull (LB.isLB_pull hF π) κ)).symm.trans ?_
    rw [cls_pull (LB.isLB_pull hF π), cls_pull hF, cls_linComb hL]
    simp only [map_sum, map_zsmul, pull_comp]
  obtain ⟨J, hJ⟩ := TrivRep.exists_ideal_locTriv hG R B hB hp _ hF
  have hz : J ≤ RingHom.ker (RingHom.id R) := fun a ha => by
    refine IsHausdorff.haus (I := I) ‹_› a fun n => ?_
    have := (hJ _ (Ideal.Quotient.mk (I ^ (n + 1))) _ _ _ (IsPullback.of_hasPullback B.hom (thick R I n))).1
      (fun _ => ⟨⊤, trivial, (key _ _).2 (by rw [(gen_iff_sum hL _ _).1 (h n), map_zero])⟩) ha
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq_zero_iff_mem.1 this)
  obtain ⟨U, hU, ht⟩ := (hJ R (RingHom.id R) _ (𝟙 _) B.hom (by
    rw [CommRingCat.ofHom_id, Spec.map_id]; exact IsPullback.id_horiz _)).2 hz s
  refine ⟨U, hU, (gen_iff_sum hL _ _).2 ?_⟩
  simpa only [map_sum, map_zsmul, ← pull_comp, Category.id_comp] using (key _ _).1 ht

theorem exists_gen_through {X₁ X₂ E Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (h₁ : L₁.IsLB) (h₂ : L₂.IsLB)
    {F₁ : E ⟶ X₁} {F₂ : E ⟶ X₂} (w : LB.Iso (L₁.pull F₁) (L₂.pull F₂)) (hw : w.IsGen) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ E)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L₁ (fun k => φ k ≫ F₁) ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L₂ (fun k => φ k ≫ F₂) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (N), Good L₂ z J → Good L₁ z N →
        val t r z J = (∏ k, gw w (r ≫ φ k) z (J ((r ≫ φ k) ≫ F₂)) (fun _ => N ((r ≫ φ k) ≫ F₁)) ^ ε k) *
          val a r z N := by
  have le : ∀ j : K → PUnit → L₁.ι, LB.wchart (L₁.pull F₁) φ j ≤
      LB.wchart L₁ (fun k => φ k ≫ F₁) (fun k => j k PUnit.unit) := fun j y hy =>
    Set.mem_iInter.2 fun k => (mem_pull (F := F₁) (x := φ k y)).1 (Set.mem_iInter.1 hy k)
  let a' : LB.Gen (LB.LinComb (L₁.pull F₁) φ ε) := ⟨fun j => res (le j) (a.s fun k => j k PUnit.unit)⟩
  have ha' : a'.IsGen := isGen_of_gm _ fun y j j' h h' => by
    refine (gm_res (𝟙 Y) y _ h _).trans ((gen_trans ha (𝟙 Y) y (le j h) (le j' h')).trans
      (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))
    refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (Eq.symm ?_)
    exact (gm_pull_g L₁ F₁ (𝟙 Y ≫ φ k) y (j k) (j' k) (Set.mem_iInter.1 h k) (Set.mem_iInter.1 h' k)).trans
      (by rw [Category.assoc])
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (LB.isLB_pull h₁ F₁) a' ha'
  refine ⟨t, ht, fun Z r z J N hJ hN => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull F₁) φ (fun k _ => N (r ≫ φ k ≫ F₁)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hN (r ≫ φ k ≫ F₁))
  refine (hv Z r z _ _ (hJ.mem _ r) m).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ m _))
  simp only [Geo.Tor.pw, Category.assoc]

theorem exists_unit_of_formal {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (u : LB.Gen (LB.LinComb M φ ε)) (hu : u.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J → val u r z J = gm r z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

theorem unit_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {H : Over S} [GrpObj H] [ConnectedSpace H.left]
    (ρ : Γ((splitTorus S X ⊗ H).left, ⊤)ˣ)
    (hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ H) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ)
    (h₁ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left), gm (lift t (1 : Z ⟶ H)).left z ⊤ ρ = 1)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ H) (z : Z.left) : gm (lift t y).left z ⊤ ρ = 1 := by
  obtain ⟨χ, hχ⟩ := TorusInvariance.exists_char ρ fun Z t t' y => unit_ext fun z _ => by
    rw [map_mul, TorusInvariance.gm_pullTop, TorusInvariance.gm_pullTop, TorusInvariance.gm_pullTop, hm]
  rw [← TorusInvariance.gm_pullTop, hχ, ← hχ Z t 1, TorusInvariance.gm_pullTop, h₁]

section Level

open TorusInvariance

theorem add_left_of_cube {P V : Type} [CommGroup P] [CommGroup V] (W : P → V) {x x' y a a' b : P}
    {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W (x * x' * b) * (W (x * x'))⁻¹ * (W (x * b))⁻¹ * (W (x' * b))⁻¹ * W x * W x' * W b * (W 1)⁻¹ * c₁)
    (h₂ : 1 = W (a * a' * y) * (W (a * a'))⁻¹ * (W (a * y))⁻¹ * (W (a' * y))⁻¹ * W a * W a' * W y * (W 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    W (a * a' * y) * (W (a * a'))⁻¹ * (W y)⁻¹ * (W (x * x' * b))⁻¹ * W (x * x') * W b * v =
      (W (a * y) * (W a)⁻¹ * (W y)⁻¹ * (W (x * b))⁻¹ * W x * W b * v₁) *
        (W (a' * y) * (W a')⁻¹ * (W y)⁻¹ * (W (x' * b))⁻¹ * W x' * W b * v₂) := by
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

theorem add_right_of_cube {P V : Type} [CommGroup P] [CommGroup V] (W : P → V) {x x' y a b b' : P}
    {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W (y * b * b') * (W (y * b))⁻¹ * (W (y * b'))⁻¹ * (W (b * b'))⁻¹ * W y * W b * W b' * (W 1)⁻¹ * c₁)
    (h₂ : 1 = W (a * x * x') * (W (a * x))⁻¹ * (W (a * x'))⁻¹ * (W (x * x'))⁻¹ * W a * W x * W x' * (W 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    W (a * (x * x')) * (W a)⁻¹ * (W (x * x'))⁻¹ * (W (y * (b * b')))⁻¹ * W y * W (b * b') * v =
      (W (a * x) * (W a)⁻¹ * (W x)⁻¹ * (W (y * b))⁻¹ * W y * W b * v₁) *
        (W (a * x') * (W a)⁻¹ * (W x')⁻¹ * (W (y * b'))⁻¹ * W y * W b' * v₂) := by
  rw [← _root_.mul_assoc a, ← _root_.mul_assoc y]
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem push_fstG {G' : Over (Spec (CommRingCat.of R))} (f : G' ⟶ G) :
    push (fstG I e G) ((Over.pullback (thick R I e)).map f) = fstG I e G' ≫ f :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

omit [IsDomain R] [IsCommMonObj G] in
theorem fstG_mul {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G) :
    push (fstG I e G) (x * y) = push (fstG I e G) x * push (fstG I e G) y :=
  push_mul _ (𝟙 _) (Category.id_comp _).symm x y

theorem push_pG {f : G ⟶ G} {a : D.toPre.P.A ⟶ D.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) :
    push (U.gt e).pG ((Over.pullback (thick R I e)).map f) = (U.gt e).pG ≫ a := by
  rw [push, GtCoord.pG, ← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (push_fstG e a)

variable {f g : G ⟶ G} [IsMonHom f] [IsMonHom g] {a b : D.toPre.P.A ⟶ D.toPre.P.A} [IsMonHom a] [IsMonHom b]
  (hf : (Over.pullback (thick R I e)).map f ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a)
  (hg : (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b)
include hf hg

theorem exists_gen_mul (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom)
    (u : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u (zero2 G)) (LB.oneGen U.LG.L)) :
    ∃ v : LB.Gen (LB.LinComb D.toPre.P.L (fun k => rosatiφ (thickObj R I e G) ((Over.pullback (thick R I e)).map f)
        ((Over.pullback (thick R I e)).map g) k ≫ (U.gt e).pG.left) rosatiε), v.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J), Good D.toPre.P.L z J →
        ∀ x x' y : T ⟶ thickObj R I e G, push (U.gt e).pG x = 1 →
          val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧
          val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J := by
  let f' := (Over.pullback (thick R I e)).map f
  let g' := (Over.pullback (thick R I e)).map g
  obtain ⟨u', hu', vu⟩ := exists_gen U.LG.isLB
    (φ' := fun k => rosatiφ (thickObj R I e G) f' g' k ≫ (fstG I e G).left) (ε' := rosatiε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ rosatiε k)
      (ros_push' (fstG I e G) (fstG_mul e) (push_fstG e f) (push_fstG e g) k))
    (LB.pullGen U.LG.L _ _ u _) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨v, hv, vv⟩ := exists_gen_through U.LG.isLB D.toPre.P.isLB (U.w e) (U.w_gen e) _ _ u' hu'
  refine ⟨v, hv, fun T z J hJ x x' y hx => ?_⟩
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
  have hN' : Good U.LG.L z N := hN
  let W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ := fun p => wVal U e z J N p.left
  let p : (T ⟶ thickObj R I e G) → ((Over.map (thick R I e)).obj T ⟶ G) := push (fstG I e G)
  let p' : (T ⟶ thickObj R I e G) → ((Over.map (thick R I e)).obj T ⟶ D.toPre.P.A) := push (U.gt e).pG
  have hV : ∀ x y : T ⟶ thickObj R I e G, val v (lift x y).left z J =
      W ((x ≫ f') * y) * (W (x ≫ f'))⁻¹ * (W y)⁻¹ * (W (x * (y ≫ g')))⁻¹ * W x * W (y ≫ g') *
        @id (T.left.presheaf.stalk z)ˣ (val₂ u (T := (Over.map (thick R I e)).obj T) z N (p x) (p y)) := fun x y =>
    (vv _ _ z J N hJ hN').trans (congrArg₂ (· * ·) (prod_ros f' g' x y (wVal U e z J N))
      ((vu _ _ z N hN').trans ((val_pull hN' _ _ _).trans (congrArg (val u · z N) (lift_push _ x y)))))
  have hc : ∀ x y w : T ⟶ thickObj R I e G,
      @id (T.left.presheaf.stalk z)ˣ (cubV D.toPre.cub (T := (Over.map (thick R I e)).obj T) z J (p' x) (p' y) (p' w)) =
      W (x * y * w) * (W (x * y))⁻¹ * (W (x * w))⁻¹ * (W (y * w))⁻¹ * W x * W y * W w * (W 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U.cubG (T := (Over.map (thick R I e)).obj T) z N (p x) (p y) (p w)) :=
    fun x y w => (cube_val U ![x, y, w] hJ hN').trans (congrArg (· * _) (prod_psum x y w (wVal U e z J N)))
  have C := isCub_cubV D.toPre.cub (T := (Over.map (thick R I e)).obj T) hJ
  have c₁ : ∀ x y w, p' x = 1 → _ := fun x y w h =>
    ((congrArg (cubV D.toPre.cub (T := (Over.map (thick R I e)).obj T) z J · (p' y) (p' w)) h).trans
      (C.face _ _)).symm.trans (hc x y w)
  have c₂ : ∀ x y w, p' y = 1 → _ := fun x y w h =>
    ((congrArg (cubV D.toPre.cub (T := (Over.map (thick R I e)).obj T) z J (p' x) · (p' w)) h).trans
      (C.face₂ _ _)).symm.trans (hc x y w)
  have xf : p' (x ≫ f') = 1 := (push_comp _ (push_pG U e hf) x).trans (by rw [hx, MonObj.one_comp])
  have xg : p' (x ≫ g') = 1 := (push_comp _ (push_pG U e hg) x).trans (by rw [hx, MonObj.one_comp])
  have pf : ∀ x, p x ≫ f = p (x ≫ f') := fun x => (push_comp _ (push_fstG e f) x).symm
  have pg : ∀ x, p x ≫ g = p (x ≫ g') := fun x => (push_comp _ (push_fstG e g) x).symm
  have pm : p x * p x' = p (x * x') := (fstG_mul e x x').symm
  obtain ⟨r₁, r₂⟩ := RosatiCube.ros_add_of_surj U.cubG sj f g u hu h₀ (T := (Over.map (thick R I e)).obj T) hN'
    (p x) (p x') (p y)
  rw [pm, pf, pf, pg] at r₁
  rw [pm, pf, pg, pg] at r₂
  rw [hV, hV, hV, hV, hV, hV, MonObj.mul_comp x x' f', MonObj.mul_comp x x' g']
  exact ⟨add_left_of_cube W (c₁ _ _ _ hx) (c₁ _ _ _ xf) r₁, add_right_of_cube W (c₂ _ _ _ xg) (c₂ _ _ _ hx) r₂⟩

end Level

end GlobalTheory.EndRosati
end
