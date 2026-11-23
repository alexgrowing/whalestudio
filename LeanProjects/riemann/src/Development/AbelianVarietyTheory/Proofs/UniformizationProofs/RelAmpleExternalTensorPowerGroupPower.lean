import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineAndGeneratedOfWideProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Segre
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

def IsWideProduct {B Y : Scheme.{0}} {j : ℕ} {D : Fin j → Scheme.{0}} (s : Y ⟶ B)
    (d : ∀ i, D i ⟶ B) (pr : ∀ i, Y ⟶ D i) : Prop :=
  (∀ i, pr i ≫ d i = s) ∧ ∀ (Z : Scheme.{0}) (z : Z ⟶ B) (f : ∀ i, Z ⟶ D i),
    (∀ i, f i ≫ d i = z) → ∃! g : Z ⟶ Y, g ≫ s = z ∧ ∀ i, g ≫ pr i = f i

section
variable {B Y : Scheme.{0}} {j : ℕ} {D : Fin j → Scheme.{0}} {s : Y ⟶ B}
    {d : ∀ i, D i ⟶ B} {pr : ∀ i, Y ⟶ D i}

theorem IsWideProduct.resLE (h : IsWideProduct s d pr) (V : B.Opens) (W : ∀ i, (D i).Opens)
    (W' : Y.Opens) (hW : ∀ i, W i ≤ d i ⁻¹ᵁ V) (h₁ : W' ≤ s ⁻¹ᵁ V) (h₂ : ∀ i, W' ≤ pr i ⁻¹ᵁ W i)
    (h₃ : ∀ y : Y, s y ∈ V → (∀ i, pr i y ∈ W i) → y ∈ W') :
    IsWideProduct (s.resLE V W' h₁) (fun i => (d i).resLE V (W i) (hW i))
      (fun i => (pr i).resLE (W i) W' (h₂ i)) := by
  refine ⟨fun i => ?_, fun Z z f hf => ?_⟩
  · rw [← cancel_mono V.ι]; simp [h.1 i]
  obtain ⟨g, ⟨hg₁, hg₂⟩, hu⟩ := h.2 Z (z ≫ V.ι) (fun i => f i ≫ (W i).ι) (fun i => by
    rw [← hf i]; simp)
  have hr : Set.range g ⊆ Set.range W'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine h₃ _ ?_ fun i => ?_
    · exact (congrArg (fun q => q y ∈ V) hg₁).mpr (z y).2
    · exact (congrArg (fun q => q y ∈ W i) (hg₂ i)).mpr (f i y).2
  refine ⟨IsOpenImmersion.lift W'.ι g hr, ⟨?_, fun i => ?_⟩, fun g' hg' => ?_⟩
  · rw [← cancel_mono V.ι]; simp [hg₁]
  · rw [← cancel_mono (W i).ι]; simp [hg₂]
  · rw [← cancel_mono W'.ι, IsOpenImmersion.lift_fac]
    refine hu _ ⟨?_, fun i => ?_⟩
    · rw [← hg'.1]; simp
    · rw [← hg'.2 i]; simp

theorem IsWideProduct.affine [IsAffine B] (h : IsWideProduct s d pr) (hD : ∀ i, IsAffine (D i)) :
    IsAffine Y ∧ ∀ A : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ A) →
      (∀ i a, (pr i).appTop.hom a ∈ A) → A = ⊤ := by
  obtain ⟨h₁, h₂⟩ := isAffine_and_generated_of_wide_product Γ(B, ⊤) j Y D (s ≫ B.isoSpec.hom)
    (fun i => d i ≫ B.isoSpec.hom) pr (fun i => by rw [← Category.assoc, h.1 i])
    (fun Z z f hf => by
      obtain ⟨g, ⟨hg₁, hg₂⟩, hu⟩ := h.2 Z (z ≫ B.isoSpec.inv) f (fun i => by
        rw [← hf i]; simp)
      refine ⟨g, ⟨by rw [← Category.assoc, hg₁]; simp, hg₂⟩, fun g' hg' => hu _ ⟨?_, hg'.2⟩⟩
      rw [← hg'.1]; simp) hD
  exact ⟨h₁, fun A hs hp => h₂ A (fun a => hs _) hp⟩

theorem IsWideProduct.affineOpen (h : IsWideProduct s d pr) (V : B.Opens) (W : ∀ i, (D i).Opens)
    (W' : Y.Opens) (hW : ∀ i, W i ≤ d i ⁻¹ᵁ V) (h₁ : W' ≤ s ⁻¹ᵁ V) (h₂ : ∀ i, W' ≤ pr i ⁻¹ᵁ W i)
    (h₃ : ∀ y : Y, s y ∈ V → (∀ i, pr i y ∈ W i) → y ∈ W') (hV : IsAffineOpen V)
    (hA : ∀ i, IsAffineOpen (W i)) :
    IsAffineOpen W' ∧ ∀ A : Subring Γ(Y, W'), (∀ a, (s.appLE V W' h₁).hom a ∈ A) →
      (∀ i a, ((pr i).appLE (W i) W' (h₂ i)).hom a ∈ A) → A = ⊤ := by
  have : IsAffine V := hV
  obtain ⟨k₁, k₂⟩ := (h.resLE V W W' hW h₁ h₂ h₃).affine hA
  refine ⟨k₁, fun A hs hp => ?_⟩
  have key : ∀ {X : Scheme.{0}} (f : Y ⟶ X) (O : X.Opens) (e : W' ≤ f ⁻¹ᵁ O) a,
      W'.topIso.hom.hom ((f.resLE O W' e).appTop.hom a) = (f.appLE O W' e).hom (O.topIso.hom.hom a) := by
    intro X f O e a
    have := congrArg (fun q => q.hom a) (arrowResLEAppIso f O W' e).hom.w
    exact this.symm
  have := k₂ (A.comap W'.topIso.hom.hom) (fun a => by rw [Subring.mem_comap, key]; exact hs _)
    (fun i a => by rw [Subring.mem_comap, key]; exact hp _ _)
  rw [eq_top_iff]
  intro a _
  have h4 : W'.topIso.inv.hom a ∈ A.comap W'.topIso.hom.hom := by rw [this]; trivial
  rw [Subring.mem_comap] at h4
  rwa [show W'.topIso.hom.hom (W'.topIso.inv.hom a) = a from Iso.inv_hom_id_apply W'.topIso a] at h4

end

section
variable {B Y Y' : Scheme.{0}}

def Embeds (π : Y ⟶ B) (P : LB Y) {I : Type} (s : I → LB.Sec P) : Prop :=
  (⨆ i, nonzeroLocus (s i) = ⊤) ∧
    ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
      ∃ r : I → Γ(Y, nonzeroLocus (s i)),
        (∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
            nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
          (Y.presheaf.map (homOfLE (inf_le_left :
            nonzeroLocus (s i) ⊓ P.U k ≤ nonzeroLocus (s i))).op).hom (r j) *
          (Y.presheaf.map (homOfLE (inf_le_right :
            nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom
          (π.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)

theorem Embeds.reindex {π : Y ⟶ B} {P : LB Y} {I J : Type} {s : I → LB.Sec P} (h : Embeds π P s)
    (e : J ≃ I) : Embeds π P (fun j => s (e j)) := by
  refine ⟨by rw [← h.1]; exact e.iSup_comp (g := fun i => nonzeroLocus (s i)), fun i => ?_⟩
  obtain ⟨h₁, r, h₂, h₃⟩ := h.2 (e i)
  refine ⟨h₁, fun j => r (e j), fun j k => h₂ _ _, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := h₃ x
  refine ⟨MvPolynomial.rename e.symm p, ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  congr 1
  funext a
  simp

theorem gs_finprod {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {K : Type}
    [Fintype K] (a : K → Γ(X, U)) : gs r z U (∏ k, a k) = ∏ k, gs r z U (a k) := by
  simp only [gs_eq r z U h, map_prod]

theorem gs_compat {P : LB Y} (s : LB.Sec P) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {k k' : P.ι}
    (hk : r z ∈ P.U k) (hk' : r z ∈ P.U k') :
    gs r z _ (s.f k) = (gm r z _ (P.g k k')).val * gs r z _ (s.f k') := by
  have hm : r z ∈ P.U k ⊓ P.U k' := ⟨hk, hk'⟩
  have e := congrArg (gs r z _) (s.compat k k')
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

theorem mem_nonzeroLocus_pull {P : LB Y} (s : LB.Sec P) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {k : P.ι} (hk : r z ∈ P.U k) : r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f k)) := by
  rw [mem_nonzeroLocus, gs_stalkMap r z _ hk, isUnit_map_iff]
  refine ⟨fun ⟨l, hl, u⟩ => ?_, fun u => ⟨k, hk, u⟩⟩
  rw [gs_compat s (𝟙 Y) (r z) hk hl]
  exact (Units.isUnit _).mul u

variable {j : ℕ} {P : LB Y} {P' : LB Y'} {ρ : Fin j → (Y' ⟶ Y)} {idx : P'.ι → Fin j → P.ι}

theorem exists_boxSec (le : ∀ k i, P'.U k ≤ ρ i ⁻¹ᵁ P.U (idx k i))
    (hg : ∀ (y : Y') k k', y ∈ P'.U k → y ∈ P'.U k' →
      gm (𝟙 Y') y _ (P'.g k k') = ∏ i, gm (ρ i) y _ (P.g (idx k i) (idx k' i)))
    (s : Fin j → LB.Sec P) : ∃ t : LB.Sec P', ∀ k (y : Y'), y ∈ P'.U k →
      gs (𝟙 Y') y _ (t.f k) = ∏ i, gs (ρ i) y _ ((s i).f (idx k i)) := by
  have v : ∀ k (y : Y'), y ∈ P'.U k →
      gs (𝟙 Y') y _ (∏ i, ((ρ i).appLE _ _ (le k i)).hom ((s i).f (idx k i))) =
        ∏ i, gs (ρ i) y _ ((s i).f (idx k i)) := fun k y hy => by
    rw [gs_finprod _ y _ hy]
    exact Finset.prod_congr rfl fun i _ => by rw [gs_appLE _ _ _ _ _ y hy, Category.id_comp]
  refine ⟨⟨fun k => ∏ i, ((ρ i).appLE _ _ (le k i)).hom ((s i).f (idx k i)),
    fun k k' => fn_ext fun y hy => ?_⟩, v⟩
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, v k y hy.1, v k' y hy.2,
    hg y k k' hy.1 hy.2, Units.coe_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gs_compat _ _ _ (le k i hy.1) (le k' i hy.2)

theorem Embeds.box [IsAffine B] {π : Y ⟶ B} {π' : Y' ⟶ B}
    (hw : IsWideProduct π' (fun _ => π) ρ) (hc : ∀ y : Y', ∃ k, y ∈ P'.U k)
    (le : ∀ k i, P'.U k ≤ ρ i ⁻¹ᵁ P.U (idx k i))
    (hg : ∀ (y : Y') k k', y ∈ P'.U k → y ∈ P'.U k' →
      gm (𝟙 Y') y _ (P'.g k k') = ∏ i, gm (ρ i) y _ (P.g (idx k i) (idx k' i)))
    {I : Type} {s : I → LB.Sec P} (h : Embeds π P s) :
    ∃ t : (Fin j → I) → LB.Sec P', Embeds π' P' t := by
  classical
  choose t ht using fun a : Fin j → I => exists_boxSec le hg (fun i => s (a i))
  have loc : ∀ a (y : Y'), y ∈ nonzeroLocus (t a) ↔ ∀ i, ρ i y ∈ nonzeroLocus (s (a i)) := by
    intro a y
    obtain ⟨k, hk⟩ := hc y
    refine (mem_nonzeroLocus_pull (t a) (𝟙 Y') y hk).trans ?_
    rw [ht a k y hk, IsUnit.prod_univ_iff]
    exact forall_congr' fun i => (mem_nonzeroLocus_pull _ _ _ (le k i hk)).symm
  refine ⟨t, top_le_iff.1 fun y _ => ?_, fun a => ?_⟩
  · choose a ha using fun i => Opens.mem_iSup.1
      (show ρ i y ∈ ⨆ n, nonzeroLocus (s n) by rw [h.1]; trivial)
    exact Opens.mem_iSup.2 ⟨a, (loc a y).2 ha⟩
  have le' : ∀ i, nonzeroLocus (t a) ≤ ρ i ⁻¹ᵁ nonzeroLocus (s (a i)) :=
    fun i y hy => (loc a y).1 hy i
  choose haff r hr hsurj using h.2
  obtain ⟨k₁, k₂⟩ := hw.affineOpen ⊤ (fun i => nonzeroLocus (s (a i))) (nonzeroLocus (t a))
    (fun _ => le_top) le_top le' (fun y _ hy => (loc a y).2 hy) (isAffineOpen_top _)
    (fun i => haff _)
  have hr' : ∀ n m k {Z : Scheme.{0}} (q : Z ⟶ Y) (z : Z), q z ∈ nonzeroLocus (s n) → q z ∈ P.U k →
      gs q z _ ((s m).f k) = gs q z _ (r n m) * gs q z _ ((s n).f k) := by
    intro n m k Z q z h₁ h₂
    have hm : q z ∈ nonzeroLocus (s n) ⊓ P.U k := ⟨h₁, h₂⟩
    have e := congrArg (gs q z _) (hr n m k)
    rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm] at e
  have r1 : ∀ n, r n n = 1 := fun n => fn_ext fun y hy => by
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ y).1 hy
    have e := hr' n n k (𝟙 Y) y hy hk
    rw [gs_eq (𝟙 Y) y _ hy 1, map_one, map_one]
    exact u.mul_right_cancel (e.symm.trans (_root_.one_mul _).symm)
  refine ⟨k₁, fun b => ∏ i, ((ρ i).appLE _ _ (le' i)).hom (r (a i) (b i)),
    fun b k => fn_ext fun y hy => ?_, ?_⟩
  · rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, ht b k y hy.2,
      ht a k y hy.2, gs_finprod _ y _ hy.1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [gs_appLE _ _ _ _ _ y hy.1, Category.id_comp]
    exact hr' _ _ _ _ _ (le' i hy.1) (le k i hy.2)
  · rw [← RingHom.range_eq_top]
    refine k₂ _ (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩) fun i x => ?_
    obtain ⟨p, rfl⟩ := hsurj _ x
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨MvPolynomial.C c, ?_⟩
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      obtain rfl : ρ i ≫ π = π' := hw.1 i
      exact (congrArg (fun q => q.hom c)
        (Scheme.Hom.appLE_comp_appLE (ρ i) π ⊤ _ _ le_top (le' i))).symm
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | mul_X p m hp =>
      rw [map_mul, map_mul]
      refine mul_mem hp ⟨MvPolynomial.X (Function.update a i m), ?_⟩
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Finset.prod_eq_single i]
      · rw [Function.update_self]
      · intro l _ hl
        rw [Function.update_of_ne hl, r1, map_one]
      · simp

end

end GlobalTheory.Segre

namespace GlobalTheory
open Segre ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem relAmple_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → RelAmple G L → RelAmple G' (boxLB L p.pr) := by
  intro S G' G _ _ j p L hL hA U hU
  obtain ⟨N, hN, M, s, hs⟩ := hA U hU
  have : IsAffine U := hU
  have w₀ : IsWideProduct G'.hom (fun _ => G.hom) (fun i => (p.pr i).left) := by
    refine ⟨fun i => Over.w _, fun Z z f hf => ?_⟩
    let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk z) (fun i => Over.homMk (f i) (hf i))
    refine ⟨(p.lim.lift c).left, ⟨Over.w (p.lim.lift c), fun i =>
      congrArg (fun q => q.left) (p.lim.fac c ⟨i⟩)⟩, fun g hg => ?_⟩
    exact congrArg (fun q => q.left) (p.lim.uniq c (Over.homMk g hg.1)
      (fun i => Over.OverMorphism.ext (hg.2 i.as)))
  have le : ∀ i, G'.hom ⁻¹ᵁ U ≤ (p.pr i).left ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := fun i y hy =>
    (congrArg (fun q => q y ∈ U) (Over.w (p.pr i))).mpr hy
  have w₁ := w₀.resLE U (fun _ => G.hom ⁻¹ᵁ U) (G'.hom ⁻¹ᵁ U) (fun _ => le_rfl) le_rfl le
    (fun y hy _ => hy)
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at w₁
  set ρ : Fin j → ((G'.hom ⁻¹ᵁ U).toScheme ⟶ (G.hom ⁻¹ᵁ U).toScheme) :=
    fun i => (p.pr i).left.resLE _ _ (le i) with hρ
  have hι : ∀ i, ρ i ≫ (G.hom ⁻¹ᵁ U).ι = (G'.hom ⁻¹ᵁ U).ι ≫ (p.pr i).left :=
    fun i => Scheme.Hom.resLE_comp_ι _ _
  have le₂ : ∀ (k : Fin N → Fin j → L.ι) (i : Fin j), (powOver G' (boxLB L p.pr) U N).U k ≤
      ρ i ⁻¹ᵁ (powOver G L U N).U (fun n => k n i) := fun k i y hy =>
    Set.mem_iInter.2 fun n => (congrArg (fun q => q y ∈ L.U (k n i)) (hι i)).mpr
      (Set.mem_iInter.1 (Set.mem_iInter.1 hy n) i)
  obtain ⟨t, ht⟩ := Embeds.box (P := powOver G L U N) (P' := powOver G' (boxLB L p.pr) U N)
    (idx := fun k i n => k n i) w₁
    (exists_chart (LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _)) le₂
    (fun y k k' hk hk' => by
      refine (gm_linComb (boxLB L p.pr) (fun _ : Fin N => (G'.hom ⁻¹ᵁ U).ι) (fun _ => 1) (𝟙 _) y k k' hk hk').trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ =>
        (gm_linComb L (fun _ : Fin N => (G.hom ⁻¹ᵁ U).ι) (fun _ => 1) (ρ i) y _ _ (le₂ k i hk) (le₂ k' i hk')).symm)
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [zpow_one]
      refine (gm_linComb L (fun i => (p.pr i).left) (fun _ => 1) (𝟙 _ ≫ (G'.hom ⁻¹ᵁ U).ι) y _ _
        (Set.mem_iInter.1 hk n) (Set.mem_iInter.1 hk' n)).trans ?_
      simp only [hι, Category.id_comp]) (s := s) hs
  have hpos : 0 < Fintype.card (Fin j → Fin (M + 1)) := Fintype.card_pos
  obtain ⟨M', hM'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  exact ⟨N, hN, M', _, ht.reindex (Fintype.equivFinOfCardEq hM').symm⟩

end GlobalTheory
