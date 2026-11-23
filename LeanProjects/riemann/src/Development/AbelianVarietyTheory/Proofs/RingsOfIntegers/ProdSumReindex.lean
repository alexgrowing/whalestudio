import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

section Pointwise

variable {X X₁ X₂ Y Y' Z Z₁ Z₂ : Scheme.{0}}

def pw {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂))
    (r : Z ⟶ Y) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z ((L₂.pull f₂).U (fun _ => j₂) ⊓ (L₁.pull f₁).U (fun _ => j₁)) (w.s (fun _ => j₂, fun _ => j₁))

theorem iso_trans {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gm f y (L.U j ⊓ L'.U k) (w.s (j, k)) =
      gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gm f y (L.U j' ⊓ L'.U k') (w.s (j', k')) := by
  have hm : f y ∈ L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
  have e := congrArg (gm f y (L.U j ⊓ L'.U k ⊓ (L.U j' ⊓ L'.U k'))) (hw (j, k) (j', k'))
  exact (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div L' L f y (j, k) (j', k') hm) (gm_res f y _ hm _))))

theorem pw_trans {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)}
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) {j₁ j₁' : L₁.ι} {j₂ j₂' : L₂.ι} (h₁ : f₁ (r z) ∈ L₁.U j₁)
    (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    pw w r z j₁ j₂ = gm (r ≫ f₂) z _ (L₂.g j₂ j₂') * (gm (r ≫ f₁) z _ (L₁.g j₁ j₁'))⁻¹ * pw w r z j₁' j₂' := by
  have := iso_trans hw r z (fun _ => j₂) (fun _ => j₂') (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₂) (mem_pull.2 h₂')
    (mem_pull.2 h₁) (mem_pull.2 h₁')
  rw [gm_pull_g L₂ f₂ r z _ _ (mem_pull.2 h₂) (mem_pull.2 h₂'),
    gm_pull_g L₁ f₁ r z _ _ (mem_pull.2 h₁) (mem_pull.2 h₁')] at this
  exact this

theorem bw_trans {X' : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z) {a a' : Fin j → M.ι}
    {b b' : M'.ι} (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (ha' : ∀ i, pr i (ψ z) ∈ M.U (a' i)) (hb : ψ z ∈ M'.U b)
    (hb' : ψ z ∈ M'.U b') :
    bw w ψ z a b = (∏ i, gm (ψ ≫ pr i) z _ (M.g (a i) (a' i))) * (gm ψ z _ (M'.g b b'))⁻¹ * bw w ψ z a' b' := by
  have := iso_trans hw ψ z a a' b b' (Set.mem_iInter.2 ha) (Set.mem_iInter.2 ha') hb hb'
  have e := gm_linComb M pr (fun _ => 1) ψ z a a' (Set.mem_iInter.2 ha) (Set.mem_iInter.2 ha')
  simp only [zpow_one] at e
  rw [← e]
  exact this

variable {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)}
  {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
  {a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))} {g₂ : Z₂ ⟶ X₂} {h₂ : Y' ⟶ Z₂}
  {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))}

theorem isoRel_germ (r : Z ⟶ Y') (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι)
    (hz : r z ∈ GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => j₂, fun _ => j₁) (fun _ => j₁) (fun _ => j₂)) :
    gs r z _ ((Y'.presheaf.map (homOfLE (inf_le_right :
        GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => j₂, fun _ => j₁) (fun _ => j₁) (fun _ => j₂) ≤
          h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => j₂))).op).hom ((h₂.app _).hom (b.f (fun _ => j₂)))) =
      gs (r ≫ h₂) z (LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => j₂)) (b.f (fun _ => j₂)) ∧
    gs r z _ ((res (inf_le_left.trans inf_le_left :
          GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => j₂, fun _ => j₁) (fun _ => j₁) (fun _ => j₂) ≤
            m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U (fun _ => j₂, fun _ => j₁))
          (pullU m _ (w.s (fun _ => j₂, fun _ => j₁)))).val ^ k *
      (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => j₂, fun _ => j₁) (fun _ => j₁) (fun _ => j₂) ≤
          h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => j₁))).op).hom ((h₁.app _).hom (a.f (fun _ => j₁)))) =
      (pw w (r ≫ m) z j₁ j₂ ^ k).val *
        gs (r ≫ h₁) z (LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => j₁)) (a.f (fun _ => j₁)) := by
  refine ⟨(gs_res r z _ hz _).trans (gs_pull r _ z _ hz.2 _), (gs_mul r z _ hz _ _).trans
    (congrArg₂ (· * ·) ?_ ((gs_res r z _ hz _).trans (gs_pull r _ z _ hz.1.2 _)))⟩
  rw [← Units.val_pow_eq_pow_val, gs_unit r z _ hz, map_pow]
  exact congrArg (fun u => (u ^ k).val) ((gm_res r z _ hz _).trans (gm_pull r m z ((L₂.pull f₂).U (fun _ => j₂) ⊓ (L₁.pull f₁).U (fun _ => j₁)) hz.1.1 _))

theorem isoRel_val (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b) (r : Z ⟶ Y') (z : Z) {J₁ J₂}
    (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval b (r ≫ h₂) z J₂ =
      (pw w (r ≫ m) z (J₁ ((r ≫ m) ≫ f₁)) (J₂ ((r ≫ m) ≫ f₂)) ^ k).val * sval a (r ≫ h₁) z J₁ := by
  obtain ⟨e₁, e₂, H⟩ := H
  have c₁ : (r ≫ h₁) ≫ g₁ = (r ≫ m) ≫ f₁ := by rw [Category.assoc, e₁, Category.assoc]
  have c₂ : (r ≫ h₂) ≫ g₂ = (r ≫ m) ≫ f₂ := by rw [Category.assoc, e₂, Category.assoc]
  rw [sval_of a _ z J₁ (fun _ => J₁ ((r ≫ m) ≫ f₁)) (fun _ => congrArg J₁ c₁),
    sval_of b _ z J₂ (fun _ => J₂ ((r ≫ m) ≫ f₂)) (fun _ => congrArg J₂ c₂)]
  have hz : r z ∈ GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => J₂ ((r ≫ m) ≫ f₂), fun _ => J₁ ((r ≫ m) ≫ f₁))
      (fun _ => J₁ ((r ≫ m) ≫ f₁)) (fun _ => J₂ ((r ≫ m) ≫ f₂)) :=
    ⟨⟨⟨mem_pull.2 (hJ₂ ((r ≫ m) ≫ f₂)), mem_pull.2 (hJ₁ ((r ≫ m) ≫ f₁))⟩,
      Set.mem_iInter.2 fun _ => by have := hJ₁ ((r ≫ h₁) ≫ g₁); rw [congrArg J₁ c₁] at this; exact this⟩,
      Set.mem_iInter.2 fun _ => by have := hJ₂ ((r ≫ h₂) ≫ g₂); rw [congrArg J₂ c₂] at this; exact this⟩
  obtain ⟨k₁, k₂⟩ := isoRel_germ (w := w) (a := a) (b := b) r z _ _ hz
  exact k₁.symm.trans ((congrArg (gs r z _) (H (fun _ => J₂ ((r ≫ m) ≫ f₂), fun _ => J₁ ((r ≫ m) ≫ f₁)) _ _ rfl
    rfl)).trans k₂)

theorem isoRel_of_val (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (e₁ : h₁ ≫ g₁ = m ≫ f₁) (e₂ : h₂ ≫ g₂ = m ≫ f₂)
    (H : ∀ (y : Y') J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ → sval b h₂ y J₂ =
      (pw w m y (J₁ (m ≫ f₁)) (J₂ (m ≫ f₂)) ^ k).val * sval a h₁ y J₁) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b := by
  refine ⟨e₁, e₂, ?_⟩
  rintro ⟨p₂, p₁⟩ j₁ j₂ q₁ q₂
  obtain rfl : j₁ = fun _ => p₁ PUnit.unit := funext fun i => (congrArg j₁ (Subsingleton.elim i 0)).trans q₁
  obtain rfl : j₂ = fun _ => p₂ PUnit.unit := funext fun i => (congrArg j₂ (Subsingleton.elim i 0)).trans q₂
  refine fn_ext fun y hy => ?_
  obtain ⟨k₁, k₂⟩ := isoRel_germ (w := w) (a := a) (b := b) (𝟙 _) y (p₁ PUnit.unit) (p₂ PUnit.unit) hy
  obtain ⟨J₁, hJ₁, c₁⟩ := exists_good L₁ hL₁ y (fun _ : Unit => m ≫ f₁) (fun _ => p₁ PUnit.unit) (fun _ _ _ => rfl)
    (fun _ => (mem_pull (F := f₁) (x := m y)).1 hy.1.1.2)
  obtain ⟨J₂, hJ₂, c₂⟩ := exists_good L₂ hL₂ y (fun _ : Unit => m ≫ f₂) (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl)
    (fun _ => (mem_pull (F := f₂) (x := m y)).1 hy.1.1.1)
  have := H y J₁ J₂ hJ₁ hJ₂
  rw [sval_of a _ y J₁ (fun _ => p₁ PUnit.unit) (fun _ => (congrArg J₁ e₁).trans (c₁ ())),
    sval_of b _ y J₂ (fun _ => p₂ PUnit.unit) (fun _ => (congrArg J₂ e₂).trans (c₂ ())), c₁ (), c₂ ()] at this
  simp only [Category.id_comp] at k₁ k₂
  exact k₁.trans (this.trans k₂.symm)

end Pointwise

section Lin

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem secLin_val {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} {c : Fin n → Γ(Y', ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  simp only [sval_of (s _) (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs r z _) e).trans ((gs_fsum r z _ hm _ _).trans
    (Finset.sum_congr rfl fun i _ => ?_)))
  exact (gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _)
    ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)))

theorem exists_secLin (hL : L.IsLB) {F : Type} [CommRing F] (π : Y' ⟶ Spec (CommRingCat.of F)) (h : Y' ⟶ Y)
    (φ₁ : K → (Y' ⟶ X)) (hφ : ∀ a, φ₁ a = h ≫ φ a) {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (c : Fin n → F) :
    ∃ s₁ : LB.Sec (LB.LinComb L φ₁ ε), GeneratorPullback.SecLin L φ₁ ε s₁ φ ε s h (fun i => scal π (c i)) := by
  obtain rfl : φ₁ = fun a => h ≫ φ a := funext hφ
  exact ⟨_, (secLin_iff (π' := π) hL _ s h c (fun i => pullSec L φ ε (s i) h)
    (fun i y J hJ => SectionScalarValuation.sval_pullSec φ ε (s i) h (𝟙 _) y hJ)).2 rfl⟩

def constHomVal {F : Type} [CommRing F] (π : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  ((Z.presheaf.germ (π ⁻¹ᵁ ⊤) z trivial).hom.comp (π.app ⊤).hom).comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem constVal_eq {F : Type} [CommRing F] (π : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal π z c = constHomVal π z c := gs_eq π z ⊤ trivial _

theorem prod_sum_reindex {S F : Type} [CommRing S] [CommRing F] (χ : F →+* S) {j : ℕ} {n : Fin j → ℕ} {N : ℕ}
    (e : Fin N ≃ ∀ i, Fin (n i)) (C : F) (c : ∀ i, Fin (n i) → F) (x : ∀ i, Fin (n i) → S) :
    ∑ l, χ (C * ∏ i, c i (e l i)) * ∏ i, x i (e l i) = χ C * ∏ i, ∑ a, χ (c i a) * x i a := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_prod, Finset.prod_mul_distrib, _root_.mul_assoc]

end Lin

section Box

variable {X X' Y Y' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {p : Fin j → (Y' ⟶ Y)} (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
      p i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((p i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ p i) y J := by
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  refine ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit q y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w φ' ε q y _ _ hm))) (gs_res q y _ hm _))).symm.trans (E.trans ((gs_prod q y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (s i) _ y J (fun a => J ((q ≫ φ' a) ≫ pr i)) (fun a => by rw [Category.assoc, ← hφ, Category.assoc])]
  exact (gs_res q y (hle _ _ i) hm _).trans (gs_pull q (p i) y _ (hle _ _ i hm) _)

theorem boxG_val {R : Type} [CommRing R] [IsDomain R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {LG : LB G.left} {LG' : LB G'.left} {pG : IsPowGrp G' G j}
    {w : LB.Iso LG' (boxLB LG pG.pr)} {k : ℕ} {σ' : H0 LG' k} {σ : Fin j → H0 LG k} (H : IsBoxSecG pG w k σ' σ)
    (q : Z ⟶ G'.left) (y : Z) {J J'} (hJ : Good LG y J) (hJ' : Good LG' y J') :
    (bw w q y (fun i => J (q ≫ (pG.pr i).left)) (J' q) ^ k).val * sval σ' q y J' =
      ∏ i, sval (σ i) (q ≫ (pG.pr i).left) y J := by
  have mL : q y ∈ (LB.div (boxLB LG pG.pr) LG').U (fun i => J (q ≫ (pG.pr i).left), J' q) :=
    ⟨Set.mem_iInter.2 fun i => hJ (q ≫ (pG.pr i).left), hJ' q⟩
  have Sg := congrArg (gs q y ((LB.div (boxLB LG pG.pr) LG').U (fun i => J (q ≫ (pG.pr i).left), J' q)))
    (H (fun i => J (q ≫ (pG.pr i).left)) (J' q))
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  rw [sval_of σ' q y J' (fun _ => J' q) (fun _ => by rw [Category.comp_id])]
  refine (congrArg₂ (· * ·) rfl (gs_res q y (boxG_le_b pG _ _) mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (σ i) _ y J (fun _ => J (q ≫ (pG.pr i).left)) (fun _ => by rw [Category.comp_id])]
  exact (gs_res q y (boxG_le_c pG _ _ i) mL _).trans
    (gs_pull q (pG.pr i).left y _ (boxG_le_c pG _ _ i mL) _)

end Box

section Ratio

variable {X X' Γ Γ' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB Γ} {M' : LB Γ'} {j : ℕ}
  {pr : Fin j → (X' ⟶ X)} {qr : Fin j → (Γ' ⟶ Γ)} {f₁ : Y ⟶ X} {f₂ : Y ⟶ Γ} {f₁' : Y' ⟶ X'} {f₂' : Y' ⟶ Γ'}
  {ρ : Fin j → (Y' ⟶ Y)}

theorem exists_ratio (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    (e₁ : ∀ i, f₁' ≫ pr i = ρ i ≫ f₁) (e₂ : ∀ i, f₂' ≫ qr i = ρ i ≫ f₂)
    {wA : LB.Iso L' (LB.LinComb L pr (fun _ => 1))} (hA : wA.IsGen)
    {wL : LB.Iso M' (LB.LinComb M qr (fun _ => 1))} (hG : wL.IsGen)
    {w : LB.Iso (L.pull f₁) (M.pull f₂)} (hw : w.IsGen) {w' : LB.Iso (L'.pull f₁') (M'.pull f₂')} (hw' : w'.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : Fin j → L.ι) (a' : L'.ι) (b : Fin j → M.ι) (b' : M'.ι),
      (∀ i, pr i (f₁' (r z)) ∈ L.U (a i)) → f₁' (r z) ∈ L'.U a' → (∀ i, qr i (f₂' (r z)) ∈ M.U (b i)) →
      f₂' (r z) ∈ M'.U b' →
      bw wL (r ≫ f₂') z b b' * pw w' r z a' b' =
        gm r z ⊤ u * ((∏ i, pw w (r ≫ ρ i) z (a i) (b i)) * bw wA (r ≫ f₁') z a a') := by
  let I := ((Fin j → L.ι) × L'.ι) × ((Fin j → M.ι) × M'.ι)
  let W : I → Y'.Opens := fun p => f₁' ⁻¹ᵁ (LB.wchart L pr p.1.1 ⊓ L'.U p.1.2) ⊓ f₂' ⁻¹ᵁ (LB.wchart M qr p.2.1 ⊓ M'.U p.2.2)
  have m₁ : ∀ (y : Y') (a : L.ι) i, pr i (f₁' y) ∈ L.U a → f₁ (ρ i y) ∈ L.U a := fun y a i h =>
    (congrArg (fun g : Y' ⟶ X => g y ∈ L.U a) (e₁ i)).mp h
  have m₂ : ∀ (y : Y') (a : M.ι) i, qr i (f₂' y) ∈ M.U a → f₂ (ρ i y) ∈ M.U a := fun y a i h =>
    (congrArg (fun g : Y' ⟶ Γ => g y ∈ M.U a) (e₂ i)).mp h
  have l₃ : ∀ p : I, W p ≤ (M'.pull f₂').U (fun _ => p.2.2) ⊓ (L'.pull f₁').U (fun _ => p.1.2) := fun p y hy =>
    ⟨mem_pull.2 hy.2.2, mem_pull.2 hy.1.2⟩
  have l₄ : ∀ (p : I) i, W p ≤ ρ i ⁻¹ᵁ ((M.pull f₂).U (fun _ => p.2.1 i) ⊓ (L.pull f₁).U (fun _ => p.1.1 i)) :=
    fun p i y hy => ⟨mem_pull.2 (m₂ y _ i (Set.mem_iInter.1 hy.2.1 i)), mem_pull.2 (m₁ y _ i (Set.mem_iInter.1 hy.1.1 i))⟩
  let θ : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), I → (Z.presheaf.stalk z)ˣ := fun Z r z p =>
    bw wL (r ≫ f₂') z p.2.1 p.2.2 * pw w' r z p.1.2 p.2.2 *
      ((∏ i, pw w (r ≫ ρ i) z (p.1.1 i) (p.2.1 i)) * bw wA (r ≫ f₁') z p.1.1 p.1.2)⁻¹
  obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y', W p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
      gm r z (W p) (u p) = θ Z r z p := by
    refine ⟨fun p => res inf_le_right (pullU f₂' (LB.wchart M qr p.2.1 ⊓ M'.U p.2.2) (wL.s (p.2.1, p.2.2))) *
      res (l₃ p) (w'.s (fun _ => p.2.2, fun _ => p.1.2)) *
      ((∏ i, res (l₄ p i) (pullU (ρ i) ((M.pull f₂).U (fun _ => p.2.1 i) ⊓ (L.pull f₁).U (fun _ => p.1.1 i))
        (w.s (fun _ => p.2.1 i, fun _ => p.1.1 i)))) *
       res inf_le_left (pullU f₁' (LB.wchart L pr p.1.1 ⊓ L'.U p.1.2) (wA.s (p.1.1, p.1.2))))⁻¹, fun Z r z p hz => ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, map_prod]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r f₂' z _ hz.2 _))
      (gm_res r z _ hz _)) (congrArg (·⁻¹) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ =>
        (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (l₄ p i hz) _))
        ((gm_res r z _ hz _).trans (gm_pull r f₁' z _ hz.1 _))))
  have hθ : ∀ (y : Y') (p q : I), y ∈ W p → y ∈ W q → θ _ (𝟙 Y') y p = θ _ (𝟙 Y') y q := by
    intro y p q hp hq
    have t₁ := bw_trans hG (𝟙 Y' ≫ f₂') y (a := p.2.1) (a' := q.2.1) (b := p.2.2) (b' := q.2.2)
      (Set.mem_iInter.1 hp.2.1) (Set.mem_iInter.1 hq.2.1) hp.2.2 hq.2.2
    have t₂ := bw_trans hA (𝟙 Y' ≫ f₁') y (a := p.1.1) (a' := q.1.1) (b := p.1.2) (b' := q.1.2)
      (Set.mem_iInter.1 hp.1.1) (Set.mem_iInter.1 hq.1.1) hp.1.2 hq.1.2
    have t₃ := pw_trans hw' (𝟙 Y') y (j₁ := p.1.2) (j₁' := q.1.2) (j₂ := p.2.2) (j₂' := q.2.2) hp.1.2 hq.1.2 hp.2.2 hq.2.2
    have t₄ := fun i => pw_trans hw (𝟙 Y' ≫ ρ i) y (j₁ := p.1.1 i) (j₁' := q.1.1 i) (j₂ := p.2.1 i) (j₂' := q.2.1 i)
      (m₁ y _ i (Set.mem_iInter.1 hp.1.1 i)) (m₁ y _ i (Set.mem_iInter.1 hq.1.1 i))
      (m₂ y _ i (Set.mem_iInter.1 hp.2.1 i)) (m₂ y _ i (Set.mem_iInter.1 hq.2.1 i))
    simp only [θ]
    rw [t₁, t₂, t₃, Finset.prod_congr rfl fun i _ => t₄ i]
    simp only [Category.assoc, e₁, e₂, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      choose a ha using fun i => exists_chart hL (pr i (f₁' y))
      choose b hb using fun i => exists_chart hM (qr i (f₂' y))
      obtain ⟨a', ha'⟩ := exists_chart hL' (f₁' y)
      obtain ⟨b', hb'⟩ := exists_chart hM' (f₂' y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨((a, a'), (b, b')), ⟨Set.mem_iInter.2 ha, ha'⟩, Set.mem_iInter.2 hb, hb'⟩) u
    (fun p q y hy => (hu _ _ y p hy.1).trans ((hθ y p q hy.1 hy.2).trans (hu _ _ y q hy.2).symm))
  refine ⟨s, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩
  have hz : r z ∈ W ((a, a'), (b, b')) := ⟨⟨Set.mem_iInter.2 ha, ha'⟩, Set.mem_iInter.2 hb, hb'⟩
  have := (gm_res r z le_top hz s).symm.trans ((congrArg (gm r z _) (hs ((a, a'), (b, b')))).trans (hu Z r z _ hz))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

end Ratio

section Combine

variable {F : Type} [CommRing F] {j : ℕ} {n : Fin j → ℕ} {N : ℕ} (e : Fin N ≃ ∀ i, Fin (n i)) (C : F)
  (c : ∀ i, Fin (n i) → F)

theorem secLin_box {X X' Y Y' B B' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    {pr : Fin j → (X' ⟶ X)} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ψ' : K → (B' ⟶ X')} {ψ : Fin j → K → (B ⟶ X)}
    {p : Fin j → (Y' ⟶ Y)} {q : Fin j → (B' ⟶ B)} {h' : Y' ⟶ B'} {h : Y ⟶ B}
    {π' : Y' ⟶ Spec (CommRingCat.of F)} {π : Y ⟶ Spec (CommRingCat.of F)}
    (e₁ : ∀ a, φ' a = h' ≫ ψ' a) (e₂ : ∀ i, h' ≫ q i = p i ≫ h) (e₃ : ∀ i, p i ≫ π = π')
    (S S₁ : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (f : ∀ i, Fin (n i) → LB.Sec (LB.LinComb M (ψ i) ε)) (f' : Fin N → LB.Sec (LB.LinComb M' ψ' ε))
    (hS₁ : ∀ jj, S₁.f jj = resTop _ (scal π' C) * S.f jj)
    (hS : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval S (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ p i) y J)
    (hf : ∀ l y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval (f' l) h' y J' = ∏ i, sval (f i (e l i)) (h' ≫ q i) y J)
    (hs : ∀ i, GeneratorPullback.SecLin M (φ i) ε (s i) (ψ i) ε (f i) h (fun a => scal π (c i a))) :
    GeneratorPullback.SecLin M' φ' ε S₁ ψ' ε f' h' (fun l => scal π' (C * ∏ i, c i (e l i))) := by
  refine (secLin_iff_val hM' _ _ _ _).2 fun y J' hJ' => ?_
  choose J hJ using fun χ : Y' ⟶ X => exists_chart hM (χ y)
  have hJ : Good M y J := hJ
  have a₁ := hS y J J' hJ hJ'
  have a₂ := fun l => hf l y J J' hJ hJ'
  have a₃ := fun i => secLin_val (hs i) (p i) y hJ
  have a₄ : sval S₁ (𝟙 Y') y J' = constHomVal π' y C * sval S (𝟙 Y') y J' := by
    have hm := hJ'.mem φ' (𝟙 Y')
    refine (congrArg (gs (𝟙 Y') y _) (hS₁ _)).trans ((gs_mul _ y _ hm _ _).trans (congrArg (· * _) ?_))
    exact (gs_const π' _ y _ hm C).trans (by rw [Category.id_comp, constVal_eq])
  simp only [Category.id_comp, gs_scal, e₃, constVal_eq, e₁, e₂] at a₁ a₂ a₃ ⊢
  refine (Units.mul_right_inj (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a)).1 ?_
  rw [a₄, mul_left_comm, a₁, Finset.mul_sum, Finset.prod_congr rfl fun i _ => a₃ i, ← prod_sum_reindex _ e]
  exact Finset.sum_congr rfl fun l _ => by rw [← a₂ l, mul_left_comm]

variable {X X' Γ Γ' Y Y' T T' E E' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB Γ} {M' : LB Γ'}
  {pr : Fin j → (X' ⟶ X)} {qr : Fin j → (Γ' ⟶ Γ)} {f₁ : Y ⟶ X} {f₂ : Y ⟶ Γ} {f₁' : Y' ⟶ X'} {f₂' : Y' ⟶ Γ'}
  {ρ : Fin j → (Y' ⟶ Y)}

theorem isoRel_box (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    (e₁ : ∀ i, f₁' ≫ pr i = ρ i ≫ f₁) (e₂ : ∀ i, f₂' ≫ qr i = ρ i ≫ f₂)
    (wA : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (wL : LB.Iso M' (LB.LinComb M qr (fun _ => 1)))
    (w : LB.Iso (L.pull f₁) (M.pull f₂)) (w' : LB.Iso (L'.pull f₁') (M'.pull f₂')) (u : Γ(Y', ⊤)ˣ)
    (hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : Fin j → L.ι) (a' : L'.ι) (b : Fin j → M.ι) (b' : M'.ι),
      (∀ i, pr i (f₁' (r z)) ∈ L.U (a i)) → f₁' (r z) ∈ L'.U a' → (∀ i, qr i (f₂' (r z)) ∈ M.U (b i)) →
      f₂' (r z) ∈ M'.U b' →
      bw wL (r ≫ f₂') z b b' * pw w' r z a' b' =
        gm r z ⊤ u * ((∏ i, pw w (r ≫ ρ i) z (a i) (b i)) * bw wA (r ≫ f₁') z a a'))
    {k : ℕ} {m : T ⟶ Y} {m' : T' ⟶ Y'} {τ : Fin j → (T' ⟶ T)} {g : E ⟶ X} {g' : E' ⟶ X'} {h : T ⟶ E} {h' : T' ⟶ E'}
    {κ : Fin j → (E' ⟶ E)} {π' : T' ⟶ Spec (CommRingCat.of F)} {π : T ⟶ Spec (CommRingCat.of F)}
    (e₃ : ∀ i, τ i ≫ m = m' ≫ ρ i) (e₄ : ∀ i, h' ≫ κ i = τ i ≫ h) (e₅ : h' ≫ g' = m' ≫ f₁') (e₆ : ∀ i, τ i ≫ π = π')
    (hC : ∀ y, (gm m' y ⊤ u ^ k).val = constVal π' y C)
    (t : Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))))
    (t' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (k : ℤ))))
    (ht : ∀ y J J', Good L y J → Good L' y J' →
      (bw wA (h' ≫ g') y (fun i => J ((h' ≫ g') ≫ pr i)) (J' (h' ≫ g')) ^ k).val * sval t' h' y J' =
        ∏ i, sval (t i) (h' ≫ κ i) y J)
    (s : Fin j → LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ))))
    (s' : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => m' ≫ f₂') (fun _ => (k : ℤ))))
    (σ : ∀ i, Fin (n i) → H0 M k) (σ' : Fin N → H0 M' k)
    (hσ : ∀ l y J J', Good M y J → Good M' y J' →
      (bw wL (m' ≫ f₂') y (fun i => J ((m' ≫ f₂') ≫ qr i)) (J' (m' ≫ f₂')) ^ k).val * sval (σ' l) (m' ≫ f₂') y J' =
        ∏ i, sval (σ i (e l i)) ((m' ≫ f₂') ≫ qr i) y J)
    (hR : ∀ i, GeneratorPullback.IsoRelM L M f₁ f₂ w m k g h (t i) (m ≫ f₂) (𝟙 T) (s i))
    (hs : ∀ i, GeneratorPullback.SecLin M (fun _ : Fin 1 => m ≫ f₂) (fun _ => (k : ℤ)) (s i) (fun _ : Fin 1 => 𝟙 Γ)
      (fun _ => (k : ℤ)) (σ i) (m ≫ f₂) (fun a => scal π (c i a)))
    (hs' : GeneratorPullback.SecLin M' (fun _ : Fin 1 => m' ≫ f₂') (fun _ => (k : ℤ)) s' (fun _ : Fin 1 => 𝟙 Γ')
      (fun _ => (k : ℤ)) σ' (m' ≫ f₂') (fun l => scal π' (C * ∏ i, c i (e l i)))) :
    GeneratorPullback.IsoRelM L' M' f₁' f₂' w' m' k g' h' t' (m' ≫ f₂') (𝟙 T') s' := by
  refine isoRel_of_val hL' hM' e₅ (Category.id_comp _) fun y J' I' hJ' hI' => ?_
  choose J hJ using fun χ : T' ⟶ X => exists_chart hL (χ y)
  choose I hI using fun χ : T' ⟶ Γ => exists_chart hM (χ y)
  have hJ : Good L y J := hJ
  have hI : Good M y I := hI
  have c₁ : ∀ i, (m' ≫ ρ i) ≫ f₁ = (m' ≫ f₁') ≫ pr i := fun i => by rw [Category.assoc, Category.assoc, e₁]
  have c₂ : ∀ i, (m' ≫ ρ i) ≫ f₂ = (m' ≫ f₂') ≫ qr i := fun i => by rw [Category.assoc, Category.assoc, e₂]
  have c₃ : ∀ i, τ i ≫ m ≫ f₂ = (m' ≫ f₂') ≫ qr i := fun i => by rw [← c₂, ← e₃, Category.assoc]
  have a₀ := hu _ m' y (fun i => J ((m' ≫ f₁') ≫ pr i)) (J' (m' ≫ f₁')) (fun i => I ((m' ≫ f₂') ≫ qr i))
    (I' (m' ≫ f₂')) (fun i => hJ ((m' ≫ f₁') ≫ pr i)) (hJ' (m' ≫ f₁')) (fun i => hI ((m' ≫ f₂') ≫ qr i))
    (hI' (m' ≫ f₂'))
  have a₁ := ht y J J' hJ hJ'
  have a₂ := fun l => hσ l y I I' hI hI'
  have a₃ := fun i => secLin_val (hs i) (τ i) y hI
  have a₄ := secLin_val hs' (𝟙 _) y hI'
  have a₅ := fun i => isoRel_val (hR i) (τ i) y hJ hI
  have a₆ := (hC y).trans (constVal_eq _ _ _)
  simp only [gs_scal, e₆, constVal_eq, c₃, Category.id_comp] at a₃ a₄
  simp only [Category.comp_id, e₃, c₁, c₂] at a₅
  simp only [e₅, e₄] at a₁
  refine (Units.mul_right_inj (bw wL (m' ≫ f₂') y (fun i => I ((m' ≫ f₂') ≫ qr i)) (I' (m' ≫ f₂')) ^ k)).1 ?_
  rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, a₀, mul_pow, mul_pow, Units.val_mul, Units.val_mul, a₆,
    _root_.mul_assoc, _root_.mul_assoc, a₁, ← Finset.prod_pow, Units.coe_prod, ← Finset.prod_mul_distrib,
    ← Finset.prod_congr rfl fun i _ => a₅ i, Finset.prod_congr rfl fun i _ => a₃ i, ← prod_sum_reindex _ e, a₄,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← a₂ l, mul_left_comm]

end Combine

theorem unit_const (hG : GlobalFnsSt) {K : Type} [Field K] (A : PolAV (Spec (CommRingCat.of K)))
    {Y : Over (Spec (CommRingCat.of K))} (g : Y ≅ A.A) (u : Γ(Y.left, ⊤)ˣ) :
    ∃ c : K, c ≠ 0 ∧ u.val = scal Y.hom c := by
  have hb : Function.Bijective (scal Y.hom : K → Γ(Y.left, ⊤)) := by
    have h₁ := hG _ A.A A.isAb
    have : IsIso g.hom.left := inferInstanceAs (IsIso ((Over.forget _).map g.hom))
    have h₂ : Function.Bijective g.hom.left.appTop.hom := ConcreteCategory.bijective_of_isIso (g.hom.left.app ⊤)
    have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv
    rw [← Over.w g.hom]
    exact h₂.comp (h₁.comp h₃)
  obtain ⟨c, hc⟩ := hb.2 u.val
  refine ⟨c, fun h => ?_, hc.symm⟩
  have h₀ : scal Y.hom (0 : K) = 0 := by simp [scal]
  have h₁ : scal Y.hom (1 : K) = 1 := by simp [scal]
  rw [h, h₀] at hc
  exact zero_ne_one (hb.1 (h₀.trans (Eq.trans (by rw [← u.mul_inv, ← hc, zero_mul]) h₁.symm)))

set_option maxHeartbeats 1000000 in

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (w' : LB.Iso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R)))), w'.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ c : F, c ≠ 0 ∧ ∀ (t : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (s : Fin j → Fam D.toPre F k) (t' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))) (S : Fam D'.toPre F k), (∀ i, U.ExpandsF F k w (t i) (s i)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) → IsBoxFam pD F k S s → U'.ExpandsF F k w' t' (c • S) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P w hw w' hw' F _ _ k
  classical
  have e₁ : ∀ i, U'.gen.hom.left ≫ (pA.pr i).left = prK pG i ≫ U.gen.hom.left := fun i =>
    congrArg (fun q => q.left) (P.gen_pr i)
  have e₂ : ∀ i, pullback.fst G'.hom (jK R) ≫ (pG.pr i).left = prK pG i ≫ pullback.fst G.hom (jK R) := fun i =>
    (prK_fst pG i).symm
  obtain ⟨u, hu⟩ := exists_ratio A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w_gen P.wL_gen hw hw'
  obtain ⟨c₀, hc₀, huc⟩ := unit_const hG A' U'.gen u
  refine ⟨algebraMap (FractionRing R) F c₀ ^ k, pow_ne_zero _ ((map_ne_zero _).2 hc₀), fun t s t' S hE ht hS => ?_⟩
  choose σF hR n c σ f hA hs hf using hE
  let e := (Fintype.equivFin (∀ i, Fin (n i))).symm
  let σ' := fun l => boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k (fun i => σ i (e l i))
  obtain ⟨s', hs'⟩ := exists_secLin U'.LG.isLB (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left
    (UnifPre.gFK (G := G') F) (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => (Category.comp_id _).symm) σ'
    (fun l => algebraMap (FractionRing R) F c₀ ^ k * ∏ i, c i (e l i))
  refine ⟨s', ?_, _, _, σ', fun l => boxFamB pD k (fun i => f i (e l i)), fun l ee => ?_, hs', fun α' => ?_⟩
  · refine isoRel_box e (algebraMap (FractionRing R) F c₀ ^ k) c A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w P.wL w w'
      u hu (τ := fun i => (TFK (R := R) F ◁ (Over.pullback (jK R)).map (pG.pr i)).left)
      (κ := fun i => (TFK (R := R) F ◁ pA.pr i).left) (fun i => ?_) (fun i => ?_) ?_ (fun i => ?_) (fun y => ?_) t t'
      (fun y J J' hJ hJ' => ht _ _ y J J' hJ hJ') σF s' σ σ'
      (fun l y J J' hJ hJ' => boxG_val (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k _) _ y hJ hJ') hR hs hs'
    · exact congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map (pG.pr i)))
    · refine congrArg (fun q => q.left) (?_ : U'.genF F ≫ TFK (R := R) F ◁ pA.pr i =
        TFK (R := R) F ◁ (Over.pullback (jK R)).map (pG.pr i) ≫ U.genF F)
      ext1
      · simp
      · simp [P.gen_pr]
    · exact congrArg (fun q => q.left) (lift_snd (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G'))
        (snd _ _ ≫ U'.gen.hom))
    · exact congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map (pG.pr i)))
    · have e₃ : (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left ≫ ((Over.pullback (jK R)).obj G').hom =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left ≫ jFK (R := R) F :=
        (Over.w _).trans (Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G'))).symm
      have a := ((gs_unit (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left y ⊤ trivial u).symm.trans
        (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
          ((constVal_specMap _ _ y c₀).trans (constVal_eq _ _ _))))
      exact (Units.val_pow_eq_pow_val _ _).trans ((congrArg (· ^ k) a).trans
        ((map_pow _ _ _).symm.trans (constVal_eq _ _ _).symm))
  · exact expandsAt_box' P k ee _ _ (fun i => hA i (e l i) ee) _ _
      (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k _) (isBoxFamB_boxFamB pD k _)
  · obtain ⟨hφ, hb⟩ := hS α'
    refine secLin_box e (algebraMap (FractionRing R) F c₀ ^ k) c D.toPre.P.isLB D'.toPre.P.isLB pD.w
      (p := prB pD F) (q := fun i => (pD.pw.pr i).left) (GC.famφ_eq D'.toPre F α') (fun i => ?_) (fun i => ?_)
      (S.s α') _ (fun i => (s i).s (pD.xe α' i)) (fun i a => f i a (pD.xe α' i)) _ (fun _ => rfl)
      (fun y J J' hJ hJ' => box_val pD.w hφ _ _ _ hb (𝟙 _) y hJ hJ') (fun l y J J' hJ hJ' => ?_)
      (fun i => hf i (pD.xe α' i))
    · exact congrArg (fun q => q.left) (whiskerLeft_snd (TF (R := R) F) (pD.pw.pr i)).symm
    · exact congrArg (fun q => q.left) (whiskerLeft_fst (TF (R := R) F) (pD.pw.pr i))
    · obtain ⟨hψ, H⟩ := isBoxFamB_boxFamB pD k (fun i => f i (e l i)) α'
      exact box_val pD.w hψ _ _ _ H _ y hJ hJ'

end GlobalTheory.BoxExpansion
