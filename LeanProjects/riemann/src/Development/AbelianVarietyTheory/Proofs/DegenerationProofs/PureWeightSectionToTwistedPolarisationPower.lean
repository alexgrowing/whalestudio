import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TwSec

section Cochain
variable {X Y Z : Scheme.{0}} {I I' : Type}

def Fam (W : I → X.Opens) (c : ∀ y : X, I → I → (X.presheaf.stalk y)ˣ) (a : ∀ i, Γ(X, W i)) : Prop :=
  ∀ y i j, y ∈ W i → y ∈ W j → gs (𝟙 X) y (W i) (a i) = (c y i j).val * gs (𝟙 X) y (W j) (a j)

def Cob (W : I → X.Opens) (c : ∀ y : X, I → I → (X.presheaf.stalk y)ˣ) : Prop :=
  ∃ u : ∀ i, Γ(X, W i)ˣ, ∀ y i j, y ∈ W i → y ∈ W j → gm (𝟙 X) y (W i) (u i) = c y i j * gm (𝟙 X) y (W j) (u j)

variable {W : I → X.Opens} {W' : I' → X.Opens} {c c₁ : ∀ y : X, I → I → (X.presheaf.stalk y)ˣ}
  {c' : ∀ y : X, I' → I' → (X.presheaf.stalk y)ˣ}

theorem Cob.refine (h : Cob W c) (τ : I' → I) (le : ∀ i, W' i ≤ W (τ i)) :
    Cob W' (fun y i j => c y (τ i) (τ j)) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨fun i => res (le i) (u (τ i)), fun y i j hi hj => by
    rw [gm_res _ y _ hi, gm_res _ y _ hj, hu y _ _ (le i hi) (le j hj)]⟩

theorem Cob.congr (h : Cob W c) (e : ∀ y i j, y ∈ W i → y ∈ W j → c₁ y i j = c y i j) : Cob W c₁ := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun y i j hi hj => by rw [hu y i j hi hj, e y i j hi hj]⟩

theorem Cob.mul (h : Cob W c) (h₁ : Cob W c₁) : Cob W (fun y i j => c y i j * c₁ y i j) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h₁
  exact ⟨fun i => u i * v i, fun y i j hi hj => by
    rw [map_mul, map_mul, hu y i j hi hj, hv y i j hi hj, _root_.mul_mul_mul_comm]⟩

theorem Cob.zpow (h : Cob W c) (n : ℤ) : Cob W (fun y i j => c y i j ^ n) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨fun i => u i ^ n, fun y i j hi hj => by
    rw [map_zpow, map_zpow, hu y i j hi hj, mul_zpow]⟩

theorem Cob.inv (h : Cob W c) : Cob W (fun y i j => (c y i j)⁻¹) := by
  simpa only [zpow_neg, zpow_one] using h.zpow (-1)

theorem Cob.descend (τ : I' → I) (le : ∀ i, W' i ≤ W (τ i)) (cov : ∀ i, ∀ y ∈ W i, ∃ i', τ i' = i ∧ y ∈ W' i')
    (one : ∀ y i, y ∈ W i → c y i i = 1) (h : Cob W' (fun y i j => c y (τ i) (τ j))) : Cob W c := by
  obtain ⟨u, hu⟩ := h
  have glue : ∀ i, ∃ s : Γ(X, W i)ˣ, ∀ i' (_ : τ i' = i) y, y ∈ W' i' →
      gm (𝟙 X) y (W i) s = gm (𝟙 X) y (W' i') (u i') := by
    intro i
    obtain ⟨s, hs⟩ := glue_unit (J := {i' // τ i' = i}) (W i) (fun p => W' p.1) (fun p => (le p.1).trans (by rw [p.2]))
      (fun y hy => by
        obtain ⟨i', e, h⟩ := cov i y hy
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i', e⟩, h⟩) (fun p => u p.1) (fun p q y hy => by
        have := hu y p.1 q.1 hy.1 hy.2
        dsimp only at this
        rw [this, p.2, q.2, one y i (by rw [← p.2]; exact le p.1 hy.1), _root_.one_mul])
    exact ⟨s, fun i' e y hy => by rw [← hs ⟨i', e⟩, gm_res _ y _ hy]⟩
  choose s hs using glue
  refine ⟨s, fun y i j hi hj => ?_⟩
  obtain ⟨i', rfl, hi'⟩ := cov i y hi
  obtain ⟨j', rfl, hj'⟩ := cov j y hj
  rw [hs _ i' rfl y hi', hs _ j' rfl y hj', hu y i' j' hi' hj']

theorem Fam.move {a : ∀ i, Γ(X, W i)} (ha : Fam W c a) (cov : ∀ y, ∃ i, y ∈ W i)
    (one : ∀ y i, y ∈ W' i → c' y i i = 1)
    (h : Cob (fun p : I' × I => W' p.1 ⊓ W p.2) (fun y p q => c' y p.1 q.1 * (c y p.2 q.2)⁻¹)) :
    ∃ b : ∀ i, Γ(X, W' i), Fam W' c' b ∧ ∀ y i j, y ∈ W' i → y ∈ W j →
      ∃ u : (X.presheaf.stalk y)ˣ, gs (𝟙 X) y (W' i) (b i) = u.val * gs (𝟙 X) y (W j) (a j) := by
  obtain ⟨u, hu⟩ := h
  let v : ∀ i j, Γ(X, W' i ⊓ W j) := fun i j => (u (i, j)).val * resG X inf_le_right (a j)
  have hv : ∀ y i j, y ∈ W' i ⊓ W j → gs (𝟙 X) y _ (v i j) =
      (gm (𝟙 X) y (W' i ⊓ W j) (u (i, j))).val * gs (𝟙 X) y (W j) (a j) := fun y i j hy =>
    (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _))
  have rel : ∀ y i j i' j', y ∈ W' i ⊓ W j → y ∈ W' i' ⊓ W j' →
      gs (𝟙 X) y _ (v i j) = (c' y i i').val * gs (𝟙 X) y _ (v i' j') := fun y i j i' j' h h' => by
    have e := hu y (i, j) (i', j') h h'
    dsimp only at e
    rw [hv y i j h, hv y i' j' h', e, ha y j j' h.2 h'.2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]
  have glue : ∀ i, ∃ b : Γ(X, W' i), ∀ j y, y ∈ W' i ⊓ W j → gs (𝟙 X) y (W' i) b = gs (𝟙 X) y _ (v i j) := by
    intro i
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun j => W' i ⊓ W j) (W' i) (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨j, hj⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy, hj⟩) (v i)
      (fun j j' => fn_ext (V := W' i ⊓ W j ⊓ (W' i ⊓ W j')) fun y hy => by
        refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
        rw [rel y i j i j' hy.1 hy.2, one y i hy.1.1, Units.val_one, _root_.one_mul])
    exact ⟨b, fun j y hy => (gs_res (𝟙 X) y inf_le_left hy b).symm.trans (congrArg (gs (𝟙 X) y _) (hb j))⟩
  choose b hb using glue
  refine ⟨b, fun y i i' hi hi' => ?_, fun y i j hi hj => ⟨_, (hb i j y ⟨hi, hj⟩).trans (hv y i j ⟨hi, hj⟩)⟩⟩
  obtain ⟨j, hj⟩ := cov y
  rw [hb i j y ⟨hi, hj⟩, hb i' j y ⟨hi', hj⟩, rel y i j i' j ⟨hi, hj⟩ ⟨hi', hj⟩]

abbrev tr (L : LB X) (r : Z ⟶ X) (z : Z) (i j : L.ι) : (Z.presheaf.stalk z)ˣ := gm r z (L.U i ⊓ L.U j) (L.g i j)

theorem gs_sec {L : LB X} (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {i j : L.ι} (hi : r z ∈ L.U i) (hj : r z ∈ L.U j) :
    gs r z _ (θ.f i) = (tr L r z i j).val * gs r z _ (θ.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (θ.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

def Fam.sec {L : LB X} {a : ∀ i, Γ(X, L.U i)} (h : Fam L.U (tr L (𝟙 X)) a) : LB.Sec L :=
  ⟨a, fun i j => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, h y i j hy.1 hy.2]⟩

theorem cob_gen {L : LB X} (h : ∃ t : LB.Gen L, t.IsGen) : Cob L.U (tr L (𝟙 X)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t.s, fun y i j hi hj => ?_⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gm (𝟙 X) y _) (ht i j)
  rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e

theorem cob_iso {L M : LB X} (h : LBIso L M) : Cob (fun p : M.ι × L.ι => M.U p.1 ⊓ L.U p.2)
    (fun y p q => tr M (𝟙 X) y p.1 q.1 * (tr L (𝟙 X) y p.2 q.2)⁻¹) :=
  (cob_gen h).congr fun y p q hp hq => (gm_div L M (𝟙 X) y p q ⟨hp, hq⟩).symm

theorem cob_self {L : LB X} (hL : L.IsLB) : Cob (fun p : L.ι × L.ι => L.U p.1 ⊓ L.U p.2)
    (fun y p q => tr L (𝟙 X) y p.1 q.1 * (tr L (𝟙 X) y p.2 q.2)⁻¹) :=
  ⟨fun p => L.g p.1 p.2, fun y p q hp hq => by
    rw [← gm_cocycle hL (𝟙 X) y hp.1 hq.1 hp.2, ← gm_cocycle hL (𝟙 X) y hq.1 hp.2 hq.2, _root_.mul_assoc, mul_comm (gm _ _ _ (L.g q.1 p.2)), inv_mul_cancel_left]⟩

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Z.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem mem_locus_iff {L : LB X} (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {k : L.ι}
    (hk : r z ∈ L.U k) : r z ∈ Out.nonzeroLocus θ ↔ IsUnit (gs r z _ (θ.f k)) := by
  rw [isUnit_gs_iff r z _ hk]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨k, h⟩⟩
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ L.U j := X.basicOpen_le _ hj
  rw [← isUnit_gs_iff r z _ hk, gs_sec θ r z hk hj']
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj' _).2 hj)

theorem gm_stalkMap (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)ˣ) :
    gm r z U f = Units.map (r.stalkMap z).hom.toMonoidHom (gm (𝟙 X) (r z) U f) :=
  Units.ext ((gs_unit r z U h f).symm.trans ((gs_stalkMap r z U h _).trans
    (congrArg (r.stalkMap z).hom (gs_unit (𝟙 X) (r z) U h f))))

theorem stalkMap_inj (r : Z ⟶ X) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom :=
  (injective_iff_map_eq_zero _).2 fun a ha => zero_dvd_iff.1 (dvd_descend r z (by rw [ha, map_zero]))

theorem exists_pull {Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ψ : K → (Y' ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (e : ∀ k, ψ k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L ψ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι), r z ∈ LB.wchart L ψ j →
        gs r z (LB.wchart L ψ j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain rfl : ψ = fun k => h ≫ φ k := funext e
  have le := Out.wchart_comp_le L φ h
  let a : ∀ j, Γ(Y', (LB.LinComb L (fun k => h ≫ φ k) ε).U j) := fun j => resG _ (le j) ((h.app _).hom (s.f j))
  have ha : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs r z (LB.wchart L (fun k => h ≫ φ k) j) (a j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) :=
    fun Z r z j hz => (gs_res r z (le j) hz _).trans (gs_pull r h z _ (le j hz) _)
  refine ⟨Fam.sec (a := a) fun y i j hi hj => ?_, ha⟩
  refine (ha _ (𝟙 Y') y i hi).trans ((sec_trans s (𝟙 Y' ≫ h) y (le i hi) (le j hj)).trans
    (congrArg₂ (· * ·) (congrArg Units.val ?_) (ha _ (𝟙 Y') y j hj).symm))
  refine Eq.trans ?_ (gm_linComb L _ ε (𝟙 Y') y i j hi hj).symm
  simp only [trF, Category.assoc]

end Cochain

section Datum
variable {S Z : Scheme.{0}} (E : SplitExt S)

def cb (χ : E.X) (r : Z ⟶ E.B.left) (z : Z) (j j' : E.ChartIdx) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, tr (E.O (E.basis k)).L r z (j k) (j' k) ^ E.basis.repr χ k

theorem cb_add (χ χ' : E.X) (r : Z ⟶ E.B.left) (z : Z) (j j' : E.ChartIdx) :
    cb E (χ + χ') r z j j' = cb E χ r z j j' * cb E χ' r z j j' := by
  simp only [cb, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem cb_zero (r : Z ⟶ E.B.left) (z : Z) (j j' : E.ChartIdx) : cb E 0 r z j j' = 1 := by
  simp only [cb, map_zero, Finsupp.zero_apply, zpow_zero, Finset.prod_const_one]

theorem cb_basis (k) (r : Z ⟶ E.B.left) (z : Z) (j j' : E.ChartIdx) :
    cb E (E.basis k) r z j j' = tr (E.O (E.basis k)).L r z (j k) (j' k) := by
  classical
  rw [cb, Finset.prod_eq_single k (fun k' _ h => by rw [E.basis.repr_self_apply, if_neg h.symm, zpow_zero])
    (fun h => absurd (Finset.mem_univ k) h), E.basis.repr_self_apply, if_pos rfl, zpow_one]

theorem cb_self (χ : E.X) (r : Z ⟶ E.B.left) (z : Z) (j : E.ChartIdx) (h : r z ∈ E.chart j) :
    cb E χ r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [tr, gm_self (E.O (E.basis k)).isLB r z (E.chart_le j k h), one_zpow]

theorem cb_stalkMap (χ : E.X) (r : Z ⟶ E.B.left) (z : Z) (j j' : E.ChartIdx) (h : r z ∈ E.chart j)
    (h' : r z ∈ E.chart j') :
    cb E χ r z j j' = Units.map (r.stalkMap z).hom.toMonoidHom (cb E χ (𝟙 _) (r z) j j') := by
  rw [cb, cb, map_prod]
  exact Finset.prod_congr rfl fun k _ => by
    rw [map_zpow, tr, gm_stalkMap r z (_ ⊓ _) ⟨E.chart_le j k h, E.chart_le j' k h'⟩]

def IsProd (χ : E.X) : Prop :=
  Cob (fun p : (E.O χ).L.ι × E.ChartIdx => (E.O χ).L.U p.1 ⊓ E.chart p.2)
    (fun y p q => tr (E.O χ).L (𝟙 _) y p.1 q.1 * (cb E χ (𝟙 _) y p.2 q.2)⁻¹)

theorem cob_add (χ χ' : E.X) : Cob (fun p : ((E.O (χ + χ')).L.ι × (E.O χ).L.ι) × (E.O χ').L.ι =>
      (E.O (χ + χ')).L.U p.1.1 ⊓ (E.O χ).L.U p.1.2 ⊓ (E.O χ').L.U p.2)
    (fun y p q => tr (E.O (χ + χ')).L (𝟙 _) y p.1.1 q.1.1 * (tr (E.O χ).L (𝟙 _) y p.1.2 q.1.2)⁻¹ *
      (tr (E.O χ').L (𝟙 _) y p.2 q.2)⁻¹) :=
  (cob_iso (E.addIso χ χ')).congr fun y p q hp hq =>
    congrArg (· * _) (gm_div _ _ (𝟙 _) y p.1 q.1 ⟨hp.1, hq.1⟩).symm

theorem one_of (χ : E.X) (y : E.B.left) (p : (E.O χ).L.ι × E.ChartIdx) (h : y ∈ (E.O χ).L.U p.1 ⊓ E.chart p.2) :
    tr (E.O χ).L (𝟙 _) y p.1 p.1 * (cb E χ (𝟙 _) y p.2 p.2)⁻¹ = 1 := by
  rw [tr, gm_self (E.O χ).isLB (𝟙 _) y h.1, cb_self E χ (𝟙 _) y _ h.2, inv_one, _root_.mul_one]

variable {E}

theorem IsProd.add {χ χ' : E.X} (h : IsProd E χ) (h' : IsProd E χ') : IsProd E (χ + χ') := by
  let W : ((E.O (χ + χ')).L.ι × E.ChartIdx) × (E.O χ).L.ι × (E.O χ').L.ι → E.B.left.Opens := fun p =>
    (E.O (χ + χ')).L.U p.1.1 ⊓ E.chart p.1.2 ⊓ ((E.O χ).L.U p.2.1 ⊓ (E.O χ').L.U p.2.2)
  refine Cob.descend (W' := W) Prod.fst (fun _ => inf_le_left) (fun p y hy => ?_) (one_of E _) ?_
  · obtain ⟨a, ha⟩ := exists_chart (E.O χ).isLB y
    obtain ⟨b, hb⟩ := exists_chart (E.O χ').isLB y
    exact ⟨(p, a, b), rfl, hy, ha, hb⟩
  refine (((cob_add E χ χ').refine (W' := W) (fun p => ((p.1.1, p.2.1), p.2.2)) fun p y hy => ⟨⟨hy.1.1, hy.2.1⟩, hy.2.2⟩).mul
    ((Cob.refine (W' := W) h (fun p => (p.2.1, p.1.2)) fun p y hy => ⟨hy.2.1, hy.1.2⟩).mul
      (Cob.refine (W' := W) h' (fun p => (p.2.2, p.1.2)) fun p y hy => ⟨hy.2.2, hy.1.2⟩))).congr fun y p q _ _ => ?_
  rw [cb_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem IsProd.sub {χ χ' : E.X} (h : IsProd E χ) (h' : IsProd E (χ + χ')) : IsProd E χ' := by
  let W : ((E.O χ').L.ι × E.ChartIdx) × (E.O χ).L.ι × (E.O (χ + χ')).L.ι → E.B.left.Opens := fun p =>
    (E.O χ').L.U p.1.1 ⊓ E.chart p.1.2 ⊓ ((E.O χ).L.U p.2.1 ⊓ (E.O (χ + χ')).L.U p.2.2)
  refine Cob.descend (W' := W) Prod.fst (fun _ => inf_le_left) (fun p y hy => ?_) (one_of E _) ?_
  · obtain ⟨a, ha⟩ := exists_chart (E.O χ).isLB y
    obtain ⟨b, hb⟩ := exists_chart (E.O (χ + χ')).isLB y
    exact ⟨(p, a, b), rfl, hy, ha, hb⟩
  refine (((cob_add E χ χ').refine (W' := W) (fun p => ((p.2.2, p.2.1), p.1.1)) fun p y hy => ⟨⟨hy.2.2, hy.2.1⟩, hy.1.1⟩).inv.mul
    ((Cob.refine (W' := W) h (fun p => (p.2.1, p.1.2)) fun p y hy => ⟨hy.2.1, hy.1.2⟩).inv.mul
      (Cob.refine (W' := W) h' (fun p => (p.2.2, p.1.2)) fun p y hy => ⟨hy.2.2, hy.1.2⟩))).congr fun y p q _ _ => ?_
  rw [cb_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable (E)

theorem isProd_zero : IsProd E 0 :=
  ((cob_gen E.zeroTriv).refine Prod.fst fun _ => inf_le_left).congr fun y p q _ _ => by
    rw [cb_zero, inv_one, _root_.mul_one]

theorem isProd (χ : E.X) : IsProd E χ := by
  let H : AddSubgroup E.X :=
    { carrier := {χ | IsProd E χ}
      add_mem' := IsProd.add
      zero_mem' := isProd_zero E
      neg_mem' := fun {χ} h => IsProd.sub h (by rw [add_neg_cancel]; exact isProd_zero E) }
  rw [← E.basis.sum_repr χ]
  refine H.sum_mem fun k _ => H.zsmul_mem ?_ _
  exact ((cob_self (E.O (E.basis k)).isLB).refine (fun p : _ × E.ChartIdx => (p.1, p.2 k))
    fun p => inf_le_inf_left _ (E.chart_le _ _)).congr fun y p q _ _ => by rw [cb_basis]

variable {E} {G : Over S} [GrpObj G] (D : E.GtDatum G)

def mg (χ : E.X) (z : G.left) (j : E.ChartIdx) : (G.left.presheaf.stalk z)ˣ :=
  ∏ k, gm (𝟙 _) z (D.q.left ⁻¹ᵁ E.chart j) (D.u j k) ^ E.basis.repr χ k

theorem gs_mono (χ : E.X) (z : G.left) (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j)
    (hz : D.q.left z ∈ V) :
    gs (𝟙 _) z (D.q.left ⁻¹ᵁ V) (WtPart.mono D j V h (Multiplicative.ofAdd χ)) = (mg D χ z j).val := by
  refine (gs_unit (𝟙 _) z (D.q.left ⁻¹ᵁ V) hz (Additive.toMul (E.basis.constr ℤ (fun k => Additive.ofMul
    (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k))) χ))).trans (congrArg Units.val ?_)
  rw [Module.Basis.constr_apply_fintype, toMul_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [toMul_zsmul, map_zpow, toMul_ofMul, gm_res (𝟙 _) z _ hz]
  rfl

theorem mg_trans (χ : E.X) (z : G.left) (j j' : E.ChartIdx) (h : D.q.left z ∈ E.chart j)
    (h' : D.q.left z ∈ E.chart j') : mg D χ z j' = cb E χ D.q.left z j j' * mg D χ z j := by
  rw [mg, mg, cb, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hm : D.q.left ((𝟙 G.left : G.left ⟶ G.left) z) ∈ E.chart j ⊓ E.chart j' := ⟨h, h'⟩
  have e := congrArg (gm (𝟙 _) z (D.q.left ⁻¹ᵁ (E.chart j ⊓ E.chart j'))) (D.trans j j' k)
  have e' := (gm_res (𝟙 _) z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_pull (𝟙 _) D.q.left z _ hm _).trans (gm_res (𝟙 _ ≫ D.q.left) z _ hm _)) (gm_res (𝟙 _) z _ hm _))))
  rw [e', mul_zpow, Category.id_comp]

end Datum

section Fibre
variable {k : Type} [Field k] (Φ : FibPre k) (d : ℕ) (α : Φ.E.X)

def cP (y : Φ.E.B.left) (l l' : Φ.N₀.ι) : (Φ.E.B.left.presheaf.stalk y)ˣ :=
  tr Φ.N₀ (𝟙 _) y l l' ^ d * cb Φ.E α (𝟙 _) y (Φ.ch l) (Φ.ch l')

theorem cPoint_self (y : Φ.E.B.left) (l : Φ.N₀.ι) (h : y ∈ Φ.N₀.U l) : cP Φ d α y l l = 1 := by
  rw [cP, tr, gm_self Φ.isLB (𝟙 _) y h, cb_self _ _ (𝟙 _) y _ (Φ.le l h), one_pow, _root_.one_mul]

def term (l : Φ.N₀.ι) (w : Γ(Φ.E.B.left, Φ.N₀.U l)) : Γ(Φ.G.left, (Φ.H d).U l) :=
  (Φ.D.q.left.app (Φ.N₀.U l)).hom w * WtPart.mono Φ.D (Φ.ch l) _ (Φ.le l) (Multiplicative.ofAdd α)

theorem gs_term (l : Φ.N₀.ι) (w : Γ(Φ.E.B.left, Φ.N₀.U l)) (z : Φ.G.left) (hz : Φ.D.q.left z ∈ Φ.N₀.U l) :
    gs (𝟙 _) z ((Φ.H d).U l) (term Φ d α l w) =
      (Φ.D.q.left.stalkMap z).hom (gs (𝟙 _) (Φ.D.q.left z) _ w) * (mg Φ.D α z (Φ.ch l)).val :=
  (gs_mul (𝟙 _) z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) hz _ _).trans (congrArg₂ (· * ·)
    ((gs_pull (𝟙 _) Φ.D.q.left z _ hz w).trans (by rw [Category.id_comp, gs_stalkMap _ z _ hz]))
    (gs_mono Φ.D α z _ _ _ hz))

theorem tr_mg (z : Φ.G.left) (l l' : Φ.N₀.ι) (h : Φ.D.q.left z ∈ Φ.N₀.U l) (h' : Φ.D.q.left z ∈ Φ.N₀.U l') :
    tr (Φ.H d) (𝟙 _) z l l' * mg Φ.D α z (Φ.ch l') =
      Units.map (Φ.D.q.left.stalkMap z).hom.toMonoidHom (cP Φ d α (Φ.D.q.left z) l l') * mg Φ.D α z (Φ.ch l) := by
  have hm : Φ.D.q.left z ∈ Φ.N₀.U l ⊓ Φ.N₀.U l' := ⟨h, h'⟩
  have e : tr (Φ.H d) (𝟙 _) z l l' = tr Φ.N₀ Φ.D.q.left z l l' ^ d :=
    (map_pow _ _ _).trans (congrArg (· ^ d) ((gm_pull (𝟙 _) Φ.D.q.left z _ hm _).trans (by rw [Category.id_comp])))
  rw [e, mg_trans Φ.D α z (Φ.ch l) (Φ.ch l') (Φ.le l h) (Φ.le l' h'), cP, map_mul, map_pow,
    ← cb_stalkMap _ _ _ _ _ _ (Φ.le l h) (Φ.le l' h'), tr, gm_stalkMap _ z _ hm, _root_.mul_assoc]

variable {Φ d α}

theorem eq_term {φ : (Φ.H d).Sec} (h : Φ.Pure α φ) (l : Φ.N₀.ι) : φ.f l = term Φ d α l (Φ.wt φ α l) := by
  refine WtPart.cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => ?_
  refine Eq.trans ?_ (WtPart.cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _).symm
  change Φ.wt φ β l = _
  split_ifs with e
  · rw [e]
  · by_contra hn
    exact e (h ⟨l, hn⟩).symm

theorem fam_of_term {φ : (Φ.H d).Sec} {w : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l)} (h : ∀ l : Φ.N₀.ι, φ.f l = term Φ d α l (w l)) :
    Fam Φ.N₀.U (cP Φ d α) w := by
  intro y l l' hl hl'
  obtain ⟨z, rfl⟩ := Φ.D.q_surjective.surj y
  have := Φ.D.q_flat
  have e := gs_sec φ (𝟙 _) z (i := l) (j := l') hl hl'
  erw [h l, h l'] at e
  rw [gs_term Φ d α l _ z hl, gs_term Φ d α l' _ z hl', mul_left_comm, ← Units.val_mul, tr_mg Φ d α z l l' hl hl',
    Units.val_mul, ← _root_.mul_assoc] at e
  refine stalkMap_inj Φ.D.q.left z ?_
  rw [map_mul, mul_comm]
  exact (Units.mul_left_inj _).1 e

theorem exists_term {w : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l)} (h : Fam Φ.N₀.U (cP Φ d α) w) :
    ∃ φ : (Φ.H d).Sec, Φ.Pure α φ ∧ ∀ l, φ.f l = term Φ d α l (w l) := by
  refine ⟨Fam.sec (a := fun l => term Φ d α l (w l)) fun z l l' hl hl' => ?_, ?_, fun _ => rfl⟩
  · rw [gs_term Φ d α l _ z hl, gs_term Φ d α l' _ z hl', mul_left_comm, ← Units.val_mul, tr_mg Φ d α z l l' hl hl',
      h _ l l' hl hl', map_mul, Units.val_mul, ← _root_.mul_assoc, mul_comm _ (Units.val (Units.map _ _))]
    rfl
  · rintro β ⟨l, hl⟩
    by_contra hn
    exact hl ((WtPart.cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _).trans
      (if_neg fun e => hn e.symm))

theorem mem_locus_term {φ : (Φ.H d).Sec} {w : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l)} (h : ∀ l : Φ.N₀.ι, φ.f l = term Φ d α l (w l))
    (z : Φ.G.left) (l : Φ.N₀.ι) (hl : Φ.D.q.left z ∈ Φ.N₀.U l) :
    z ∈ Out.nonzeroLocus φ ↔ IsUnit (gs (𝟙 _) (Φ.D.q.left z) _ (w l)) := by
  refine (mem_locus_iff φ (𝟙 _) z (k := l) hl).trans ?_
  erw [h l]
  rw [gs_term Φ d α l _ z hl, Units.isUnit_mul_units, isUnit_map_iff]

variable {N : ℕ} (π : Φ.Pol N) (α)

def ψ : Fin 2 → (Φ.E.B.left ⟶ π.PB.A.left) :=
  ![π.β.hom.left, (π.β.hom * (Over.homMk Φ.E.B.hom (Category.comp_id _) ≫ π.c α)).left]

variable (d)

abbrev tw : LB Φ.E.B.left := LB.LinComb π.PB.L (ψ α π) ![((N * d : ℕ) : ℤ) - 1, 1]

theorem cob_tw : Cob (fun p : (tw d α π).ι × Φ.N₀.ι => (tw d α π).U p.1 ⊓ Φ.N₀.U p.2)
    (fun y p q => tr (tw d α π) (𝟙 _) y p.1 q.1 * (cP Φ d α y p.2 q.2)⁻¹) := by
  have hT : (tw d α π).IsLB := LB.isLB_linComb π.PB.isLB _ _
  let W : ((tw d α π).ι × Φ.N₀.ι) × (Φ.E.O α).L.ι → Φ.E.B.left.Opens := fun p =>
    (tw d α π).U p.1.1 ⊓ Φ.N₀.U p.1.2 ⊓ (Φ.E.O α).L.U p.2
  refine Cob.descend (W' := W) Prod.fst (fun _ => inf_le_left) (fun p y hy => ?_) (fun y p hy => ?_) ?_
  · obtain ⟨a, ha⟩ := exists_chart (Φ.E.O α).isLB y
    exact ⟨(p, a), rfl, hy, ha⟩
  · rw [tr, gm_self hT (𝟙 _) y hy.1, cPoint_self Φ d α y _ hy.2, inv_one, _root_.mul_one]
  have m₀ : ∀ (j : (tw d α π).ι) y, y ∈ (tw d α π).U j → π.β.hom.left y ∈ (lbPow π.PB.L N).U (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have m₁ : ∀ (j : (tw d α π).ι) y, y ∈ (tw d α π).U j → y ∈ LB.wchart π.PB.L ![ψ α π 1, ψ α π 0] ![j 1, j 0] :=
    fun j y hy => Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 hy 1, Set.mem_iInter.1 hy 0⟩)
  refine ((((cob_iso π.w₀).refine (W' := W) (fun p => (fun _ _ => p.1.1 0, p.1.2))
      fun p y hy => ⟨mem_pull.2 (m₀ _ y hy.1.1), hy.1.2⟩).zpow d).mul
    (((cob_iso (π.wO α)).refine (W' := W) (fun p => (![p.1.1 1, p.1.1 0], p.2))
      fun p y hy => ⟨m₁ _ y hy.1.1, hy.2⟩).mul
      (Cob.refine (W' := W) (isProd Φ.E α) (fun p => (p.2, Φ.ch p.1.2))
        fun p y hy => ⟨hy.2, Φ.le _ hy.1.2⟩))).congr fun y p q hp hq => ?_
  have e₁ := gm_linComb π.PB.L (ψ α π) ![((N * d : ℕ) : ℤ) - 1, 1] (𝟙 _) y p.1.1 q.1.1 hp.1.1 hq.1.1
  have e₂ := gm_linComb π.PB.L ![ψ α π 1, ψ α π 0] ![1, -1] (𝟙 _) y _ _ (m₁ _ y hp.1.1) (m₁ _ y hq.1.1)
  have e₃ := (gm_pull_g (lbPow π.PB.L N) π.β.hom.left (𝟙 _) y (fun _ _ => p.1.1 0) (fun _ _ => q.1.1 0)
    (mem_pull.2 (m₀ _ y hp.1.1)) (mem_pull.2 (m₀ _ y hq.1.1))).trans
    (gm_linComb π.PB.L (fun _ : PUnit => 𝟙 _) (fun _ => (N : ℤ)) (𝟙 _ ≫ π.β.hom.left) y _ _ (m₀ _ y hp.1.1) (m₀ _ y hq.1.1))
  rw [Fin.prod_univ_two] at e₁ e₂
  rw [Fintype.prod_unique, Category.comp_id] at e₃
  refine (congrArg (· * _) e₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => (t * _) ^ (d : ℤ)) e₃)
    (congrArg (fun t => (t * _) * _) e₂)).symm)
  change tr π.PB.L (𝟙 _ ≫ π.β.hom.left) y (p.1.1 0) (q.1.1 0) ^ (((N * d : ℕ) : ℤ) - 1) *
      tr π.PB.L (𝟙 _ ≫ ψ α π 1) y (p.1.1 1) (q.1.1 1) ^ (1 : ℤ) * _ =
    (tr π.PB.L (𝟙 _ ≫ π.β.hom.left) y (p.1.1 0) (q.1.1 0) ^ (N : ℤ) * _) ^ (d : ℤ) *
      (tr π.PB.L (𝟙 _ ≫ ψ α π 1) y (p.1.1 1) (q.1.1 1) ^ (1 : ℤ) *
        tr π.PB.L (𝟙 _ ≫ π.β.hom.left) y (p.1.1 0) (q.1.1 0) ^ (-1 : ℤ) * _ * _)
  rw [cP]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  push_cast
  module

variable {α d}

def ρ : Φ.E.B ⟶ Out.baseOver (Sp k) ⊗ π.PB.A := lift (Over.homMk Φ.E.B.hom (Category.comp_id _)) π.β.hom

theorem base_ext {T : Over (Sp k)} (f g : T ⟶ Out.baseOver (Sp k)) : f = g :=
  Over.mkIdTerminal.hom_ext f g

theorem ψ_eq (i : Fin 2) : ψ α π i = (ρ π).left ≫
    ![(snd (Out.baseOver (Sp k)) π.PB.A).left, (Out.translPt π.PB.A (π.c α)).left] i := by
  have := π.PB.isAb.comm
  revert i
  refine Fin.forall_fin_two.2 ⟨congrArg (fun f => f.left) (lift_snd _ π.β.hom).symm, ?_⟩
  refine congrArg (fun f => f.left) (?_ : _ = ρ π ≫ Out.translPt π.PB.A (π.c α))
  rw [_root_.mul_comm, Hom.mul_def, Out.translPt, ρ, comp_lift_assoc, lift_fst_assoc, lift_snd]

theorem ρ_inv : (ρ π).left ≫ (snd (Out.baseOver (Sp k)) π.PB.A ≫ π.β.inv).left = 𝟙 _ :=
  congrArg (fun f => f.left) (by rw [ρ, lift_snd_assoc, Iso.hom_inv_id] :
    ρ π ≫ snd (Out.baseOver (Sp k)) π.PB.A ≫ π.β.inv = 𝟙 _)

theorem inv_ρ : (snd (Out.baseOver (Sp k)) π.PB.A ≫ π.β.inv).left ≫ (ρ π).left = 𝟙 _ :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.hom_ext _ _ (base_ext _ _) (by simp [ρ]) :
    (snd (Out.baseOver (Sp k)) π.PB.A ≫ π.β.inv) ≫ ρ π = 𝟙 _)

theorem ρ_mem (n : ℕ) (j : Fin 2 → π.PB.L.ι) (y : Φ.E.B.left) (hy : y ∈ (tw d α π).U j) :
    (ρ π).left y ∈ (Out.twistLB π.PB.A π.PB.L n (π.c α)).U j :=
  Set.mem_iInter.2 fun i => by
    have h : ψ α π i y ∈ π.PB.L.U (j i) := Set.mem_iInter.1 hy i
    rw [ψ_eq] at h
    exact h

theorem locus_iff {φ : (Φ.H d).Sec} {w : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l)} (h : ∀ l : Φ.N₀.ι, φ.f l = term Φ d α l (w l))
    (s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)))
    (H : ∀ y j l, y ∈ (tw d α π).U j → y ∈ Φ.N₀.U l →
      (IsUnit (gs (ρ π).left y _ (s.f j)) ↔ IsUnit (gs (𝟙 _) y _ (w l)))) (x : Φ.Pt) :
    ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔
      ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s := by
  have e : Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom) = x ≫ Φ.D.q ≫ ρ π :=
    CartesianMonoidalCategory.hom_ext _ _ (base_ext _ _) (by simp [ρ, Out.ptSecT])
  have key : ∀ z : Φ.G.left, z ∈ Out.nonzeroLocus φ ↔ (ρ π).left (Φ.D.q.left z) ∈ Out.nonzeroLocus s := fun z => by
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left z)
    obtain ⟨j, hj⟩ := exists_chart (L := tw d α π) (LB.isLB_linComb π.PB.isLB _ _) (Φ.D.q.left z)
    rw [mem_locus_term h z l hl, ← H _ j l hj hl, mem_locus_iff s _ _ (ρ_mem π _ j _ hj)]
  rw [e]
  exact forall₂_congr fun p _ => key (x.left p)

end Fibre

theorem pure_sec_twist : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N d : ℕ) (π : Φ.Pol N) (α : Φ.E.X), 1 ≤ N → 1 ≤ d → (∀ φ : (Φ.H d).Sec, Φ.Pure α φ → ∃ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ((∀ j, s.f j = 0) → ∀ l, φ.f l = 0) ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) ∧ ∀ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ∃ φ : (Φ.H d).Sec, Φ.Pure α φ ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) := by
  intro k _ _ Φ N d π α _ _
  have hT : (tw d α π).IsLB := LB.isLB_linComb π.PB.isLB _ _
  refine ⟨fun φ hφ => ?_, fun s => ?_⟩
  · obtain ⟨b, hb, hu⟩ := (fam_of_term (eq_term hφ)).move (W' := (tw d α π).U) (c' := tr (tw d α π) (𝟙 _)) (exists_chart Φ.isLB)
      (fun y j hy => gm_self hT (𝟙 _) y hy) (cob_tw d α π)
    obtain ⟨s, hs⟩ := exists_pull π.PB.L (ψ α π)
      ![(snd (Out.baseOver (Sp k)) π.PB.A).left, (Out.translPt π.PB.A (π.c α)).left] ![((N * d : ℕ) : ℤ) - 1, 1]
      (snd (Out.baseOver (Sp k)) π.PB.A ≫ π.β.inv).left
      (fun i => by rw [ψ_eq, ← Category.assoc, inv_ρ, Category.id_comp]) (Fam.sec (L := tw d α π) hb)
    have hv : ∀ y j, y ∈ (tw d α π).U j → gs (ρ π).left y ((Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)).U j) (s.f j) =
        gs (𝟙 _) y ((tw d α π).U j) (b j) := fun y j hj =>
      (hs _ (ρ π).left y j (ρ_mem π (N * d) j y hj)).trans (by rw [ρ_inv]; rfl)
    refine ⟨s, fun h0 l => ?_, locus_iff π (eq_term hφ) s fun y j l hj hl => ?_⟩
    · have hw : Φ.wt φ α l = 0 := fn_ext fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hT y
        obtain ⟨u, e⟩ := hu y j l hj hy
        have e₀ : gs (𝟙 _) y ((tw d α π).U j) (b j) = 0 :=
          (hv y j hj).symm.trans ((congrArg (gs (ρ π).left y _) (h0 j)).trans
            ((gs_eq _ y _ (ρ_mem π (N * d) j y hj) _).trans (by rw [map_zero, map_zero])))
        rw [(Units.mul_right_eq_zero u).1 (e.symm.trans e₀), gs_eq (𝟙 _) y _ hy, map_zero, map_zero]
      refine (eq_term hφ l).trans ?_
      rw [hw]
      exact (congrArg (· * _) (map_zero (Φ.D.q.left.app (Φ.N₀.U l)).hom)).trans (zero_mul _)
    · obtain ⟨u, e⟩ := hu y j l hj hl
      rw [(hv y j hj).trans e, Units.isUnit_units_mul]
  · obtain ⟨s', hs⟩ := exists_pull π.PB.L _ (ψ α π) _ (ρ π).left (ψ_eq π) s
    obtain ⟨w, hw, hu⟩ := Fam.move (W := (tw d α π).U) (c := tr (tw d α π) (𝟙 _)) (a := s'.f)
      (fun y i j hi hj => gs_sec s' (𝟙 _) y hi hj) (exists_chart hT) (cPoint_self Φ d α)
      (((cob_tw d α π).refine Prod.swap fun p => (inf_comm _ _).le).inv.congr fun y p q _ _ => by
        rw [mul_inv_rev, inv_inv]; rfl)
    obtain ⟨φ, hφ, e⟩ := exists_term hw
    refine ⟨φ, hφ, locus_iff π e s fun y j l hj hl => ?_⟩
    obtain ⟨u, e'⟩ := hu y l j hl hj
    have e₁ := hs _ (𝟙 _) y j hj
    rw [Category.id_comp] at e₁
    rw [e', Units.isUnit_units_mul]
    exact (congrArg IsUnit e₁).symm.to_iff

end GlobalTheory.ZH.TwSec
end
