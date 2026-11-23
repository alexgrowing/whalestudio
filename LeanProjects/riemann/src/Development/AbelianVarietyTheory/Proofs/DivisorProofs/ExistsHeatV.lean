import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatVAlg
open GlobalTheory.KS GlobalTheory.HeatGlue

variable {Y X : Scheme.{0}}

theorem pbT_id {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : pbT (𝟙 Y) s O = rsT s O := by
  rw [pbT_of_le (𝟙 Y) h, rsT_of_le h]
  rfl

theorem cst_eq (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)) :
    GlobalTheory.HeatV.cst π V h r = pbT π r O := (pbT_of_le π h r).symm

theorem rsT_unit {O₀ O : Y.Opens} (h : O ≤ O₀) (w : Γ(Y, O₀)ˣ) : rsT w.val O * rsT w⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem rsT_cocycle (L : LB Y) (hL : L.IsLB) (i j k : L.ι) {O : Y.Opens} (hO : O ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    rsT (L.g i j).val O * rsT (L.g j k).val O = rsT (L.g i k).val O := by
  have e := congrArg (fun u : Γ(Y, L.U i ⊓ L.U j ⊓ L.U k)ˣ => rsT u.val O) (hL.cocycle i j k)
  simp only [Units.val_mul, rsT_mul] at e
  have r : ∀ {V V' : Y.Opens} (h : V' ≤ V) (u : Γ(Y, V)ˣ), O ≤ V' →
      rsT (ReciprocityTheory.ChartRestriction.G.Semi.res h u).val O = rsT u.val O := fun h u hO' => by
    show rsT (resG Y h u.val) O = _
    rw [← rsT_of_le h, rsT_rsT h hO']
  rw [r _ _ hO, r _ _ hO, r _ _ hO] at e
  exact e

theorem exists_heatV : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) (V : X.Opens) (L : LB Y), L.IsLB → IsUnit (2 : Γ(X, V)) → ∀ (n : ℕ) (dd : Fin n → Fld Y), (∀ a, IsField ⊤ (dd a)) → (∀ a O (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)), dd a O (GlobalTheory.HeatV.cst π V h r) = 0) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)), Θᵀ = Θ → ∀ (J : Type) (W : J → Y.Opens) (j : J → L.ι) (d : J → Fld Y) (hW : ∀ i, W i ≤ π ⁻¹ᵁ V), (∀ i, W i ≤ L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst π V (h.trans (inf_le_left.trans (hW i))) (Θ a b) * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) * dd a O f) → (∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(X, V)) (y : ∀ i, Γ(Y, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst π V (inf_le_left.trans (hW i)) (cc b) * (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i'))) → ∃ (e u : Fin n → Γ(X, V)) (pf pf' : ∀ i, Γ(Y, W i)), ∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i' O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f := by
  intro Y X π V L hL h2 n dd hddF _hddC Θ hΘ J W j d hW hWL hdF hKS hH1
  simp only [cst_eq] at hKS hH1
  have hdd : ∀ a (O : Y.Opens), IsDer (dd a O) := fun a O => isDer_of_isField (hddF a) le_top
  obtain ⟨t, ht⟩ : ∃ t : Γ(X, V), 2 * t = 1 := ⟨_, h2.mul_val_inv⟩
  have hc2 : ∀ O : Y.Opens, O ≤ π ⁻¹ᵁ V → 2 * pbT π t O = 1 := fun O hO => by
    have e := congrArg (fun s => pbT π s O) ht
    simp only [pbT_mul, pbT_one π hO] at e
    rw [show (2 : Γ(X, V)) = 1 + 1 from one_add_one_eq_two.symm, pbT_add, pbT_one π hO, one_add_one_eq_two] at e
    exact e
  have hs : ∀ (O : Y.Opens) a b, pbT π (Θ a b) O = pbT π (Θ b a) O := fun O a b => by
    rw [show Θ a b = Θᵀ b a from rfl, hΘ]
  have hV2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ π ⁻¹ᵁ V := fun i i' O h => h.trans (inf_le_left.trans (hW i))
  have hm2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ L.U (j i) ⊓ L.U (j i') := fun i i' O h =>
    le_inf (h.trans (inf_le_left.trans (hWL i))) (h.trans (inf_le_right.trans (hWL i')))
  have hm3 : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    fun i i' i'' O h => le_inf (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans (hWL i))))
      (h.trans (inf_le_left.trans (inf_le_right.trans (hWL i'))))) (h.trans (inf_le_right.trans (hWL i'')))
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → J → J → ∀ O : Y.Opens, Γ(Y, O), ∀ b i i' O,
      φ b i i' O = dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O := ⟨_, fun _ _ _ _ => rfl⟩
  have rφ : ∀ b i i' (O₁ O : Y.Opens), O₁ ≤ W i ⊓ W i' → O ≤ O₁ → rsT (φ b i i' O₁) O = φ b i i' O := by
    intro b i i' O₁ O h1 h
    rw [hφ, hφ, rsT_mul, ← field_rsT (hddF b) le_top h, rsT_rsT (hm2 i i' O₁ h1) h, rsT_rsT (hm2 i i' O₁ h1) h]
  have dlc : ∀ i i' i'' (O : Y.Opens) (δ : Γ(Y, O) → Γ(Y, O)), IsDer δ → O ≤ W i ⊓ W i' ⊓ W i'' →
      δ (rsT (L.g (j i) (j i'')).val O) * rsT (L.g (j i) (j i''))⁻¹.val O =
        δ (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O +
        δ (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O := by
    intro i i' i'' O δ hδ hO
    have h3 := hm3 i i' i'' O hO
    exact hδ.dlog_mul (rsT_unit (h3.trans inf_le_left) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_right)) (h3.trans inf_le_right)) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_left)) (h3.trans inf_le_right)) _)
      (rsT_cocycle L hL _ _ _ h3)
  have cφ : ∀ b i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' →
      φ b i i'' O = φ b i i' O + φ b i' i'' O := fun b i i' i'' O hO => by
    rw [hφ, hφ, hφ]; exact dlc i i' i'' O _ (hdd b O) hO
  have ks : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' →
      d i O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O =
        d i' O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O +
        ∑ a, ∑ b, pbT π (Θ a b) O * φ b i i' O * φ a i' i'' O := fun i i' i'' O hO => by
    rw [← sub_eq_iff_eq_add', ← sub_mul, hKS i i' O hO, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hφ, hφ]; ring

  obtain ⟨z₁, hz₁⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      -(pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      d i (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i') -
        pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          φ a i i' (W i ⊓ W i') * φ b i i' (W i ⊓ W i') := ⟨_, fun _ _ => rfl⟩
  have rz₁ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₁ i i') O =
      -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) := by
    intro i i' O hO
    have e : ∀ a b, rsT (dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) O = dd a O (φ b i i' O) := fun a b => by
      rw [← field_rsT (hddF a) le_top hO, rφ b i i' _ O le_rfl hO]
    rw [hz₁]
    simp only [rsT_neg, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
  have rz₂ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₂ i i') O =
      d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O := by
    intro i i' O hO
    have e : ∀ b, rsT (φ b i i' (W i ⊓ W i')) O = φ b i i' O := fun b => rφ b i i' _ O le_rfl hO
    rw [hz₂]
    simp only [rsT_sub, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
    rw [← field_rsT (hdF i) inf_le_left hO, rsT_rsT (hm2 i i' _ le_rfl) hO, rsT_rsT (hm2 i i' _ le_rfl) hO]
  have tri : ∀ i i' i'', (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ∧ (W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ∧
      (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') :=
    fun _ _ _ => ⟨inf_le_left, le_inf (inf_le_left.trans inf_le_right) inf_le_right,
      le_inf (inf_le_left.trans inf_le_left) inf_le_right⟩
  have coc₁ : IsCoc W z₁ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₁ i i' _ t1, rz₁ i' i'' _ t2, rz₁ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e, (hdd _ _).1, mul_add, Finset.sum_add_distrib]
    ring
  have coc₂ : IsCoc W z₂ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₂ i i' _ t1, rz₂ i' i'' _ t2, rz₂ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e]
    rw [dlc i i' i'' _ _ (isDer_of_isField (hdF i) (t1.trans inf_le_left)) le_rfl, ks i i' i'' _ t1,
      quad_add (hs _) (fun a => φ a i i' _) (fun a => φ a i' i'' _)]
    linear_combination (∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i' ⊓ W i'') * φ b i i' _ * φ a i' i'' _) *
      hc2 _ (hV2 i i' _ t1)
  obtain ⟨c, y₁, hy₁⟩ := hH1 z₁ coc₁
  obtain ⟨e, y₂, hy₂⟩ := hH1 z₂ coc₂
  have A1 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₁ i') O - rsT (y₁ i) O = -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) -
        ∑ b, pbT π (c b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₁ i i')
    simp only [rz₁ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  have A2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₂ i') O - rsT (y₂ i) O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O - ∑ b, pbT π (e b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₂ i i')
    simp only [rz₂ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  refine ⟨fun a => -e a, fun a => -c a, y₂, y₁, ?_⟩
  intro k i i' O h f
  have hO : O ≤ π ⁻¹ᵁ V := hV2 i i' O h
  rw [pbT_id (hm2 i i' O h)]
  have hg := rsT_unit (hm2 i i' O h) (L.g (j i) (j i'))
  have hdi : IsDer (fun f : Γ(Y, O) => d i O f + ∑ a, pbT π (-e a) O * dd a O f) := by
    have h1 := isDer_of_isField (hdF i) (h.trans inf_le_left)
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · simp only [h1.1, (hdd _ O).1, mul_add, Finset.sum_add_distrib]
      ring
    · have s : ∑ a, pbT π (-e a) O * (x * dd a O y + y * dd a O x) =
          x * ∑ a, pbT π (-e a) O * dd a O y + y * ∑ a, pbT π (-e a) O * dd a O x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [h1.2, (hdd _ O).2, s]
      ring
  have key := ringOp_conj hdi (fun a => hdd a O) (Θ := Θ.map (GlobalTheory.HeatV.cst π V hO))
    (fun a b => by show GlobalTheory.HeatV.cst π V hO (Θ a b) = GlobalTheory.HeatV.cst π V hO (Θ b a)
                   rw [show Θ a b = Θᵀ b a from rfl, hΘ])
    (fun a => GlobalTheory.HeatV.cst π V hO (-c a)) (rsT (y₂ i) O) (rsT (y₁ i) O) hg k f
  refine key.trans ?_
  congr 1
  have F1 := hKS i i' O h f
  have F2 := A2 i i' O h
  have F3 := A1 i i' O h
  simp only [hφ] at F2 F3
  simp only [ringOp, GlobalTheory.HeatV.opV, Matrix.map_apply, cst_eq]
  have E : (d i O (rsT (L.g (j i) (j i')).val O) + ∑ a, pbT π (-e a) O * dd a O (rsT (L.g (j i) (j i')).val O)) *
      rsT (L.g (j i) (j i'))⁻¹.val O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        ∑ b, pbT π (e b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  have U1 : ∑ a, pbT π (-c a) O * (dd a O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) =
      -∑ b, pbT π (c b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  rw [E, U1]
  set g := rsT (L.g (j i) (j i')).val O
  set gi := rsT (L.g (j i) (j i'))⁻¹.val O
  linear_combination (2 * (k : Γ(Y, O))) * F1 +
    (k : Γ(Y, O)) ^ 2 * f * (-2 * F2 + (∑ a, ∑ b, pbT π (Θ a b) O * (dd a O g * gi) * (dd b O g * gi)) * hc2 O hO) +
    (k : Γ(Y, O)) * f * (-2 * F3 + (∑ a, ∑ b, pbT π (Θ a b) O * dd a O (dd b O g * gi)) * hc2 O hO)

end GlobalTheory.HeatVAlg
