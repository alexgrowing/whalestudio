import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Points

namespace GlobalTheory.FlagEmb.QuotLine

section Pull

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X)

def pu (W : Z.Opens) (i j : L.ι) (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) : Γ(Z, W)ˣ :=
  Units.map (f.appLE (L.U i ⊓ L.U j) W (le_inf hi hj)).hom (L.g i j)

variable {f L} {W V : Z.Opens} {i j k : L.ι}

theorem res_pu (h : V ≤ W) (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) :
    res h (pu f L W i j hi hj) = pu f L V i j (h.trans hi) (h.trans hj) :=
  Units.ext (resG_appLE f _ h _)

theorem pu_self (hL : L.IsLB) (hi hi' : W ≤ f ⁻¹ᵁ L.U i) : pu f L W i i hi hi' = 1 := by
  have h := congrArg (fun u : Γ(X, L.U i)ˣ => (f.appLE (L.U i) W hi).hom u.val) (hL.g_self i)
  exact Units.ext ((appLE_resG f _ hi _).symm.trans (h.trans (map_one _)))

theorem pu_mul (hL : L.IsLB) (hi : W ≤ f ⁻¹ᵁ L.U i) (hj hj' : W ≤ f ⁻¹ᵁ L.U j) (hk : W ≤ f ⁻¹ᵁ L.U k) :
    pu f L W i j hi hj * pu f L W j k hj' hk = pu f L W i k hi hk := by
  have hW : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_inf (le_inf hi hj) hk
  have h := congrArg (fun u : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => (f.appLE _ W hW).hom u.val) (hL.cocycle i j k)
  simp only [Units.val_mul, map_mul] at h
  refine Units.ext (Eq.trans ?_ (h.trans (appLE_resG f _ hW _)))
  exact congrArg₂ (· * ·) (appLE_resG f _ hW _).symm (appLE_resG f _ hW _).symm

theorem valR_pu {C : Type} [CommRing C] (w : Sp C ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ W) (hi : W ≤ f ⁻¹ᵁ L.U i)
    (hj : W ≤ f ⁻¹ᵁ L.U j) : valR w W (pu f L W i j hi hj).val = valR (w ≫ f) _ (L.g i j).val :=
  valR_appLE w f _ hw _

theorem valR_cocycle (hL : L.IsLB) {C : Type} [CommRing C] (x : Sp C ⟶ X) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x _ (L.g i j).val * valR x _ (L.g j k).val = valR x _ (L.g i k).val := by
  have h := congrArg (fun u : Γ(Sp C, ⊤)ˣ => valR (𝟙 _) ⊤ u.val) (pu_mul (f := x) hL hi hj hj hk)
  simp only [Units.val_mul] at h
  rwa [valR_mul _ _ (le_preimage_top _), valR_pu _ (le_preimage_top _), valR_pu _ (le_preimage_top _),
    valR_pu _ (le_preimage_top _), Category.id_comp] at h

theorem exists_mem (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i :=
  Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))

end Pull

section Three

variable {X X₀ X₁ Z : Scheme.{0}} (f : Z ⟶ X) (f₀ : Z ⟶ X₀) (f₁ : Z ⟶ X₁) (L : LB X) (L₀ : LB X₀) (L₁ : LB X₁)
  {I : Type} (a : I → L.ι) (b : I → L₀.ι) (c : I → L₁.ι)

def cov (i : I) : Z.Opens := f ⁻¹ᵁ L.U (a i) ⊓ (f₀ ⁻¹ᵁ L₀.U (b i) ⊓ f₁ ⁻¹ᵁ L₁.U (c i))

variable {f f₀ f₁ L L₀ L₁ a b c}

theorem le_a {W : Z.Opens} {i : I} (h : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i) : W ≤ f ⁻¹ᵁ L.U (a i) := h.trans inf_le_left

theorem le_b {W : Z.Opens} {i : I} (h : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i) : W ≤ f₀ ⁻¹ᵁ L₀.U (b i) :=
  h.trans (inf_le_right.trans inf_le_left)

theorem le_c {W : Z.Opens} {i : I} (h : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i) : W ≤ f₁ ⁻¹ᵁ L₁.U (c i) :=
  h.trans (inf_le_right.trans inf_le_right)

def tr (W : Z.Opens) (i j : I) (hi : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i) (hj : W ≤ cov f f₀ f₁ L L₀ L₁ a b c j) : Γ(Z, W)ˣ :=
  pu f L W _ _ (le_a hi) (le_a hj) * pu f₀ L₀ W _ _ (le_b hi) (le_b hj) * pu f₁ L₁ W _ _ (le_c hj) (le_c hi)

theorem res_tr {W V : Z.Opens} (h : V ≤ W) {i j : I} (hi : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i)
    (hj : W ≤ cov f f₀ f₁ L L₀ L₁ a b c j) : res h (tr W i j hi hj) = tr V i j (h.trans hi) (h.trans hj) := by
  simp only [tr, map_mul, res_pu]

theorem isLB_tr (hL : L.IsLB) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hs : ∀ x y z, ∃ i, a i = x ∧ b i = y ∧ c i = z) :
    LB.IsLB ⟨I, cov f f₀ f₁ L L₀ L₁ a b c, fun i j => tr _ i j inf_le_left inf_le_right⟩ where
  cover := by
    refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨x, hx⟩ := exists_mem hL (f t)
    obtain ⟨y, hy⟩ := exists_mem hL₀ (f₀ t)
    obtain ⟨z, hz⟩ := exists_mem hL₁ (f₁ t)
    obtain ⟨i, rfl, rfl, rfl⟩ := hs x y z
    exact Opens.mem_iSup.2 ⟨i, hx, hy, hz⟩
  g_self i := by
    rw [res_tr, tr, pu_self hL, pu_self hL₀, pu_self hL₁, one_mul, one_mul]
  cocycle i j k := by
    rw [res_tr, res_tr, res_tr, tr, tr, tr, mul_mul_mul_comm, mul_mul_mul_comm (pu f L _ _ _ _ _), pu_mul hL, pu_mul hL₀,
      mul_comm (pu f₁ L₁ _ _ _ _ _), pu_mul hL₁]

theorem valR_tr {C : Type} [CommRing C] {W : Z.Opens} (w : Sp C ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ W) {i j : I}
    (hi : W ≤ cov f f₀ f₁ L L₀ L₁ a b c i) (hj : W ≤ cov f f₀ f₁ L L₀ L₁ a b c j) :
    valR w W (tr W i j hi hj).val = valR (w ≫ f) _ (L.g (a i) (a j)).val * valR (w ≫ f₀) _ (L₀.g (b i) (b j)).val *
      valR (w ≫ f₁) _ (L₁.g (c j) (c i)).val := by
  simp only [tr, Units.val_mul]
  rw [valR_mul _ _ hw, valR_mul _ _ hw, valR_pu _ hw, valR_pu _ hw, valR_pu _ hw]

end Three

section Val

variable {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U)

theorem valR_chart {C : Type} [CommRing C] (φ : Γ(Z, U) →+* C) (s : Γ(Z, U)) : valR (spMap φ ≫ hU.fromSpec) U s = φ s := by
  have h := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  exact (valR_eq _ U h s).trans (congrArg (fun t => t.hom s) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h))

theorem isUnit_coord {O : Type} [CommRing O] {N : ℕ} {g : Z ⟶ PSpace O N} {c : O →+* Γ(Z, U)} {v : Fin (N + 1) → Γ(Z, U)}
    {hv} (e : hU.fromSpec ≫ g = pt c v hv) (q : Fin (N + 1)) (h : W ≤ U) (hq : W ≤ g ⁻¹ᵁ chart O N q) :
    IsUnit (resG Z h (v q)) := by
  refine isUnit_of_basicOpen_eq _ ?_
  refine (Scheme.basicOpen_res _ _ _).trans (inf_eq_left.2 fun t ht => ?_)
  obtain ⟨y, rfl⟩ : t ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact h ht
  have h1 : y ∈ (hU.fromSpec ≫ g) ⁻¹ᵁ chart O N q := hq ht
  rw [e, pt_preimage_chart] at h1
  change y ∈ hU.fromSpec ⁻¹ᵁ Z.basicOpen (v q)
  rw [hU.fromSpec_preimage_basicOpen]
  exact h1

theorem valR_O1 {O k : Type} [CommRing O] [Field k] {N : ℕ} {c : O →+* k} {v : Fin (N + 1) → k} {hv}
    {x : Sp k ⟶ PSpace O N} (e : x = pt c v hv) (i j : Fin (N + 1)) (hi : ⊤ ≤ x ⁻¹ᵁ chart O N i)
    (hj : ⊤ ≤ x ⁻¹ᵁ chart O N j) : v i ≠ 0 ∧ valR x _ ((O1 O N).g i j).val * v i = v j := by
  subst e
  have hu := (le_pt_preimage_chart_iff c v hv i).1 hi
  refine ⟨hu.ne_zero, ?_⟩
  have h := valR_res (pt c v hv) (inf_le_left : chart O N i ⊓ chart O N j ≤ _) (le_inf hi hj) (ratio O N i j)
  rw [valR_pt_ratio c v hv hu] at h
  refine (congrArg (· * v i) h).trans ?_
  rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

theorem trans_alg {k : Type} [Field k] {r r' γ γ' g a a' b b' u v : k} (n : γ' ≠ 0) (n' : b' ≠ 0)
    (t : r * (γ * b) = a) (t' : r' * (γ' * b') = a') (s : g * γ' = γ) (s₀ : u * a = a') (s₁ : v * b' = b) :
    r' = g * u * v * r := by
  refine mul_right_cancel₀ (mul_ne_zero n n') (t'.trans ?_)
  rw [← s₀, ← t, ← s, ← s₁]
  ring

end Val

theorem exists_line {X Z : Scheme.{0}} (π : Z ⟶ X) (L : FinLB X) {O : Type} [CommRing O] {N₀ N₁ : ℕ}
    (g₀ : Z ⟶ PSpace O N₀) (g₁ : Z ⟶ PSpace O N₁) {A : Type} (U : A → Z.affineOpens) (ι : A → Fin L.n)
    (hU : ∀ a, (U a).1 ≤ π ⁻¹ᵁ L.U (ι a)) (c : ∀ a, O →+* Γ(Z, (U a).1)) (v₀ : ∀ a, Fin (N₀ + 1) → Γ(Z, (U a).1))
    (v₁ : ∀ a, Fin (N₁ + 1) → Γ(Z, (U a).1)) (e₀ : ∀ a, ∃ hv, (U a).2.fromSpec ≫ g₀ = pt (c a) (v₀ a) hv)
    (e₁ : ∀ a, ∃ hv, (U a).2.fromSpec ≫ g₁ = pt (c a) (v₁ a) hv) :
    ∃ (L' : FinLB Z) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (N₀ + 1)) (q₁ : Fin L'.n → Fin (N₁ + 1))
      (r : ∀ (a : A) (i : Fin L'.n), Γ(Z, (U a).1 ⊓ L'.U i)ˣ),
      (∀ i, L'.U i ≤ π ⁻¹ᵁ L.U (ix i) ⊓ (g₀ ⁻¹ᵁ chart _ _ (q₀ i) ⊓ g₁ ⁻¹ᵁ chart _ _ (q₁ i))) ∧
      (∀ (k : Type) [Field k] (w : Sp k ⟶ Z) a i i', ⊤ ≤ w ⁻¹ᵁ ((U a).1 ⊓ (L'.U i ⊓ L'.U i')) →
        valF w _ (r a i').val = valF w _ (L'.g i i').val * valF w _ (r a i).val) ∧
      ∀ (k : Type) [Field k] a i (φ : Γ(Z, (U a).1) →+* k), ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ L'.U i →
        valF (spMap φ ≫ (U a).2.fromSpec) _ (r a i).val *
          (valF ((spMap φ ≫ (U a).2.fromSpec) ≫ π) _ (L.g (ix i) (ι a)).val * φ (v₁ a (q₁ i))) = φ (v₀ a (q₀ i)) := by
  choose h₀ e₀ using e₀
  choose h₁ e₁ using e₁
  let e := (Fintype.equivFin (Fin L.n × Fin (N₀ + 1) × Fin (N₁ + 1))).symm
  let ix := fun i => (e i).1
  let q₀ := fun i => (e i).2.1
  let q₁ := fun i => (e i).2.2
  let C := cov π g₀ g₁ L.lb (O1 O N₀) (O1 O N₁) ix q₀ q₁
  let L' : FinLB Z := ⟨_, C, fun i j => tr _ i j inf_le_left inf_le_right,
    isLB_tr L.isLB (O1_isLB _ _) (O1_isLB _ _) fun x y z => ⟨e.symm (x, y, z), by simp [ix, q₀, q₁]⟩⟩
  have u₀ := fun a i => isUnit_coord (U a).2 (W := (U a).1 ⊓ C i) (e₀ a) (q₀ i) inf_le_left (le_b inf_le_right)
  have u₁ := fun a i => isUnit_coord (U a).2 (W := (U a).1 ⊓ C i) (e₁ a) (q₁ i) inf_le_left (le_c inf_le_right)
  let r : ∀ (a : A) i, Γ(Z, (U a).1 ⊓ C i)ˣ := fun a i =>
    (u₀ a i).unit * (pu π L.lb _ (ix i) (ι a) (le_a inf_le_right) (inf_le_left.trans (hU a)) * (u₁ a i).unit)⁻¹
  have val : ∀ (k : Type) [Field k] a i (φ : Γ(Z, (U a).1) →+* k), ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ C i →
      valR (spMap φ ≫ (U a).2.fromSpec) _ (r a i).val *
        (valR ((spMap φ ≫ (U a).2.fromSpec) ≫ π) _ (L.g (ix i) (ι a)).val * φ (v₁ a (q₁ i))) = φ (v₀ a (q₀ i)) := by
    intro k _ a i φ h
    have hw : ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ ((U a).1 ⊓ C i) :=
      le_inf (le_preimage_specMap_fromSpec (U a).2 (CommRingCat.ofHom φ)) h
    have h1 : r a i * (pu π L.lb _ (ix i) (ι a) (le_a inf_le_right) (inf_le_left.trans (hU a)) * (u₁ a i).unit) =
        (u₀ a i).unit := inv_mul_cancel_right _ _
    have h2 := congrArg (fun u : Γ(Z, (U a).1 ⊓ C i)ˣ => valR (spMap φ ≫ (U a).2.fromSpec) _ u.val) h1
    simp only [Units.val_mul, IsUnit.unit_spec] at h2
    rwa [valR_mul _ _ hw, valR_mul _ _ hw, valR_pu _ hw, valR_res _ _ hw, valR_res _ _ hw, valR_chart (U a).2 φ,
      valR_chart (U a).2 φ] at h2
  refine ⟨L', ix, q₀, q₁, r, fun i => le_rfl, fun k _ w a i i' h => ?_, val⟩
  have ha : ⊤ ≤ w ⁻¹ᵁ (U a).1 := le_preimage_mono w inf_le_left h
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Z, (U a).1) →+* k, spMap φ ≫ (U a).2.fromSpec = w :=
    ⟨(valMap w _ ha).hom, specMap_valMap_fromSpec (U a).2 w ha⟩
  have hh : ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ (C i ⊓ C i') := le_preimage_mono _ inf_le_right h
  have hi : ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ C i := le_preimage_mono _ inf_le_left hh
  have hi' : ⊤ ≤ (spMap φ ≫ (U a).2.fromSpec) ⁻¹ᵁ C i' := le_preimage_mono _ inf_le_right hh
  have p₀ : (spMap φ ≫ (U a).2.fromSpec) ≫ g₀ = pt (φ.comp (c a)) (φ ∘ v₀ a) (span_range_comp_eq_top _ (h₀ a) φ) := by
    rw [Category.assoc, e₀, GlobalTheory.ProjSpace.spMap_pt]
  have p₁ : (spMap φ ≫ (U a).2.fromSpec) ≫ g₁ = pt (φ.comp (c a)) (φ ∘ v₁ a) (span_range_comp_eq_top _ (h₁ a) φ) := by
    rw [Category.assoc, e₁, GlobalTheory.ProjSpace.spMap_pt]
  obtain ⟨n₀, s₀⟩ := valR_O1 p₀ (q₀ i) (q₀ i') (le_preimage_comp _ g₀ (le_b le_rfl) hi)
    (le_preimage_comp _ g₀ (le_b le_rfl) hi')
  obtain ⟨n₁, s₁⟩ := valR_O1 p₁ (q₁ i') (q₁ i) (le_preimage_comp _ g₁ (le_c le_rfl) hi')
    (le_preimage_comp _ g₁ (le_c le_rfl) hi)
  have ga := le_preimage_comp _ π (hU a) ha
  have gi' := le_preimage_comp _ π (le_a (L := L.lb) le_rfl) hi'
  have s := valR_cocycle L.isLB _ (le_preimage_comp _ π (le_a (L := L.lb) le_rfl) hi) gi' ga
  have n : valR ((spMap φ ≫ (U a).2.fromSpec) ≫ π) _ (L.g (ix i') (ι a)).val ≠ 0 := by
    rw [valR_eq _ _ (le_inf gi' ga)]
    exact ((Units.isUnit _).map _).ne_zero
  have t := val k a i φ hi
  have t' := val k a i' φ hi'
  change valR _ _ (r a i').val = valR _ _ (tr (C i ⊓ C i') i i' inf_le_left inf_le_right).val * valR _ _ (r a i).val
  exact (trans_alg n n₁ t t' s s₀ s₁).trans (congrArg (· * _) (valR_tr _ hh _ _).symm)

theorem plk_scale {S ι : Type} [CommRing S] {M k : ℕ} (γ : S) (c : ι → Fin (M + 1) → S) (e : Fin k → ι) (q) :
    plk (fun z => γ • c z) e q = γ ^ k * plk c e q := by
  have h := Matrix.det_smul (Matrix.of fun l l' => c (e l) (plE M k q l')) γ
  rw [Fintype.card_fin] at h
  exact h

theorem spMap_dual_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  have : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [dualMap]
  rw [this]
  exact Spec.map_id _

theorem exists_isLine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ en₀ en₁ : En Dw.mult, en₁.1 = en₀.1 + 1 → ∃ (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M en₀.1 + 1)) (q₁ : Fin L'.n → Fin (plN M en₁.1 + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g en₀ en₁ L' ix q₀ q₁ r := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T en₀ en₁ hen
  have hU : ∀ a, (Z.U a).1 ≤ Z.π ⁻¹ᵁ L.U (ι a) := fun a t ht => by
    obtain ⟨y, rfl⟩ : t ∈ Set.range (Z.U a).2.fromSpec := by
      rw [(Z.U a).2.range_fromSpec]
      exact ht
    have h := le_preimage_specMap_fromSpec (aff (ι a)) (CommRingCat.ofHom (ρ a))
    have h' : ⊤ ≤ (Z.chart a ≫ Z.π) ⁻¹ᵁ L.U (ι a) := T.res a ▸ h
    exact h' (Set.mem_univ y)
  obtain ⟨L', ix, q₀, q₁, r, h1, h2, h3⟩ := exists_line Z.π L (g en₀) (g en₁) Z.U ι hU _ _ _
    (fun a => T.plk a en₀) (fun a => T.plk a en₁)
  refine ⟨L', ix, q₀, q₁, r, h1, h2, fun k _ a i φ ψ hψ h => ?_⟩
  have hφ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π := by
    rw [← T.res a, ← Category.assoc]
    congr 1
    exact Spec.map_comp _ _
  have tan : ∀ z : Let Dw.mult, IsTanAtG (Y Z.i).t (spMap (ρ a) ≫ (aff (ι a)).fromSpec) (Z.fr a z.1 z.2) := by
    intro z
    have h1 := ((T.frame a _ (RingHom.id _)).1 z.1 z.2).1
    have h2 : spMap (RingHom.id Γ(Z.X, (Z.U a).1)) = 𝟙 _ := Spec.map_id _
    rw [h2, Category.id_comp, Vecs.bc, spMap_dual_id, Category.id_comp] at h1
    rw [T.res a]
    exact h1
  have nat : (fun z : Let Dw.mult => φ ∘ crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) =
      fun z : Let Dw.mult => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) :=
    funext fun z => (T.emb.nat (ι a) _ k (ρ a) φ _ (tan z)).symm
  have tr : (fun z : Let Dw.mult => crd (ix i) k ψ ((Z.fr a).bc φ z.1 z.2)) =
      fun z : Let Dw.mult => valF ((spMap φ ≫ Z.chart a) ≫ Z.π) _ (L.g (ix i) (ι a)).val •
        crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) := by
    rw [Category.assoc, ← hψ]
    exact funext fun z => T.emb.trans (ix i) (ι a) k ψ (φ.comp (ρ a)) _ (hψ.trans hφ.symm)
      (by rw [hψ]; exact ((T.frame a k φ).1 z.1 z.2).1)
  have t : valF (spMap φ ≫ Z.chart a) _ (r a i).val * (valF ((spMap φ ≫ Z.chart a) ≫ Z.π) _ (L.g (ix i) (ι a)).val *
      (φ ∘ plk (fun z : Let Dw.mult => crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) en₁.2.1) (q₁ i)) =
      (φ ∘ plk (fun z : Let Dw.mult => crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) en₀.2.1) (q₀ i) := h3 k a i φ h
  rw [map_plk, map_plk, nat] at t
  rw [tr, plk_scale, plk_scale, ← t]
  have hp : ∀ γ : k, γ ^ en₁.1 = γ ^ en₀.1 * γ := fun γ => by rw [hen, pow_succ]
  rw [hp]
  ring

end GlobalTheory.FlagEmb.QuotLine
