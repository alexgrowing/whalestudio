import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_comp_map {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (V : X.Opens) (hz : h (g z) ∈ V)
    (a : Γ(X, V)) : gs (g ≫ h) z V a = (g.stalkMap z).hom (gs h (g z) V a) := by
  rw [← gs_pull g h z V hz a, gs_eq_map_gs g z (h ⁻¹ᵁ V) hz, gs_pull (𝟙 Y) h (g z) V hz a, Category.id_comp]

theorem secCarriedOver_of_lift {X Z P : Scheme.{0}} (q : Z ⟶ X) (p₁ : Z ⟶ P) (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (d : ℕ) (B : Fin d → Γ(P, ⊤))
    (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k))
    (hdec : ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
      gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs p₁ z ⊤ (B l) * gs q z (O ⊓ L.U k) (s l k))
    (huniq : ∀ (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U →
      (∀ z : Z, q z = x → ∑ l, gs p₁ z ⊤ (B l) * gs q z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0)
    (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)) (f' : Z ⟶ Z) (hf'q : f' ≫ q = q ≫ φ) (hf'p : f' ≫ p₁ = p₁)
    (hcar : FrameCarriedAlong L q (q ⁻¹ᵁ W) τ φ w f') (l : Fin d) : SecCarriedOver L O (s l) φ w := by
  have hpt : ∀ z, q (f' z) = φ (q z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hf'q, Scheme.Hom.comp_apply]
  intro x j k hxO hφxO hxk hφxj
  let U' : X.Opens := O ⊓ L.U k ⊓ φ ⁻¹ᵁ (O ⊓ L.U j) ⊓ ((L.pull φ).U (fun _ => j) ⊓ L.U k)
  have h1 : U' ≤ φ ⁻¹ᵁ (O ⊓ L.U j) := fun _ h => h.1.2
  have h2 : U' ≤ (L.pull φ).U (fun _ => j) ⊓ L.U k := fun _ h => h.2
  have h3 : U' ≤ O ⊓ L.U k := fun _ h => h.1.1
  let a : Fin d → Γ(X, U') := fun l' =>
    (X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j)) -
      (X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val * (X.presheaf.map (homOfLE h3).op).hom (s l' k)
  have ha : ∀ {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (hy : g y ∈ U') (l' : Fin d),
      gs g y U' (a l') = gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) -
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val * gs g y (O ⊓ L.U k) (s l' k) := by
    intro Y g y hy l'
    have e1 : gs g y U' ((X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j))) =
        gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) :=
      (gs_res g y h1 hy _).trans (gs_pull g φ y (O ⊓ L.U j) (h1 hy) _)
    have e2 : gs g y U' ((X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val) =
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val :=
      (gs_res g y h2 hy _).trans (gs_unit g y _ (h2 hy) _)
    have e3 : gs g y U' ((X.presheaf.map (homOfLE h3).op).hom (s l' k)) = gs g y (O ⊓ L.U k) (s l' k) :=
      gs_res g y h3 hy _
    rw [gs_sub' g y U' hy, gs_mul g y U' hy, e1, e2, e3]
  have hxU : x ∈ U' := ⟨⟨⟨hxO, hxk⟩, hφxO, hφxj⟩, mem_pull.2 hφxj, hxk⟩
  have key := huniq U' a x hxU (by
    intro z hz
    have hzU : q z ∈ U' := hz ▸ hxU
    have hzO : q z ∈ O := hz ▸ hxO
    have hzk : q z ∈ L.U k := hz ▸ hxk
    have hzW : z ∈ q ⁻¹ᵁ W := hOW hzO
    have hf'zO : q (f' z) ∈ O := by rw [hpt, hz]; exact hφxO
    have hf'zj : q (f' z) ∈ L.U j := by rw [hpt, hz]; exact hφxj
    have hmj : q (f' z) ∈ O ⊓ L.U j := ⟨hf'zO, hf'zj⟩
    have hmWj : f' z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j := ⟨hOW hf'zO, hf'zj⟩
    have hmWk : (𝟙 Z) z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := ⟨hzW, hzk⟩
    have hcz := hcar z j k hzW (hOW hf'zO) hzk hf'zj
    have S1 : ∑ l', gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) =
        (gm f' z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j) (τ j)).val := by
      have e1 : ∀ l', gs p₁ z ⊤ (B l') = (f'.stalkMap z).hom (gs p₁ (f' z) ⊤ (B l')) := fun l' => by
        conv_lhs => rw [← hf'p]
        exact gs_comp_map f' p₁ z ⊤ trivial _
      have e2 : ∀ l', gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) = (f'.stalkMap z).hom (gs q (f' z) (O ⊓ L.U j) (s l' j)) :=
        fun l' => by rw [← hf'q]; exact gs_comp_map f' q z _ hmj _
      simp only [e1, e2, ← map_mul, ← map_sum]
      rw [← hdec (f' z) j hf'zO hf'zj, ← gs_eq_map_gs f' z _ hmWj, gs_unit f' z _ hmWj]
    have S3 := hdec z k hzO hzk
    rw [gs_unit (𝟙 Z) z _ hmWk] at S3
    have e4 : ∀ l', gs p₁ z ⊤ (B l') * gs q z U' (a l') =
        gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) -
          (gw w q z j k).val * (gs p₁ z ⊤ (B l') * gs q z (O ⊓ L.U k) (s l' k)) := fun l' => by
      rw [ha q z hzU l', gw]; ring
    rw [Finset.sum_congr rfl (fun l' _ => e4 l'), Finset.sum_sub_distrib, ← Finset.mul_sum, S1, ← S3, hcz,
      Units.val_mul, sub_self])
  have e := key l
  rw [ha (𝟙 X) x hxU l, Category.id_comp, sub_eq_zero] at e
  exact e

theorem secCarriedOver_of_frameCarriedAlong : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  intro R R₁ _ _ ρ₁ d b hb X f L W O hOW τ s hdec φ w hφ hcar l
  have hcond : (pullback.fst f (spMap ρ₁) ≫ φ) ≫ f = pullback.snd f (spMap ρ₁) ≫ spMap ρ₁ := by
    rw [Category.assoc, hφ, pullback.condition]
  have hf'q : pullback.lift _ _ hcond ≫ pullback.fst f (spMap ρ₁) = pullback.fst f (spMap ρ₁) ≫ φ :=
    pullback.lift_fst _ _ _
  have hf'p : pullback.lift _ _ hcond ≫ pullback.snd f (spMap ρ₁) = pullback.snd f (spMap ρ₁) :=
    pullback.lift_snd _ _ _
  exact secCarriedOver_of_lift (pullback.fst f (spMap ρ₁)) (pullback.snd f (spMap ρ₁)) L W O hOW τ d
    (fun l => (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) s hdec
    (fun U a x hx hz => GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange R R₁ ρ₁ d b hb X f U a x hx hz) φ w _ hf'q hf'p (hcar _ hf'q hf'p) l

end GlobalTheory.Mum
