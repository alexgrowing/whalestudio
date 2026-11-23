import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TrCoef

theorem exists_nestSec {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2))) :
    ∃ T : LB.Sec (LB.LinComb (LB.LinComb L F ε) ψ δ), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (I : (Z ⟶ X) → L.ι), Good L z I → sval T r z (fun χ j => I (χ ≫ F j)) = sval s r z I := by
  have le : ∀ q : K → J → L.ι, LB.wchart (LB.LinComb L F ε) ψ q ≤
      LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => q p.1 p.2) := fun q y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  have v : ∀ (q : K → J → L.ι) (y : Y) (hy : y ∈ LB.wchart (LB.LinComb L F ε) ψ q),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2)) =
        gs (𝟙 Y) y _ (s.f fun p => q p.1 p.2) := fun q y hy => gs_res _ y (le q) hy _
  refine ⟨⟨fun q => (Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2),
    fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z I hI => ?_⟩
  · have htr : trF (L := LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' =
        trF (L := L) (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2) (𝟙 Y) y
          (fun p => q p.1 p.2) (fun p => q' p.1 p.2) := by
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
        (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (q k) (q' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k))).trans ?_
      simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
    refine ((gs_res (𝟙 Y) y _ hy _).trans (v q y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb (LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (v q' y hy.2)))).symm)
    refine (sec_trans s (𝟙 Y) y (le q hy.1) (le q' hy.2)).trans ?_
    rw [← htr]
    rfl
  · have hI' : Good (LB.LinComb L F ε) z (fun χ j => I (χ ≫ F j)) := fun χ => hI.mem F χ
    have hm := hI'.mem ψ r
    rw [sval_of s r z I (fun p => I ((r ≫ ψ p.1) ≫ F p.2)) (fun p => by rw [Category.assoc])]
    exact gs_res r z (le _) hm _

end GlobalTheory.MumCmp.TrCoef

namespace GlobalTheory.MumCmp.TrCoef

theorem formEq_coef {R : Type} [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (g : GtPt D (𝟙_ (Over (Sp R)))) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k)
        (Sum.elim (fun k => (toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k)
          (fun k => (toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k)))
      (Sum.elim (DegPre.famε 1) (Sum.elim DegPre.gtε ![-1, 1]))
      (fun p : Fin 4 × Fin 3 => D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2)
      (fun p => DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) := by
  intro U _ h
  have hu : ∀ x : D₂.P.A ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit D₂.P.A := fun x => toUnit_unique _ _
  have ht : ∀ x : D₂.P.A ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit D₂.P.A ≫ g.b)).left * (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ g.b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.famφB χ₂ k = ((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
      Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2) ^
      (DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
        Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k ≫ β) * (toUnit D₂.P.A ≫ g.b)).left *
        (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left) ^ DegPre.famε 1 k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (DegPre.famε 1 k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have hL1 : ∏ k, h (GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k) ^ DegPre.famε 1 k =
      h ((β * (toUnit D₂.P.A ≫ g.b)) * (toUnit D₂.P.A ≫ D.c χ)).left * (h (toUnit D₂.P.A ≫ D.c χ).left)⁻¹ *
        h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ 𝟙 D.P.A).left ^ (((1 : ℕ) : ℤ) - 1) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c χ))).left ^ (1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ D.c χ).left ^ (-1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      toUnit_unique ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A) (toUnit D₂.P.A)]
    simp only [Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, zpow_one, zpow_neg_one]
    rfl
  have hL2 : ∏ k, h ((toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k) ^ DegPre.gtε k =
      (h ((toUnit D₂.P.A ≫ D.c χ) * (toUnit D₂.P.A ≫ g.b)).left)⁻¹ * h (toUnit D₂.P.A ≫ D.c χ).left *
        h (toUnit D₂.P.A ≫ g.b).left * (h (1 : D₂.P.A ⟶ D.P.A).left)⁻¹ := by
    rw [Fin.prod_univ_four]
    show h (toUnit D₂.P.A ≫ ((toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ) * g.b)).left ^ (-1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ g.b).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc (toUnit D₂.P.A), ← Category.assoc (toUnit D₂.P.A),
      toUnit_unique (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R)))) (toUnit D₂.P.A)]
    simp only [zpow_one, zpow_neg_one]
    rfl
  have hL3 : ∏ k, h ((toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k) ^ (![-1, 1] : Fin 2 → ℤ) k =
      (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_two]
    show h (toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) * h (toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [zpow_one, zpow_neg_one]
    rfl
  have h0 : (𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂)) ≫ β = β * (toUnit D₂.P.A ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hc]
  have h2 : (toUnit D₂.P.A ≫ D₂.c χ₂) ≫ β = toUnit D₂.P.A ≫ D.c χ := by rw [Category.assoc, hc]
  have h3 : (1 : D₂.P.A ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL1, hL2, hL3, hA, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Category.id_comp, h0, h2, h3, _root_.one_mul]
  rw [mul_right_comm β (toUnit D₂.P.A ≫ D.c χ)]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_translated_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ D D₂ β hβ g xe hc w hw ν hν f
  have key : ∀ χ : D₂.X, ∃ f₂ : D₂.SecB 1 χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι),
      Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' →
      Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval f₂ r z J' := by
    intro χ
    haveI := hβ
    let u := LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit D₂.P.A).left)
      (LB.pullGen D.P.L _ _ ν (toUnit D₂.P.A).left)
    have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.isGen _) _)
      (DVR.pullGen_isGen _ _ _ _ hν _)
    let S := pullMulSec (f (xe χ)) (GlobalTheory.MumCmp.twφ D₂ D β g.b 0) u hu
    obtain ⟨S', hS'⟩ := exists_sec D.P.isLB (formEq_coef D D₂ β g χ (xe χ) (hc χ)) S
    obtain ⟨T, hT⟩ := exists_nestSec (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε (D₂.famφB χ) (DegPre.famε 1) S'
    have hA := LB.isLB_linComb D₂.P.isLB (D₂.famφB χ) (DegPre.famε 1)
    have hB := LB.isLB_linComb (LB.isLB_linComb D.P.isLB (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε)
      (D₂.famφB χ) (DegPre.famε 1)
    have hU := DVR.linCombIso_isGen w hw (D₂.famφB χ) (DegPre.famε 1)
    refine ⟨DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB,
      fun Z r z J J' hJ hJ' => ?_⟩
    have hJ'' : Good (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε) z
        (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := fun χ' => hJ.mem _ χ'
    have m₁ := hJ'.mem (D₂.famφB χ) r
    have m₂ := hJ''.mem (D₂.famφB χ) r
    have e1 : Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
        Geo.Tor.sval T r z (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := by
      rw [hT Z r z J hJ, hS' Z r z J hJ, sval_pullMulSec _ _ _ hu r z hJ, val_mul hJ, val_pull hJ, val_pull hJ]
    rw [e1]
    have e2 := DVR.ps_gs_secOfIso (LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB
      (fun k => J' (r ≫ D₂.famφB χ k)) (fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) r z ⟨m₁, m₂⟩
    have e3 := DVR.ps_gm_linCombIso w (D₂.famφB χ) (DegPre.famε 1)
      ((fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)), (fun k => J' (r ≫ D₂.famφB χ k))) r z ⟨m₂, m₁⟩
    rw [show Geo.Tor.sval (DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB) r z J' = _ from e2,
      e3]
    exact (Units.mul_inv_cancel_left _ _).symm
  choose f₂ hf₂ using key
  exact ⟨f₂, hf₂⟩

end GlobalTheory.MumCmp.TrCoef
