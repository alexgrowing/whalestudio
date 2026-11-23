import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SymSec
open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem sec_gs {N : LB X} (s : LB.Sec N) (r : Y ⟶ X) (y : Y) {i j : N.ι} (hi : r y ∈ N.U i) (hj : r y ∈ N.U j) :
    gs r y (N.U i) (s.f i) = (gm r y (N.U i ⊓ N.U j) (N.g i j)).val * gs r y (N.U j) (s.f j) := by
  have hm : r y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  exact (gs_res r y _ hm _).symm.trans ((congrArg (gs r y _) (s.compat i j)).trans ((gs_mul r y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r y _ hm _) (gs_res r y _ hm _))))

theorem glue {N : LB X} (hN : N.IsLB) {I : Type} (W : I → X.Opens) (c : I → N.ι) (hc : ∀ i, W i ≤ N.U (c i))
    (hW : ∀ x : X, ∃ i, x ∈ W i) (a : ∀ i, Γ(X, W i))
    (h : ∀ i i' x, x ∈ W i → x ∈ W i' → gs (𝟙 X) x (W i) (a i) =
      (gm (𝟙 X) x (N.U (c i) ⊓ N.U (c i')) (N.g (c i) (c i'))).val * gs (𝟙 X) x (W i') (a i')) :
    ∃ s : LB.Sec N, ∀ i x, x ∈ W i → gs (𝟙 X) x (N.U (c i)) (s.f (c i)) = gs (𝟙 X) x (W i) (a i) := by
  have gl : ∀ j : N.ι, ∃ b : Γ(X, N.U j), ∀ i x, x ∈ N.U j → x ∈ W i →
      gs (𝟙 X) x (N.U j) b = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) := by
    intro j
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X, N.U j ⊓ W i), ∀ i x, x ∈ N.U j ⊓ W i →
        gs (𝟙 X) x _ (u i) = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) :=
      ⟨fun i => (X.presheaf.map (homOfLE (inf_le_inf_left _ (hc i) : N.U j ⊓ W i ≤ N.U j ⊓ N.U (c i))).op).hom
          (N.g j (c i)).val * (X.presheaf.map (homOfLE (inf_le_right : N.U j ⊓ W i ≤ W i)).op).hom (a i),
        fun i x hx => (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res _ x _ hx _).trans
          (gs_unit (𝟙 X) x (N.U j ⊓ N.U (c i)) ⟨hx.1, hc i hx.2⟩ _)) (gs_res _ x _ hx _))⟩
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i => N.U j ⊓ W i) (N.U j)
      (fun i => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := hW x
        exact Opens.mem_iSup.2 ⟨i, hx, hi⟩) u
      (fun i i' => fn_ext (V := (N.U j ⊓ W i) ⊓ (N.U j ⊓ W i')) fun x hx => by
        refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_ (gs_res (𝟙 X) x inf_le_right hx _).symm)
        rw [hu i x hx.1, hu i' x hx.2, h i i' x hx.1.2 hx.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hN (𝟙 X) x hx.1.1 (hc i hx.1.2) (hc i' hx.2.2)])
    refine ⟨b, fun i x h₁ h₂ => ?_⟩
    have hx : x ∈ N.U j ⊓ W i := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 X) x inf_le_left hx b).symm.trans ((congrArg (gs (𝟙 X) x (N.U j ⊓ W i)) (hb i)).trans
      (hu i x hx))
  choose b hb using gl
  refine ⟨⟨b, fun j j' => fn_ext fun x hx => ?_⟩, fun i x hx => ?_⟩
  · obtain ⟨i, hi⟩ := hW x
    refine (gs_res (𝟙 X) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)
    rw [hb j i x hx.1 hi, hb j' i x hx.2 hi, ← _root_.mul_assoc, ← Units.val_mul,
      gm_cocycle hN (𝟙 X) x hx.1 hx.2 (hc i hi)]
  · show gs (𝟙 X) x _ (b (c i)) = _
    rw [hb (c i) i x (hc i hx) hx, gm_self hN (𝟙 X) x (hc i hx), Units.val_one, _root_.one_mul]

theorem gs_ne [IsIntegral Y] (r : Y ⟶ X) [IsIso r] (y : Y) {U : X.Opens} (hy : r y ∈ U) {a : Γ(X, U)} (ha : a ≠ 0) :
    gs r y U a ≠ 0 := by
  rw [gs_eq r y U hy]
  have h₁ : Function.Injective (r.app U).hom := (ConcreteCategory.bijective_of_isIso (r.app U)).1
  intro h
  apply ha
  apply h₁
  apply germ_injective_of_isIntegral Y y (show y ∈ r ⁻¹ᵁ U from hy)
  rw [map_zero, map_zero]
  exact h

theorem sec_ne [IsIntegral X] {N : LB X} (s : LB.Sec N) (hs : ∃ j, s.f j ≠ 0) {i : N.ι} {x : X} (hx : x ∈ N.U i) :
    s.f i ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (N.U j : Set X).Nonempty := by
    by_contra hn
    exact hj (fn_ext fun y hy => (hn ⟨y, hy⟩).elim)
  obtain ⟨y, hy, hyi, hyj⟩ := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _ (N.U i).isOpen
    (N.U j).isOpen ⟨x, trivial, hx⟩ (by simpa using hne)
  intro h0
  have e := sec_gs s (𝟙 X) y (i := j) (j := i) hyj hyi
  rw [h0, gs_eq (𝟙 X) y (N.U i) hyi, map_zero, map_zero, mul_zero] at e
  exact gs_ne (𝟙 X) y hyj hj e

theorem alg {R : Type} [CommRing R] (k : ℕ) {A B C D E F E' F' : Rˣ} {P Q P' Q' : R}
    (e₁ : P' = (A ^ k * C⁻¹).val * P) (e₂ : Q' = (B ^ k * D⁻¹).val * Q) (e₃ : E' = C * D * E)
    (e₄ : F' = B * A⁻¹ * F) :
    P' * Q' * (E' * (F' ^ k)⁻¹).val = (A ^ (2 * k)).val * (P * Q * (E * (F ^ k)⁻¹).val) := by
  subst e₁ e₂ e₃ e₄
  have : (A ^ k * C⁻¹) * (B ^ k * D⁻¹) * (C * D * E * ((B * A⁻¹ * F) ^ k)⁻¹) = A ^ (2 * k) * (E * (F ^ k)⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have := congrArg Units.val this
  simp only [Units.val_mul] at this ⊢
  linear_combination (P * Q) * this

theorem core [IsIntegral X] {L O : LB X} (hL : L.IsLB) (hO : O.IsLB) (σ z : X ⟶ X) [IsIso σ] (p₀ : O.ι)
    (hz : ∀ x, z x ∈ O.U p₀) (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1])) (hsy : sy.IsGen)
    (t : LB.Gen (LB.LinComb O (K := Fin 3) ![𝟙 X, σ, z] ![1, 1, -2])) (ht : t.IsGen) (k : ℕ)
    (s : LB.Sec (LB.div (pw L k) O)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (pw L (2 * k : ℕ)), ∃ j, s.f j ≠ 0 := by
  let W : (L.ι × L.ι) × (O.ι × O.ι) → X.Opens := fun i =>
    (L.U i.1.1 ⊓ O.U i.2.1) ⊓ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)
  have l₁ : ∀ i, W i ≤ LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.2.1, hx.1.1]
  have l₂ : ∀ i, W i ≤ LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.1.2, hx.2.2, hz x]
  obtain ⟨a, ha⟩ : ∃ a : ∀ i, Γ(X, W i), ∀ i x, x ∈ W i → gs (𝟙 X) x (W i) (a i) =
      gs (𝟙 X) x (L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) * gs σ x (L.U i.1.2 ⊓ O.U i.2.2) (s.f (i.1.2, i.2.2)) *
        (gm (𝟙 X) x (LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀]) (t.s ![i.2.1, i.2.2, p₀]) *
          ((gm (𝟙 X) x (LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1]) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val := by
    refine ⟨fun i => rs X (inf_le_left : W i ≤ L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) *
      rs X (inf_le_right : W i ≤ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)) ((σ.app (L.U i.1.2 ⊓ O.U i.2.2)).hom (s.f (i.1.2, i.2.2))) *
      (res (l₂ i) (t.s ![i.2.1, i.2.2, p₀]) * ((res (l₁ i) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val, fun i x hx => ?_⟩
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_res _ x _ hx _) ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 X) σ x _ hx.2 _).trans (by rw [Category.id_comp])))))
      ((gs_unit _ x _ hx _).trans (congrArg Units.val ?_)))
    rw [map_mul, map_inv, map_pow]
    exact congrArg₂ (· * ·) (gm_res _ x _ hx _) (congrArg (fun q => (q ^ k)⁻¹) (gm_res _ x _ hx _))
  have cov : ∀ x : X, ∃ i, x ∈ W i := fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL x
    obtain ⟨j', hj'⟩ := exists_chart hL (σ x)
    obtain ⟨p, hp⟩ := exists_chart hO x
    obtain ⟨q, hq⟩ := exists_chart hO (σ x)
    exact ⟨((j, j'), (p, q)), ⟨hj, hp⟩, ⟨hj', hq⟩⟩
  obtain ⟨s', hs'⟩ := glue (isLB_pw hL (2 * k : ℕ)) W (fun i => i.1.1) (fun i x hx => hx.1.1) cov a (by
    intro i i' x hx hx'
    have tr : ∀ (r : X ⟶ X) (p q : L.ι × O.ι), r x ∈ L.U p.1 ⊓ O.U p.2 → r x ∈ L.U q.1 ⊓ O.U q.2 →
        gs r x (L.U p.1 ⊓ O.U p.2) (s.f p) = (gm r x (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ k *
          (gm r x (O.U p.2 ⊓ O.U q.2) (O.g p.2 q.2))⁻¹).val * gs r x (L.U q.1 ⊓ O.U q.2) (s.f q) := by
      intro r p q hp hq
      refine (sec_gs s r x (i := p) (j := q) hp hq).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
      refine (gm_div O (pw L k) r x p q ⟨hp, hq⟩).trans (congrArg₂ (· * ·) ?_ rfl)
      exact (map_zpow _ _ _).trans (zpow_natCast _ _)
    have e₁ := tr (𝟙 X) (i.1.1, i.2.1) (i'.1.1, i'.2.1) hx.1 hx'.1
    have e₂ := tr σ (i.1.2, i.2.2) (i'.1.2, i'.2.2) hx.2 hx'.2
    have e₃ := gen_trans ht (𝟙 X) x (l₂ i hx) (l₂ i' hx')
    have e₄ := gen_trans hsy (𝟙 X) x (l₁ i hx) (l₁ i' hx')
    have f₃ : trF (L := O) ![𝟙 X, σ, z] ![1, 1, -2] (𝟙 X) x ![i.2.1, i.2.2, p₀] ![i'.2.1, i'.2.2, p₀] =
        gm (𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) * gm σ x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) := by
      rw [trF, Fin.prod_univ_three]
      show gm (𝟙 X ≫ 𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ σ) x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ z) x (O.U p₀ ⊓ O.U p₀) (O.g _ _) ^ (-2 : ℤ) = _
      rw [gm_self hO (𝟙 X ≫ z) x (hz x), one_zpow, _root_.mul_one, zpow_one, zpow_one, Category.id_comp,
        Category.id_comp]
    have f₄ : trF (L := L) ![σ, 𝟙 X] ![1, -1] (𝟙 X) x ![i.1.2, i.1.1] ![i'.1.2, i'.1.1] =
        gm σ x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) * (gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _))⁻¹ := by
      rw [trF, Fin.prod_univ_two]
      show gm (𝟙 X ≫ σ) x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ 𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (-1 : ℤ) = _
      rw [zpow_one, zpow_neg_one, Category.id_comp, Category.id_comp]
    have f₅ : gm (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1 ⊓ (pw L (2 * k : ℕ)).U i'.1.1) ((pw L (2 * k : ℕ)).g i.1.1 i'.1.1) =
        gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (2 * k) :=
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    rw [ha i x hx, ha i' x hx', f₅]
    exact alg k e₁ e₂ (e₃.trans (congrArg₂ (· * ·) f₃ rfl)) (e₄.trans (congrArg₂ (· * ·) f₄ rfl)))
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hi⟩ := cov x
  refine ⟨s', i.1.1, fun h0 => ?_⟩
  have e := (hs' i x hi).trans (ha i x hi)
  rw [h0, gs_eq (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1) hi.1.1, map_zero, map_zero] at e
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Units.ne_zero _) e.symm
  · exact gs_ne (𝟙 X) x hi.1 (sec_ne s hs (i := (i.1.1, i.2.1)) hi.1)
  · exact gs_ne σ x hi.2 (sec_ne s hs (i := (i.1.2, i.2.2)) hi.2)

theorem exists_sec_sq : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] (M : CP B) (k : ℕ) (O : LB B.left), O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → (∃ s : LB.Sec (LB.div (pw M.L.L k) O), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (pw M.L.L (2 * k : ℕ)), (∃ j, s.f j ≠ 0) := by
  intro A _ _ B _ _ _ M k O hO ⟨u, hu⟩ ⟨s, hs⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, ∀ y : Spec (CommRingCat.of A), eSec B y ∈ O.U p₀ := by
    obtain ⟨i, hi⟩ := exists_chart hO (eSec B (IsLocalRing.closedPoint A))
    exact ⟨i, fun y => ((IsLocalRing.specializes_closedPoint y).map (eSec B).continuous).mem_open (O.U i).isOpen hi⟩
  have hι : (𝟙 B : B ⟶ B)⁻¹ = ι[B] := by rw [Hom.inv_def, Category.id_comp]
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (𝟙 B) ι[B]).left ≫ (psum B (x2 B) I.down).left =
      (psum B ![𝟙 B, ι[B]] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift (𝟙 B) ι[B])) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  obtain ⟨t, ht, -⟩ := exists_gen hO (φ' := ![𝟙 B.left, (ι[B]).left, (1 : B ⟶ B).left]) (ε' := ![1, 1, -2])
    (fun V _ h => by
      have p := GlobalTheory.JetSer.prod_lam (𝟙 B) ι[B] h
      rw [← hι, mul_inv_cancel, hι] at p
      simp only [e, zpow_neg, Finset.prod_inv_distrib, p, Fin.prod_univ_three]
      show _ = h (𝟙 B.left) ^ (1 : ℤ) * h (ι[B]).left ^ (1 : ℤ) * h (1 : B ⟶ B).left ^ (-2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left]
      module)
    (LB.invGen O _ _ (LB.pullGen O (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) u (lift (𝟙 B) ι[B]).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  haveI : IsIso (ι[B]).left := inferInstanceAs (IsIso ((Over.forget _).map ι[B]))
  exact core M.L.isLB hO (ι[B]).left (1 : B ⟶ B).left p₀ (fun x => hp₀ (B.hom x))
    M.sym M.sym_gen t ht k s hs

end GlobalTheory.UU.SymSec
