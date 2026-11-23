import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsArch

theorem eq_of_norm_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {W : (Fin g → ℂ) → ℂ} (hW : Differentiable ℂ W)
    (hp : ∀ l ∈ Λ, ∀ z, ‖W (z + l)‖ = ‖W z‖) (z w : Fin g → ℂ) : W z = W w := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : b → Fin g → ℂ)) := by
    rw [Subtype.range_coe, hspan, hf]
  let B : Module.Basis b ℝ (Fin g → ℂ) := Module.Basis.mk hli hsp
  haveI : Finite b := Module.Finite.finite_basis B
  haveI : Fintype b := Fintype.ofFinite b
  have hmem : ∀ x ∈ Submodule.span ℤ (Set.range B), x ∈ Λ := by
    intro x hx
    refine (Submodule.span_le (p := Λ)).2 ?_ hx
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.mk_apply]
    exact hb i.2
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).isCompact_closure.exists_bound_of_continuousOn
    (f := W) hW.continuous.continuousOn
  refine hW.apply_eq_apply_of_bounded ?_ z w
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x = ZSpan.fract B x + (ZSpan.floor B x : Fin g → ℂ) := by
    rw [ZSpan.fract_apply]; abel
  rw [hx, hp _ (hmem _ (ZSpan.floor B x).2)]
  exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain B x))

section Val

variable {X Y : Scheme.{0}}

def c0 : Sp ℂ := (default : PrimeSpectrum ℂ)

theorem top_le_iff_pt (x : Sp ℂ ⟶ X) (V : X.Opens) : ⊤ ≤ x ⁻¹ᵁ V ↔ x c0 ∈ V :=
  ⟨fun h => h (show c0 ∈ (⊤ : (Sp ℂ).Opens) from trivial), fun h p _ => by
    have : p = c0 := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this; exact h⟩

def ev (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valF x U f = ev x U h f :=
  dif_pos h

theorem valAt'_eq (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f = ev x U h f :=
  dif_pos h

theorem ev_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ev x V h ((X.presheaf.map (homOfLE hVU).op).hom f) = ev x U h' f :=
  congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (t.hom f)) (x.map_appLE h (homOfLE hVU).op)

theorem ev_pull (x : Sp ℂ ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ F ⁻¹ᵁ U) (h' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev x (F ⁻¹ᵁ U) h ((F.app U).hom f) = ev (x ≫ F) U h' f :=
  (congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (t.hom f)) (Scheme.Hom.comp_appLE x F U ⊤ h')).symm

theorem valF_unit_ne (x : Sp ℂ ⟶ X) {U : X.Opens} (t : Γ(X, U)ˣ) (h : x c0 ∈ U) : valF x U t.val ≠ 0 := by
  rw [valF_eq x U ((top_le_iff_pt x U).2 h)]
  exact (t.isUnit.map (ev x U _)).ne_zero

theorem valF_g_linComb (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (x : Sp ℂ ⟶ Y)
    (j j' : K → L.ι) (h : x c0 ∈ LB.wchart L φ j) (h' : x c0 ∈ LB.wchart L φ j') :
    valF x (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valF (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  have h0 : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := (top_le_iff_pt x _).2 ⟨h, h'⟩
  refine (valF_eq x _ h0 _).trans ?_
  show (Units.map (ev x _ h0).toMonoidHom (∏ k, _)).val = _
  rw [map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  congr 1
  have hk : (x ≫ φ k) c0 ∈ L.U (j k) ⊓ L.U (j' k) :=
    ⟨Set.mem_iInter.1 h k, Set.mem_iInter.1 h' k⟩
  have hk' : ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := (top_le_iff_pt _ _).2 hk
  rw [valF_eq _ _ hk']
  have hk2 : ⊤ ≤ x ⁻¹ᵁ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := (top_le_iff_pt x _).2 hk
  exact (ev_res x _ h0 hk2 _).trans (ev_pull x (φ k) _ hk2 hk' _)

theorem valF_gen {M : LB X} (t : LB.Gen M) (ht : t.IsGen) (x : Sp ℂ ⟶ X) (i j : M.ι) (hi : x c0 ∈ M.U i)
    (hj : x c0 ∈ M.U j) :
    valF x (M.U i) (t.s i).val = valF x (M.U i ⊓ M.U j) (M.g i j).val * valF x (M.U j) (t.s j).val := by
  have h0 : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ M.U j) := (top_le_iff_pt x _).2 ⟨hi, hj⟩
  have h1 := (top_le_iff_pt x _).2 hi
  have h2 := (top_le_iff_pt x _).2 hj
  have e := congrArg (fun u => ev x _ h0 (Units.val u)) (ht i j)
  simp only [Units.val_mul, map_mul] at e
  rw [valF_eq x _ h1, valF_eq x _ h2, valF_eq x _ h0]
  exact (ev_res x _ h0 h1 _).symm.trans (e.trans (congrArg (_ * ·) (ev_res x _ h0 h2 _)))

end Val

section Frame

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}
  (a : ArchFrame P z g)

abbrev fi (i : P.L.ι) (w : Fin g → ℂ) : ℂ := a.u.fr (fun _ => i) w

theorem left_pow {T : Over S} (x : T ⟶ G) (N : ℕ) : x.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (x ^ N).left := by
  have e : x ≫ (𝟙 G : G ⟶ G) ^ N = x ^ N := (map_pow (preHom x) (𝟙 G) N).trans (by simp [preHom])
  exact congrArg (fun t => t.left) e

theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := rfl

theorem ex_zero : a.u.ex 0 = 1 := (a.u.ker 0).2 (zero_mem _)

theorem ex_nsmul (N : ℕ) (w : Fin g → ℂ) : a.u.ex (N • w) = a.u.ex w ^ N := by
  induction N with
  | zero => simpa using ex_zero a
  | succ k ih => rw [succ_nsmul, a.u.ex_add, ih, pow_succ]

theorem pt_eq_push (w : Fin g → ℂ) :
    a.pt w = (pushHom a.cart (𝟙_ (Over (Sp ℂ))) (a.u.ex w)).left := rfl

theorem pt_nsmul (N : ℕ) (w : Fin g → ℂ) : a.pt (N • w) = a.pt w ≫ ((𝟙 G : G ⟶ G) ^ N).left := by
  rw [pt_eq_push, pt_eq_push, left_pow, ex_nsmul, map_pow]

theorem pt_add_lat (w : Fin g → ℂ) {l : Fin g → ℂ} (hl : l ∈ a.u.Λ) : a.pt (w + l) = a.pt w := by
  rw [ArchFrame.pt, ArchFrame.pt, a.u.ex_add, (a.u.ker l).2 hl, _root_.mul_one]

theorem pt_zero : a.pt 0 = (1 : Over.mk z ⟶ G).left := by
  rw [pt_eq_push, ex_zero, map_one, one_left, one_left]
  simp

theorem mem_lat_of_tors (y : Over.mk z ⟶ G) (w : Fin g → ℂ) (N : ℕ) (hy : y.left = a.pt w) (hN : y ^ N = 1) :
    N • w ∈ a.u.Λ := by
  refine (a.u.ker _).1 (Over.OverMorphism.ext (a.cart.1.hom_ext ?_ ?_))
  · have e1 : (a.u.ex (N • w)).left ≫ a.φ = a.pt (N • w) := rfl
    have e2 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ a.A).left ≫ a.φ = a.pt 0 := by
      rw [ArchFrame.pt, ex_zero]
    rw [e1, e2, pt_nsmul, ← hy, left_pow, hN, pt_zero]
  · rw [Over.w, Over.w]

theorem top_pull {i : P.L.ι} {w : Fin g → ℂ} (h : a.pt w c0 ∈ P.L.U i) :
    ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i) :=
  (top_le_iff_pt (X := a.A.left) (a.u.ex w).left _).2 (Set.mem_iInter.2 fun _ => h)

theorem exists_chart (x : Sp ℂ ⟶ G.left) : ∃ i, x c0 ∈ P.L.U i := by
  have h : x c0 ∈ ⨆ i, P.L.U i := by rw [P.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem fi_ne {i : P.L.ι} {w : Fin g → ℂ} (h : a.pt w c0 ∈ P.L.U i) : fi a i w ≠ 0 :=
  a.u.fr_ne _ _ (top_pull a h)

theorem fi_compat {i i' : P.L.ι} {w : Fin g → ℂ} (h : a.pt w c0 ∈ P.L.U i) (h' : a.pt w c0 ∈ P.L.U i') :
    fi a i w = valF (a.pt w) (P.L.U i ⊓ P.L.U i') (P.L.g i i').val * fi a i' w := by
  have h0 : ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ ((P.L.pull a.φ).U (fun _ => i) ⊓ (P.L.pull a.φ).U (fun _ => i')) :=
    (top_le_iff_pt (X := a.A.left) (a.u.ex w).left _).2
      ⟨Set.mem_iInter.2 fun _ => h, Set.mem_iInter.2 fun _ => h'⟩
  refine (a.u.fr_compat (fun _ => i) (fun _ => i') w h0).trans (congrArg (· * _) ?_)
  refine (valAt'_eq (X := a.A.left) (a.u.ex w).left _ h0 _).trans ?_
  refine (valF_eq (X := a.A.left) (a.u.ex w).left _ h0 _).symm.trans ?_
  refine (valF_g_linComb P.L (K := PUnit) (fun _ => a.φ) (fun _ => 1) (a.u.ex w).left (fun _ => i) (fun _ => i')
    (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h')).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem norm_fi {i : P.L.ι} {w : Fin g → ℂ} (h : a.pt w c0 ∈ P.L.U i) (l : a.u.Λ) :
    ‖fi a i w‖ = Real.exp (Real.pi * (a.herm w l).re + Real.pi / 2 * (a.herm l l).re) * ‖fi a i (w + l)‖ := by
  obtain ⟨-, -, hχ, hAH⟩ := a.ah
  have e := hAH l (fun _ => i) w (top_pull a h)
  rw [fi, e, norm_mul, norm_mul, hχ, _root_.one_mul, Complex.norm_exp]
  congr 2
  simp [ArchFrame.herm, Complex.add_re, Complex.mul_re]

theorem alg_indep {A B gN gj F F' u u' : ℂ} {m : ℕ} (hgN : gN ≠ 0) (hgj : gj ≠ 0) (hF' : F' ≠ 0)
    (hA : A = gN * (gj ^ m)⁻¹ * B) (hF : F = gN * F') (hu : u = gj * u') : A * u ^ m / F = B * u' ^ m / F' := by
  subst hA hF hu
  rw [mul_pow]
  field_simp

theorem dualNumber_unit_mul_decomposition {T A0 r Aw q F ϑ : ℂ} {m n : ℕ} (hr : r ≠ 0) (hq : q ≠ 0) (hF : F ≠ 0) (hA0 : A0 ≠ 0)
    (hE : T * (A0 * r ^ m) ^ n = (ϑ * q ^ n) ^ m * Aw ^ n) (hc : Aw * q ^ m / F = A0 * r ^ m / r) :
    T * r ^ n = ϑ ^ m * F ^ n := by
  have hc0 : A0 * r ^ m / r ≠ 0 := div_ne_zero (mul_ne_zero hA0 (pow_ne_zero _ hr)) hr
  generalize hcdef : A0 * r ^ m / r = c at hc hc0
  have h1 : A0 * r ^ m = c * r := by rw [← hcdef]; field_simp
  have h2 : Aw * q ^ m = c * F := by rw [div_eq_iff hF] at hc; exact hc
  have h3 : (ϑ * q ^ n) ^ m * Aw ^ n = ϑ ^ m * (Aw * q ^ m) ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm n m]; ring
  rw [h1, h3, h2, mul_pow, mul_pow] at hE
  apply mul_left_cancel₀ (pow_ne_zero n hc0)
  linear_combination hE

abbrev GenN (P : RigLB G) (N : ℕ) :=
  LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])

variable {N : ℕ}

def R (t : GenN P N) (i j : P.L.ι) (v : Fin g → ℂ) : ℂ :=
  valF (a.pt v) _ (t.s ![i, j]).val * fi a j v ^ (N ^ 2) / fi a i (N • v)

theorem mem_wc {i j : P.L.ι} {v : Fin g → ℂ} (hi : a.pt (N • v) c0 ∈ P.L.U i) (hj : a.pt v c0 ∈ P.L.U j) :
    a.pt v c0 ∈ LB.wchart P.L ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![i, j] := by
  rw [pt_nsmul] at hi
  refine Set.mem_iInter.2 fun k => ?_
  fin_cases k
  · exact hi
  · exact hj

theorem R_indep (t : GenN P N) (ht : t.IsGen) {i j i' j' : P.L.ι} {v : Fin g → ℂ}
    (hi : a.pt (N • v) c0 ∈ P.L.U i) (hj : a.pt v c0 ∈ P.L.U j)
    (hi' : a.pt (N • v) c0 ∈ P.L.U i') (hj' : a.pt v c0 ∈ P.L.U j') : R a t i j v = R a t i' j' v := by
  have hc := mem_wc a hi hj
  have hc' := mem_wc a hi' hj'
  have e2 : valF (a.pt v) (LB.wchart P.L ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![i, j] ⊓
        LB.wchart P.L ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![i', j'])
        ((LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left]
          ![1, -((N : ℤ) ^ 2)]).g ![i, j] ![i', j']).val =
      valF (a.pt (N • v)) (P.L.U i ⊓ P.L.U i') (P.L.g i i').val *
        (valF (a.pt v) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val ^ (N ^ 2))⁻¹ := by
    refine (valF_g_linComb P.L _ _ (a.pt v) ![i, j] ![i', j'] hc hc').trans ?_
    rw [Fin.prod_univ_two, pt_nsmul]
    change valF (a.pt v ≫ ((𝟙 G : G ⟶ G) ^ N).left) (P.L.U i ⊓ P.L.U i') (P.L.g i i').val ^ (1 : ℤ) *
      valF (a.pt v ≫ 𝟙 G.left) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val ^ (-((N : ℤ) ^ 2)) = _
    rw [zpow_one, Category.comp_id, zpow_neg]
    congr 2
  have e1 := (valF_gen t ht (a.pt v) ![i, j] ![i', j'] hc hc').trans (congrArg (· * _) e2)
  exact alg_indep (valF_unit_ne (a.pt (N • v)) (P.L.g i i') ⟨hi, hi'⟩)
    (valF_unit_ne (a.pt v) (P.L.g j j') ⟨hj, hj'⟩) (fi_ne a hi') e1
    (fi_compat a hi hi') (fi_compat a hj hj')

def Wf (t : GenN P N) (v : Fin g → ℂ) : ℂ :=
  R a t (exists_chart (P := P) (a.pt (N • v))).choose (exists_chart (P := P) (a.pt v)).choose v

theorem Wf_eq (t : GenN P N) (ht : t.IsGen) {i j : P.L.ι} {v : Fin g → ℂ}
    (hi : a.pt (N • v) c0 ∈ P.L.U i) (hj : a.pt v c0 ∈ P.L.U j) : Wf a t v = R a t i j v :=
  R_indep a t ht (exists_chart (P := P) _).choose_spec (exists_chart (P := P) _).choose_spec hi hj

theorem isOpen_chart (V : G.left.Opens) : IsOpen {v | a.pt v c0 ∈ V} := by
  have e : {v | a.pt v c0 ∈ V} = {z | ⊤ ≤ (a.u.ex z).left ⁻¹ᵁ a.φ ⁻¹ᵁ V} :=
    Set.ext fun v => (top_le_iff_pt (X := a.A.left) (a.u.ex v).left (a.φ ⁻¹ᵁ V)).symm
  rw [e]
  exact (a.u.hol (a.φ ⁻¹ᵁ V) 0).1

theorem diffAt_val (V : G.left.Opens) (f : Γ(G.left, V)) {v₀ : Fin g → ℂ} (h : a.pt v₀ c0 ∈ V) :
    DifferentiableAt ℂ (fun v => valF (a.pt v) V f) v₀ := by
  have hh := a.u.hol (a.φ ⁻¹ᵁ V) ((a.φ.app V).hom f)
  have hv : ∀ v, a.pt v c0 ∈ V → ⊤ ≤ (a.u.ex v).left ⁻¹ᵁ a.φ ⁻¹ᵁ V := fun v hv =>
    (top_le_iff_pt (X := a.A.left) (a.u.ex v).left _).2 hv
  have hmem := hh.1.mem_nhds (hv _ h)
  refine (hh.2.differentiableAt hmem).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_chart a V).mem_nhds h] with v hvV
  have t0 : ⊤ ≤ a.pt v ⁻¹ᵁ V := (top_le_iff_pt _ _).2 hvV
  rw [valF_eq _ _ t0, valAt'_eq (X := a.A.left) _ _ (hv v hvV)]
  exact (ev_pull (Y := a.A.left) (a.u.ex v).left a.φ V _ t0 f).symm

theorem diffAt_fi {i : P.L.ι} {v₀ : Fin g → ℂ} (h : a.pt v₀ c0 ∈ P.L.U i) : DifferentiableAt ℂ (fi a i) v₀ := by
  have O : IsOpen {z | ⊤ ≤ (a.u.ex z).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i)} := (a.u.hol _ 0).1
  exact (a.u.fr_hol _).differentiableAt (O.mem_nhds (top_pull a h))

theorem Wf_diff (t : GenN P N) (ht : t.IsGen) : Differentiable ℂ (Wf a t) := by
  intro v₀
  obtain ⟨i, hi⟩ := exists_chart (P := P) (a.pt (N • v₀))
  obtain ⟨j, hj⟩ := exists_chart (P := P) (a.pt v₀)
  have hc := mem_wc a hi hj
  have d1 := diffAt_val a _ (t.s ![i, j]).val hc
  have d2 := diffAt_fi a hj
  have hsm : DifferentiableAt ℂ (fun v : Fin g → ℂ => N • v) v₀ := differentiableAt_id.const_smul N
  have d3 : DifferentiableAt ℂ (fun v => fi a i (N • v)) v₀ :=
    DifferentiableAt.comp v₀ (diffAt_fi a hi) hsm
  have d : DifferentiableAt ℂ (R a t i j) v₀ := by
    show DifferentiableAt ℂ (fun v => R a t i j v) v₀
    simp only [R, div_eq_mul_inv]
    exact (d1.fun_mul (d2.fun_pow (N ^ 2))).fun_mul (d3.fun_inv (fi_ne a hi))
  refine d.congr_of_eventuallyEq ?_
  have o1 : IsOpen {v : Fin g → ℂ | a.pt (N • v) c0 ∈ P.L.U i} :=
    (isOpen_chart a (P.L.U i)).preimage (continuous_const_smul N)
  filter_upwards [o1.mem_nhds hi, (isOpen_chart a _).mem_nhds hj] with v h1 h2
  exact Wf_eq a t ht h1 h2

theorem herm_nsmul (M : ℕ) (v l : Fin g → ℂ) : a.herm (M • v) (M • l) = (M : ℂ) ^ 2 * a.herm v l := by
  rw [← Nat.cast_smul_eq_nsmul ℂ M v, ← Nat.cast_smul_eq_nsmul ℂ M l]
  simp [ArchFrame.herm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  ring

theorem herm_nsmul_re (M : ℕ) (v l : Fin g → ℂ) : (a.herm (M • v) (M • l)).re = (M : ℝ) ^ 2 * (a.herm v l).re := by
  rw [herm_nsmul, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem Wf_per (t : GenN P N) (ht : t.IsGen) {l : Fin g → ℂ} (hl : l ∈ a.u.Λ) (v : Fin g → ℂ) :
    ‖Wf a t (v + l)‖ = ‖Wf a t v‖ := by
  obtain ⟨i, hi⟩ := exists_chart (P := P) (a.pt (N • v))
  obtain ⟨j, hj⟩ := exists_chart (P := P) (a.pt v)
  have hNl : N • l ∈ a.u.Λ := a.u.Λ.toAddSubmonoid.nsmul_mem hl N
  have hp : a.pt (v + l) = a.pt v := pt_add_lat a v hl
  have hnv : N • (v + l) = N • v + N • l := smul_add _ _ _
  have hpN : a.pt (N • (v + l)) = a.pt (N • v) := by rw [hnv, pt_add_lat a _ hNl]
  have hi' : a.pt (N • (v + l)) c0 ∈ P.L.U i := by rw [hpN]; exact hi
  have hj' : a.pt (v + l) c0 ∈ P.L.U j := by rw [hp]; exact hj
  rw [Wf_eq a t ht hi' hj', Wf_eq a t ht hi hj]
  have n1 := norm_fi a hj ⟨l, hl⟩
  have n2 := norm_fi a hi ⟨N • l, hNl⟩
  simp only [] at n1 n2
  rw [← hnv, herm_nsmul_re, herm_nsmul_re] at n2
  have hexp : Real.exp (Real.pi * ((N : ℝ) ^ 2 * (a.herm v l).re) +
      Real.pi / 2 * ((N : ℝ) ^ 2 * (a.herm l l).re)) =
      Real.exp (Real.pi * (a.herm v l).re + Real.pi / 2 * (a.herm l l).re) ^ (N ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at n2
  have hF : ‖fi a i (N • (v + l))‖ ≠ 0 := norm_ne_zero_iff.2 (fi_ne a hi')
  have he := (Real.exp_pos (Real.pi * (a.herm v l).re + Real.pi / 2 * (a.herm l l).re)).ne'
  simp only [R, norm_div, norm_mul, norm_pow]
  rw [hp, n1, n2, mul_pow]
  field_simp

theorem norm_of_torsVal {n : ℕ} (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) (y : Over.mk z ⟶ G) (w : Fin g → ℂ)
    (N : ℕ) (T : ℂ) (hθ : a.IsFn s θ) (hy : y.left = a.pt w) (hT : TorsVal P s y N T) :
    ‖T‖ = a.nrm n θ w ^ (N ^ 2) := by
  obtain ⟨-, hN, t, i₀, i, ht, h0, hi, hE⟩ := hT
  rw [← pt_zero a] at hE h0
  rw [hy] at hE hi
  have h0' : a.pt 0 c0 ∈ P.L.U i₀ := (top_le_iff_pt _ _).1 h0
  have hi' : a.pt w c0 ∈ P.L.U i := (top_le_iff_pt _ _).1 hi
  have hl := mem_lat_of_tors a y w N hy hN
  have hptl : a.pt (N • w) = a.pt 0 := by
    have e := pt_add_lat a 0 hl
    rwa [zero_add] at e
  have hN0 : a.pt (N • (0 : Fin g → ℂ)) c0 ∈ P.L.U i₀ := by rw [smul_zero]; exact h0'
  have hNw : a.pt (N • w) c0 ∈ P.L.U i₀ := by rw [hptl]; exact h0'
  have hW : Wf a t w = Wf a t 0 :=
    eq_of_norm_periodic a.u.Λ a.u.full (Wf_diff a t ht) (fun l hl v => Wf_per a t ht hl v) w 0
  rw [Wf_eq a t ht hNw hi', Wf_eq a t ht hN0 h0'] at hW
  simp only [R] at hW
  rw [smul_zero] at hW
  have hrig := a.rig i₀ h0
  rw [← hrig] at hE
  rw [hθ i w hi] at hE
  have key := dualNumber_unit_mul_decomposition (fi_ne a h0') (fi_ne a hi') (fi_ne a hNw)
    (valF_unit_ne (a.pt 0) (t.s ![i₀, i₀]) (mem_wc a hN0 h0')) hE hW
  have hn := congrArg norm key
  simp only [norm_mul, norm_pow] at hn
  have hr := norm_fi a h0' ⟨N • w, hl⟩
  simp only [zero_add] at hr
  rw [herm_nsmul_re] at hr
  have h00 : (a.herm 0 (N • w)).re = 0 := by simp [ArchFrame.herm]
  rw [h00] at hr
  simp only [mul_zero, zero_add] at hr
  have hF : ‖fi a i₀ (N • w)‖ ≠ 0 := norm_ne_zero_iff.2 (fi_ne a hNw)
  rw [hr, mul_pow] at hn
  have hn' : ‖T‖ * Real.exp (Real.pi / 2 * ((N : ℝ) ^ 2 * (a.herm w w).re)) ^ n = ‖θ w‖ ^ (N ^ 2) :=
    mul_right_cancel₀ (pow_ne_zero n hF) (by rw [_root_.mul_assoc]; exact hn)
  rw [ArchFrame.nrm, mul_pow, ← hn', _root_.mul_assoc, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  have e0 : (n : ℝ) * (Real.pi / 2 * ((N : ℝ) ^ 2 * (a.herm w w).re)) +
      ((N ^ 2 : ℕ) : ℝ) * (-(Real.pi * n / 2) * (a.herm w w).re) = 0 := by
    push_cast
    ring
  rw [e0, Real.exp_zero, _root_.mul_one]

end Frame

theorem torsVal_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (n : ℕ) (s : Out.H0 D.t.PP.L n) (θ : (Fin D.g → ℂ) → ℂ) (y : Over.mk (emb σ) ⟶ D.t.G) (w : Fin D.g → ℂ) (N : ℕ) (T : ℂ), a.IsFn s θ → y.left = a.pt w → TorsVal D.t.PP s y N T → ‖T‖ = a.nrm n θ w ^ (N ^ 2) := by
  intro E _ _ _ H L _ _ D σ a n s θ y w N T h1 h2 h3
  exact norm_of_torsVal a s θ y w N T h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.Sl.TorsArch
