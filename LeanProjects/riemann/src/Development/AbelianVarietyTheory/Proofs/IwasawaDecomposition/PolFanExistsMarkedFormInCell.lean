import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBilinFormAbsLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BilinFormExistsPrimitiveOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureSumIndecomposableFaceOfAdditiveStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan

namespace Mark

namespace Exist

section Cone

variable {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem apply_of_cone {c : Fin m → ℝ} {x : LinearMap.BilinForm ℤ X} (h : toReal x = ∑ i, c i • toReal (γ i)) (a b : X) :
    (x a b : ℝ) = ∑ i, c i * (γ i a b : ℝ) := by
  have e := congrArg (fun f : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => f a b) h
  simpa [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using e

theorem cone_zero : InRCone γ 0 := by
  refine ⟨0, fun _ => le_rfl, ?_⟩
  ext a b
  simp [toReal_apply]

private theorem toReal_eq_sum_smul_of_coe_eq_sum {x : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    (h : ∀ a b, (x a b : ℝ) = ∑ i, c i * (γ i a b : ℝ)) : toReal x = ∑ i, c i • toReal (γ i) := by
  ext a b
  simp [toReal_apply, LinearMap.sum_apply, h a b]

theorem cone_add {x y : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) (hy : InRCone γ y) : InRCone γ (x + y) := by
  obtain ⟨c, hc, h⟩ := hx
  obtain ⟨d, hd, h'⟩ := hy
  refine ⟨c + d, fun i => add_nonneg (hc i) (hd i), toReal_eq_sum_smul_of_coe_eq_sum fun a b => ?_⟩
  rw [LinearMap.add_apply, LinearMap.add_apply, Int.cast_add, apply_of_cone h a b, apply_of_cone h' a b,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [add_mul]

theorem cone_sum {S : Finset (LinearMap.BilinForm ℤ X)} (h : ∀ x ∈ S, InRCone γ x) : InRCone γ (∑ x ∈ S, x) := by
  classical
  revert h
  refine Finset.induction_on S (fun _ => by simpa using (cone_zero : InRCone γ 0)) ?_
  intro a S ha ih h
  rw [Finset.sum_insert ha]
  exact cone_add (h a (Finset.mem_insert_self a S)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private theorem toReal_eq_sum_smul_toReal_of_coe_eq {x : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    (h : ∀ a b, (x a b : ℝ) = ∑ i, c i * (γ i a b : ℝ)) : toReal x = ∑ i, c i • toReal (γ i) := by
  ext a b
  simp [toReal_apply, LinearMap.sum_apply, h a b]

theorem cone_smul_iff {g : ℕ} (hg : 0 < g) {x : LinearMap.BilinForm ℤ X} : InRCone γ ((g : ℤ) • x) ↔ InRCone γ x := by
  have hg' : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hv : ∀ a b, ((((g : ℤ) • x) a b : ℤ) : ℝ) = g * x a b := fun a b => by simp
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => c i / g, fun i => div_nonneg (hc i) (Nat.cast_nonneg g), toReal_eq_sum_smul_toReal_of_coe_eq fun a b => ?_⟩
    have e := apply_of_cone h a b
    rw [hv] at e
    have hs : ∑ i, c i / g * (γ i a b : ℝ) = (∑ i, c i * (γ i a b : ℝ)) / g := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs, ← e]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => g * c i, fun i => mul_nonneg (Nat.cast_nonneg g) (hc i), toReal_eq_sum_smul_toReal_of_coe_eq fun a b => ?_⟩
    rw [hv, apply_of_cone h a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem cone_nonneg (hγ : ∀ i y, 0 ≤ γ i y y) {x : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) (y : X) : 0 ≤ x y y := by
  obtain ⟨c, hc, h⟩ := hx
  have e := apply_of_cone h y y
  have hr : (0 : ℝ) ≤ x y y := by
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hγ i y)
  exact_mod_cast hr

theorem cone_vanish {x : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) {y : X} (hγ : ∀ i, γ i y y = 0) : x y y = 0 := by
  obtain ⟨c, hc, h⟩ := hx
  have e := apply_of_cone h y y
  have hr : (x y y : ℝ) = 0 := by
    rw [e]
    simp [hγ]
  exact_mod_cast hr

theorem cone_bal {O : Type} [CommRing O] {bar : O → O} [Module O X] (hγ : ∀ i, γ i ∈ balForms bar X)
    {x : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) : x ∈ balForms bar X := by
  obtain ⟨c, hc, h⟩ := hx
  rw [mem_balForms]
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · have hr : (x y z : ℝ) = x z y := by
      rw [apply_of_cone h y z, apply_of_cone h z y]
      exact Finset.sum_congr rfl fun i _ => by rw [(mem_balForms.1 (hγ i)).1 y z]
    exact_mod_cast hr
  · have hr : (x (a • y) z : ℝ) = x y (bar a • z) := by
      rw [apply_of_cone h (a • y) z, apply_of_cone h y (bar a • z)]
      exact Finset.sum_congr rfl fun i _ => by rw [(mem_balForms.1 (hγ i)).2 a y z]
    exact_mod_cast hr

theorem eq_zero_of_diag {x : LinearMap.BilinForm ℤ X} (hs : ∀ y z, x y z = x z y) (h : ∀ y, x y y = 0) : x = 0 := by
  refine LinearMap.ext₂ fun y z => ?_
  have e := h (y + z)
  simp only [map_add, LinearMap.add_apply, h y, h z, hs z y] at e
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  omega

end Cone

section Label

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ} {ψ lab : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]

theorem lab_le (hl : IsCarrierDim bar q ψ lab) (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ) {x : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) :
    lab.evalZ x ≤ genRank γ := by
  have hmem : genRank γ ∈ {k : ℕ | ∃ (n : ℕ) (τ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ τ ∧ InRCone τ x ∧
      genRank τ = k} := ⟨m, γ, hγ, hx, rfl⟩
  rw [hl X hX x (cone_bal hγ.mem hx) (cone_nonneg hγ.nonneg hx)]
  exact_mod_cast Nat.sInf_le hmem

theorem exists_min (hl : IsCarrierDim bar q ψ lab) (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ) {x : LinearMap.BilinForm ℤ X} (hx : InRCone γ x) :
    ∃ (n : ℕ) (τ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ τ ∧ InRCone τ x ∧ (genRank τ : ℝ) = lab.evalZ x := by
  have hS : {k : ℕ | ∃ (n : ℕ) (τ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ τ ∧ InRCone τ x ∧
      genRank τ = k}.Nonempty := ⟨genRank γ, ⟨m, γ, hγ, hx, rfl⟩⟩
  obtain ⟨n, τ, hτ, hxτ, hr⟩ := Nat.sInf_mem hS
  refine ⟨n, τ, hτ, hxτ, ?_⟩
  rw [hl X hX x (cone_bal hγ.mem hx) (cone_nonneg hγ.nonneg hx)]
  exact_mod_cast hr

omit [Module.Projective O X] in

theorem evalZ_zero' (φ : InvFun O) : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  have e := φ.eval_comp (X := X) (X₁ := Fin 0 → O) (r := 0) (fun _ => ⟨0, Subsingleton.elim _ _⟩)
    (fun _ _ => (0 : ℝ))
  rw [φ.eval_of_subsingleton (X := Fin 0 → O)] at e
  show φ.eval X (fun a b => (((0 : LinearMap.BilinForm ℤ X) a b : ℤ) : ℝ)) = 0
  simpa using e

omit [Module.Projective O X] in

theorem evalZ_sum {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : ψ.LinearOn γ)
    (S : Finset (LinearMap.BilinForm ℤ X)) (h : ∀ x ∈ S, InRCone γ x) :
    ψ.evalZ (∑ x ∈ S, x) = ∑ x ∈ S, ψ.evalZ x := by
  classical
  revert h
  refine Finset.induction_on S (fun _ => by simpa using evalZ_zero' (X := X) ψ) ?_
  intro a S ha ih h
  have ha' := h a (Finset.mem_insert_self a S)
  have hS' : ∀ x ∈ S, InRCone γ x := fun x hx => h x (Finset.mem_insert_of_mem hx)
  rw [Finset.sum_insert ha, Finset.sum_insert ha,
    evalZ_add_of_linearOn_inRCone O ψ X m γ hγ a _ ha' (cone_sum hS'), ih hS']

end Label

section Face

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {q : ℕ} {ψ lab : InvFun (𝓞 E)}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]

theorem inFace_iff (hψ : IsPolyFan H.bar q ψ) (hl : IsCarrierDim H.bar q ψ lab) (hX : Module.finrank (𝓞 E) X ≤ q)
    (hD : Dominates H.bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X} (hτ : IsCell H.bar ψ τ)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β) (x : LinearMap.BilinForm ℤ X) :
    InFace H.bar ψ lab β x ↔ InRCone τ x := by
  unfold InFace
  have hβb := cone_bal hτ.mem hβ
  have hβp := cone_nonneg hτ.nonneg hβ
  constructor
  · rintro ⟨hxb, hxp, -, hadd, hlab⟩
    exact GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField E H q ψ lab hψ hl X hX hD m τ hτ β hβb hβp hβ x hxb hxp hadd hlab
  · intro hx
    obtain ⟨c, hc, hcx⟩ := id hx
    have hbx := cone_add hβ hx
    refine ⟨cone_bal hτ.mem hx, cone_nonneg hτ.nonneg hx,
      fun y hy => cone_vanish hx fun j => GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal E H q ψ lab hψ hl X hX hD m τ hτ β hβb hβp hβ hr j y hy,
      evalZ_add_of_linearOn_inRCone (𝓞 E) ψ X m τ hτ.linear β x hβ hx, ?_⟩
    have hup : lab.evalZ (β + x) ≤ genRank τ := lab_le hl hX hτ hbx
    have e : toReal (β + x) = (1 : ℝ) • toReal β + ∑ k, c k • toReal (τ k) := by
      rw [one_smul, ← hcx]
      ext a b
      simp [toReal_apply]
    have hdown : lab.evalZ β ≤ lab.evalZ (β + x) :=
      carrierDim_le_of_add_cell (𝓞 E) H.bar q ψ lab hl X hX m τ hτ β hβb hβp (β + x) (cone_bal hτ.mem hbx)
        (cone_nonneg hτ.nonneg hbx) hβ 1 c one_pos hc e
    linarith

theorem isIndec_iff (hψ : IsPolyFan H.bar q ψ) (hl : IsCarrierDim H.bar q ψ lab) (hX : Module.finrank (𝓞 E) X ≤ q)
    (hD : Dominates H.bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X} (hτ : IsCell H.bar ψ τ)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β) (x : LinearMap.BilinForm ℤ X) :
    IsIndec H.bar ψ lab β x ↔
      InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x := by
  unfold IsIndec
  simp only [inFace_iff hψ hl hX hD hτ hβ hr]

end Face

end Exist

open _root_.GlobalTheory.PolFan.Mark.Exist in

theorem exists_isMarked_inRCone (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)) (i : ℕ)
    (hDom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X)
    (hψ : IsPolyFan H.bar q ψ) (hl : IsCarrierDim H.bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X) (hv : IsCell H.bar ψ v)
    (β : LinearMap.BilinForm ℤ X) (hb : β ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ β y y) (hvβ : InRCone v β)
    (hlab : lab.evalZ β = ((i + 1 : ℕ) : ℝ)) :
    ∃ β₀ : LinearMap.BilinForm ℤ X, IsMarked H.bar ψ lab i X β₀ ∧ InRCone v β₀ := by
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hD := hDom X
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [evalZ_zero'] at hlab
    have : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    linarith
  obtain ⟨n, τ, hτ, hβτ, hrk⟩ := exists_min hl hX hv hvβ
  have hr : (genRank τ : ℝ) ≤ lab.evalZ β := hrk.le
  obtain ⟨S, hSmem⟩ : ∃ S : Finset (LinearMap.BilinForm ℤ X), ∀ x, x ∈ S ↔
      InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x :=
    ⟨(finite_indec_inRCone X n τ).toFinset, fun x => Set.Finite.mem_toFinset _⟩
  have hScone : ∀ x ∈ S, InRCone τ x := fun x hx => ((hSmem x).1 hx).1
  have hστ : InRCone τ (∑ x ∈ S, x) := cone_sum hScone
  have F := fun x => inFace_iff hψ hl hX hD hτ hβτ hr x
  have hcl : β ∈ AddSubmonoid.closure {y | IsIndec H.bar ψ lab β y} := by
    refine GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive (𝓞 E) H.bar ψ lab X β ?_ ?_ ?_ β ((F β).2 hβτ)
    · intro x y hx hy
      exact ⟨(F _).2 (cone_add ((F x).1 hx) ((F y).1 hy)),
        evalZ_add_of_linearOn_inRCone (𝓞 E) ψ X n τ hτ.linear x y ((F x).1 hx) ((F y).1 hy)⟩
    · intro x hx
      have hx' := (F x).1 hx
      exact (hψ X hX).integral x (cone_bal hτ.mem hx') (cone_nonneg hτ.nonneg hx')
    · intro x hx hx0
      have hx' := (F x).1 hx
      exact (hψ X hX).pos x (cone_bal hτ.mem hx') (cone_nonneg hτ.nonneg hx') hx0
  have key : ∀ z, z ∈ AddSubmonoid.closure {y | IsIndec H.bar ψ lab β y} →
      ∃ (N : ℕ) (w : LinearMap.BilinForm ℤ X), InRCone τ w ∧ N • (∑ x ∈ S, x) = z + w := by
    intro z hz
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz =>
      have hzS : z ∈ S := (hSmem z).2 ((isIndec_iff hψ hl hX hD hτ hβτ hr z).1 hz)
      refine ⟨1, ∑ x ∈ S.erase z, x, cone_sum fun x hx => hScone x (Finset.mem_of_mem_erase hx), ?_⟩
      rw [one_smul]
      exact (Finset.add_sum_erase S (fun x => x) hzS).symm
    | zero => exact ⟨0, 0, cone_zero, by simp⟩
    | add z z' _ _ ih ih' =>
      obtain ⟨N, w, hw, e⟩ := ih
      obtain ⟨N', w', hw', e'⟩ := ih'
      refine ⟨N + N', w + w', cone_add hw hw', ?_⟩
      rw [add_smul, e, e']
      abel
  obtain ⟨N, w, hw, hNw⟩ := key β hcl
  have hN : (N + 1) • (∑ x ∈ S, x) = β + (w + ∑ x ∈ S, x) := by
    rw [add_smul, one_smul, hNw, add_assoc]
  have hww : InRCone τ (w + ∑ x ∈ S, x) := cone_add hw hστ
  have hσ0 : (∑ x ∈ S, x) ≠ 0 := by
    intro h0
    rw [h0, smul_zero, add_zero] at hN
    apply hβ0
    refine eq_zero_of_diag (mem_balForms.1 hb).1 fun y => le_antisymm ?_ (hp y)
    have h1 := congrArg (fun f : LinearMap.BilinForm ℤ X => f y y) hN
    have h2 := cone_nonneg hτ.nonneg hw y
    simp only [LinearMap.add_apply, LinearMap.zero_apply] at h1
    linarith
  obtain ⟨g, β₀, hg, hgβ, hprim⟩ := GlobalTheory.bilinForm_exists_primitive_of_ne_zero X _ hσ0
  have hβ₀τ : InRCone τ β₀ := (cone_smul_iff hg).1 (by rw [hgβ]; exact hστ)
  have hβ₀b := cone_bal hτ.mem hβ₀τ
  have hβ₀p := cone_nonneg hτ.nonneg hβ₀τ
  have hle : lab.evalZ β₀ ≤ genRank τ := lab_le hl hX hτ hβ₀τ
  have hge : lab.evalZ β ≤ lab.evalZ β₀ := by
    obtain ⟨c, hc, hcw⟩ := hww
    have hM : (0 : ℝ) < ((N : ℝ) + 1) * g := by positivity
    refine carrierDim_le_of_add_cell (𝓞 E) H.bar q ψ lab hl X hX n τ hτ β hb hp β₀ hβ₀b hβ₀p hβτ
      (1 / (((N : ℝ) + 1) * g)) (fun k => c k / (((N : ℝ) + 1) * g)) (by positivity)
      (fun k => div_nonneg (hc k) hM.le) ?_
    ext a b
    have e1 := congrArg (fun f : LinearMap.BilinForm ℤ X => f a b) hN
    have e3 := congrArg (fun f : LinearMap.BilinForm ℤ X => f a b) hgβ
    have e2 := apply_of_cone hcw a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul] at e1 e3
    simp only [LinearMap.add_apply, Int.cast_add] at e2
    have e1' : ((N : ℝ) + 1) * ((∑ x ∈ S, x) a b : ℤ) = (β a b : ℝ) + ((w a b : ℝ) + ((∑ x ∈ S, x) a b : ℤ)) := by
      exact_mod_cast e1
    have e3' : (g : ℝ) * (β₀ a b : ℝ) = (((∑ x ∈ S, x) a b : ℤ) : ℝ) := by exact_mod_cast e3
    have hs : ∑ k, c k / (((N : ℝ) + 1) * g) * (τ k a b : ℝ) = (∑ k, c k * (τ k a b : ℝ)) / (((N : ℝ) + 1) * g) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [toReal_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      smul_eq_mul]
    have hMne : ((N : ℝ) + 1) * g ≠ 0 := hM.ne'
    have hb0 : (β₀ a b : ℝ) = ((β a b : ℝ) + ((w a b : ℝ) + (((∑ x ∈ S, x) a b : ℤ) : ℝ))) / (((N : ℝ) + 1) * g) := by
      rw [eq_div_iff hMne]
      linear_combination ((N : ℝ) + 1) * e3' + e1'
    rw [hs, ← e2, hb0]
    ring
  have hlab0 : lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) := by linarith
  have hr0 : (genRank τ : ℝ) ≤ lab.evalZ β₀ := by linarith
  have hface := (F β₀).2 hβ₀τ
  unfold InFace at hface
  obtain ⟨-, -, -, hadd, hlabeq⟩ := hface
  have hv₀ : InRCone v β₀ := GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField E H q ψ lab hψ hl X hX hD m v hv β hb hp hvβ β₀ hβ₀b hβ₀p hadd hlabeq
  refine ⟨β₀, ?_, hv₀⟩
  unfold IsMarked
  refine ⟨hβ₀b, hβ₀p, hprim, hlab0, S, fun x => ?_, g, hg, hgβ⟩
  rw [hSmem x, isIndec_iff hψ hl hX hD hτ hβ₀τ hr0 x]

end Mark

end GlobalTheory.PolFan
