import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagTie

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

def Lower (g : Mat m K) : Prop := ∀ τ (i k : Fin (m τ)), i < k → g τ i k = 0

theorem lower_iff_blockTriangular (g : Mat m K) (τ : ι) :
    (∀ i k : Fin (m τ), i < k → g τ i k = 0) ↔ (g τ).BlockTriangular OrderDual.toDual :=
  ⟨fun h _ _ hik => h _ _ hik, fun h _ _ hik => h hik⟩

theorem Lower.mul {g h : Mat m K} (hg : Lower g) (hh : Lower h) : Lower (g * h) := fun τ =>
  (lower_iff_blockTriangular (g * h) τ).2
    (((lower_iff_blockTriangular g τ).1 (hg τ)).mul ((lower_iff_blockTriangular h τ).1 (hh τ)))

theorem Lower.inv {g : Mat m K} (hg : Lower g) : Lower g⁻¹ := fun τ => by
  by_cases hd : (g τ).det = 0
  · intro i k _
    show (g τ)⁻¹ i k = 0
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hd])]
    rfl
  · have := (g τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    exact (lower_iff_blockTriangular g⁻¹ τ).2
      (Matrix.blockTriangular_inv_of_blockTriangular ((lower_iff_blockTriangular g τ).1 (hg τ)))

theorem Lower.det_eq {g : Mat m K} (hg : Lower g) (τ : ι) : (g τ).det = ∏ i, g τ i i :=
  Matrix.det_of_lowerTriangular _ ((lower_iff_blockTriangular g τ).1 (hg τ))

theorem lower_one : Lower (1 : Mat m K) := fun _ _ _ hik => Matrix.one_apply_ne hik.ne

theorem par_full_iff {O : Subring K} {g : Mat m K} : Par m O g ↔ Par 0 O g ∧ Lower g := by
  constructor
  · intro h
    exact ⟨h.mono (fun _ => Nat.zero_le _) le_rfl, fun τ i k hik => (h τ).2.2.2 i k i.2 hik⟩
  · rintro ⟨h, hl⟩ τ
    exact ⟨(h τ).1, (h τ).2.1, (h τ).2.2.1, fun i k _ hik => hl τ i k hik⟩

theorem lower_mul_iff {B L : Mat m K} (hl : Lower L) (hL : ∀ τ, (L τ).det ≠ 0) : Lower (B * L) ↔ Lower B := by
  refine ⟨fun h => ?_, fun h => h.mul hl⟩
  have := h.mul hl.inv
  rwa [mul_assoc, Mat.mul_inv hL, mul_one] at this

end Tri

section Nhds

variable {F : Type} [Field F] {ι : Type} [Finite ι] {m : ι → ℕ}

theorem mem_O_generic (Y : Var F) (x : Y.Fn) : x ∈ ((ratOf Y).O (genericPoint Y.X)).toSubring :=
  (mem_O_ratOf (Y := Y) (y := genericPoint Y.X) (g := x)).2 ⟨x, by
    show (Y.X.presheaf.stalkSpecializes _).hom x = x
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl⟩

theorem eventually_mem_O {Y : Var F} {z : Y.X} {g : Y.Fn} (h : g ∈ ((ratOf Y).O z).toSubring) :
    ∀ᶠ z' in nhds z, g ∈ ((ratOf Y).O z').toSubring := by
  obtain ⟨U, hz, a, rfl⟩ := (mem_O_ratOf.1 h).exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun z' hz' => mem_O_ratOf.2 (regAt_fnOf hz' _ a)

theorem eventually_par {Y : Var F} {z : Y.X} {g : Mat m Y.Fn} (h : Par 0 ((ratOf Y).O z).toSubring g) :
    ∀ᶠ z' in nhds z, Par 0 ((ratOf Y).O z').toSubring g := by
  have h1 : ∀ᶠ z' in nhds z, ∀ τ i j, g τ i j ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_mem_O ((h τ).1 i j)
  have h2 : ∀ᶠ z' in nhds z, ∀ τ, (g τ).det⁻¹ ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => eventually_mem_O (h τ).2.2.1
  filter_upwards [h1, h2] with z' h1 h2 τ
  exact ⟨h1 τ, (h τ).2.1, h2 τ, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩

end Nhds

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev base (C : FlagCpt Z e) : Fr (ratOf C.Y) Dw.mult 0 := TieBase.fam e C.Y C.π C.π_str C.f0

theorem exists_lower (C : FlagCpt Z e) (y : C.Y.X) :
    ∃ (L : Mat Dw.mult C.Y.Fn) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      L⁻¹ ∈ (base C).S y ∧ (∀ τ, (L τ).det ≠ 0) ∧ Lower L ∧ (∀ τ i, L τ i i = t τ i) ∧
        ∀ τ i, (C.gr τ i).IsEqn y (t τ i) := by
  obtain ⟨φ, f, t, htri, hgr⟩ := C.gr_spec y
  obtain ⟨L, hc, hd, hl⟩ := (EigFrame.tri_iff f _ C.f0 t).1 htri
  have hL : ∀ τ, (L τ).det ≠ 0 := fun τ => by
    rw [Lower.det_eq hl τ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hd]; exact (t τ i).ne_zero
  refine ⟨L, t, ?_, hL, hl, hd, hgr⟩
  show (∀ τ, (L⁻¹ τ).det ≠ 0) ∧ _
  refine ⟨fun τ => (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hL) τ)).ne_zero, φ, f, ?_⟩
  rw [Mat.inv_inv hL]
  exact hc

theorem one_mem_base (C : FlagCpt Z e) : (1 : Mat Dw.mult C.Y.Fn) ∈ (base C).S (genericPoint C.Y.X) := by
  obtain ⟨A, hA⟩ := (base C).nonempty (genericPoint C.Y.X)
  refine (Fr.mem_iff hA).2 fun τ => ?_
  refine ⟨fun _ _ => mem_O_generic _ _, ?_, mem_O_generic _ _, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [one_mul]
  exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul (Fr.det_ne hA)) τ)).ne_zero

def flagFam (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn) (hA₁ : ∀ τ, (A₁ τ).det ≠ 0) : Fr (ratOf C.Y) Dw.mult Dw.mult where
  S y := {A' | A' * A₁⁻¹ ∈ (base C).S y ∧ Lower (A' * A₁⁻¹)}
  loc z := by
    obtain ⟨L, -, hLS, hL, hl, -, -⟩ := exists_lower C z
    obtain ⟨U₀, T, hz, -, hU₀⟩ := (base C).loc z
    have hev : ∀ᶠ z' in nhds z, L⁻¹ ∈ (base C).S z' :=
      (Filter.eventually_and.2 ⟨Filter.eventually_of_mem (U₀.isOpen.mem_nhds hz) fun _ h => h,
        eventually_par ((hU₀ z hz L⁻¹).1 hLS)⟩).mono fun z' h => (hU₀ z' h.1 L⁻¹).2 h.2
    obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1 hev
    refine ⟨⟨W, hWo⟩, L⁻¹ * A₁, hzW, fun τ => ?_, fun z' hz' A' => ?_⟩
    · rw [Pi.mul_apply, Matrix.det_mul]
      exact mul_ne_zero (Fr.det_ne hLS τ) (hA₁ τ)
    · have hz'' : L⁻¹ ∈ (base C).S z' := hW z' hz'
      show (A' * A₁⁻¹ ∈ (base C).S z' ∧ Lower (A' * A₁⁻¹)) ↔ _
      rw [Fr.mem_iff hz'', Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, par_full_iff, lower_mul_iff hl hL]

theorem exists_tied_isGraded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type)
    [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn), (∀ τ, (A₁ τ).det ≠ 0) →
    ∃ E' : Fr (ratOf C.Y) Dw.mult Dw.mult, Tied e C.Y C.π C.f0 E' A₁ ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C A₁ hA₁
  have hA : A₁ ∈ (flagFam C A₁ hA₁).S (genericPoint C.Y.X) := by
    show A₁ * A₁⁻¹ ∈ (base C).S _ ∧ Lower (A₁ * A₁⁻¹)
    rw [Mat.mul_inv hA₁]
    exact ⟨one_mem_base C, lower_one⟩
  refine ⟨flagFam C A₁ hA₁, ⟨hA, fun y A h => ?_⟩, ⟨A₁, hA, fun y x => ?_⟩⟩
  · obtain ⟨-, φ, f, hf⟩ := h.1
    rw [Mat.mul_inv_rev, Mat.inv_inv hA₁] at hf
    exact ⟨φ, f, hf⟩
  · obtain ⟨L, t, hLS, hL, hl, hd, hgr⟩ := exists_lower C y
    refine ⟨L⁻¹ * A₁, ?_, t x.1 x.2, ?_, hgr x.1 x.2⟩
    · show L⁻¹ * A₁ * A₁⁻¹ ∈ (base C).S y ∧ Lower (L⁻¹ * A₁ * A₁⁻¹)
      rw [mul_assoc, Mat.mul_inv hA₁, mul_one]
      exact ⟨hLS, hl.inv⟩
    · rw [Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, Mat.mul_inv hA₁, one_mul]
      exact hd _ _

end Main

end GlobalTheory.ShFam.FlagTie
