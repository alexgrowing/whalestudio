import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixOpen

variable {A₀ X T : Scheme.{0}} {N : LB A₀} {mA mB : ℕ}

theorem isUnit_comb_chart (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (z : X) {q q' : N.ι} (hq : φ z ∈ N.U q) (hq' : φ z ∈ N.U q') (j : Fin mB) :
    IsUnit (comb a φ p c z q j) ↔ IsUnit (comb a φ p c z q' j) := by
  have e : comb a φ p c z q j = (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    simp only [comb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_compat (a i) φ z hq hq', mul_left_comm]
  rw [e, Units.isUnit_units_mul]

theorem comb_comp {Y : Scheme.{0}} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (h : Y ⟶ X) (y : Y) (q : N.ι) (hq : φ (h y) ∈ N.U q) (j : Fin mB) :
    comb a (h ≫ φ) (h ≫ p) c y q j = (h.stalkMap y).hom (comb a φ p c (h y) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp h p y ⊤ trivial, gs_comp h φ y (N.U q) hq]

theorem gs_top {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X) (c : Γ(Z, ⊤)) :
    gs f z ⊤ (g.appTop.hom c) = gs (f ≫ g) z ⊤ c :=
  gs_pull f g z ⊤ trivial c

theorem gs_sum' {Y : Scheme.{0}} (f : X ⟶ Y) (z : X) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (b : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, b i) = ∑ i, gs f z U (b i) := by
  simp only [gs_eq f z U h, map_sum]

def good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Set X :=
  {z | ∃ q, φ z ∈ N.U q ∧ ∃ j, IsUnit (comb a φ p c z q j)}

def combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) : Γ(X, φ ⁻¹ᵁ N.U q) :=
  ∑ i, (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (c i j)) * (φ.app (N.U q)).hom ((a i).f q)

theorem gs_combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) (z : X) (hz : φ z ∈ N.U q) : gs (𝟙 X) z _ (combFn a φ p c q j) = comb a φ p c z q j := by
  have hz' : (𝟙 X) z ∈ φ ⁻¹ᵁ N.U q := hz
  rw [combFn, gs_sum' (𝟙 X) z _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hz', gs_res _ z le_top hz', gs_top, gs_pull (𝟙 X) φ z (N.U q) hz, Category.id_comp,
    Category.id_comp]

theorem isOpen_good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) :
    IsOpen (good a φ p c) := by
  have e : good a φ p c = ⋃ q, ⋃ j, (X.basicOpen (combFn a φ p c q j) : Set X) := by
    ext z
    simp only [good, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, j, hu⟩
      refine ⟨q, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq] at hu
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).1 hu
    · rintro ⟨q, j, hz⟩
      have hq : φ z ∈ N.U q := X.basicOpen_le _ hz
      refine ⟨q, hq, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq]
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).2 hz
  rw [e]
  exact isOpen_iUnion fun q => isOpen_iUnion fun j => (X.basicOpen _).isOpen

end GlobalTheory.HomFixOpen

namespace GlobalTheory.HomFixOpen

theorem main : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  intro Rg _ A₀ f _ N mA mB a hN
  let π₁ := pullback.fst f (affπ Rg (mA * mB))
  let π₂ := pullback.snd f (affπ Rg (mA * mB))
  let G := good a π₁ π₂ (matOf (𝟙 (Sp (MvPolynomial (Fin (mA * mB)) Rg))))
  have hG : IsOpen G := isOpen_good _ _ _ _
  have hC : IsClosed (π₂ '' Gᶜ) := π₂.isClosedMap _ hG.isClosed_compl
  refine ⟨⟨(π₂ '' Gᶜ)ᶜ, hC.isOpen_compl⟩, fun T X' g φ p hP => ?_⟩
  have w : φ ≫ f = (p ≫ g) ≫ affπ Rg (mA * mB) := by rw [Category.assoc]; exact hP.w
  let h := pullback.lift φ (p ≫ g) w
  have h1 : h ≫ π₁ = φ := pullback.lift_fst _ _ _
  have h2 : h ≫ π₂ = p ≫ g := pullback.lift_snd _ _ _
  have hπ₁ : ∀ z, π₁ (h z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, h1]
  have key : ∀ z q j, φ z ∈ N.U q → comb a φ p (matOf g) z q j =
      (h.stalkMap z).hom (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j) := by
    intro z q j hq
    rw [← comb_comp a π₁ π₂ _ h z q (by rw [hπ₁]; exact hq) j]
    simp only [comb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [h2, matOf, matOf, coord, coord, gs_top, gs_top, Category.comp_id]
  have unitIff : ∀ z q j, φ z ∈ N.U q → (IsUnit (comb a φ p (matOf g) z q j) ↔
      IsUnit (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j)) := by
    intro z q j hq; rw [key z q j hq]; exact isUnit_map_iff _ _
  have stepA : Generates a φ p (matOf g) ↔ ∀ z, h z ∈ G := by
    constructor
    · intro hg z
      obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hN (φ z)
      obtain ⟨j, hj⟩ := hg z q hq
      exact ⟨q, by rw [hπ₁]; exact hq, j, (unitIff z q j hq).1 hj⟩
    · intro hg z q hq
      obtain ⟨q', hq', j, hj⟩ := hg z
      exact ⟨j, (unitIff z q j hq).2 ((isUnit_comb_chart a π₁ π₂ _ (h z) hq' (by rw [hπ₁]; exact hq) j).1 hj)⟩
  rw [stepA]
  have hP' : IsPullback h p π₂ g := IsPullback.of_right (by rw [h1]; exact hP) h2 (IsPullback.of_hasPullback _ _)
  constructor
  · intro hg τ
    show g τ ∈ (π₂ '' Gᶜ)ᶜ
    rintro ⟨w', hw, he⟩
    obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π₂) (g := g) w' τ he
    apply hw
    have e : h (hP'.isoPullback.inv y) = w' := by
      rw [← Scheme.Hom.comp_apply, hP'.isoPullback_inv_fst, hy1]
    rw [← e]; exact hg _
  · intro hg z
    by_contra hz
    exact hg (p z) ⟨h z, hz, by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]⟩

end GlobalTheory.HomFixOpen
