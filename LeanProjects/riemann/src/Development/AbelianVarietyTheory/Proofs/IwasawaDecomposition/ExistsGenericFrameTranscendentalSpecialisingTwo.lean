import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrame

open Matrix ReciprocityTheory.ChartRestriction.G.PullbackSections

def mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) R := (1 - u) • (1 : Matrix (Fin n) (Fin n) R) + u • A.map κ

theorem mixM_map {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ} (κ : K →+* R) (u : R)
    (A : Matrix (Fin n) (Fin n) K) (ψ : R →+* R') : (mixM κ u A).map ψ = mixM (ψ.comp κ) (ψ u) A := by
  ext a b
  by_cases h : a = b
  · subst h; simp [mixM]
  · simp [mixM, Matrix.one_apply_ne h]

def detPoly {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Polynomial K :=
  (mixM Polynomial.C Polynomial.X A).det

theorem det_mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    (mixM κ u A).det = (detPoly A).eval₂ κ u := by
  rw [detPoly, ← Polynomial.coe_eval₂RingHom, RingHom.map_det, RingHom.mapMatrix_apply, mixM_map]
  congr 2
  · ext a; simp
  · simp

theorem mixM_zero {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 0 A = 1 := by
  simp [mixM]

theorem mixM_one {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 1 A = A := by
  simp [mixM]

theorem detPoly_ne_zero {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : detPoly A ≠ 0 := by
  intro h
  have := det_mixM (RingHom.id K) 0 A
  rw [h, mixM_zero, Polynomial.eval₂_zero, det_one] at this
  exact one_ne_zero this

end GlobalTheory.GenFrame

namespace GlobalTheory.GenFrame

open Matrix Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions GlobalTheory.CxPts GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_co_eq {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (hT : ∀ τ, IsUnit (T τ).det) :
    ∃ g : EigFrame Z φ x, ∀ τ, f.co g τ = T τ := by
  have hsum : ∀ τ (a : Fin (Dw.mult τ) → R),
      ∑ i, a i • ∑ j, T τ j i • f.vec τ j = ∑ j, (T τ *ᵥ a) j • f.vec τ j := by
    intro τ a
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  let g : EigFrame Z φ x := EigFrame.ofVec (fun τ i => ∑ j, T τ j i • f.vec τ j)
    (fun τ i a => by
      simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _)
    (fun τ w hw => by
      obtain ⟨b, hb, hbu⟩ := f.existsUnique_sum τ w hw
      refine ⟨(T τ)⁻¹ *ᵥ b, ?_, fun a ha => ?_⟩
      · show w = ∑ i, ((T τ)⁻¹ *ᵥ b) i • ∑ j, T τ j i • f.vec τ j
        rw [hsum, mulVec_mulVec, mul_nonsing_inv _ (hT τ), one_mulVec]
        exact hb
      · have h1 : T τ *ᵥ a = b := hbu _ (ha.trans (hsum τ a))
        rw [← h1, mulVec_mulVec, nonsing_inv_mul _ (hT τ), one_mulVec])
  refine ⟨g, fun τ => EigFrame.co_eq fun i => ?_⟩
  exact (isComb_iff (f.vec τ) (fun a => T τ a i) (∑ j, T τ j i • f.vec τ j)).2 rfl

theorem co_eq_one {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f₀ f₁ f₂ : EigFrame Z φ x}
    {τ : E →+* ℂ} (h : f₀.co f₁ τ = f₀.co f₂ τ) : f₁.co f₂ τ = 1 := by
  rw [← f₁.co_mul f₀ f₂ τ, ← h, f₁.co_mul f₀ f₁ τ, f₁.co_self τ]

theorem tri_of_co_eq_one {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (hf : f.IsMap ψ f') (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (h : ∀ τ, f'.co g τ = 1) : f.Tri ψ g 1 := by
  refine ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, by simp [h], fun k hk => by
    simp [h, Matrix.one_apply_ne hk.ne'], ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g τ i

theorem isMap_id {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) :
    f.IsMap (RingHom.id R) f := fun τ i => by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenFrame

open Matrix in

theorem GlobalTheory.GenFrame.exists_generic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ χ x g g' L _ ι s hs xL hxL
  have hP : ∀ τ, (GlobalTheory.GenFrame.detPoly (g.co g' τ)).eval₂ ι s ≠ 0 := fun τ h =>
    GlobalTheory.GenFrame.detPoly_ne_zero _ (hs _ h)
  obtain ⟨gB, hgB⟩ := g.exists_isMap ι (φ' := ι.comp χ) rfl hxL
  obtain ⟨gL, hgL⟩ := GlobalTheory.GenFrame.exists_co_eq gB (fun τ => GlobalTheory.GenFrame.mixM ι s (g.co g' τ)) fun τ => by
    rw [GlobalTheory.GenFrame.det_mixM]
    exact (hP τ).isUnit
  refine ⟨gL, fun V _ _ ν ιV r sV hνι hrι hker hνs => ?_⟩
  obtain ⟨gVB, hgVB⟩ := g.exists_isMap ιV (φ' := ιV.comp χ) (x' := spMap ιV ≫ x) rfl rfl
  have hxν : xL = spMap ν ≫ spMap ιV ≫ x := by
    rw [hxL, ← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hνι]
  have hxr : x = spMap r ≫ spMap ιV ≫ x := by
    rw [← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hrι]
    exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  have hφν : ι.comp χ = ν.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hνι]
  have hφr : χ = r.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hrι]; rfl
  have hBν : gVB.IsMap ν gB := fun τ i => by
    rw [hgB τ i, hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hνι]
  have hBr : gVB.IsMap r g := fun τ i => by
    rw [hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hrι]
    exact (GlobalTheory.GenFrame.isMap_id g τ i)

  have main : ∀ (hu : ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det),
      ∃ gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x), gV.Tri ν gL 1 ∧
        ∃ gVr : EigFrame Z χ x, gV.IsMap r gVr ∧ ∀ τ, g.co gVr τ = GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ) := by
    intro hu
    obtain ⟨gV, hgV⟩ := GlobalTheory.GenFrame.exists_co_eq gVB (fun τ => GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)) hu
    obtain ⟨gVν, hgVν⟩ := gV.exists_isMap ν hφν hxν
    obtain ⟨gVr, hgVr⟩ := gV.exists_isMap r hφr hxr
    refine ⟨gV, GlobalTheory.GenFrame.tri_of_co_eq_one hgVν hφν hxν fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := gB) ?_, gVr, hgVr,
      fun τ => ?_⟩
    · rw [hBν.co τ hgVν hxν, hgV, hgL, GlobalTheory.GenFrame.mixM_map, hνι, hνs]
    · rw [hBr.co τ hgVr hxr, hgV, GlobalTheory.GenFrame.mixM_map, hrι]
  have hunit : (∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det ≠ 0) →
      ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det := fun h τ => by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker]
    exact h τ
  have hr : ∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det =
      (GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ)).det := fun τ => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.GenFrame.mixM_map, hrι]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h0, GlobalTheory.GenFrame.mixM_zero, det_one]; exact one_ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h0, GlobalTheory.GenFrame.mixM_zero, g.co_self]
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h1, GlobalTheory.GenFrame.mixM_one]; exact (g.isUnit_det_co g' τ).ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h1, GlobalTheory.GenFrame.mixM_one]
