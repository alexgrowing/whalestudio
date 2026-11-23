import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

abbrev Mat {ι : Type} (m : ι → ℕ) (K : Type) : Type := ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) K

variable {ι : Type} {m : ι → ℕ}

def Mat.map {K K' : Type} (g : Mat m K) (f : K → K') : Mat m K' := fun τ => (g τ).map f

def Par (k : ι → ℕ) {K : Type} [Field K] (O : Subring K) (g : Mat m K) : Prop :=
  ∀ τ, (∀ i j, g τ i j ∈ O) ∧ (g τ).det ≠ 0 ∧ (g τ).det⁻¹ ∈ O ∧
    ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0

section Par

variable {k k' : ι → ℕ} {K K' : Type} [Field K] [Field K'] {O O' : Subring K} {g h : Mat m K}

theorem Mat.map_mul (g h : Mat m K) (φ : K →+* K') : (g * h).map φ = g.map φ * h.map φ :=
  funext fun _ => Matrix.map_mul

theorem Mat.map_one (φ : K →+* K') : (1 : Mat m K).map φ = 1 :=
  funext fun _ => Matrix.map_one _ φ.map_zero φ.map_one

theorem Mat.det_map (g : Mat m K) (φ : K →+* K') (τ : ι) : (g.map φ τ).det = φ (g τ).det :=
  (φ.map_det (g τ)).symm

theorem Mat.mul_inv (hg : ∀ τ, (g τ).det ≠ 0) : g * g⁻¹ = 1 :=
  funext fun τ => Matrix.mul_nonsing_inv _ (Ne.isUnit (hg τ))

theorem Mat.inv_mul (hg : ∀ τ, (g τ).det ≠ 0) : g⁻¹ * g = 1 :=
  funext fun τ => Matrix.nonsing_inv_mul _ (Ne.isUnit (hg τ))

theorem Mat.mul_inv_rev (g h : Mat m K) : (g * h)⁻¹ = h⁻¹ * g⁻¹ :=
  funext fun _ => Matrix.mul_inv_rev _ _

theorem Mat.inv_inv (hg : ∀ τ, (g τ).det ≠ 0) : g⁻¹⁻¹ = g :=
  funext fun τ => Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit (hg τ))

theorem Mat.map_inv (g : Mat m K) (φ : K →+* K') : g⁻¹.map φ = (g.map φ)⁻¹ := by
  funext τ
  by_cases h : (g τ).det = 0
  · have h' : (g.map φ τ).det = 0 := by rw [Mat.det_map, h, map_zero]
    show ((g τ)⁻¹).map φ = (g.map φ τ)⁻¹
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [h]),
      Matrix.nonsing_inv_apply_not_isUnit _ (by simp [h']), Matrix.map_zero _ φ.map_zero]
  · refine (Matrix.inv_eq_left_inv ?_).symm
    show ((g τ)⁻¹).map φ * (g τ).map φ = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit h), Matrix.map_one _ φ.map_zero φ.map_one]

theorem det_mem {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n K} (h : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

theorem Par.one : Par k O (1 : Mat m K) := fun τ =>
  ⟨fun i j => by
      show (1 : Matrix _ _ K) i j ∈ O
      rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem],
    by simp, by simp [O.one_mem], fun i j _ h => Matrix.one_apply_ne h.ne⟩

theorem Par.det_ne (hg : Par k O g) (τ : ι) : (g τ).det ≠ 0 := (hg τ).2.1

theorem Par.mul (hg : Par k O g) (hh : Par k O h) : Par k O (g * h) := fun τ => by
  refine ⟨fun i j => ?_, ?_, ?_, fun i j hi hij => ?_⟩
  · rw [Pi.mul_apply, Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem ((hg τ).1 i l) ((hh τ).1 l j)
  · rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hg.det_ne τ) (hh.det_ne τ)
  · rw [Pi.mul_apply, Matrix.det_mul, _root_.mul_inv]; exact O.mul_mem (hg τ).2.2.1 (hh τ).2.2.1
  · rw [Pi.mul_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge i l with h | h
    · rw [(hg τ).2.2.2 i l hi h, zero_mul]
    · rw [(hh τ).2.2.2 l j (lt_of_le_of_lt h hi) (lt_of_le_of_lt h hij), mul_zero]

theorem Par.inv (hg : Par k O g) : Par k O g⁻¹ := fun τ => by
  refine ⟨fun i j => ?_, ?_, ?_, fun i j hi hij => ?_⟩
  · rw [Pi.inv_apply, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
    refine O.mul_mem (hg τ).2.2.1 (det_mem fun a b => ?_)
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    · exact (hg τ).1 a b
  · rw [Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hg.det_ne τ)
  · rw [Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.inv_inv]; exact det_mem (hg τ).1
  · have := (g τ).invertibleOfIsUnitDet (Ne.isUnit (hg.det_ne τ))
    have hb : (g τ).BlockTriangular fun i => OrderDual.toDual (min (i : ℕ) (k τ)) := fun a b hab => by
      have hab' : min (a : ℕ) (k τ) < min (b : ℕ) (k τ) := hab
      exact (hg τ).2.2.2 a b (by omega) (by show (a : ℕ) < b; omega)
    refine Matrix.blockTriangular_inv_of_blockTriangular hb ?_
    show min (i : ℕ) (k τ) < min (j : ℕ) (k τ)
    have : (i : ℕ) < j := hij
    omega

theorem Par.mono (hg : Par k O g) (hk : k' ≤ k) (hO : O ≤ O') : Par k' O' g := fun τ =>
  ⟨fun i j => hO ((hg τ).1 i j), (hg τ).2.1, hO (hg τ).2.2.1,
    fun i j hi => (hg τ).2.2.2 i j (lt_of_lt_of_le hi (hk τ))⟩

theorem Par.map (hg : Par k O g) (φ : K →+* K') {O' : Subring K'} (h : ∀ x ∈ O, φ x ∈ O') : Par k O' (g.map φ) :=
  fun τ => ⟨fun i j => h _ ((hg τ).1 i j), by rw [Mat.det_map]; exact (map_ne_zero φ).2 (hg.det_ne τ),
    by rw [Mat.det_map, ← map_inv₀]; exact h _ (hg τ).2.2.1,
    fun i j hi hij => by show φ (g τ i j) = 0; rw [(hg τ).2.2.2 i j hi hij, map_zero]⟩

theorem Par.map_mul_of (hg : Par k O g) (hh : Par k' O h) (v : K → K') (ψ : O →+* K') (hv : ∀ x : O, v x = ψ x) :
    (g * h).map v = g.map v * h.map v := by
  funext τ
  ext i j
  have e : (g * h) τ i j = ((∑ l, (⟨_, (hg τ).1 i l⟩ * ⟨_, (hh τ).1 l j⟩ : O) : O) : K) := by
    simp [Matrix.mul_apply]
  show v ((g * h) τ i j) = ∑ l, v (g τ i l) * v (h τ l j)
  rw [e, hv, map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [_root_.map_mul, ← hv, ← hv]

theorem Par.map_of (hg : Par k O g) (v : K → K') (ψ : O →+* K') (hv : ∀ x : O, v x = ψ x) :
    Par k ⊤ (g.map v) := fun τ => by
  let A : Matrix (Fin (m τ)) (Fin (m τ)) O := fun i j => ⟨_, (hg τ).1 i j⟩
  have e1 : g τ = A.map O.subtype := rfl
  have e2 : g.map v τ = A.map ψ := by ext i j; exact hv (A i j)
  have e3 : (A.det : K) = (g τ).det := O.subtype.map_det A
  have e4 : A.det * ⟨_, (hg τ).2.2.1⟩ = 1 := Subtype.ext (by
    show (A.det : K) * (g τ).det⁻¹ = 1
    rw [e3]; exact mul_inv_cancel₀ (hg.det_ne τ))
  refine ⟨fun _ _ => trivial, ?_, trivial, fun i j hi hij => ?_⟩
  · rw [e2]
    show (ψ.mapMatrix A).det ≠ 0
    rw [← ψ.map_det]
    exact left_ne_zero_of_mul_eq_one ((map_mul ψ _ _).symm.trans (by rw [e4, map_one]))
  · show v (g τ i j) = 0
    rw [(hg τ).2.2.2 i j hi hij]
    exact (hv 0).trans (map_zero ψ)

end Par

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

structure Fr (M : RatModel F Ω) (m k : ι → ℕ) : Type where

  S : M.Z → Set (Mat m Ω)
  loc : ∀ z, ∃ (U : M.Z.Opens) (A : Mat m Ω), z ∈ U ∧ (∀ τ, (A τ).det ≠ 0) ∧
    ∀ z' ∈ U, ∀ A', A' ∈ S z' ↔ Par k (M.O z').toSubring (A' * A⁻¹)

namespace Fr

variable {M : RatModel F Ω} {k : ι → ℕ}

def ofBasis (M : RatModel F Ω) (k : ι → ℕ) (A : Mat m Ω) (hA : ∀ τ, (A τ).det ≠ 0) : Fr M m k where
  S z := {A' | Par k (M.O z).toSubring (A' * A⁻¹)}
  loc _ := ⟨⊤, A, trivial, hA, fun _ _ _ => Iff.rfl⟩

instance : Inhabited (Fr M m k) := ⟨ofBasis M k 1 fun _ => by simp⟩

variable (S : Fr M m k)

theorem nonempty (z : M.Z) : (S.S z).Nonempty := by
  obtain ⟨U, A, hz, hA, h⟩ := S.loc z
  exact ⟨A, (h z hz A).2 (by rw [Mat.mul_inv hA]; exact Par.one)⟩

variable {S} {z : M.Z} {A A' : Mat m Ω}

theorem det_ne (h : A ∈ S.S z) (τ : ι) : (A τ).det ≠ 0 := by
  obtain ⟨U, B, hz, hB, hU⟩ := S.loc z
  have := ((hU z hz A).1 h).det_ne τ
  rw [Pi.mul_apply, Matrix.det_mul] at this
  exact left_ne_zero_of_mul this

theorem mem_iff (h : A ∈ S.S z) : A' ∈ S.S z ↔ Par k (M.O z).toSubring (A' * A⁻¹) := by
  obtain ⟨U, B, hz, hB, hU⟩ := S.loc z
  have h1 := (hU z hz A).1 h
  rw [hU z hz A']
  constructor
  · intro h2
    have := h2.mul h1.inv
    rwa [Mat.mul_inv_rev, Mat.inv_inv hB, ← mul_assoc, mul_assoc A', Mat.inv_mul hB, mul_one] at this
  · intro h2
    have := h2.mul h1
    rwa [← mul_assoc, mul_assoc A', Mat.inv_mul (det_ne h), mul_one] at this

theorem mem_of_specializes (h : A ∈ S.S z) {ξ : M.Z} (hξ : ξ ⤳ z) : A ∈ S.S ξ := by
  obtain ⟨U, B, hz, hB, hU⟩ := S.loc z
  exact (hU ξ (hξ.mem_open U.isOpen hz) A).2
    (((hU z hz A).1 h).mono le_rfl fun _ hx => RatModel.O_le_of_specializes hξ hx)

theorem mem_genericPoint (h : A ∈ S.S z) : A ∈ S.S (genericPoint M.Z) :=
  mem_of_specializes h (genericPoint_specializes z)

end Fr

def Rad {K : Type} [Field K] (O : Subring K) (g : K) : Prop :=
  g ≠ 0 ∧ g ∈ O ∧ ∀ (x : K) (n : ℕ), x ∈ O → x ^ n / g ∈ O → x / g ∈ O

def KeepsRad (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) : Prop :=
  ∀ (z' : M'.Z) (g : Ω), Rad (M.O (f z')).toSubring g → Rad (M'.O z').toSubring (φ g)

def Bears {M' : RatModel F Ω'} {k' : ι → ℕ} (S' : Fr M' m k') (φ : Ω →ₐ[F] Ω') (A : Mat m Ω) {K : Type} [Field K]
    (h : Mat m K) (p : Sp K ⟶ M'.Z) : Prop :=
  ∃ A' ∈ S'.S (p (IsLocalRing.closedPoint K)), Par k' ⊤ (h * ((A' * (A.map φ)⁻¹).map (M'.val p))⁻¹)

structure Refines {M : RatModel F Ω} {M' : RatModel F Ω'} {k k' : ι → ℕ} (S : Fr M m k) (S' : Fr M' m k')
    (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) : Prop where
  le : k ≤ k'
  hom : M.IsHom M' φ f
  sub : ∀ z', ∀ A' ∈ S'.S z', ∀ A ∈ S.S (f z'), Par k (M'.O z').toSubring (A' * (A.map φ)⁻¹)
  rad : KeepsRad M M' φ f
  lifts : ∀ (K : Type) [Field K] (x : Sp K ⟶ M.Z), ∀ A ∈ S.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K,
    Par k ⊤ h → ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p

def Good (M : RatModel F Ω) (d : ℕ) : Prop :=
  IsProjOver M.s ∧ SmoothOfRelativeDimension d M.s ∧ GeometricallyIntegral M.s

def AffCover (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ) : Prop :=
  M.IsHom M' φ f ∧ ∀ z' : M'.Z, ∃ (U : M'.Z.Opens) (W : M.Z.Opens) (t : Fin r → Ω'), IsAffineOpen U ∧ IsAffineOpen W ∧
    z' ∈ U ∧ (∀ y ∈ U, f y ∈ W) ∧
    (∀ P : MvPolynomial (Fin r) Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) ∧
    M'.ringOn U = Algebra.adjoin F (φ '' (M.ringOn W : Set Ω) ∪ Set.range t)

structure ProjBundle (M : RatModel F Ω) {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (M' : RatModel F Ω')
    (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω') : Prop where
  hom : M.IsHom M' φ f
  gen : ∀ B : Matrix J J Ω, B.det ≠ 0 → ∀ i, (B.map φ).mulVec s i ≠ 0 ∧ ∀ P : MvPolynomial {j // j ≠ i} Ω,
    MvPolynomial.eval₂ (φ : Ω →+* Ω') (fun j => (B.map φ).mulVec s j.1 / (B.map φ).mulVec s i) P = 0 → P = 0
  chart : ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty →
    (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) →
    (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 →
      ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧
        M'.ringOn U = Algebra.adjoin F (φ '' (M.ringOn W : Set Ω) ∪
          Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i)

structure ProjPoints (M : RatModel F Ω) {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (M' : RatModel F Ω')
    (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω') : Prop where
  hom : M.IsHom M' φ f
  cover : ∀ (z' : M'.Z) (B : Matrix J J Ω), B.det ≠ 0 → EE.E (f z') = Submodule.span (M.O (f z')) (Set.range B) →
    ∃ i, M'.Div ((B.map φ).mulVec s) i z'
  lifts : ∀ (K : Type) [Field K] (x : Sp K ⟶ M.Z) (B : Matrix J J Ω), B.det ≠ 0 →
    EE.E (x (IsLocalRing.closedPoint K)) = Submodule.span (M.O (x (IsLocalRing.closedPoint K))) (Set.range B) →
    ∀ c : J → K, c ≠ 0 → ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧
      ∃ i, M'.Div ((B.map φ).mulVec s) i (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, c j = c i * M'.val p ((B.map φ).mulVec s j / (B.map φ).mulVec s i)

abbrev Rest (m k : ι → ℕ) (τ : ι) : Type := {j : Fin (m τ) // k τ ≤ (j : ℕ)}

def dualBlock (k : ι → ℕ) (τ : ι) (A₀ A : Mat m Ω) : Matrix (Rest m k τ) (Rest m k τ) Ω :=
  ((((A * A₀⁻¹) τ).submatrix Subtype.val Subtype.val : Matrix (Rest m k τ) (Rest m k τ) Ω)⁻¹).transpose

def stepSet {M : RatModel F Ω} {k : ι → ℕ} (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (M' : RatModel F Ω')
    (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : Rest m k τ → Ω') (z' : M'.Z) : Set (Mat m Ω') :=
  {A' | (∀ A ∈ S.S (f z'), Par k (M'.O z').toSubring (A' * (A.map φ)⁻¹)) ∧
    ∃ a : Ω', ∀ j : Rest m k τ, (A' * (A₀.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * s j}

section Var

variable (Y : GlobalTheory.ProjVar.Var F)

theorem valR_spMap_fromSpecStalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have h' : ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => h (x := spMap ψ w) trivial
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (GlobalTheory.Points.valR_appLE (spMap ψ) (X.fromSpecStalk x) h (GlobalTheory.Points.le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ) _

theorem valF_fromSpecStalk {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : genericPoint X ∈ U) (a : Γ(X, U)) :
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X)) U a = fnOf U hU a := by
  have := valR_spMap_fromSpecStalk (RingHom.id (X.presheaf.stalk (genericPoint X))) hU a
  rw [show spMap (RingHom.id (X.presheaf.stalk (genericPoint X))) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  exact this

def ratOf : RatModel F Y.Fn where
  Z := Y.X
  s := Y.str
  sep := inferInstance
  lft := inferInstance
  qc := inferInstance
  pt := Y.X.fromSpecStalk (genericPoint Y.X)
  pt_s := by
    refine GlobalTheory.Points.ext_of_valR (isAffineOpen_top (Sp F)) (GlobalTheory.Points.le_preimage_top _)
      (GlobalTheory.Points.le_preimage_top _) fun a => ?_
    obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (.of F)).commRingCatIsoToRingEquiv.symm.surjective a
    refine ((GlobalTheory.Points.valR_appLE _ Y.str (V := ⊤) le_top (GlobalTheory.Points.le_preimage_top _) _).symm.trans
      (valF_fromSpecStalk (X := Y.X) (U := ⊤) trivial _)).trans ?_
    exact (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom (algebraMap F Y.Fn)) a).symm
  gen := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, Scheme.fromSpecStalk_closedPoint⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    have : w = IsLocalRing.closedPoint Y.Fn := Subsingleton.elim (α := PrimeSpectrum Y.Fn) _ _
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint
  onto x := by
    obtain ⟨U, h, a, rfl⟩ := Y.X.presheaf.germ_exist (x := genericPoint Y.X) x
    exact ⟨U, a, ⟨_, h⟩, valF_fromSpecStalk h a⟩

theorem good_ratOf : Good (ratOf Y) Y.dim := ⟨Y.isProjOver, Y.smooth_str, Y.geometricallyIntegral_str⟩

variable {Y}

theorem mem_O_ratOf {y : Y.X} {g : Y.Fn} : g ∈ (ratOf Y).O y ↔ RegAt y g := by
  constructor
  · rintro ⟨U, a, hy, rfl⟩
    exact (valF_fromSpecStalk (gen_mem hy) a).symm ▸ regAt_fnOf hy _ a
  · intro h
    obtain ⟨U, hy, a, rfl⟩ := h.exists_fnOf
    exact ⟨U, a, hy, valF_fromSpecStalk (gen_mem hy) a⟩

theorem val_ratOf {y : Y.X} {K : Type} [Field K] (ψ : Y.X.presheaf.stalk y →+* K) (a : Y.X.presheaf.stalk y) :
    (ratOf Y).val (spMap ψ ≫ Y.X.fromSpecStalk y) (algebraMap _ Y.X.functionField a) = ψ a := by
  obtain ⟨U, hy, a, rfl⟩ := Y.X.presheaf.germ_exist a
  rw [algebraMap_germ hy, ← valF_fromSpecStalk (gen_mem hy) a, ← valR_spMap_fromSpecStalk ψ hy a]
  refine RatModel.val_valF (M := ratOf Y) ?_ a
  rintro _ ⟨w, rfl⟩
  have : Y.X.fromSpecStalk y (spMap ψ w) ∈ Set.range (Y.X.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open this U.isOpen hy

theorem spMap_stalkClosedPointTo {X : Scheme.{0}} {K : Type} [CommRing K] [IsLocalRing K] (p : Sp K ⟶ X) :
    spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ X.fromSpecStalk (p (IsLocalRing.closedPoint K)) = p :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) p

theorem map_algebraMap_stalk {B : GlobalTheory.ProjVar.Var F} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X}
    (h : (ratOf B).IsHom (ratOf Y) φ f) (y : Y.X) (a : B.X.presheaf.stalk (f y)) :
    φ (algebraMap _ B.X.functionField a) = algebraMap _ Y.X.functionField ((f.stalkMap y).hom a) := by
  obtain ⟨U, hy, a, rfl⟩ := B.X.presheaf.germ_exist a
  rw [algebraMap_germ hy, ← valF_fromSpecStalk (gen_mem hy) a, Scheme.Hom.germ_stalkMap_apply,
    algebraMap_germ (U := f ⁻¹ᵁ U) hy, ← valF_fromSpecStalk (gen_mem (U := f ⁻¹ᵁ U) hy)]
  exact (h.valF_app ⟨_, hy⟩ a).symm

end Var

end GlobalTheory.FlagBundle
