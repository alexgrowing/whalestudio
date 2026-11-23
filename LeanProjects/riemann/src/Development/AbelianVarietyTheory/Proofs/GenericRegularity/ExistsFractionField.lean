import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RankOfQuasiIdem

open NumberField

namespace GlobalTheory.Reg.CellChart

noncomputable def genLower {V Ω : Type} [CommRing Ω] {r : ℕ} (X : ∀ i j : Fin r, j < i → V) (x : V → Ω) :
    Matrix (Fin r) (Fin r) Ω := fun i j => if h : j < i then x (X i j h) else if i = j then 1 else 0

theorem adjoin_insert_eq' {K O A F Ω : Type} [Field K] [CommRing O] [Algebra O K] [CommRing A] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω] (i : A →+* F) (a₀ : A) (gens X : Set Ω)
    (h1 : ∀ a, algebraMap F Ω (i a) ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens))
    (h2 : X ⊆ gens)
    (h3 : gens ⊆ Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X)) :
    Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact Algebra.subset_adjoin (Or.inl ⟨(i a₀)⁻¹, Algebra.subset_adjoin (Or.inl rfl), map_inv₀ _ _⟩)
    · exact h3 hx
  · rw [Algebra.adjoin_le_iff]
    rintro x (⟨y, hy, rfl⟩ | hx)
    · have : Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) ≤
          (Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens)).comap (IsScalarTower.toAlgHom K F Ω) := by
        rw [Algebra.adjoin_le_iff]
        rintro z (rfl | ⟨a, rfl⟩)
        · exact Algebra.subset_adjoin (Or.inl (map_inv₀ (algebraMap F Ω) _))
        · have : Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens) ≤
              (Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens)).toSubring := by
            rw [Subring.closure_le]
            rintro w (⟨o, rfl⟩ | hw)
            · exact Subalgebra.algebraMap_mem _ _
            · exact Algebra.subset_adjoin (Or.inr hw)
          exact this (h1 a)
      exact this hy
    · exact Algebra.subset_adjoin (Or.inr (h2 hx))

theorem adjoin_insert_eq {K O A F Ω : Type} [Field K] [CommRing O] [Algebra O K] [CommRing A] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω] (i : A →+* F) (g : A →+* Ω)
    (hg : ∀ a, g a = algebraMap F Ω (i a)) (a₀ : A) (gens X : Set Ω)
    (h1 : ∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens))
    (h2 : X ⊆ gens)
    (h3 : gens ⊆ Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X)) :
    Algebra.adjoin K (insert (g a₀)⁻¹ gens) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X) := by
  rw [hg]
  exact adjoin_insert_eq' i a₀ gens X (fun a => hg a ▸ h1 a) h2 h3

theorem mul_inv_mem {K F : Type} [Field K] [Field F] [Algebra K F] (R : Subalgebra K F) {n r : ℕ}
    (C : Matrix (Fin n) (Fin r) F) (D : Matrix (Fin r) (Fin r) F) (hC : ∀ i j, C i j ∈ R) (hD : ∀ i j, D i j ∈ R)
    (hd : D.det⁻¹ ∈ R) (i : Fin n) (j : Fin r) : (C * D⁻¹) i j ∈ R := by
  let D' : Matrix (Fin r) (Fin r) R := fun i j => ⟨D i j, hD i j⟩
  have h : D = R.val.toRingHom.mapMatrix D' := rfl
  have hadj : ∀ i j, D.adjugate i j ∈ R := fun i j => by
    rw [h, ← RingHom.map_adjugate]
    exact (D'.adjugate i j).2
  rw [Matrix.mul_apply, Matrix.inv_def, Ring.inverse_eq_inv]
  exact R.sum_mem fun k _ => R.mul_mem (hC i k) (R.mul_mem hd (hadj k j))

theorem basis_over_subalgebra {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) {n r : ℕ}
    (ix : Fin r ↪ Fin n) (κ : Fin r → Fin n) (P : Matrix (Fin n) (Fin n) R) (N : R) (hN : N ≠ 0)
    (hr : (P.map R.val).rank = r) (hd : ((P.map R.val).submatrix ix κ).det ≠ 0)
    (u : Matrix (Fin n) (Fin r) R) (hu : P * u = N • u) (hc : InCell ix u) (x : Fin n → R)
    (hx : P.mulVec x = N • x) : ∃! a, u.mulVec a = x := by
  have hdet : IsUnit (u.submatrix ix id).det := by rw [det_of_inCell ix u hc]; exact isUnit_one
  have hrow : ∀ a, (u.submatrix ix id).mulVec a = u.mulVec a ∘ ix := fun a => rfl
  refine ⟨(u.submatrix ix id)⁻¹.mulVec (x ∘ ix), ?_, fun a ha => ?_⟩
  · set a := (u.submatrix ix id)⁻¹.mulVec (x ∘ ix) with ha
    have h1 : u.mulVec a ∘ ix = x ∘ ix := by
      rw [← hrow, ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h2 : P.mulVec (u.mulVec a) = N • u.mulVec a := by
      rw [Matrix.mulVec_mulVec, hu, Matrix.smul_mulVec]
    have hN' : (N : Ω) ≠ 0 := fun h => hN (Subtype.ext h)
    have key : ∀ y : Fin n → R, P.mulVec y = N • y →
        P.map R.val * (Matrix.of fun i (_ : Fin 1) => (y i : Ω)) = (N : Ω) • Matrix.of fun i (_ : Fin 1) => (y i : Ω) := by
      intro y hy
      ext i j
      have := congrArg Subtype.val (congrFun hy i)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have e1 := eq_of_rows _ hr (N : Ω) hN' ix κ hd _ (key _ h2)
    have e2 := eq_of_rows _ hr (N : Ω) hN' ix κ hd _ (key _ hx)
    have e3 : (Matrix.of fun i (_ : Fin 1) => (u.mulVec a i : Ω)).submatrix ix id =
        (Matrix.of fun i (_ : Fin 1) => (x i : Ω)).submatrix ix id := by
      ext i j
      exact congrArg Subtype.val (congrFun h1 i)
    rw [e3, ← e2] at e1
    funext i
    exact Subtype.ext (congrFun (congrFun e1 i) 0)
  · rw [← ha, ← hrow, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem exists_fraction_field (K O A : Type) [Field K] [CommRing O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [IsDomain A] (α : O →+* A) (hinj : Function.Injective α) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (i : A →+* F), Function.Injective i ∧
      i.comp α = (algebraMap K F).comp (algebraMap O K) ∧ ∀ x : F, ∃ a b : A, i b ≠ 0 ∧ x * i b = i a := by
  have h := IsFractionRing.injective A (FractionRing A)
  have h' : Function.Injective ((algebraMap A (FractionRing A)).comp α) := h.comp hinj
  obtain ⟨φ, hφ⟩ : ∃ φ : K →+* FractionRing A, ∀ o, φ (algebraMap O K o) = algebraMap A (FractionRing A) (α o) :=
    ⟨IsFractionRing.lift (K := K) h', fun o => IsFractionRing.lift_algebraMap h' o⟩
  refine ⟨FractionRing A, inferInstance, φ.toAlgebra, algebraMap A _, h,
    RingHom.ext fun o => (hφ o).symm, fun x => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) x
  exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩

theorem exists_polyChart (K F V : Type) [Field K] [Field F] [Algebra K F] [Finite V] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (_ : Algebra F Ω) (_ : IsScalarTower K F Ω) (x : V → Ω),
      ∀ (R₀ : Subalgebra K F) (R : Subalgebra K Ω),
        R = Algebra.adjoin K (algebraMap F Ω '' (R₀ : Set F) ∪ Set.range x) →
        (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧
        ((∀ y : F, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ y * b = a) → ∀ y : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ y * b = a) ∧
        ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S,
          (∀ (a : R₀) (h : algebraMap F Ω a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : x v ∈ R), ψ' ⟨_, h⟩ = t v :=
  ⟨FractionRing (MvPolynomial V F), inferInstance, inferInstance, inferInstance, inferInstance, _,
    GlobalTheory.polyChart_smooth_fraction_lift K F V⟩

set_option maxHeartbeats 400000 in
theorem exists_cell_algebra (K O A T : Type) [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [IsDomain A] [Finite T] (α : O →+* A) (hft : α.FiniteType) (hinj : Function.Injective α)
    (es : Finset A) (hes : ∀ e ∈ es, e ≠ 0) (hne : es.Nonempty) (n : ℕ) (r : T → ℕ)
    (ix : ∀ τ, Fin (r τ) ↪ Fin n) (N : T → O) (hN : ∀ τ, N τ ≠ 0) (p : T → Matrix (Fin n) (Fin n) A)
    (hpp : ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
      ∀ τ, (p τ).map f * (p τ).map f = f (α (N τ)) • (p τ).map f)
    (hrk : ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = r τ)
    (hsm : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) → ∀ d : A, Function.Injective f →
      IsUnit (f d) → (∀ x : R, ∃ (a : A) (k : K) (m : ℕ), x * f (e * d) ^ m = algebraMap K R k * f a) →
      Algebra.Smooth K R)
    (κ₀ : ∀ τ, Fin (r τ) → Fin n) (hκ₀ : ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (gens es' : Finset Ω) (g : A →+* Ω)
      (u : ∀ τ, Matrix (Fin n) (Fin (r τ)) Ω),
      Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ ∧ es'.Nonempty ∧
      (∀ e ∈ es', e ≠ 0 ∧
        e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))) ∧
      (∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))) ∧
      (∀ τ i j, u τ i j ∈ gens) ∧ (∀ x ∈ gens, (∃ a, x = g a) ∨ ∃ τ i j, x = u τ i j) ∧
      (∀ τ, InCell (ix τ) (u τ)) ∧
      (∀ e ∈ es', Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) ∧
        ∃ (fe : A →+* Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))
          (ue : ∀ τ, Matrix (Fin n) (Fin (r τ)) (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))),
          (∀ a, (fe a : Ω) = g a) ∧ (∀ τ i j, (ue τ i j : Ω) = u τ i j) ∧
          fe.comp α = (algebraMap K _).comp (algebraMap O K) ∧ (∃ e₀ ∈ es, IsUnit (fe e₀)) ∧
          (∀ τ, (p τ).map fe * ue τ = fe (α (N τ)) • ue τ) ∧
          ∀ τ x, ((p τ).map fe).mulVec x = fe (α (N τ)) • x → ∃! a, (ue τ).mulVec a = x) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
        ∀ e₀ ∈ es, f e₀ ≠ 0 → ∀ u' : ∀ τ, Matrix (Fin n) (Fin (r τ)) L,
        (∀ τ, (p τ).map f * u' τ = f (α (N τ)) • u' τ) → (∀ τ, InCell (ix τ) (u' τ)) →
        ∃ e ∈ es', ∃ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →ₐ[K] L,
          (∀ a (h : g a ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), ψ ⟨g a, h⟩ = f a) ∧
          ∀ τ i j (h : u τ i j ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), ψ ⟨u τ i j, h⟩ = u' τ i j := by
  classical
  haveI := Fintype.ofFinite T
  obtain ⟨F, _, _, i, hi, hiα, hfr⟩ := exists_fraction_field K O A α hinj
  obtain ⟨sA, hsA⟩ : ∃ sA : Finset A, ∀ a, a ∈ Subring.closure (Set.range α ∪ (sA : Set A)) := by
    letI := α.toAlgebra
    obtain ⟨s, hs⟩ := hft.out
    exact ⟨s, fun a => Algebra.mem_adjoin_iff.mp (hs ▸ Algebra.mem_top)⟩
  let V : Type := Σ τ, {q : Fin (r τ) × Fin (r τ) // q.2 < q.1}
  obtain ⟨Ω, _, _, _, _, x, hpoly⟩ := exists_polyChart K F V
  obtain ⟨g, hgi⟩ : ∃ g : A →+* Ω, ∀ a, g a = algebraMap F Ω (i a) := ⟨(algebraMap F Ω).comp i, fun _ => rfl⟩
  have hg : Function.Injective g := fun a b h => hi ((algebraMap F Ω).injective (by rw [← hgi, ← hgi, h]))
  have hg0 : ∀ a, a ≠ 0 → g a ≠ 0 := fun a ha => (map_ne_zero_iff g hg).mpr ha
  have hi0 : ∀ a, a ≠ 0 → i a ≠ 0 := fun a ha => (map_ne_zero_iff i hi).mpr ha
  have hgα : g.comp α = (algebraMap K Ω).comp (algebraMap O K) := by
    ext o
    have := RingHom.congr_fun hiα o
    simp only [RingHom.comp_apply] at this ⊢
    rw [hgi, this, ← IsScalarTower.algebraMap_apply]
  have hgα' : ∀ o, g (α o) = algebraMap K Ω (algebraMap O K o) := fun o => RingHom.congr_fun hgα o
  have hαN : ∀ τ, α (N τ) ≠ 0 := fun τ => (map_ne_zero_iff α hinj).mpr (hN τ)
  obtain ⟨e₁, he₁⟩ := hne
  have hrΩ : ∀ τ, ((p τ).map g).rank = r τ := hrk Ω g hgα e₁ he₁ (hg0 _ (hes _ he₁))
  have hdet : ∀ {B : Type} [CommRing B] (f : A →+* B) τ (κ : Fin (r τ) → Fin n),
      (((p τ).map f).submatrix (ix τ) κ).det = f ((p τ).submatrix (ix τ) κ).det := fun f τ κ =>
    (RingHom.map_det f ((p τ).submatrix (ix τ) κ)).symm
  let ℓ : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) Ω := fun τ => genLower (fun a b h => (⟨τ, ⟨(a, b), h⟩⟩ : V)) x
  obtain ⟨u, hu1, hu2⟩ : ∃ u : ∀ τ, Matrix (Fin n) (Fin (r τ)) Ω, (∀ τ, (u τ).submatrix (ix τ) id = ℓ τ) ∧
      ∀ τ, (p τ).map g * u τ = g (α (N τ)) • u τ := by
    refine ⟨fun τ => ((p τ).map g).submatrix id (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ,
      fun τ => ?_, fun τ => ?_⟩
    · have : (((p τ).map g).submatrix id (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ).submatrix
          (ix τ) id = ((p τ).map g).submatrix (ix τ) (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ := rfl
      rw [this, Matrix.mul_nonsing_inv _ (by rw [hdet]; exact (hg0 _ (hκ₀ τ)).isUnit), Matrix.one_mul]
    · have : (p τ).map g * ((p τ).map g).submatrix id (κ₀ τ) =
          g (α (N τ)) • ((p τ).map g).submatrix id (κ₀ τ) :=
        congrArg (fun M => Matrix.submatrix M id (κ₀ τ)) (hpp Ω g hgα τ)
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.smul_mul, Matrix.smul_mul]
  have hu1' : ∀ τ a b, u τ (ix τ a) b = ℓ τ a b := fun τ a b => congrFun (congrFun (hu1 τ) a) b
  have hcell : ∀ τ, InCell (ix τ) (u τ) := fun τ => ⟨fun a b hab => by
      rw [hu1']; simp [ℓ, genLower, hab.not_gt, hab.ne], fun a => by rw [hu1']; simp [ℓ, genLower]⟩
  have hux : ∀ τ a b (h : b < a), u τ (ix τ a) b = x ⟨τ, ⟨(a, b), h⟩⟩ := fun τ a b h => by
    rw [hu1']; simp [ℓ, genLower, h]
  obtain ⟨gens, hsg, hug, hgens⟩ : ∃ gens : Finset Ω, (∀ a ∈ sA, g a ∈ gens) ∧ (∀ τ a b, u τ a b ∈ gens) ∧
      ∀ y ∈ gens, (∃ a, y = g a) ∨ ∃ τ a b, y = u τ a b := by
    refine ⟨sA.image g ∪ Finset.univ.image (fun q : Σ τ, Fin n × Fin (r τ) => u q.1 q.2.1 q.2.2),
      fun a ha => Finset.mem_union_left _ (Finset.mem_image_of_mem g ha), fun τ a b =>
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨τ, a, b⟩, Finset.mem_univ _, rfl⟩), ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨a, rfl⟩
    · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨_, _, _, rfl⟩
  have hgB : ∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω)) := by
    intro a
    have : Subring.closure (Set.range α ∪ (sA : Set A)) ≤
        (Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))).comap g := by
      rw [Subring.closure_le]
      rintro w (⟨o, rfl⟩ | hw)
      · exact Subring.subset_closure (Or.inl ⟨o, (hgα' o).symm⟩)
      · exact Subring.subset_closure (Or.inr (hsg _ hw))
    exact this (hsA a)
  obtain ⟨d, hdd⟩ : ∃ d : (∀ τ, Fin (r τ) → Fin n) → A, ∀ κ, d κ = ∏ τ, ((p τ).submatrix (ix τ) (κ τ)).det :=
    ⟨_, fun _ => rfl⟩
  have hd : ∀ κ, d κ ≠ 0 ↔ ∀ τ, ((p τ).submatrix (ix τ) (κ τ)).det ≠ 0 := fun κ => by
    simp [hdd, Finset.prod_ne_zero_iff]
  obtain ⟨es', hes', hes''⟩ : ∃ es' : Finset Ω, (∀ e' ∈ es', ∃ e ∈ es, ∃ κ, d κ ≠ 0 ∧ e' = g (e * d κ)) ∧
      ∀ e ∈ es, ∀ κ, d κ ≠ 0 → g (e * d κ) ∈ es' := by
    refine ⟨(es ×ˢ Finset.univ.filter fun κ => d κ ≠ 0).image fun q => g (q.1 * d q.2), ?_, fun e he κ hκ =>
      Finset.mem_image.mpr ⟨(e, κ), Finset.mem_product.mpr
        ⟨he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ⟩⟩, rfl⟩⟩
    intro e' he'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    exact ⟨q.1, h1, q.2, (Finset.mem_filter.mp h2).2, rfl⟩
  have hR : ∀ e ∈ es, ∀ κ, d κ ≠ 0 → Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω)) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) : Set F) ∪
        Set.range x) := by
    intro e he κ hκ
    refine adjoin_insert_eq (O := O) i g hgi (e * d κ) gens (Set.range x) hgB ?_ ?_
    · rintro _ ⟨⟨τ, ⟨a, b⟩, h⟩, rfl⟩
      rw [← hux τ a b h]
      exact hug _ _ _
    · set R' := Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) : Set F) ∪
        Set.range x) with hR'
      have hA : ∀ a, g a ∈ R' := fun a =>
        Algebra.subset_adjoin (Or.inl ⟨i a, Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩), (hgi a).symm⟩)
      have hI : (g (e * d κ))⁻¹ ∈ R' :=
        Algebra.subset_adjoin (Or.inl ⟨(i (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl), by rw [map_inv₀, hgi]⟩)
      intro y hy
      rcases hgens y hy with ⟨a, rfl⟩ | ⟨τ, a, b, rfl⟩
      · exact hA a
      · have hdτ := hg0 _ ((hd κ).mp hκ τ)
        rw [eq_of_rows _ (hrΩ τ) _ (hg0 _ (hαN τ)) (ix τ) (κ τ) (by rw [hdet]; exact hdτ) (u τ) (hu2 τ), hu1,
          Matrix.mul_apply]
        refine R'.sum_mem fun k _ => R'.mul_mem (mul_inv_mem R' (((p τ).map g).submatrix id (κ τ))
          (((p τ).map g).submatrix (ix τ) (κ τ)) (fun _ _ => hA _) (fun _ _ => hA _) ?_ _ _) ?_
        · obtain ⟨w, hw⟩ : ((p τ).submatrix (ix τ) (κ τ)).det ∣ e * d κ :=
            Dvd.dvd.mul_left (hdd κ ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) e
          have hw0 : g w ≠ 0 := hg0 _ fun h => mul_ne_zero (hes e he) hκ (by rw [hw, h, mul_zero])
          have : (g ((p τ).submatrix (ix τ) (κ τ)).det)⁻¹ = (g (e * d κ))⁻¹ * g w := by
            rw [hw, map_mul]; field_simp
          rw [hdet, this]
          exact R'.mul_mem hI (hA w)
        · simp only [ℓ, genLower]
          split_ifs
          · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
          · exact R'.one_mem
          · exact R'.zero_mem
  have hP := fun e he κ hκ => hpoly _ _ (hR e he κ hκ)
  have hAR : ∀ e' a, g a ∈ Algebra.adjoin K (insert e' (gens : Set Ω)) := by
    intro e' a
    have : Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω)) ≤
        (Algebra.adjoin K (insert e' (gens : Set Ω))).toSubring := by
      rw [Subring.closure_le]
      rintro w (⟨o, rfl⟩ | hw)
      · exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin (Or.inr hw)
    exact this (hgB a)
  have hA₀ : ∀ a₀ a, i a ∈ Algebra.adjoin K (insert a₀ (Set.range i)) := fun a₀ a =>
    Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  have hκ₀' := (hd κ₀).mpr hκ₀
  refine ⟨Ω, inferInstance, inferInstance, gens, es', g, u, ?_, ⟨_, hes'' e₁ he₁ κ₀ hκ₀'⟩, ?_, hgB, hug, hgens,
    hcell, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hP e₁ he₁ κ₀ hκ₀').2.1 (fun z => by
      obtain ⟨a, b, h1, h2⟩ := hfr z
      exact ⟨i a, hA₀ _ a, i b, hA₀ _ b, h1, h2⟩) y
    have hle : ∀ z ∈ Algebra.adjoin K (insert (g (e₁ * d κ₀))⁻¹ (gens : Set Ω)),
        z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := by
      intro z hz
      rw [Algebra.mem_adjoin_iff] at hz
      refine (Subring.closure_le (t := (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))).toSubring)).mpr
        ?_ hz
      rintro w (hw | rfl | hw)
      · exact Subfield.subset_closure (Or.inl hw)
      · refine Subfield.inv_mem _ ((Subring.closure_le
          (t := (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))).toSubring)).mpr ?_ (hgB _))
        rintro w (⟨o, rfl⟩ | hw)
        · exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
        · exact Subfield.subset_closure (Or.inr hw)
      · exact Subfield.subset_closure (Or.inr hw)
    rw [eq_div_of_mul_eq hb0 hab]
    exact Subfield.div_mem _ (hle a ha) (hle b hb)
  · intro e' he'
    obtain ⟨e, he, κ, hκ, rfl⟩ := hes' e' he'
    exact ⟨hg0 _ (mul_ne_zero (hes e he) hκ), hgB _⟩
  · intro e' he'
    obtain ⟨e, he, κ, hκ, rfl⟩ := hes' e' he'
    have hed := mul_ne_zero (hes e he) hκ
    constructor
    · refine (hP e he κ hκ).1 ?_
      set R₀ := Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) with hR₀
      let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring (hA₀ _)
      have hi₀ : ∀ o, i₀ (α o) = algebraMap K R₀ (algebraMap O K o) := fun o =>
        Subtype.ext (RingHom.congr_fun hiα o)
      have hun : IsUnit (i₀ e * i₀ (d κ)) := by
        rw [← map_mul]
        exact IsUnit.of_mul_eq_one (⟨(i (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
          (Subtype.ext (mul_inv_cancel₀ (hi0 _ hed)))
      refine hsm e he R₀ i₀ (RingHom.ext hi₀) (isUnit_of_mul_isUnit_left hun) (d κ)
        (fun a b h => hi (congrArg Subtype.val h)) (isUnit_of_mul_isUnit_right hun) fun z => ?_
      obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hiα (e * d κ) (hi0 _ hed) z z.2
      have hb' : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hb
      refine ⟨a, (algebraMap O K b)⁻¹, m, ?_⟩
      have h' : z * i₀ (α b * (e * d κ) ^ m) = i₀ a := Subtype.ext h
      rw [← h', map_mul i₀ (α b), hi₀, map_pow]
      have : algebraMap K R₀ (algebraMap O K b)⁻¹ * algebraMap K R₀ (algebraMap O K b) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hb', map_one]
      linear_combination (-(z * i₀ (e * d κ) ^ m)) * this
    · set R := Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω)) with hRdef
      let fe : A →+* R := g.codRestrict R.toSubring (hAR _)
      let ue : ∀ τ, Matrix (Fin n) (Fin (r τ)) R := fun τ a b =>
        ⟨u τ a b, Algebra.subset_adjoin (Or.inr (hug τ a b))⟩
      have hun : IsUnit (fe e * fe (d κ)) := by
        rw [← map_mul]
        exact IsUnit.of_mul_eq_one (⟨(g (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R)
          (Subtype.ext (mul_inv_cancel₀ (hg0 _ hed)))
      have hpu : ∀ τ, (p τ).map fe * ue τ = fe (α (N τ)) • ue τ := by
        intro τ
        ext a b
        have := congrFun (congrFun (hu2 τ) a) b
        simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        rw [AddSubmonoidClass.coe_finset_sum]
        exact this
      refine ⟨fe, ue, fun _ => rfl, fun _ _ _ => rfl, RingHom.ext fun o => Subtype.ext (hgα' o),
        ⟨e, he, isUnit_of_mul_isUnit_left hun⟩, hpu, fun τ y hy => ?_⟩
      have hmap : ((p τ).map fe).map R.val = (p τ).map g := by
        ext a b
        rfl
      refine basis_over_subalgebra R (ix τ) (κ τ) ((p τ).map fe) (fe (α (N τ)))
        (fun h => hg0 _ (hαN τ) (congrArg Subtype.val h)) (by rw [hmap]; exact hrΩ τ)
        ?_ (ue τ) (hpu τ) ⟨fun a b h => Subtype.ext ((hcell τ).1 a b h), fun a => Subtype.ext ((hcell τ).2 a)⟩ y hy
      rw [hmap, hdet]
      exact hg0 _ ((hd κ).mp hκ τ)
  · intro L _ _ f hf e he hfe u' hu' hc'
    have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
    have hfN : ∀ τ, f (α (N τ)) ≠ 0 := fun τ => by
      rw [hf']
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (hN τ))
    choose κ hκL using fun τ => exists_minor _ _ (hfN τ) (ix τ) (u' τ) (hu' τ) (hc' τ)
    have hfd : f (d κ) ≠ 0 := by
      simp only [hdd, map_prod, Finset.prod_ne_zero_iff]
      exact fun τ _ => hdet f τ (κ τ) ▸ hκL τ
    have hκ : d κ ≠ 0 := fun h => hfd (by rw [h, map_zero])
    have hed := mul_ne_zero (hes e he) hκ
    obtain ⟨ψ₀, hψ₀⟩ := loc_lift α i hi hiα (e * d κ) (hi0 _ hed) f hf (by rw [map_mul]; exact mul_ne_zero hfe hfd)
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := (hP e he κ hκ).2.2 L ψ₀ (fun v => u' v.1 (ix v.1 v.2.1.1) v.2.1.2)
    have hψA : ∀ a (h : g a ∈ Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω))), ψ ⟨g a, h⟩ = f a :=
      fun a h => (congrArg ψ (Subtype.ext (hgi a))).trans
        ((hψ1 ⟨i a, hA₀ _ a⟩ (by rw [← hgi a]; exact h)).trans (hψ₀ a _))
    refine ⟨_, hes'' e he κ hκ, ψ, hψA, fun τ a b h => ?_⟩
    let R := Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω))
    let ue : Matrix (Fin n) (Fin (r τ)) R := fun a b => ⟨u τ a b, Algebra.subset_adjoin (Or.inr (hug τ a b))⟩
    have hpu : (p τ).map f * ue.map ψ = f (α (N τ)) • ue.map ψ := by
      ext a b
      have h0 := congrFun (congrFun (hu2 τ) a) b
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h0 ⊢
      have h1 : ∑ j, (⟨g (p τ a j), hAR _ _⟩ : R) * ue j b = (⟨g (α (N τ)), hAR _ _⟩ : R) * ue a b := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        exact h0
      have h2 := congrArg ψ h1
      rw [map_sum ψ, map_mul ψ ⟨g (α (N τ)), _⟩, hψA] at h2
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
      rw [map_mul ψ, hψA]
      rfl
    have hrow : (ue.map ψ).submatrix (ix τ) id = (u' τ).submatrix (ix τ) id := by
      ext a b
      show ψ (ue (ix τ a) b) = u' τ (ix τ a) b
      rcases lt_trichotomy a b with h | rfl | h
      · rw [(hc' τ).1 a b h, show ue (ix τ a) b = 0 from Subtype.ext ((hcell τ).1 a b h), map_zero]
      · rw [(hc' τ).2 a, show ue (ix τ a) a = 1 from Subtype.ext ((hcell τ).2 a), map_one]
      · have hm : x ⟨τ, ⟨(a, b), h⟩⟩ ∈ R := hux τ a b h ▸ (ue (ix τ a) b).2
        rw [show ue (ix τ a) b = ⟨x ⟨τ, ⟨(a, b), h⟩⟩, hm⟩ from Subtype.ext (hux τ a b h)]
        exact hψ2 ⟨τ, ⟨(a, b), h⟩⟩ hm
    have e1 := eq_of_rows _ (hrk L f hf e he hfe τ) _ (hfN τ) (ix τ) (κ τ) (hκL τ) _ hpu
    have e2 := eq_of_rows _ (hrk L f hf e he hfe τ) _ (hfN τ) (ix τ) (κ τ) (hκL τ) _ (hu' τ)
    rw [hrow, ← e2] at e1
    exact congrFun (congrFun e1 a) b

end GlobalTheory.Reg.CellChart
