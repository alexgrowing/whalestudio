import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProLUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_prime_power_pow_eq_one (l n N : ℕ) {B E : Type} [CommRing B] [Ring E] [Algebra B E] (m : Ideal B)
    (hN : ∀ a ∈ m ^ N, algebraMap B E a = 0) (hl : (l : B) ∈ m) (x : E) (p : Polynomial B)
    (hp : Polynomial.aeval x p = 0) (hc : ∀ i, (p - (Polynomial.X - 1) ^ n).coeff i ∈ m) :
    ∃ e : ℕ, x ^ l ^ e = 1 := by
  let K : Ideal (Polynomial B) := RingHom.ker (Polynomial.aeval x : Polynomial B →ₐ[B] E)
  have hm : m.map Polynomial.C ≤ K.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine ⟨N, ?_⟩
    show Polynomial.aeval x (Polynomial.C a ^ N) = 0
    rw [← map_pow, Polynomial.aeval_C]
    exact hN _ (Ideal.pow_mem_pow ha N)
  have h1 : (Polynomial.X - 1 : Polynomial B) ∈ K.radical := by
    have h2 : p ∈ K.radical := Ideal.le_radical hp
    have h3 := K.radical.sub_mem h2 (hm (Ideal.mem_map_C_iff.2 hc))
    rw [sub_sub_cancel] at h3
    exact Ideal.mem_radical_of_pow_mem h3
  have h2 : (l : Polynomial B) ∈ K.radical := by
    have := hm (Ideal.mem_map_of_mem Polynomial.C hl)
    rwa [map_natCast] at this
  let J : Ideal (Polynomial B) := Ideal.span {(l : Polynomial B), Polynomial.X - 1}
  have hJ : J ≤ K.radical := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact h2
    · exact h1
  obtain ⟨j, hj⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (Submodule.fg_span (Set.toFinite _))
  have h4 := pow_mem_of_sub_one_mem l (Polynomial B) J.toTwoSided
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp))) j Polynomial.X
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp)))
  rw [Ideal.asIdeal_toTwoSided] at h4
  have h5 : Polynomial.aeval x ((Polynomial.X : Polynomial B) ^ l ^ j - 1) = 0 :=
    hj (Ideal.pow_le_pow_right (Nat.le_succ j) h4)
  refine ⟨j, ?_⟩
  simpa [sub_eq_zero] using h5

private theorem ch_mem {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    Polynomial.aeval y (D.chi y) ∈ TwoSidedIdeal.span D.CH := by
  rw [← UpperTheory.V.CA.d_toDet_CH]
  have h1 := (UpperTheory.V.CA.d_chS D.toDet A).1 (1 ⊗ₜ y)
  have h2 : D.toDet.chiS A (1 ⊗ₜ y) = D.chi y := by
    show D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    rw [map_sub, Algebra.TensorProduct.map_tmul, ofT_tmul, ofT_tmul, map_one, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  rw [h2] at h1
  have key : ∀ w ∈ Submodule.span A ((fun z : MonoidAlgebra A G => (1 : A) ⊗ₜ[A] z) '' (D.toDet.CH : Set (MonoidAlgebra A G))),
      Algebra.TensorProduct.lid A (MonoidAlgebra A G) w ∈ D.toDet.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      simpa using hz
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G)
    (h : ∀ i, χ i g = 1) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) = (Polynomial.X - 1) ^ n := by
  show (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  have : GDet.repAlg (diagRep χ) (Polynomial k) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)) =
      diagonal fun _ => Polynomial.X - 1 := by
    have e : diagRep χ g = 1 := by
      show diagonal (fun i => (χ i g : k)) = 1
      simp [h]
    ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, e, hab, Matrix.one_apply]
  rw [this, det_diagonal]
  simp

theorem UpperTheory.V.Pa.pl_chBar :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → ∀ (Z : Set (MonoidAlgebra B G.G₀)) (k : G.G₀), (k : G.Γ) ∈ PL l H → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar Z := by
  intro l _ L G n O _ _ _ hO _ r B _ _ _ u H _ _ hH hχ Z k hk
  simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
  intro N V
  generalize hS : (u.D.CH ∪ Z ∪ _ ∪ _ : Set (MonoidAlgebra B G.G₀)) = S
  let I := TwoSidedIdeal.span S
  have hsub := hS.trans_subset (TwoSidedIdeal.subset_span (s := S))
  let q : MonoidAlgebra B G.G₀ →ₐ[B] I.ringCon.Quotient := RingCon.mkₐ B I.ringCon
  have hq : ∀ a b, q a = q b ↔ a - b ∈ I := fun a b =>
    (RingCon.eq _).trans (TwoSidedIdeal.rel_iff I a b)
  have hq0 : ∀ a ∈ I, q a = 0 := fun a ha => by
    rw [← map_zero q, hq, sub_zero]; exact ha
  let f : G.G₀ →* I.ringCon.Quotient := (q : _ →* _).comp (MonoidAlgebra.of B G.G₀)
  have hf : ∀ g, g ∈ f.ker ↔ MonoidAlgebra.single g 1 - 1 ∈ I := fun g => by
    rw [← hq, map_one]; rfl
  have hV : V.toSubgroup ≤ f.ker := fun g hg => (hf g).2 (hsub (Or.inr ⟨g, hg, rfl⟩))
  let U : OpenNormalSubgroup G.G₀ :=
    { toSubgroup := f.ker
      isOpen' := Subgroup.isOpen_mono hV V.isOpen
      isNormal' := MonoidHom.normal_ker f }
  refine (hf k).1 (pl_sub l G.Γ H G.η.ker G.η_open hH U (fun h hh => ?_) k hk)
  have hl : (l : B) ∈ maximalIdeal B := by
    haveI := hO.char
    rw [← res_eq_zero_iff O, map_natCast, CharP.cast_eq_zero]
  have hchi : (u.D.chi (MonoidAlgebra.single h 1)).map (res O B : B →+* ResidueField O) = (Polynomial.X - 1) ^ n := by
    rw [← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, u.red, MonoidAlgebra.mapRingHom_single, map_one]
    exact chi_diag _ _ (hχ h hh)
  obtain ⟨e, he⟩ := exists_prime_power_pow_eq_one l n N (maximalIdeal B)
    (fun a ha => by
      rw [← q.commutes]
      exact hq0 _ (hsub (Or.inl (Or.inr ⟨a, ha, rfl⟩)))) hl (q (MonoidAlgebra.single h 1))
    (u.D.chi (MonoidAlgebra.single h 1))
    (by
      rw [Polynomial.aeval_algHom_apply]
      exact hq0 _ (TwoSidedIdeal.span_le.2 (fun z hz => hsub (Or.inl (Or.inl (Or.inl hz)))) (ch_mem u.D _)))
    (fun i => by
      rw [← res_eq_zero_iff O]
      show (res O B : B →+* ResidueField O) _ = 0
      rw [← Polynomial.coeff_map, Polynomial.map_sub, hchi]
      simp)
  refine ⟨e, ?_⟩
  show f (h ^ l ^ e) = 1
  rw [map_pow]
  exact he
