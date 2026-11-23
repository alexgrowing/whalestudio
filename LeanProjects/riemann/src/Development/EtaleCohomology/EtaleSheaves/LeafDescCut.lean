import Development.EtaleCohomology.EtaleSheaves.H1MultiplicativeGroup

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H1MultiplicativeGroup
open scoped TensorProduct

namespace LateralTheory.E.LeafDescCut

def d0 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeRight

def d1 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeLeft

def p12 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeLeft

def p13 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeRight

def p23 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.includeRight

def cob1 (A : Type) [CommRing A] (U : Cov A) : (U.B ⊗[A] U.B)ˣ →* (U.B ⊗[A] (U.B ⊗[A] U.B))ˣ :=
  Units.map (p13 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) /
    (Units.map (p12 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) *
      Units.map (p23 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)))

def cob0 (A : Type) [CommRing A] (U : Cov A) : U.Bˣ →* (U.B ⊗[A] U.B)ˣ :=
  Units.map (d0 A U : U.B →* U.B ⊗[A] U.B) / Units.map (d1 A U : U.B →* U.B ⊗[A] U.B)

def Z1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob1 A U).ker

def B1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob0 A U).range

abbrev Cech (A : Type) [CommRing A] (U : Cov A) : Type := Additive (Z1 A U ⧸ (B1 A U).subgroupOf (Z1 A U))

def cls (A : Type) [CommRing A] (U : Cov A) (u : Z1 A U) : Cech A U := Additive.ofMul (QuotientGroup.mk u)

def tmap (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) : (U.B ⊗[A] U.B)ˣ →* (V.B ⊗[A] V.B)ˣ :=
  Units.map (Algebra.TensorProduct.map g g : U.B ⊗[A] U.B →* V.B ⊗[A] V.B)

def LeafZMap : Prop := ∀ (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : (U.B ⊗[A] U.B)ˣ),
  u ∈ Z1 A U → tmap A U V g u ∈ Z1 A V

theorem mem_Z1_iff_cocycle (A : Type) [CommRing A] (U : Cov A) (u : (U.B ⊗[A] U.B)ˣ) :
    u ∈ Z1 A U ↔ p13 A U (u : U.B ⊗[A] U.B) = p12 A U u * p23 A U u := by
  rw [Z1, MonoidHom.mem_ker, cob1, MonoidHom.div_apply, div_eq_one, MonoidHom.mul_apply, Units.ext_iff]
  simp

abbrev g3 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) :
    U.B ⊗[A] (U.B ⊗[A] U.B) →ₐ[A] V.B ⊗[A] (V.B ⊗[A] V.B) :=
  Algebra.TensorProduct.map g (Algebra.TensorProduct.map g g)

theorem p12_tensorProduct_map_eq_g3_p12 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p12 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p12 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p12]

theorem p13_tensorProduct_map_eq_g3_p13 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p13 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p13 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p13]

theorem p23_tensorProduct_map_eq_g3_p23 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p23 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p23 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p23]

theorem zmap : LeafZMap := by
  intro A _ U V g u hu
  rw [mem_Z1_iff_cocycle] at hu ⊢
  have ht : ((tmap A U V g u : (V.B ⊗[A] V.B)ˣ) : V.B ⊗[A] V.B) = Algebra.TensorProduct.map g g (u : U.B ⊗[A] U.B) := rfl
  rw [ht, p12_tensorProduct_map_eq_g3_p12, p13_tensorProduct_map_eq_g3_p13, p23_tensorProduct_map_eq_g3_p23, hu, map_mul]

def LeafDescH : Prop := Hyps → ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerH A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : H ℤ (sp A) Gm 1) = c U (cls A U u)

def LeafDescP : Prop := ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerP A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : Additive (CommRing.Pic A)) = c U (cls A U u)

theorem goal_of (hH : LeafDescH) (hP : LeafDescP) : LateralTheory.E.H1MultiplicativeGroup.LeafDesc := by
  intro hy A _
  obtain ⟨cH, hcH⟩ := hH hy A
  obtain ⟨cP, hcP⟩ := hP A
  refine ⟨fun U => (cH U).symm.trans (cP U), ?_⟩
  intro U V g x hU hV
  obtain ⟨u, hu⟩ : ∃ u : Z1 A U, cls A U u = (cH U).symm ⟨x, hU⟩ := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul ((cH U).symm ⟨x, hU⟩))
    exact ⟨u, by rw [cls, hu]; rfl⟩
  let v : Z1 A V := ⟨tmap A U V g u, zmap A U V g u u.2⟩
  have h1 := hcH U V g u v rfl
  have h2 := hcP U V g u v rfl
  have hv : (cH V).symm ⟨x, hV⟩ = cls A V v := by
    apply (cH V).injective
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [h1, hu, AddEquiv.apply_symm_apply]
  simp only [AddEquiv.trans_apply]
  rw [← hu, hv, h2]

end LateralTheory.E.LeafDescCut
