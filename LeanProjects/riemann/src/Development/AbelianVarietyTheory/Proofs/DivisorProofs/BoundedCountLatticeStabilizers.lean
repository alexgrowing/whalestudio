import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCountFiniteIndexSubgroupsStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.StabClassCount

section Abstract

variable {ι A G : Type} [AddCommGroup A] [Group G] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  (Λ : ∀ i, AddSubgroup (V i)) (φ : ∀ i, A →+ V i) (ρ : ∀ i, G →* AddMonoid.End (V i)) (m : ℕ)

def sub (g : G) : AddSubgroup A := ⨅ i, ((Λ i).map (m • (ρ i g : V i →+ V i))).comap (φ i)

theorem mem_sub {g : G} {x : A} : x ∈ sub Λ φ ρ m g ↔ ∀ i, ∃ y ∈ Λ i, m • ρ i g y = φ i x := by
  simp only [sub, AddSubgroup.mem_iInf, AddSubgroup.mem_comap, AddSubgroup.mem_map]
  rfl

theorem act_mul (i : ι) (g h : G) (y : V i) : ρ i (g * h) y = ρ i g (ρ i h y) := by
  rw [map_mul]; rfl

theorem act_inv (i : ι) (g : G) (y : V i) : ρ i g (ρ i g⁻¹ y) = y := by
  rw [← act_mul, mul_inv_cancel, map_one]; rfl

theorem inv_act (i : ι) (g : G) (y : V i) : ρ i g⁻¹ (ρ i g y) = y := by
  rw [← act_mul, inv_mul_cancel, map_one]; rfl

theorem smul_act_smul (i : ι) (g : G) (z : V i) : m • ρ i g (m • ρ i g⁻¹ z) = m ^ 2 • z := by
  rw [map_nsmul, act_inv, smul_smul, sq]

variable {Λ φ ρ m}

theorem keep (htf : ∀ i (x : V i), m • x = 0 → x = 0)
    (happ : ∀ v, ∀ y ∈ Λ v, ∃ x, (∃ z ∈ Λ v, φ v x = y + m ^ 2 • z) ∧ ∀ u, u ≠ v → ∃ z ∈ Λ u, φ u x = m ^ 2 • z)
    {g x : G} (hg : ∀ v, ∀ y ∈ Λ v, m • ρ v g y ∈ Λ v ∧ m • ρ v g⁻¹ y ∈ Λ v)
    (hx : ∀ v, ∀ y ∈ Λ v, m • ρ v x y ∈ Λ v ∧ m • ρ v x⁻¹ y ∈ Λ v)
    (e : sub Λ φ ρ m g ≤ sub Λ φ ρ m x) (v : ι) {y : V v} (hy : y ∈ Λ v) : ρ v (x⁻¹ * g) y ∈ Λ v := by
  obtain ⟨a, ⟨z, hz, h1⟩, h2⟩ := happ v _ (hg v y hy).1
  have ha : a ∈ sub Λ φ ρ m g := by
    refine (mem_sub Λ φ ρ m).2 fun u => ?_
    by_cases hu : u = v
    · subst hu
      exact ⟨y + m • ρ u g⁻¹ z, add_mem hy (hg u z hz).2, by rw [map_add, smul_add, smul_act_smul, h1]⟩
    · obtain ⟨w, hw, h3⟩ := h2 u hu
      exact ⟨m • ρ u g⁻¹ w, (hg u w hw).2, by rw [smul_act_smul, h3]⟩
  obtain ⟨y', hy', h4⟩ := (mem_sub Λ φ ρ m).1 (e ha) v
  have h5 := congrArg (ρ v x⁻¹) (h4.trans h1)
  rw [map_nsmul, inv_act, map_add, map_nsmul, map_nsmul, ← act_mul] at h5
  have h6 : ρ v (x⁻¹ * g) y = y' - m • ρ v x⁻¹ z := by
    refine sub_eq_zero.1 (htf v _ ?_)
    rw [smul_sub, smul_sub, h5, smul_smul, sq]
    abel
  rw [h6]
  exact sub_mem hy' (hx v z hz).2

theorem count (hφ : ∀ i x, φ i x ∈ Λ i) (htf : ∀ i (x : V i), m • x = 0 → x = 0)
    (happ : ∀ v, ∀ y ∈ Λ v, ∃ x, (∃ z ∈ Λ v, φ v x = y + m ^ 2 • z) ∧ ∀ u, u ≠ v → ∃ z ∈ Λ u, φ u x = m ^ 2 • z)
    (T : Finset (AddSubgroup A)) (hT : ∀ H : AddSubgroup A, (∀ x, m ^ 2 • x ∈ H) → H ∈ T) :
    ∃ T' : Finset G, T'.card ≤ T.card ∧ ∀ g : G, (∀ v, ∀ y ∈ Λ v, m • ρ v g y ∈ Λ v ∧ m • ρ v g⁻¹ y ∈ Λ v) →
      ∃ x ∈ T', ∀ v y, y ∈ Λ v ↔ ρ v (x⁻¹ * g) y ∈ Λ v := by
  classical
  let S : G → Prop := fun g => ∀ v, ∀ y ∈ Λ v, m • ρ v g y ∈ Λ v ∧ m • ρ v g⁻¹ y ∈ Λ v
  let f : AddSubgroup A → G := fun H => if h : ∃ g, S g ∧ sub Λ φ ρ m g = H then h.choose else 1
  refine ⟨T.image f, Finset.card_image_le, fun g hg => ?_⟩
  have h : ∃ x, S x ∧ sub Λ φ ρ m x = sub Λ φ ρ m g := ⟨g, hg, rfl⟩
  have hf : f (sub Λ φ ρ m g) = h.choose := dif_pos h
  obtain ⟨hx, e⟩ := h.choose_spec
  refine ⟨h.choose, hf ▸ Finset.mem_image_of_mem f (hT _ fun a => ?_), fun v y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · exact (mem_sub Λ φ ρ m).2 fun u =>
      ⟨m • ρ u g⁻¹ (φ u a), (hg u _ (hφ u a)).2, by rw [smul_act_smul, map_nsmul]⟩
  · exact keep htf happ hg hx e.ge v hy
  · have := keep htf happ hx hg e.le v hy
    rwa [← act_mul, show g⁻¹ * h.choose * (h.choose⁻¹ * g) = 1 by group, map_one] at this

end Abstract

def colAct (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R →* AddMonoid.End (Fin n → R) where
  toFun g := (Matrix.mulVecLin g.1).toAddMonoidHom
  map_one' := AddMonoidHom.ext fun y => Matrix.one_mulVec y
  map_mul' g h := AddMonoidHom.ext fun y => (Matrix.mulVec_mulVec y g.1 h.1).symm

theorem exists_card_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] :
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → ∃ T : Finset (GAd σ J), T.card ≤ m ^ c ∧ ∀ g : GAd σ J,
      (∀ v, ∀ y ∈ latLoc F L v, m • ((matHom (Fv F v) σ J (proj σ J v g)).1 *ᵥ y) ∈ latLoc F L v ∧
        m • ((matHom (Fv F v) σ J (proj σ J v g)⁻¹).1 *ᵥ y) ∈ latLoc F L v) →
      ∃ x ∈ T, ∀ v, (proj σ J v x)⁻¹ * proj σ J v g ∈ stabLoc σ J L v := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (A := E))
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨c, hc⟩ := GlobalTheory.T.bounded_count_finite_index_subgroups L
  refine ⟨2 * c, fun m hm => ?_⟩
  obtain ⟨T, hT, hT'⟩ := hc (m ^ 2) (pow_pos hm 2)
  let φ : ∀ v : HeightOneSpectrum (𝓞 F), L →+ (Fin n → Fv F v ⊗[F] E) := fun v =>
    { toFun := fun x i => (1 : Fv F v) ⊗ₜ[F] x.1 i
      map_zero' := funext fun i => TensorProduct.tmul_zero _ _
      map_add' := fun x y => funext fun i => TensorProduct.tmul_add _ _ _ }
  let ρ : ∀ v : HeightOneSpectrum (𝓞 F), GAd σ J →* AddMonoid.End (Fin n → Fv F v ⊗[F] E) := fun v =>
    (colAct n _).comp ((matHom (Fv F v) σ J).comp (proj σ J v))
  obtain ⟨T', h1, h2⟩ := count (Λ := fun v => (latLoc F L v).toAddSubgroup) (φ := φ) (ρ := ρ) (m := m)
    (fun v x => tmul_mem_latLoc (one_mem _) x.2)
    (fun v x hx => by
      rw [← Nat.cast_smul_eq_nsmul F] at hx
      exact (smul_eq_zero.1 hx).resolve_left (Nat.cast_ne_zero.2 hm.ne'))
    (fun v y hy => by
      obtain ⟨x, hx, h⟩ := GlobalTheory.T.strong_approximation_lattice F E n L (m ^ 2) (pow_pos hm 2) v y hy
      exact ⟨⟨x, hx⟩, h⟩) T hT'
  refine ⟨T', h1.trans (by rwa [pow_mul]), fun g hg => ?_⟩
  obtain ⟨x, hx, h3⟩ := h2 g fun v y hy => ⟨(hg v y hy).1, by
    have := (hg v y hy).2
    rwa [← map_inv] at this⟩
  refine ⟨x, hx, fun v => mem_stabLoc.2 fun y => ?_⟩
  rw [← map_inv, ← map_mul]
  exact h3 v y

end GlobalTheory.StabClassCount
