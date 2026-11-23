import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.UnitVectorStabiliser

section General

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)

theorem hf_add_right (x y z : n → A) : hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_add_left (x y z : n → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hf_smul_right (c : A) (x y : n → A) : hform s J x (c • y) = c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_smul_left (c : A) (x y : n → A) : hform s J (c • x) y = s c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_herm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : n → A) :
    s (hform s J x y) = hform s J y x := by
  simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hf_eq (x y : n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hf_mulVec (g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hf_eq, hf_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT s g)]
  congr 1
  funext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem hf_single (i j : n) : hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]

def hfLin (x : n → A) : (n → A) →ₗ[A] A where
  toFun := hform s J x
  map_add' := hf_add_right s J x
  map_smul' c y := hf_smul_right s J c x y

theorem exists_proj (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) :
    ∃ (c : (n → A) →ₗ[A] A) (p : (n → A) →ₗ[A] P), (∀ y, y = c y • x + (p y : n → A)) ∧
      c x = 1 ∧ ∀ y : P, c y = 0 := by
  obtain ⟨b, hb⟩ := hx.exists_left_inv
  refine ⟨b • hfLin s J x,
    LinearMap.codRestrict P (LinearMap.id - (b • hfLin s J x).smulRight x) fun y => ?_,
    fun y => ?_, hb, fun y => ?_⟩
  · rw [hP]
    show hfLin s J x (y - (b * hfLin s J x y) • x) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    have : b * hfLin s J x x = 1 := hb
    linear_combination (- hfLin s J x y) * this
  · show y = (b * hfLin s J x y) • x + (y - (b * hfLin s J x y) • x)
    abel
  · show b * hform s J x y = 0
    rw [(hP y).1 y.2, mul_zero]

theorem exists_extend (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hd : IsUnit J.det) (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) (u : P →ₗ[A] P)
    (hu : ∀ y z : P, hform s J (u y) (u z) = hform s J y z) :
    ∃ g : GL n A, g ∈ UJ s J ∧ (g : Matrix n n A) *ᵥ x = x ∧
      ∀ y : P, (g : Matrix n n A) *ᵥ y = u y := by
  obtain ⟨c, p, h1, h2, h3⟩ := exists_proj s J x hx P hP
  let f : (n → A) →ₗ[A] (n → A) := c.smulRight x + P.subtype ∘ₗ u ∘ₗ p
  have hf : ∀ y, f y = c y • x + (u (p y) : n → A) := fun y => rfl
  have o1 : ∀ y : P, hform s J x y = 0 := fun y => (hP y).1 y.2
  have o2 : ∀ y : P, hform s J y x = 0 := fun y => by rw [← hf_herm s J hs hJ, o1, map_zero]
  have hiso : ∀ y z, hform s J (f y) (f z) = hform s J y z := by
    intro y z
    conv_rhs => rw [h1 y, h1 z]
    simp only [hf, hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, o1, o2, hu]
  have hg : cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f = J := by
    ext i j
    rw [← hf_single s (cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f) i j, ← hf_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hiso,
      hf_single]
  have hdet : IsUnit (LinearMap.toMatrix' f).det := by
    rw [← hg, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨g, hg'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨g, ?_, ?_, fun y => ?_⟩
  · show cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
    rw [hg', hg]
  · have : p x = 0 := by
      have := h1 x
      rw [h2, one_smul] at this
      exact Subtype.ext (by simpa using this)
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h2, this]
    simp
  · have : p y = y := by
      have := h1 y
      rw [h3, zero_smul, zero_add] at this
      exact Subtype.ext this.symm
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h3, this]
    simp

end General

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem mem_stabVec (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

theorem act_mul (g h : HA (Fv F v) σ J) (x : Fin M → Ev F E v) :
    act σ J v (g * h) x = act σ J v g (act σ J v h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : Fin M → Ev F E v) : act σ J v 1 x = x := Matrix.one_mulVec x

theorem hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by
  unfold hR act
  rw [hf_mulVec]
  congr 1
  exact (show HR (Fv F v) σ J from g).2

theorem act_mem_perp_iff (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x)
    (y : Fin M → Ev F E v) : act σ J v g y ∈ perp σ J v x ↔ y ∈ perp σ J v x := by
  show hR (Fv F v) σ J x (act σ J v g y) = 0 ↔ hR (Fv F v) σ J x y = 0
  rw [← hR_act σ J v g x y, (mem_stabVec σ J v x g).1 hg]

def restr (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x) :
    perp σ J v x ≃ₗ[Ev F E v] perp σ J v x where
  toFun y := ⟨act σ J v g y, (act_mem_perp_iff σ J v x g hg y).2 y.2⟩
  invFun y := ⟨act σ J v g⁻¹ y, (act_mem_perp_iff σ J v x g⁻¹ (inv_mem hg) y).2 y.2⟩
  map_add' y z := Subtype.ext (by
    show act σ J v g (y.1 + z.1) = act σ J v g y.1 + act σ J v g z.1
    unfold act
    rw [Matrix.mulVec_add])
  map_smul' c y := Subtype.ext (by
    show act σ J v g (c • y.1) = c • act σ J v g y.1
    unfold act
    rw [Matrix.mulVec_smul])
  left_inv y := Subtype.ext (by
    show act σ J v g⁻¹ (act σ J v g y) = y
    rw [← act_mul, inv_mul_cancel, act_one])
  right_inv y := Subtype.ext (by
    show act σ J v g (act σ J v g⁻¹ y) = y
    rw [← act_mul, mul_inv_cancel, act_one])

def restrHom (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v) :
    (stabLat σ J v L' ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) →*
      unitaryLatIn σ J v (perp σ J v x) L' where
  toFun g := ⟨restr σ J v x g g.2.2, fun y z => hR_act σ J v g y z, fun y => g.2.1 y⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_one σ J v y))
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_mul σ J v g h y))

theorem restrHom_injective (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) : Function.Injective (restrHom σ J v L' x) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, p, h1, -, -⟩ := exists_proj _ _ x hx (perp σ J v x) (fun _ => Iff.rfl)
  have h0 : ∀ y : perp σ J v x, act σ J v g y = y := fun y =>
    congrArg (fun u : unitaryLatIn σ J v (perp σ J v x) L' =>
      ((u.1 y : perp σ J v x) : Fin M → Ev F E v)) hg
  have hx' := (mem_stabVec σ J v x g).1 g.2.2
  have h2 : ∀ y, act σ J v g y = y := by
    intro y
    rw [h1 y]
    have := h0 (p y)
    unfold act at *
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx', this]
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  exact (h2 y).trans (act_one σ J v y).symm

theorem restrHom_surjective (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) :
    Function.Surjective (restrHom σ J v (perpLat σ J v L x) x) := by
  rintro ⟨u, hu, hu'⟩
  have hJ' : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J j i) = JR (Fv F v) J i j := by
    intro i j
    show (1 : Fv F v) ⊗ₜ[F] σ (J j i) = (1 : Fv F v) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hd : IsUnit (JR (F := F) (Fv F v) J).det := by
    have := (RingHom.map_det (inclR (F := F) (Fv F v)) J)
    rw [show JR (F := F) (Fv F v) J = (inclR (F := F) (Fv F v)).mapMatrix J from rfl, ← this]
    exact (hJ.2.isUnit).map _
  obtain ⟨g, hg, hgx, hgu⟩ := exists_extend _ _
    (GlobalTheory.SelfDualLatticeCompare.sigR_sigR (Fv F v) h) hJ' hd x hx (perp σ J v x)
    (fun _ => Iff.rfl) u.toLinearMap hu
  let g' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hv : g' ∈ stabVec σ J v x := (mem_stabVec σ J v x g').2 hgx
  have hgu' : ∀ y : perp σ J v x, act σ J v g' y = u y := hgu
  have hl : g' ∈ stabLat σ J v (perpLat σ J v L x) := by
    show ∀ y, y ∈ perpLat σ J v L x ↔ act σ J v g' y ∈ perpLat σ J v L x
    intro y
    by_cases hy : y ∈ perp σ J v x
    · rw [hgu' ⟨y, hy⟩]
      exact hu' ⟨y, hy⟩
    · exact ⟨fun h => (hy h.1).elim,
        fun h => (hy ((act_mem_perp_iff σ J v x g' hv y).1 h.1)).elim⟩
  exact ⟨⟨g', hl, hv⟩, Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (hgu' y))⟩

end Place

theorem stabiliser_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), ∀ x : Fin M → Ev F E v, IsUnit (hR (Fv F v) σ J x x) → ∃ φ : (stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃* unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x), ∀ g (y : perp σ J v x), (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) = act σ J v (g : HA (Fv F v) σ J) y := by
  intro F E _ _ _ _ _ σ h M J hJ v L x hx
  exact ⟨MulEquiv.ofBijective (restrHom σ J v (perpLat σ J v L x) x)
    ⟨restrHom_injective σ J v _ x hx, restrHom_surjective σ J v h hJ L x hx⟩, fun _ _ => rfl⟩

end GlobalTheory.UnitVectorStabiliser
