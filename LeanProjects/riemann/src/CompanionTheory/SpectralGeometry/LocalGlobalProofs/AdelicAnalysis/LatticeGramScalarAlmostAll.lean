import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermConstantsEqAlongAffineSpaceSquare
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodTrans

theorem transit_ring {T : Type} [CommRing T] (O : Subring T) (s : T →+* T)
    (hs : ∀ y ∈ O, s y ∈ O) (hss : ∀ y, s (s y) = y) {M : ℕ} (JT : Matrix (Fin M) (Fin M) T)
    (hJO : ∀ i j, JT i j ∈ O) (hJ : ∀ i j, s (JT j i) = JT i j) (x y : Fin M → T)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (hxy : hform s JT x x = hform s JT y y)
    (w : T) (hw : w ∈ O) (hxw : hform s JT x x * w = 1)
    (hgood : ∀ p β : O, IsUnit β → s β = β → ∃ ε z : O,
      (ε : T) * s ε = 1 ∧ ((β : T) - s ε * p) * z = 1) :
    ∃ g ∈ UJ s JT, (g : Matrix (Fin M) (Fin M) T) *ᵥ x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) T) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) i j ∈ O := by
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨JT i j, hJO i j⟩
  let x0 : Fin M → O := fun i => ⟨x i, hx i⟩
  let y0 : Fin M → O := fun i => ⟨y i, hy i⟩
  have hcoe : ∀ p q : Fin M → O, ((hform τ JO p q : O) : T) =
      hform s JT (fun i => (p i : T)) (fun i => (q i : T)) := by
    intro p q
    simp [hform, hτ, JO]
  have hβ0 : ((hform τ JO x0 x0 : O) : T) = hform s JT x x := hcoe x0 x0
  have hxy0 : hform τ JO x0 x0 = hform τ JO y0 y0 := Subtype.ext (by
    rw [hβ0, hxy]; exact (hcoe y0 y0).symm)
  have hunit : IsUnit (hform τ JO x0 x0) :=
    IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext (by
      rw [Subring.coe_mul, hβ0]; exact hxw))
  have hτinv : ∀ a : O, τ (τ a) = a := fun a => Subtype.ext (hss a)
  have hJ0 : ∀ i j, τ (JO j i) = JO i j := fun i j => Subtype.ext (hJ i j)
  have hfix : s (hform τ JO x0 x0 : O) = (hform τ JO x0 x0 : O) := by
    have := GlobalTheory.CompanionTheory.SW.QuasiRefl.hform_conj_symm hτinv hJ0 x0 x0
    exact congrArg Subtype.val this
  obtain ⟨ε, z, hε, hz⟩ := hgood (hform τ JO y0 x0) _ hunit hfix
  have hε' : ε * τ ε = 1 := Subtype.ext hε
  have hu : IsUnit (hform τ JO x0 x0 - τ ε * hform τ JO y0 x0) :=
    IsUnit.of_mul_eq_one z (Subtype.ext hz)
  obtain ⟨g0, hg0, hgx, -⟩ := GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry O τ hτinv M JO hJ0 x0 y0 ε
    hxy0 hunit hε' hu
  have hval : ∀ g : GL (Fin M) O, ((bc O.subtype g : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) =
      (g : Matrix (Fin M) (Fin M) O).map O.subtype := fun g => rfl
  refine ⟨bc O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin M) (Fin M) O) * JO * (g0 : Matrix (Fin M) (Fin M) O) = JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) * JT *
      ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) = JT
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin M) (Fin M) O)) =
        cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype JO = JT := by
      ext i j
      rfl
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin M) (Fin M) O) =
        ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have := congrArg Subtype.val (congrFun hgx i)
    simpa [Matrix.mulVec, dotProduct, hval, x0, y0] using this
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin M) (Fin M) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin M) O) : Matrix (Fin M) (Fin M) O) i j).2

theorem mem_latV_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
  ⟨fun h a i => (hO _).2 (h a i), fun h a i => (hO _).1 (h a i)⟩

theorem mulVec_mem {T : Type} [CommRing T] (O : Subring T) {M : ℕ} (g : Matrix (Fin M) (Fin M) T)
    (hg : ∀ i j, g i j ∈ O) (x : Fin M → T) (hx : ∀ i, x i ∈ O) (i : Fin M) : (g *ᵥ x) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hg i j) (hx j)

theorem good_trans : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ h M J hJ t ht d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, I.2 t ht,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j)] with v hring hv hJv
  obtain ⟨O, hO, hstab, -, -, -, hgood, -⟩ := hring
  intro x y hx hy hxt hyx
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hc : ∀ c : Fv F v, c ∈ v.adicCompletionIntegers F → c ⊗ₜ[F] (1 : E) ∈ O := by
    intro c hcv
    refine (hO _).2 fun k => ?_
    have e : c ⊗ₜ[F] (1 : E) = c • (1 : Fv F v ⊗[F] E) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hcv ((hO 1).1 O.one_mem k)
  set c : Fv F v := algebraMap F (Fv F v) t with hcdef
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hβ : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) = c ⊗ₜ[F] (1 : E) :=
    congrFun (congrFun hxt 0) 0
  have hxy : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) =
      hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (y 0) :=
    (congrFun (congrFun hyx 0) 0).symm
  have hci : c⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hmul : c ⊗ₜ[F] (1 : E) * c⁻¹ ⊗ₜ[F] (1 : E) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hc0, mul_one,
      Algebra.TensorProduct.one_def]
  obtain ⟨g, hg, hgx, hgO, hgiO⟩ := transit_ring O (sigR (Fv F v) σ) hstab hss (JR (Fv F v) J)
    (fun i j => (hO _).2 (hJv i j))
    (fun i j => by
      show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
      rw [← hJ.1 i j]
      rfl)
    (x 0) (y 0) (fun i => (hO _).2 (hx 0 i)) (fun i => (hO _).2 (hy 0 i)) hxy
    (c⁻¹ ⊗ₜ[F] (1 : E)) (hc _ hci) (by rw [hβ, hmul]) hgood
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ {n : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  refine ⟨h', ?_, fun n X => ?_⟩
  · funext a
    rw [hact, Fin.fin_one_eq_zero a, hgx]
  · rw [mem_latV_iff b v O hO, mem_latV_iff b v O hO]
    constructor
    · intro hX a i
      have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
          ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [e]
      exact mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
    · intro hX a i
      rw [hact]
      exact mulVec_mem O _ hgO _ (hX a) i

end GlobalTheory.CompanionTheory.SW.GoodTrans
