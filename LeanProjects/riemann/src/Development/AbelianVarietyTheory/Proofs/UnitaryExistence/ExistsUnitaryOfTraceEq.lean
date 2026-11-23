import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgreeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunctionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfSpanEqTop

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CharRead

section Det

open GlobalTheory.AdLat
open scoped nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_add_nsmul {ι : Type} (N : ℕ) (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (d x : ι → RA F E) (hd : ∀ i, d i ∈ hat1 F (I i : Set E)) (hx : ∀ i, x i ∈ hat1 F (I i : Set E)) :
    ∃ w ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ i ∈ s, (d i + N • x i) = ∏ i ∈ s, d i + N • w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, e⟩ := ih
    simp only [Finset.prod_insert ha]
    have hm := (adelicCompletion_fractionalIdeal_properties F E).1 (I a) (∏ i ∈ s, I i)
    refine ⟨d a * w + x a * ∏ i ∈ s, d i + N • (x a * w), add_mem (add_mem (hm _ (hd a) _ hw)
      (hm _ (hx a) _ (prod_mem_adelicCompletionOfElementSet F s I d fun i _ => hd i))) (nsmul_mem (hm _ (hx a) _ hw) _), ?_⟩
    rw [e]
    simp only [nsmul_eq_mul]
    ring

theorem det_one_add_nsmul {n : ℕ} (N : ℕ) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (Y : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, Y i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E), (1 + N • Y).det - 1 = N • w := by
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (RA F E)) i j ∈
      hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_inv_cancel₀ (hc i), Algebra.TensorProduct.one_def]
      exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem _
  have h2 : ∀ s : Equiv.Perm (Fin n), ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ j, (1 + N • Y) (s j) j = ∏ j, (1 : Matrix (Fin n) (Fin n) (RA F E)) (s j) j + N • w := by
    intro s
    obtain ⟨w, hw, e⟩ := prod_add_nsmul F N Finset.univ (fun j => cI (s j) * (cI j)⁻¹)
      (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (s j) j) (fun j => Y (s j) j) (fun j => h1 _ _) (fun j => h _ _)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp s cI, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i)] at hw
    exact ⟨w, hw, e⟩
  choose w hw e using h2
  refine ⟨∑ s : Equiv.Perm (Fin n), Equiv.Perm.sign s • w s, sum_mem fun s _ => ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (hw s) _
  · rw [sub_eq_iff_eq_add']
    conv_rhs => rw [← Matrix.det_one (n := Fin n) (R := RA F E)]
    rw [Matrix.det_apply, Matrix.det_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [e s, smul_add, smul_comm N]

theorem det_cong_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (N : ℕ) (hN : N ≠ 0) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hG : ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), G *ᵥ z - z = N • y) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), G.det - 1 = N • w := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) (RA F E), X = (N : F)⁻¹ • (G - 1) := ⟨_, rfl⟩
  have hGX : G = 1 + N • X := by
    rw [hX, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hNF, one_smul]; abel
  have hXL : ∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
    intro z hz
    obtain ⟨y, hy, ey⟩ := hG z hz
    rw [hX, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ey, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      inv_mul_cancel₀ hNF, one_smul]
    exact hy
  have hPk : P * (Q * X * P) = X * P := by
    simp only [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : (1 + N • (Q * X * P)).det = G.det := by
    have h1 : 1 + N • (Q * X * P) = Q * G * P := by
      rw [hGX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP, Matrix.mul_smul, Matrix.smul_mul]
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [h1, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, (Q * X * P) i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hXL _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  obtain ⟨w, hw, ew⟩ := det_one_add_nsmul F N cI hc _ hk
  have hr : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  exact ⟨w, hr ▸ hw, hkdet ▸ ew⟩

end Det

section Ext

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top
  | exact _root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top
  | (apply _root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top ..)

theorem exists_matrix_of_lattice (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (ψ : Λ →ₗ[𝓞 E] (Fin n → E)) :
    ∃ M : Matrix (Fin n) (Fin n) E, ∀ x : Λ, M *ᵥ (x : Fin n → E) = ψ x := by
  have hun : ∀ s : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) (Fin n → E)) s) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 E)) (Fin n → E) E).map_units
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) Λ.subtype :=
    { map_units := hun
      surj := fun v => by
        obtain ⟨d, hd, h⟩ := exists_smul_mem Λ hΛ v
        exact ⟨(⟨_, h⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  let T := IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) Λ.subtype ψ hun
  refine ⟨LinearMap.toMatrix' (T.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E), fun x => ?_⟩
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) Λ.subtype ψ hun x

theorem eq_zero_of_trace (z : E) (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (a * z) = 0) : z = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 z fun y => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) y
  obtain ⟨q, m, hm, rfl⟩ := q
  have hm0 : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hm)
  have h1 := h p
  have h2 : (p : E) * z = (m : ℚ) • (z * y) := by
    have : (p : E) = y * m := by simpa using hpq.symm
    rw [this, Algebra.smul_def]; simp; ring
  rw [h2, map_smul, smul_eq_zero] at h1
  exact h1.resolve_left hm0

variable [IsCMField E]

theorem herm_smul (G : Matrix (Fin n) (Fin n) E) (a b : E) (x y : Fin n → E) :
    herm G (a • x) (b • y) = a * cc b * herm G x y := by
  simp only [herm, cc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_unitary_of_trace_eq {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    (Λ Λ' : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hΛ' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤) (φ : La ≃ₗ[𝓞 E] Λ) (φ' : La ≃ₗ[𝓞 E] Λ')
    (G : Matrix (Fin n) (Fin n) E) (ξ : E) (hξ : ξ ≠ 0)
    (h : ∀ a b, Algebra.trace ℚ E (ξ * herm G (φ a : Fin n → E) (φ b)) =
      Algebra.trace ℚ E (ξ * herm G (φ' a : Fin n → E) (φ' b))) :
    ∃ δ : GL (Fin n) E, (∀ a, (δ : Matrix (Fin n) (Fin n) E) *ᵥ (φ a : Fin n → E) = φ' a) ∧
      (∀ v, v ∈ Λ ↔ (δ : Matrix (Fin n) (Fin n) E) *ᵥ v ∈ Λ') ∧
      ∀ u v, herm G ((δ : Matrix (Fin n) (Fin n) E) *ᵥ u) ((δ : Matrix (Fin n) (Fin n) E) *ᵥ v) = herm G u v := by
  obtain ⟨M, hM⟩ := exists_matrix_of_lattice Λ hΛ (Λ'.subtype ∘ₗ φ'.toLinearMap ∘ₗ φ.symm.toLinearMap)
  have hM' : ∀ a, M *ᵥ (φ a : Fin n → E) = φ' a := fun a => by rw [hM]; simp
  have hsurj : Function.Surjective M.mulVec := by
    have : LinearMap.range M.mulVecLin = ⊤ := by
      rw [eq_top_iff, ← hΛ', Submodule.span_le]
      intro v hv
      exact ⟨φ (φ'.symm ⟨v, hv⟩), by rw [Matrix.mulVecLin_apply, hM', LinearEquiv.apply_symm_apply]⟩
    exact LinearMap.range_eq_top.1 this
  have hu : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hu
  have h1 : ∀ a b, herm G (φ' a : Fin n → E) (φ' b) = herm G (φ a : Fin n → E) (φ b) := by
    intro a b
    rw [← sub_eq_zero]
    refine (mul_eq_zero.1 (eq_zero_of_trace (ξ * _) fun s => ?_)).resolve_left hξ
    have e := h (s • a) b
    have e1 : ∀ x y : Fin n → E, herm G (s • x) y = s * herm G x y := fun x y => by
      have := herm_smul G (s : E) 1 x y
      rwa [one_smul, cc, map_one, mul_one] at this
    rw [map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul, e1, e1] at e
    rw [mul_sub, mul_sub, map_sub, mul_left_comm, mul_left_comm (s : E), e, sub_self]
  refine ⟨hu.unit, hM', fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun u v => ?_⟩
  · have := hM' (φ.symm ⟨v, hv⟩)
    rw [LinearEquiv.apply_symm_apply] at this
    change M *ᵥ v ∈ Λ'
    rw [this]
    exact (φ' _).2
  · have := hM' (φ'.symm ⟨_, hv⟩)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← hinj this]
    exact (φ _).2
  · obtain ⟨d, hd, hu'⟩ := exists_smul_mem Λ hΛ u
    obtain ⟨d', hd', hv'⟩ := exists_smul_mem Λ hΛ v
    have e := h1 (φ.symm ⟨_, hu'⟩) (φ.symm ⟨_, hv'⟩)
    rw [← hM', ← hM', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    change herm G (M *ᵥ ((d : E) • u)) (M *ᵥ ((d' : E) • v)) = herm G ((d : E) • u) ((d' : E) • v) at e
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, herm_smul, herm_smul] at e
    refine mul_left_cancel₀ (mul_ne_zero ?_ ?_) e
    · exact RingOfIntegers.coe_ne_zero_iff.2 hd
    · exact (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hd')

end Ext

theorem cancel_left {R G : Type} [CommRing R] [Group G] {n : ℕ} (f : G →* GL (Fin n) R) (g g' : G) (N : ℕ)
    (p v w w' y : Fin n → R) (e : p - (f g).1 *ᵥ v = N • w) (e' : p - (f g').1 *ᵥ v = N • w')
    (ey : (f g).1 *ᵥ y = w - w') : (f (g⁻¹ * g')).1 *ᵥ v - v = N • y := by
  have e2 : (f g').1 *ᵥ v - (f g).1 *ᵥ v = N • ((f g).1 *ᵥ y) := by
    rw [ey, smul_sub, ← e, ← e']; abel
  have hi : ∀ z, (f g⁻¹).1 *ᵥ ((f g).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have e3 := congrArg (fun z => (f g⁻¹).1 *ᵥ z) e2
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hi] at e3
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact e3

theorem hom_eq_of_one {G A : Type} [Group G] [Group A] (f : G →* A) (γ g g' : G) (h : f γ = 1)
    (h' : f ((γ * g)⁻¹ * g') = 1) : f g = f g' := by
  rwa [map_mul, map_inv, map_mul, h, one_mul, inv_mul_eq_one] at h'

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem finCong_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (g g' : GA D V) (hlat : latG V g = latG V g')
    (p : Dw.La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, p a - (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', p a - (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    FinCong V l.M (g⁻¹ * g') := by
  have hhat : latGHat V g' = latGHat V g := by
    rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.2.2.2.1, hlat]
  have himg := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  rw [← (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1] at himg
  refine ((GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D H l V).1 _).2 ((((GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V) _).2 _ _).2 ?_)
  intro a ha
  rw [← hio.2, LinearMap.range_eq_map, ← Submodule.map_smul''] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨w, hw, e⟩ := hM b hb
  obtain ⟨w', hw', e'⟩ := hM' b hb
  rw [hhat] at hw'
  have hd : w - w' ∈ (latGHat V g : Set _) := sub_mem hw hw'
  rw [himg] at hd
  obtain ⟨y, hy, ey⟩ := hd
  exact ⟨y, hy, cancel_left (finHom V) g g' l.M _ _ w w' y e e' ey⟩

theorem gLat_eq_of_finCong (V : HSp D) (u : GA D V) (h : FinCong V 1 u) (h' : FinCong V 1 u⁻¹) :
    gLat V u = latHat V := by
  have key : ∀ k, FinCong V 1 k → ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key u h y hy
  · intro hz
    refine ⟨_, key _ h' z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]

set_option maxHeartbeats 800000 in

theorem xi_eq_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) :
    xi (Matrix.GeneralLinearGroup.det (finHom V g)) = xi (Matrix.GeneralLinearGroup.det (finHom V g')) := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat.symm
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  have hdet := det_cong_one D.host.F (latC V) k3 k4 l.M (by have := l.three_le; omega)
    (finHom V ((γ * g)⁻¹ * g')).1 (by rw [← k1]; exact hc)
  have e1 := h1 _ hu hdet
  have e2 := h2 γ ((r1 γ).2 ⟨δ, hγ⟩)
  exact hom_eq_of_one (xi.comp (Matrix.GeneralLinearGroup.det.comp (finHom V))) γ g g' e2 e1

theorem xi_eq_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ} {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) :
    xi (Matrix.GeneralLinearGroup.det (finHom V g)) = xi (Matrix.GeneralLinearGroup.det (finHom V g')) := by
  subst hi
  exact xi_eq_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM' xi h1 h2

set_option maxHeartbeats 1000000 in

theorem exists_sec_rdU_eq_char : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → FnAlgClosed Xo c → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → (∀ h : GA D V, ∃ a : c.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (h))) : ℂˣ)) → ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V (h))) ^ m = 1) → f ^ m = 1) ∧ ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpos hA hgood hW hD hdom hcl xi h1 h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) =
        xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) := by
    intro h γ h' γ' hm hm' hi
    refine xi_eq_of_index F V io hio.emb _ _ hi _ _ _ _ (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ ?_ (htr _) (htr _) hm.2.2 hm'.2.2 xi h1 h2
    rw [← (hW (dict h).1).2]
    exact neg_ne_zero.2 (U.X _).ξ0_ne
  have hv : ∀ i : Fin F.n, ∃ a : c.F, (∃ u : GA D V, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i →
        σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      obtain ⟨a, ha⟩ := h3 (γ * h)
      exact ⟨a, ⟨_, ha⟩, fun h' γ' hm' hi' => by rw [ha, key h γ h' γ' hm hm' (hi.trans hi'.symm)]⟩
    · obtain ⟨a, ha⟩ := h3 1
      exact ⟨a, ⟨_, ha⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose v hv1 hv2 using hv
  obtain ⟨f, hf, hf1, hf2⟩ := GlobalTheory.T.exists_weightZero_section_of_periodSpace_function D.host.E H Dw l Xo c σ g _ F hpos hgood
    ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hgood).2.2.2 Dw g e) hA hcl v
  refine ⟨f, hf, fun m hm => hf1 m fun i => σ.injective ?_, fun h γ hm => ?_⟩
  · obtain ⟨u, hu⟩ := hv1 i
    rw [map_pow, map_one, hu, ← Units.val_pow_eq_pow_val, hm u, Units.val_one]
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← hv2 _ h γ hm rfl, ← hf2 _ _ Pm hP hx]
    exact dif_pos (hdom h)

end GlobalTheory.CharRead
