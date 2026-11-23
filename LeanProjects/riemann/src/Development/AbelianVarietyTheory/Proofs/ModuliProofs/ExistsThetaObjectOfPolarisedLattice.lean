import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasisStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem obbuild_hf_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
  simp [hermForm, add_dotProduct]

theorem obbuild_hf_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem obbuild_hf_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm (r • a) c = r * hermForm Hm a c := by
  simp [hermForm, smul_dotProduct]

theorem obbuild_hf_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm a (r • c) = star r * hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

theorem obbuild_adj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im) (z z' : Fin g → ℂ) :
    hermForm Hm (F z) z' = hermForm Hm z (F' z') := by
  have hz : ∀ z : Fin g → ℂ, hermForm Hm 0 z = 0 ∧ hermForm Hm z 0 = 0 := fun z => by simp [hermForm]
  have hr : ∀ (r : ℝ) (z : Fin g → ℂ), r • z = (r : ℂ) • z := fun r z => by
    ext i; simp
  have h1 : ∀ a ∈ s, ∀ c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a ha c
    have hc : c ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact h a ha x hx
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_right, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_right, obbuild_hf_smul_right]; simp [hx]
  have h2 : ∀ a c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a c
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact h1 x hx c
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_left, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]; simp [hx]
  apply Complex.ext
  · have := h2 (Complex.I • z) z'
    rw [map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left] at this
    simpa using this
  · exact h2 z z'

theorem obbuild_ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  induction n with
  | zero => simp [(u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem obbuild_unitS {o : Type} [CommRing o] (em : o →+* ℂ) (u : oˣ) :
    unitS (spMap em) u = unitOn (Units.map em.toMonoidHom u) := by
  ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em)
  exact (congrArg (fun f => f.hom (u : o)) this).symm

theorem obbuild_unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n := by
  simp [unitOn]

theorem thetaObject_of_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro h1 h2 h3 h4 o _ g k J b em w w' La _ EF lam ac Q Hm hE ⟨hQ, hdisc, hspan, hH, hpos, him⟩ hac hw hadj hlam
  choose F hF using hac
  let Λ : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap
  let e : La ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective Q.toIntLinearMap hQ
  have he : ∀ a : Λ, Q (e.symm a) = a := fun a => congrArg Subtype.val (e.apply_symm_apply a)
  have hbij : Function.Bijective (LinearMap.BilinForm.congr e EF) := by
    have : (LinearMap.BilinForm.congr e EF : Λ → Λ →ₗ[ℤ] ℤ) = e.symm.dualMap ∘ EF ∘ e.symm := by
      funext a; ext c; simp
    rw [this]
    exact e.symm.dualMap.bijective.comp (hE.comp e.symm.bijective)
  obtain ⟨P, u, χ, hg, hΛ, hAH, -, -⟩ := principalTorus_algebraic g Λ Hm (LinearMap.BilinForm.congr e EF) hdisc
    hspan hH hpos (fun a c => by rw [← he a, ← he c, him]; simp) hbij
  subst hg
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ]; rfl
  have hhom := fun j => GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u (F j) (fun z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, (hF j x).symm⟩)
  choose act hact using fun j => (hhom j).exists
  have hFF : F w + F w' = LinearMap.id := by
    apply LinearMap.restrictScalars_injective ℝ
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [hF, ← map_add, hw]
  have hmul : act w * act w' = 𝟙 P.A := by
    haveI := P.isAb.comm
    haveI := (hact w).1
    haveI := (hact w').1
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u LinearMap.id (fun z hz => hz)).unique ⟨?_, fun z => ?_⟩
      ⟨inferInstance, fun z => by simp⟩
    · rw [Hom.mul_def]; infer_instance
    · rw [MonObj.comp_mul, ← (hact w).2, ← (hact w').2, ← u.ex_add, ← LinearMap.add_apply, hFF]
  have hadjH : ∀ z z', hermForm Hm (F w z) z' = hermForm Hm z (F w' z') := by
    refine obbuild_adj Hm _ hspan _ _ ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hF, hF, him, him, hadj]
  have hiso := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h1 h2 h3 h4 P u Hm χ _ _ _ _ hAH (hact w).1 (hact w').1 (hact w).2 (hact w').2).2 hadjH
  obtain ⟨m1, m2, m3, m4, m5, -, m7, m8⟩ := GlobalTheory.T.normalised_polarisation' h1 h3 ℂ P _ _ (hact w).1 (hact w').1 hmul hiso _ rfl
  obtain ⟨Ef, hEf, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P u Hm χ hAH
  obtain ⟨u₁, χ₁, hex, hΛ₁, hAH₁, hχ₁⟩ := GlobalTheory.T.exists_appellHumbert_frame_of_pulled_biextension h1 h2 h3 h4 P u Hm χ Ef (act w) (F w) (F w') hAH hEf
    (hact w).2 hFF hadjH
  let P₁ : Out.PolAV (Sp ℂ) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
      isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5 }
  obtain ⟨Ef₁, hEf₁, -, -, -, -, -, -, hweil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P₁ u₁ Hm χ₁ hAH₁
  have hmem₁ : ∀ z, z ∈ u₁.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ₁]; exact hmem z
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  let pt : Fin (2 * P.g) → (Out.baseOver (Sp ℂ) ⟶ P.A) := fun i => u₁.ex ((k : ℂ)⁻¹ • Q (lam i))
  have htor : ∀ i, pt i ^ k = 1 := fun i => by
    have := obbuild_ex_pow u₁ ((k : ℂ)⁻¹ • Q (lam i)) k
    rw [smul_inv_smul₀ hk, (u₁.ker _).2 ((hmem₁ _).2 ⟨_, rfl⟩)] at this
    exact this
  have hpair : ∀ i j, Out.WeilIs P.A (cubeLB P.A ![𝟙 P.A, act w] P.L) k (pt i) (pt j)
      (unitOn (Units.map em.toMonoidHom b.ζ) ^ Out.stdSymp P.g i j) := fun i j => by
    rw [← obbuild_unitOn_zpow]
    refine hweil k ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩ _ hk0 ?_
    have h5 := hEf₁ ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him (lam i) (lam j), Int.cast_inj] at h5
    rw [h5, hlam]
    simp
  have hb := GlobalTheory.T.symplectic_torsion_system_is_geometric_basis h1 ℂ P₁ k (Units.map em.toMonoidHom b.ζ) pt hk
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em)) htor hpair
  refine ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
            isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5, pt := pt, torsion := htor, bij := hb,
            pairing := fun i j => by rw [obbuild_unitS]; exact hpair i j,
            act := act, hom := fun j => (hact j).1 }, ⟨hmul, m8, m7⟩, u₁, χ₁, hAH₁, hmem₁, ?_, fun _ => rfl, ?_⟩
  · intro x l hl
    rw [hχ₁ l ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩ hl.symm (by rw [hl, hF])]
    have h5 := hEf ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him x (ac w x), Int.cast_inj] at h5
    rw [h5]
  · intro j
    refine ⟨F j, hF j, fun z => ?_⟩
    have := (hact j).2 z
    rw [← hex] at this
    exact this

end GlobalTheory
