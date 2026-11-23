import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeformationMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOmegaEqConstMulDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddingsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

namespace CoordProof

theorem diag_coords : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := GlobalTheory.T.lattice_deformation_multiplication

theorem exists_isDet : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := GlobalTheory.T.det_omega_eq_const_mul_det

theorem cmType_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := GlobalTheory.T.cm_type_separates_embeddings

theorem pull_ext {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e (by rw [Over.w x, Over.w y])

theorem jetRing_π_algebraMap {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (a : ℂ) : J.π (algebraMap ℂ J.B a) = a := by
  rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
  simp

theorem π_jet (hJ : JetCalc) {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) : J.π (jet J f) = f 0 := by
  obtain ⟨-, -, -, -, -, ht, -⟩ := hJ I n J
  simp only [jet, taylor, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [Algebra.smul_def, jetRing_π_algebraMap]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [Fin.prod_univ_succ, ht, zero_mul, mul_zero]
  · simp

end CoordProof

open CoordProof in

theorem coordEx (hGM : GlobalTheory.Published.GaussManinPeriods) (hJ : JetCalc) (hD : DiagFrame) : CoordEx := by
  obtain ⟨ε, GM⟩ := hGM
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G
  haveI := G.smooth
  have hX : ∀ z, ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (q : X'.A.left ⟶ G.X.A.left),
      X'.IsPullBy G.X (spMap (G.y z : G.B →+* ℂ)) q := fun z ↦ Obj.exists_isPullBy G.X _
  choose X q hq using hX
  have hδ : ∀ z, ∃ δ : (X z).DetGen, Obj.DetCorr (G.y z : G.B →+* ℂ) (q z) G.δ.1 δ.1 :=
    fun z ↦ ((hq z).existsUnique_detGen _ G.δ).exists
  choose δ hδ using hδ
  let mor : ∀ z, GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 ℂ) (𝟙 _) (X z).A (G.y z : G.B →+* ℂ)
      (spMap (G.y z : G.B →+* ℂ)) (q z) := fun z ↦
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hq z).grp
  have hπj : J.π.comp (G.j : G.B →+* J.B) = (G.y 0 : G.B →+* ℂ) := by
    ext b
    simp only [RingHom.comp_apply, RingHom.coe_coe, G.jet_eq, π_jet hJ]
  have h₀ : T.X.IsPullBy G.X (spMap (G.y 0 : G.B →+* ℂ)) (Y.i ≫ G.q) := by
    rw [← hπj, Cris.spMap_comp]
    exact Y.pull.comp G.pull
  obtain ⟨V, u, τ, P, P₀, hV, h0V, hVU, hper0, hper, -, hτ0, hτhol, hend, hPhol, hcrys⟩ :=
    GM G.B G.X.A _ G.X.ab G.X.dim I G.U G.y G.isOpen G.zero G.hol (fun z ↦ (X z).A) q (fun z ↦ (hq z).grp) mor
      (fun z ↦ (X z).diag T.U.c) (fun z ↦ LB.isLB_pull ((X z).isLB _) _) T.X.A (Y.i ≫ G.q) h₀.grp
      (T.X.diag T.U.c) (LB.isLB_pull (T.X.isLB _) _) T.U.u

  let ρ : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (T.U.e j) ((a : FR E) : E)
  have hreal : ∀ a j, starRingEnd ℂ (ρ a j) = ρ a j := fun a j ↦ (a : FR E).2 (φ (T.U.e j))
  have hsep : ∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k := fun j k hjk ↦
    cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hjk)
  let dg : 𝓞 (FR E) → (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun a ↦
    { toFun := fun w j ↦ ρ a j * w j
      map_add' := fun w w' ↦ funext fun j ↦ mul_add _ _ _
      map_smul' := fun s w ↦ funext fun j ↦ by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hdg : ∀ a w, dg a w = fun j ↦ ρ a j * w j := fun _ _ ↦ rfl
  have hact0 : ∀ a w, T.U.u.ex (dg a w) = T.U.u.ex w ≫ T.X.rm.act a := fun a w ↦ T.U.act a w
  have hΛ : ∀ a, ∀ x ∈ T.U.u.Λ, (fun j ↦ ρ a j * x j) ∈ T.U.u.Λ := fun a x hx ↦ by
    haveI := T.X.rm.hom a
    rw [← T.U.u.ker, ← hdg, hact0, (T.U.u.ker x).2 hx]
    exact H1.ClosedPointWeilPower.one_comp_hom _ inferInstance
  have hM0 : ∀ a w, (T.U.u.ex (dg a w)).left ≫ (Y.i ≫ G.q) =
      (T.U.u.ex w).left ≫ (Y.i ≫ G.q) ≫ (G.X.rm.act a).left := fun a w ↦ by
    rw [hact0, Over.comp_left, Category.assoc, h₀.act a]
  have hend' : ∀ z ∈ V, ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ w, ((u z).ex (M w)).left ≫ q z = ((u z).ex w).left ≫ q z ≫ (G.X.rm.act a).left) ∧
      ∀ x x' : T.U.u.Λ, (x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = dg a x → (τ z x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = M (τ z x) := fun z hz a ↦ by
    haveI := G.X.rm.hom a
    exact hend (G.X.rm.act a) (dg a) (hM0 a) z hz
  let τ' : (I → ℂ) → T.U.u.Λ →+ (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun z ↦ ((u z).Λ.subtype.toAddMonoidHom).comp (τ z).toAddMonoidHom
  have hτ' : ∀ z x, τ' z x = (τ z x : Fin (Module.finrank ℚ (FR E)) → ℂ) := fun _ _ ↦ rfl
  obtain ⟨V', D, ζ, hV', h0V', hV'V, hζ, hζ0, hζ1, hDτ, hDM⟩ := diag_coords (I → ℂ) _ (𝓞 (FR E)) ρ hreal hsep T.U.u.Λ
    T.U.u.discrete T.U.u.full hΛ V τ' hV h0V (fun x ↦ hτ0 x) (fun x ↦ hτhol x)
    (fun z hz a ↦ (hend' z hz a).imp fun M hM ↦ fun x x' hx ↦ hM.2 x x' hx)

  let ζ' : (I → ℂ) → I → ℂ := fun z i ↦ ζ z (T.U.e.symm i)
  have hdiff_ex : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L₁ L₂ : LB A.left} {g : ℕ} (u₁ : HolUnif A L₁ g) (u₂ : HolUnif A L₂ g),
      u₁.ex = u₂.ex → ∀ w v, u₂.IsDiff w v → u₁.IsDiff w v := by
    intro A _ L₁ L₂ g u₁ u₂ h w v hv
    simpa only [HolUnif.IsDiff, h] using hv
  have hU : ∀ z ∈ V', ∃ U : Unif φ (lattice c y) (ζ' z) (X z), U.e = T.U.e ∧ U.c = T.U.c ∧
      ∀ w v, (u z).IsDiff ((D z).symm w) v → U.u.IsDiff w v := by
    intro z hz
    have hzV := hV'V hz

    have hrm : ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
        (∀ w, (u z).ex (M w) = (u z).ex w ≫ (X z).rm.act a) ∧ ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
      intro a
      obtain ⟨M, hM1, hM2⟩ := hend' z hzV a
      refine ⟨M, fun w ↦ pull_ext (hq z).grp ?_, hDM z hz a M (fun x x' hx ↦ hM2 x x' hx)⟩
      rw [hM1, Over.comp_left, Category.assoc, (hq z).act a]
    obtain ⟨u1, hu1ex, hu1Λ, -, -, hu1d⟩ := GlobalTheory.exists_holUnif_reparam (X z).A _ _ (u z) (D z).symm (fun _ ↦ 1)
      (differentiable_const 1) (fun _ ↦ one_ne_zero) rfl
    have hact1 : ∀ (a : 𝓞 (FR E)) w, u1.ex (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = u1.ex w ≫ (X z).rm.act a := by
      intro a w
      obtain ⟨M, hM1, hM2⟩ := hrm a
      have : (D z).symm (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = M ((D z).symm w) := by
        apply (D z).injective
        rw [LinearEquiv.apply_symm_apply, hM2, LinearEquiv.apply_symm_apply]
      rw [hu1ex, hu1ex, this, hM1]
    obtain ⟨u2, hh, hex, χ, hAH⟩ := hD (FR E) 𝔠 (X z) T.U.c T.U.pos u1
      (fun j ↦ (φ (T.U.e j)).comp (algebraMap (FR E) E))
      (fun j k hjk ↦ by
        by_contra hne
        obtain ⟨a, ha⟩ := cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hne)
        exact ha (RingHom.congr_fun hjk (a : FR E)))
      hact1
    refine ⟨⟨T.U.e, T.U.c, T.U.pos, u2, fun w ↦ ?_, fun a w ↦ ?_, fun i ↦ hh (T.U.e.symm i), ?_⟩, rfl, rfl, ?_⟩
    · have hmem : w ∈ u2.Λ ↔ (D z).symm w ∈ (u z).Λ := by
        rw [← u2.ker w, hex, u1.ker w, hu1Λ w]
      rw [hmem]
      constructor
      · intro hw
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : T.U.u.Λ, (τ z x₀ : Fin (Module.finrank ℚ (FR E)) → ℂ) = (D z).symm w :=
          ⟨(τ z).symm ⟨_, hw⟩, by simp⟩
        obtain ⟨x, hxL, hx⟩ := (T.U.lat x₀).1 x₀.2
        refine ⟨x, hxL, ?_⟩
        have h1 := hDτ z hz x₀
        rw [hτ', hx₀, LinearEquiv.apply_symm_apply] at h1
        rw [h1]; funext j; simp [hx, defCoord, ζ']
      · rintro ⟨x, hxL, rfl⟩
        have hx₀ : (fun j ↦ defCoord φ 0 x (T.U.e j)) ∈ T.U.u.Λ := (T.U.lat _).2 ⟨x, hxL, rfl⟩
        have h1 := hDτ z hz ⟨_, hx₀⟩
        rw [hτ'] at h1
        have h2 : (fun j ↦ defCoord φ (ζ' z) x (T.U.e j)) = D z (τ z ⟨_, hx₀⟩) := by
          rw [h1]; funext j; simp [defCoord, ζ']
        rw [h2, LinearEquiv.symm_apply_apply]; exact (τ z _).2
    · rw [hex]; exact hact1 a w
    · simp only [Equiv.symm_apply_apply]; exact ⟨χ, hAH⟩
    · intro w v hv
      exact hdiff_ex u2 u1 hex w v (hu1d w v hv)

  choose U hUe hUc hUd using hU
  have hC : ∀ z (hz : z ∈ V'), ∃ C, (U z hz).IsDet (δ z).1 C := fun z hz ↦ exists_isDet (X z) _ (U z hz).u (δ z).1
  obtain ⟨-, -, -, -, -, hJt, hJprod⟩ := hJ I n J
  refine ⟨{
    V := V'
    isOpen := hV'
    zero := h0V'
    sub := hV'V.trans hVU
    X := X
    q := q
    pull := hq
    mor := mor
    δ := δ
    corr := hδ
    ζ := ζ'
    ζ_hol := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 hζ _
    ζ_zero := by funext i; simp [ζ', hζ0]
    ζ_mem := fun z hz i ↦ hζ1 z hz _
    U := U
    e_eq := hUe
    C := fun z ↦ if hz : z ∈ V' then Classical.choose (hC z hz) else 0
    det := fun z hz ↦ by simp only [dif_pos hz]; exact Classical.choose_spec (hC z hz)
    P₀ := P₀
    per := hper0
    P := fun z ↦ (P z).comp (τ z).toAddMonoidHom
    lie := fun z hz x ↦ by
      obtain ⟨v, hv1, hv2⟩ := (hper z (hV'V hz)).2.2.1 (τ z x)
      refine ⟨v, hv1, hUd z hz _ v ?_⟩
      have h1 : (fun a ↦ x.1 a + ζ' z (T.U.e a) * starRingEnd ℂ (x.1 a)) = D z (τ z x) := by
        rw [← hτ', hDτ z hz x]; funext a; simp [ζ']
      rw [h1, LinearEquiv.symm_apply_apply]; exact hv2
    P_hol := fun x c ↦ (hPhol x c).mono hV'V
    horiz := fun m' x d hd c ↦ hcrys J.B J.π J.κ J.nil (jetRing_π_algebraMap J) (n + 1) J.t hJt hJprod G.j G.jet_eq
      Y.X'.A G.q G.pull.grp m' Y.i Y.pull.grp rfl Y.mor x d hd c }⟩

end GlobalTheory.LatJet.An
