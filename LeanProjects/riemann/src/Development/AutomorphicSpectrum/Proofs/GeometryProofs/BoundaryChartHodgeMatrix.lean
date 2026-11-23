import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIffStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PuncturedPolydiscOpenConnectedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExpHomBijectiveOfLocalInjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLiftsOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLieStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeRankTwoGStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriodStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupPointsEquivCommonCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Marking

theorem punct_top (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty :=
  GlobalTheory.T.punctured_polydisc_open_connected n a ρ hρ

theorem bijective_of_exp {M : Type} [Group M] {g g' : ℕ} (ex : (Fin g' → ℂ) → M) (r : (Fin g → ℂ) → M)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hex : ∀ z w, ex (z + w) = ex z * ex w) (hc : ∀ x, ex (h x) = r x)
    (ho : Function.Surjective r) (hr : ∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x‖ < δ → r x = 1 → x = 0)
    (he : ∃ δ : ℝ, 0 < δ ∧ ∀ y, ‖y‖ < δ → ex y = 1 → y = 0) : Function.Bijective h :=
  GlobalTheory.T.exp_hom_bijective_of_local_inj M g g' ex r h hex hc ho hr he

theorem herm_transport {g g' : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (hH : Hm.IsHermitian) : ∃ Hf : Matrix (Fin g') (Fin g') ℂ, Hf.IsHermitian ∧
      ∀ x y, hermForm Hf (h x) (h y) = hermForm Hm x y := by
  let A : Matrix (Fin g) (Fin g') ℂ := LinearMap.toMatrix' (h.symm : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hA : ∀ x, A.mulVec (h x) = x := fun x => by
    simp [A, LinearMap.toMatrix'_mulVec]
  refine ⟨A.transpose * Hm * A.transpose.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun x y => ?_⟩
  unfold hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.star_vecMul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.vecMul_transpose, hA, hA]

theorem deriv_of_open {A T : Scheme.{0}} (φ : A ⟶ T) [IsOpenImmersion φ] {g : ℕ} (W : (Fin g → ℂ) → (Sp ℂ ⟶ A))
    (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T) (hv : IsDerivAt0 (fun x => W x ≫ φ) y v) :
    ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' :=
  GlobalTheory.T.tangent_vector_lifts_open_immersion A T φ g W y v hv

theorem isDerivAt0_frame {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (u : Fin g → R) :
    IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (spMap (dualMap (ψ b)) ≫ (M.pt u).left) :=
  GlobalTheory.T.family_exp_derivative_lie R G g n M B ψ e b hb u

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem finrank_of_isPeriod (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) : Module.finrank ℤ D.La = 2 * g :=
  GlobalTheory.T.period_lattice_rank_two_g E H D g ty P hP

theorem isolated_of_isPeriod (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin g → ℂ, ‖x‖ < δ → x ∈ P.range → x = 0 := by
  have hd : DiscreteTopology P.range := hP.2.2.1
  have h0 : IsOpen ({0} : Set P.range) := isOpen_discrete _
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 h0
  have h0V : (0 : Fin g → ℂ) ∈ V := by
    have : (0 : P.range) ∈ Subtype.val ⁻¹' V := hVe ▸ rfl
    exact this
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.1 hV 0 h0V
  refine ⟨δ, hδ, fun x hx hm => ?_⟩
  have h1 : (⟨x, hm⟩ : P.range) ∈ Subtype.val ⁻¹' V := hb (by simpa using hx)
  rw [hVe] at h1
  exact congrArg Subtype.val h1

theorem isHolTo_pt {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) :
    IsHolTo (punct n a 1) C.pt :=
  GlobalTheory.T.boundary_chart_holomorphic E H D l Xo σ n a C

theorem exists_index {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo σ ty) {m : ℕ} {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)} (hB : IsOpen B)
    (hc : IsPreconnected B) (hne : B.Nonempty) (hs : ∀ b ∈ B, y b ≫ Xo.s = spMap σ) (hy : IsHolTo B y) :
    ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b :=
  GlobalTheory.T.family_uniformisation_local_period E H D l Xo σ g ty FU m B y hB hc hne hs hy

theorem exists_fibre_equiv {S₁ S₂ V : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {tV : SAB H V}
    {f₁ : V ⟶ S₁} {f₂ : V ⟶ S₂} (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V)
    (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂) (h₁ : x ≫ f₁ = y₁) (h₂ : x ≫ f₂ = y₂) :
    ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧
      (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧
      ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ),
        GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ :=
  GlobalTheory.T.group_points_equiv_common_cover E H S₁ S₂ V t₁ t₂ tV f₁ f₂ m₁ m₂ x y₁ y₂ h₁ h₂

theorem isRiemannMatrix_unique {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    {A B : Matrix (Fin C.g) (Fin C.g) ℂ} (hA : C.IsRiem z A) (hB : C.IsRiem z B) : A = B := by
  have hsq : spMap (dualMap (C.ψ z)) ≫ spMap (algebraMap C.R (DualNumber C.R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ z) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hT : ∀ u : Fin C.g → C.R, ∃ v : epsAt (spMap (C.ψ z)) ⟶ C.t.G,
      v.left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt u).left := fun u =>
    ⟨Over.homMk (spMap (dualMap (C.ψ z)) ≫ (C.M.pt u).left) (by
      have hw := Over.w (C.M.pt u)
      show (spMap (dualMap (C.ψ z)) ≫ (C.M.pt u).left) ≫ C.t.G.hom =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ z)
      rw [Category.assoc, hw, ← hsq]
      simp), rfl⟩
  choose v hv using fun c : Fin C.g => hT (Pi.single c 1)
  have hvv : C.IsVal z (fun c => Pi.single c 1) v := fun c => hv c
  have he : ∀ c : Fin C.g, (fun b => C.ψ z ((Pi.single c 1 : Fin C.g → C.R) b)) = (Pi.single c 1 : Fin C.g → ℂ) :=
    fun c => by
      ext b
      by_cases h : b = c
      · subst h; simp
      · simp [Pi.single_apply, h]
  have hs : ∀ (K : Matrix (Fin C.g) (Fin C.g) ℂ) c d,
      hermForm K (Pi.single c 1) (Pi.single d 1) = K c d := fun K c d => by
    have : star (Pi.single d 1 : Fin C.g → ℂ) = Pi.single d 1 := by
      ext b
      by_cases h : b = d
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp [hermForm, this]
  have h1 := (hA C.g _ v (Matrix.of fun c d => (Real.pi : ℂ) * hermForm A
    (fun b => C.ψ z ((Pi.single c 1 : Fin C.g → C.R) b)) (fun b => C.ψ z ((Pi.single d 1 : Fin C.g → C.R) b))) hvv).2
    (fun _ _ => rfl)
  have h2 := (hB C.g _ v _ hvv).1 h1
  ext c d
  have h3 := h2 c d
  simp only [Matrix.of_apply, he, hs] at h3
  exact mul_left_cancel₀ (by exact_mod_cast Real.pi_ne_zero) h3

theorem weil_value {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (N : ℕ) (ζ : ℂˣ) (hN : 0 < N)
    (x y : (FU.Di i).La)
    (h : GlobalTheory.UU.CubWeil Xo.univ.t.cub N (FU.ex i P ((N : ℂ)⁻¹ • P x)) (FU.ex i P ((N : ℂ)⁻¹ • P y)) (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((FU.Di i).EF x y : ℂ) / N) := by
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((FU.Di i).EF x y : ℂ) / N)) (Complex.exp_ne_zero _)
  have hw := FU.ex_weil i P hP N x y c hN rfl
  have hc := (GlobalTheory.UU.cubWeil_iff_weilIs (c := Xo.univ.t.cub) GlobalTheory.SemiRigid.globalFns (univ_isAb Xo) h.1 h.2.1 (unitOn c)).2 hw
  have e0 := h.unique hc
  have e1 := congrArg (fun q : (Γ(Sp ℂ, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom q.val) e0
  simpa [unitOn, c] using e1

theorem exists_family {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {B' : Set (Fin n → ℂ)}
    (P₀ : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))) (hsub : B' ⊆ punct n a 1)
    (hP : IsHolPeriods (FU.Di i) ty B' P₀) (hu : ∀ b ∈ B', FU.u i (P₀ b) = C.pt b ≫ C.k)
    (w₀ : Sp ℂ ⟶ C.tV.G.left) :
    ∃ (r : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (C.ψ b)) ⟶ C.t.G))
      (Wt : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ C.tV.G.left)),
      ∀ b ∈ B', (∀ x y, r b (x + y) = r b x * r b y) ∧ Function.Surjective (r b) ∧
        (∀ x, r b x = 1 ↔ x ∈ (P₀ b).range) ∧
        (∀ x, Wt b x ≫ C.tV.G.hom = C.pt b ∧ Wt b x ≫ C.m₂.φ = (FU.ex i (P₀ b) x).left ∧
          Wt b x ≫ C.m₁.φ = (r b x).left) ∧
        ∀ (N : ℕ) (x x' : Fin g → ℂ) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil C.t.cub N (r b x) (r b x') ζ →
          GlobalTheory.UU.CubWeil Xo.univ.t.cub N (FU.ex i (P₀ b) x) (FU.ex i (P₀ b) x') ζ := by
  have key : ∀ b, ∃ (rb : (Fin g → ℂ) → (Over.mk (spMap (C.ψ b)) ⟶ C.t.G))
      (Wb : (Fin g → ℂ) → (Sp ℂ ⟶ C.tV.G.left)),
      b ∈ B' → (∀ x y, rb (x + y) = rb x * rb y) ∧ Function.Surjective rb ∧
        (∀ x, rb x = 1 ↔ x ∈ (P₀ b).range) ∧
        (∀ x, Wb x ≫ C.tV.G.hom = C.pt b ∧ Wb x ≫ C.m₂.φ = (FU.ex i (P₀ b) x).left ∧
          Wb x ≫ C.m₁.φ = (rb x).left) ∧
        ∀ (N : ℕ) (x x' : Fin g → ℂ) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil C.t.cub N (rb x) (rb x') ζ →
          GlobalTheory.UU.CubWeil Xo.univ.t.cub N (FU.ex i (P₀ b) x) (FU.ex i (P₀ b) x') ζ := by
    intro b
    by_cases hb : b ∈ B'
    · obtain ⟨Φ, hm, hw, hW⟩ := exists_fibre_equiv C.m₁ C.m₂ (C.pt b) (spMap (C.ψ b)) (FU.u i (P₀ b))
        (C.pt_eq b (hsub hb)).1 (hu b hb).symm
      have hper := hP.1 b hb
      choose w hw1 hw2 hw3 using hw
      have hone : Φ 1 = 1 := by
        have := hm 1 1
        rw [_root_.mul_one] at this
        exact left_eq_mul.mp this
      refine ⟨fun x => Φ (FU.ex i (P₀ b) x), fun x => w (FU.ex i (P₀ b) x), fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · intro x y
        show Φ _ = _
        rw [FU.ex_add i _ hper, hm]
      · exact Φ.surjective.comp (FU.ex_onto i _ hper)
      · intro x
        rw [← FU.ex_ker i _ hper x, ← hone]
        exact Φ.injective.eq_iff
      · exact fun x => ⟨hw1 _, hw2 _, hw3 _⟩
      · exact fun N x x' ζ h => hW N _ _ ζ h
    · exact ⟨fun _ => 1, fun _ => w₀, fun h => absurd h hb⟩
  choose r Wt h using key
  exact ⟨r, Wt, h⟩

theorem family_hol {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {B' : Set (Fin n → ℂ)}
    (P₀ : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))) (hB : IsOpen B') (hsub : B' ⊆ punct n a 1)
    (hP : IsHolPeriods (FU.Di i) ty B' P₀) (Wt : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ C.tV.G.left))
    (hW : ∀ b ∈ B', ∀ x, Wt b x ≫ C.tV.G.hom = C.pt b ∧ Wt b x ≫ C.m₂.φ = (FU.ex i (P₀ b) x).left) :
    IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Wt bz.1 bz.2) := by
  refine GlobalTheory.HolFibre.isHolTo_of_isPullback C.m₂.cart.1 ?_ ?_
  · exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn (FU.hol i n B' P₀ hB hP).2 fun bz hb => (hW _ hb.1 _).2
  · have h1 : IsHolTo (B' ×ˢ (Set.univ : Set (Fin g → ℂ)))
        (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => C.pt bz.1) := by
      intro U f
      have h0 := isHolTo_pt C U f
      have hs : {b ∈ B' | ⊤ ≤ C.pt b ⁻¹ᵁ U} = B' ∩ {b ∈ punct n a 1 | ⊤ ≤ C.pt b ⁻¹ᵁ U} := by
        ext b
        exact ⟨fun h => ⟨h.1, hsub h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      have ho : IsOpen {b ∈ B' | ⊤ ≤ C.pt b ⁻¹ᵁ U} := hs ▸ hB.inter h0.1
      have hq : {bz ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ C.pt bz.1 ⁻¹ᵁ U} =
          Prod.fst ⁻¹' {b ∈ B' | ⊤ ≤ C.pt b ⁻¹ᵁ U} := by
        ext bz
        simp
      refine ⟨by rw [hq]; exact ho.preimage continuous_fst, ?_⟩
      have hd : DifferentiableOn ℂ (fun b => valAt' (C.pt b) U f) {b ∈ B' | ⊤ ≤ C.pt b ⁻¹ᵁ U} :=
        h0.2.mono fun b hb => ⟨hsub hb.1, hb.2⟩
      rw [hq]
      exact hd.comp differentiableOn_fst fun _ h => h
    exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn h1 fun bz hb => (hW _ hb.1 _).1

def Good {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) {ρ : ℝ}
    (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ x : Fin C.g → ℂ, x ≠ 0 → 0 < (hermForm Hm x x).re) ∧ C.IsRiem z Hm ∧
    ∀ (N : ℕ) (ζ : ℂˣ), 0 < N → ∀ x ∈ e.per z, ∀ x' ∈ e.per z,
      GlobalTheory.UU.CubWeil C.t.cub N (e.ex z ((N : ℂ)⁻¹ • x)) (e.ex z ((N : ℂ)⁻¹ • x')) (unitOn ζ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm x x').im : ℂ) / N)

theorem isRiem_of_period {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) {ρ : ℝ} (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ)
    (i : Fin FU.n) {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) ρ) (hz1 : z ∈ punct n a 1)
    (P₀ : (FU.Di i).La →+ (Fin g → ℂ)) (hper : IsPeriod (FU.Di i) ty P₀) (hu : FU.u i P₀ = C.pt z ≫ C.k)
    (r : (Fin g → ℂ) → (Over.mk (spMap (C.ψ z)) ⟶ C.t.G)) (Wz : (Fin g → ℂ) → (Sp ℂ ⟶ C.tV.G.left))
    (hW : ∀ x, Wz x ≫ C.m₂.φ = (FU.ex i P₀ x).left ∧ Wz x ≫ C.m₁.φ = (r x).left)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin C.g → ℂ))
    (hd : ∀ x v, IsDerivAt0 (fun x => (r x).left) x v ↔ IsDerivAt0 (fun x => (e.ex z x).left) (h x) v)
    (Hm₀ : Matrix (Fin g) (Fin g) ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (hH₀ : Hm₀.IsHermitian)
    (him : ∀ x y, (hermForm Hm₀ (P₀ x) (P₀ y)).im = (FU.Di i).EF x y)
    (hf : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm₀ x y) : C.IsRiem z Hm := by
  intro m u v Γ hv
  let x : Fin m → Fin g → ℂ := fun c => h.symm (fun b => C.ψ z (u c b))
  have hx : ∀ c, h (x c) = fun b => C.ψ z (u c b) := fun c => h.apply_symm_apply _
  have hD : ∀ c, IsDerivAt0 (fun x => (r x).left) (x c) (v c).left := fun c => by
    rw [hd, hx, hv c]
    exact isDerivAt0_frame e hz (u c)
  haveI := C.j_open
  haveI : IsOpenImmersion C.m₁.φ := MorphismProperty.of_isPullback C.m₁.cart.1.flip ‹IsOpenImmersion C.j›
  have hD' : ∀ c, ∃ v' : Sp (DualNumber ℂ) ⟶ C.tV.G.left, v' ≫ C.m₁.φ = (v c).left ∧ IsDerivAt0 Wz (x c) v' :=
    fun c => deriv_of_open C.m₁.φ Wz (x c) _ (by
      have : (fun x => Wz x ≫ C.m₁.φ) = fun x => (r x).left := funext fun x => (hW x).2
      rw [this]; exact hD c)
  choose v' hv1 hv2 using hD'
  have hover : ∀ c, v' c ≫ C.tV.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ C.pt z := fun c => by
    rw [← cancel_mono C.j, Category.assoc, Category.assoc, ← C.m₁.cart.1.w, ← Category.assoc, hv1 c,
      (C.pt_eq z hz1).1]
    exact Over.w (v c)
  let vV : Fin m → (epsAt (C.pt z) ⟶ C.tV.G) := fun c => Over.homMk (v' c) (hover c)
  let vU : Fin m → (epsAt (FU.u i P₀) ⟶ Xo.univ.t.G) := fun c => Over.homMk (v' c ≫ C.m₂.φ) (by
    show (v' c ≫ C.m₂.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ FU.u i P₀
    rw [Category.assoc, C.m₂.cart.1.w, ← Category.assoc, hover c, hu, Category.assoc])
  have e1 := GlobalTheory.T.hodge_gram_pullback_iff E H _ _ C.t C.tV C.j C.m₁ (C.pt z) (spMap (C.ψ z)) m vV v Γ (C.pt_eq z hz1).1.symm
    (fun c => hv1 c)
  have e2 := GlobalTheory.T.hodge_gram_pullback_iff E H _ _ Xo.univ.t C.tV C.k C.m₂ (C.pt z) (FU.u i P₀) m vV vU Γ hu (fun c => rfl)
  have e3 := hodgeGram_iff_period E H D l Xo σ g ty FU i P₀ Hm₀ hper hH₀ him (FU.u i P₀) rfl m vU x Γ (fun c => by
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (hv2 c) C.m₂.φ
    have h2 : (fun x => Wz x ≫ C.m₂.φ) = fun x => (FU.ex i P₀ x).left := funext fun x => (hW x).1
    rw [h2] at this
    exact this)
  rw [← e1, e2, e3]
  refine forall₂_congr fun c d => ?_
  rw [← hf, hx, hx]

theorem isHolTo_mono' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B B' : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hs : B' ⊆ B) (ho : IsOpen B') : IsHolTo B' y := by
  intro U f
  have hq : {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U} = B' ∩ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    exact ⟨fun h => ⟨h.1, hs h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  exact ⟨hq ▸ ho.inter (h U f).1, (h U f).2.mono fun b hb => ⟨hs hb.1, hb.2⟩⟩

theorem local_marking {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) {ρ : ℝ} (hρ : ρ ≤ 1)
    (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ) (i : Fin FU.n) {B' : Set (Fin n → ℂ)}
    (P₀ : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))) (hB : IsOpen B') (hsub : B' ⊆ punct n a ρ)
    (hP : IsHolPeriods (FU.Di i) ty B' P₀) (hu : ∀ b ∈ B', FU.u i (P₀ b) = C.pt b ≫ C.k) :
    ∃ P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin C.g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) B') ∧
      ∀ z ∈ B', Module.finrank ℤ (FU.Di i).La = 2 * C.g ∧ Function.Injective (P z) ∧
        ((P z).range : Set (Fin C.g → ℂ)) = e.per z ∧ ∃ Hm : Matrix (Fin C.g) (Fin C.g) ℂ, Good C e z Hm ∧
          ∀ x y, (hermForm Hm (P z x) (P z y)).im = (FU.Di i).EF x y := by
  rcases B'.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨fun _ => 0, fun x => by simp, fun z hz => absurd hz (Set.notMem_empty z)⟩
  have hsub1 : B' ⊆ punct n a 1 := fun b hb => ⟨ball_subset_ball hρ (hsub hb).1, (hsub hb).2⟩
  have hsubB : B' ⊆ ball 0 ρ := fun b hb => (hsub hb).1
  obtain ⟨r, Wt, hr⟩ := exists_family C FU i P₀ hsub1 hP hu ((1 : Over.mk (C.pt b₀) ⟶ C.tV.G).left)
  have hol := family_hol C FU i P₀ hB hsub1 hP Wt
    (fun b hb x => ⟨((hr b hb).2.2.2.1 x).1, ((hr b hb).2.2.2.1 x).2.1⟩)
  have holr : IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (r bz.1 bz.2).left) :=
    GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_comp hol C.m₁.φ)
      fun bz hb => (((hr _ hb.1).2.2.2.1 _).2.2).symm
  obtain ⟨hl, hlhol, hl2⟩ := exists_linear_lift_of_additive_family C.R C.t.G C.g n C.M (ball 0 ρ) C.ψ e g B' r hB
    hsubB (fun b hb => (hr b hb).1) holr
  have hbij : ∀ z ∈ B', Function.Bijective (hl z) := by
    intro z hz
    obtain ⟨hadd, hons, hker, -, -⟩ := hr z hz
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_isPeriod _ (hP.1 z hz)
    refine bijective_of_exp (e.ex z) (r z) (hl z) (e.add z (hsubB hz)) (hl2 z hz).1 hons
      ⟨δ, hδ, fun x hx h1 => hiso x hx ((hker x).1 h1)⟩ ?_
    obtain ⟨W, hW, hzW, ρ', hρ', hinj⟩ := ExpLift.ex_inj_near e (hsubB hz)
    refine ⟨ρ', hρ', fun y hy h1 => hinj z hzW y (mem_ball_zero_iff.2 hy) 0 (mem_ball_self hρ') ?_⟩
    rw [h1, ExpLift.ex_zero e (hsubB hz)]
  refine ⟨fun z => ((hl z).toAddMonoidHom).comp (P₀ z), ?_, ?_⟩
  · intro x
    have hsum : ∀ z, ((hl z).toAddMonoidHom.comp (P₀ z)) x = ∑ k, (P₀ z x k) • hl z (Pi.single k 1) := fun z => by
      have : P₀ z x = ∑ k, (P₀ z x k) • (Pi.single k 1 : Fin g → ℂ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      show hl z (P₀ z x) = _
      conv_lhs => rw [this]
      simp only [map_sum, map_smul]
    simp only [hsum]
    exact DifferentiableOn.fun_sum fun k _ =>
      DifferentiableOn.smul ((differentiableOn_pi.1 (hP.2 x)) k) (hlhol _)
  · intro z hz
    have hper := hP.1 z hz
    obtain ⟨hadd, hons, hker, hWz, hwe⟩ := hr z hz
    obtain ⟨hlex, -, hlder⟩ := hl2 z hz
    let hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin C.g → ℂ) := LinearEquiv.ofBijective (hl z) (hbij z hz)
    have hhv : ∀ x, hh x = hl z x := fun _ => rfl
    obtain ⟨Hm₀, hH₀, hpos₀, him₀⟩ := hper.2.2.2.2
    obtain ⟨Hm, hHm, hf⟩ := herm_transport Hm₀ hh hH₀
    have hg : g = C.g := by simpa using hh.finrank_eq
    have hrange : (((hl z).toAddMonoidHom.comp (P₀ z)).range : Set (Fin C.g → ℂ)) = e.per z := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show e.ex z (hl z (P₀ z x)) = 1
        rw [hlex]
        exact (hker _).2 ⟨x, rfl⟩
      · intro hy
        obtain ⟨x, rfl⟩ := (hbij z hz).2 y
        have h1 : r z x = 1 := by rw [← hlex]; exact hy
        obtain ⟨c, rfl⟩ := (hker x).1 h1
        exact ⟨c, rfl⟩
    refine ⟨by rw [finrank_of_isPeriod _ hper, hg], (hbij z hz).1.comp hper.2.1, hrange, Hm,
      ⟨hHm, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := hh.surjective x
      rw [hf]
      exact hpos₀ y (fun h0 => hx (by rw [h0, map_zero]))
    · exact isRiem_of_period C FU e i (hsubB hz) (hsub1 hz) (P₀ z) hper (hu z hz) (r z) (Wt z)
        (fun x => ⟨(hWz x).2.1, (hWz x).2.2⟩) hh hlder Hm₀ Hm hH₀ him₀ hf
    · intro N ζ hN x hx x' hx' hc
      rw [← hrange] at hx hx'
      obtain ⟨c₁, rfl⟩ := hx
      obtain ⟨c₂, rfl⟩ := hx'
      have e1 : ∀ c, e.ex z ((N : ℂ)⁻¹ • ((hl z).toAddMonoidHom.comp (P₀ z)) c) = r z ((N : ℂ)⁻¹ • P₀ z c) := fun c => by
        rw [← hlex, map_smul]
        rfl
      rw [e1, e1] at hc
      have := weil_value FU i (P₀ z) hper N ζ hN c₁ c₂ (hwe N _ _ _ hc)
      have h3 : (hermForm Hm (((hl z).toAddMonoidHom.comp (P₀ z)) c₁) (((hl z).toAddMonoidHom.comp (P₀ z)) c₂)).im
          = (FU.Di i).EF c₁ c₂ := by
        show (hermForm Hm (hh (P₀ z c₁)) (hh (P₀ z c₂))).im = _
        rw [hf, him₀]
      rw [this, h3]
      push_cast
      rfl
    · intro x y
      show (hermForm Hm (hh (P₀ z x)) (hh (P₀ z y))).im = _
      rw [hf, him₀]

end GlobalTheory.CompanionTheory.Ar.Flat.Marking

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Marking in

theorem exists_marking : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (ρ : ℝ) (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ), 0 < ρ → ρ ≤ 1 → ∃ (i : Fin FU.n) (Hf : (Fin n → ℂ) → Matrix (Fin C.g) (Fin C.g) ℂ), Module.finrank ℤ (FU.Di i).La = 2 * C.g ∧ (∀ z ∈ punct n a ρ, (Hf z).IsHermitian ∧ (∀ x : Fin C.g → ℂ, x ≠ 0 → 0 < (hermForm (Hf z) x x).re) ∧ C.IsRiem z (Hf z) ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N → ∀ x ∈ e.per z, ∀ x' ∈ e.per z, GlobalTheory.UU.CubWeil C.t.cub N (e.ex z ((N : ℂ)⁻¹ • x)) (e.ex z ((N : ℂ)⁻¹ • x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hf z) x x').im : ℂ) / N)) ∧ ∀ z₀ ∈ punct n a ρ, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ punct n a ρ ∧ ∃ P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin C.g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ ((P z).range : Set (Fin C.g → ℂ)) = e.per z ∧ ∀ x y, (hermForm (Hf z) (P z x) (P z y)).im = (FU.Di i).EF x y := by
  intro E _ _ _ H D l Xo σ n a C g ty FU ρ e hρ0 hρ1
  obtain ⟨ho, hc, hne⟩ := punct_top n a ρ hρ0
  have hsub1 : punct n a ρ ⊆ punct n a 1 := fun b hb => ⟨ball_subset_ball hρ1 hb.1, hb.2⟩
  have hs : ∀ b ∈ punct n a ρ, (C.pt b ≫ C.k) ≫ Xo.s = spMap σ := fun b hb => by
    rw [Category.assoc]
    exact (C.pt_eq b (hsub1 hb)).2
  have hy : IsHolTo (punct n a ρ) (fun b => C.pt b ≫ C.k) :=
    GlobalTheory.HolFibre.isHolTo_comp (isHolTo_mono' (GlobalTheory.CompanionTheory.Ar.Flat.Marking.isHolTo_pt C) hsub1 ho) C.k
  obtain ⟨i, hi⟩ := exists_index FU ho hc hne hs hy
  have loc : ∀ z₀ ∈ punct n a ρ, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ punct n a ρ ∧
      ∃ P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin C.g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧
      ∀ z ∈ N, Module.finrank ℤ (FU.Di i).La = 2 * C.g ∧ Function.Injective (P z) ∧
        ((P z).range : Set (Fin C.g → ℂ)) = e.per z ∧ ∃ Hm : Matrix (Fin C.g) (Fin C.g) ℂ, Good C e z Hm ∧
          ∀ x y, (hermForm Hm (P z x) (P z y)).im = (FU.Di i).EF x y := fun z₀ h => by
    obtain ⟨B', P₀, hB, hz, hsub, hP, hu⟩ := hi z₀ h
    exact ⟨B', hB, hz, hsub, local_marking C FU hρ1 e i P₀ hB hsub hP hu⟩
  have good : ∀ z ∈ punct n a ρ, ∃ Hm, Good C e z Hm := fun z hz => by
    obtain ⟨N, -, hzN, -, P, -, hP⟩ := loc z hz
    obtain ⟨-, -, -, Hm, hg, -⟩ := hP z hzN
    exact ⟨Hm, hg⟩
  choose! Hf hHf using good
  obtain ⟨z₁, hz₁⟩ := hne
  refine ⟨i, Hf, ?_, fun z hz => hHf z hz, fun z₀ hz₀ => ?_⟩
  · obtain ⟨N, -, hzN, -, P, -, hP⟩ := loc z₁ hz₁
    exact (hP z₁ hzN).1
  · obtain ⟨N, hN, hz, hsub, P, hPd, hP⟩ := loc z₀ hz₀
    refine ⟨N, hN, hz, hsub, P, hPd, fun z hzN => ?_⟩
    obtain ⟨-, hinj, hrange, Hm, hg, him⟩ := hP z hzN
    have e1 : Hm = Hf z := isRiemannMatrix_unique C z hg.2.2.1 (hHf z (hsub hzN)).2.2.1
    subst e1
    exact ⟨hinj, hrange, him⟩

end GlobalTheory.CompanionTheory.Ar.Flat
