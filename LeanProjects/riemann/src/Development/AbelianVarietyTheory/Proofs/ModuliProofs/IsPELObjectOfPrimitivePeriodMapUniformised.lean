import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActOfMapLatticeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMActionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriodMapGenusStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PeriodObject

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun z i => ty i (a : E) * z i
      map_add' := fun z w => by funext i; simp [mul_add]
      map_smul' := fun c z => by funext i; simp [mul_left_comm] }
  map_one' := by ext z i; simp
  map_mul' a b := by
    ext z i
    show ty i ((a * b : 𝓞 E) : E) * _ = ty i (a : E) * (ty i (b : E) * _)
    push_cast
    rw [map_mul, _root_.mul_assoc]
  map_zero' := by ext z i; simp
  map_add' a b := by ext z i; simp [add_mul]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by simp [hermForm])
    (fun c z w => by simp [hermForm, smul_dotProduct])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun c z w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    {s : Set (Fin g → ℂ)} (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have e : (imForm Hm).comp (F.restrictScalars ℝ) = (imForm Hm).compl₂ (F'.restrictScalars ℝ) :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have im : ∀ z w, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im := fun z w =>
    LinearMap.congr_fun (LinearMap.congr_fun e z) w
  refine Complex.ext ?_ (im z w)
  have := im (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

theorem pelClass_of_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D o _ g k J b em w w' a bas ρ ty t D' f ν Q Hm hpq hw hρ hty hgen hζ hper hpol
    ⟨u, χ, hAH, hΛ, _, hpt, hF⟩ hprim
  have := t.ab.comm
  have hQ : ∀ (c : 𝓞 E) x, diagAct ty c (Q x) = Q (c • x) := fun c x => funext fun i => (hper.1 c x i).symm
  have hkeep : ∀ c, ∀ z ∈ u.Λ, diagAct ty c z ∈ u.Λ := fun c z hz => by
    obtain ⟨x, rfl⟩ := (hΛ z).1 hz
    exact (hΛ _).2 ⟨c • x, (hQ c x).symm⟩
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_oAct_of_endo_preserving_lattice h₁ h₂ h₃ h₄ (𝓞 E) t.pol u (diagAct ty) hkeep
  change OAct (𝓞 E) t.A at act
  have hj : ∀ j, act.act (a j) = t.act j := fun j => by
    obtain ⟨F, hFQ, hFe⟩ := hF j
    have e : F.restrictScalars ℝ = (diagAct ty (a j)).restrictScalars ℝ :=
      LinearMap.ext_on_range hpol.2.2.1 fun x => (hFQ x).trans (hQ _ x).symm
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h₁ h₂ h₃ h₄ t.pol t.pol t.L t.L u u (diagAct ty (a j)) (hkeep _)).unique
      ⟨act.hom _, hact _⟩ ⟨t.hom j, fun z => ?_⟩
    exact (congrArg u.ex (LinearMap.congr_fun e z).symm).trans (hFe z)
  have hadj : ∀ c, LBIso (cubeLB t.A ![fst t.A t.A ≫ act.act c, snd t.A t.A] t.L)
      (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ act.act (H.bar c)] t.L) := fun c => by
    refine (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h₁ h₂ h₃ h₄ t.pol u Hm χ _ _ _ _ hAH (act.hom c) (act.hom (H.bar c)) (hact c)
      (hact (H.bar c))).2 (hermForm_adjoint_of_span Hm (diagAct ty c) (diagAct ty (H.bar c)) hpol.2.2.1 ?_)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have e := D'.adj c x y
    rw [hQ, hQ, hpol.2.2.2.2.2, hpol.2.2.2.2.2, e]
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation h₁.globalFns E H _ t.A act t.L t.ab
    t.isLB (h₃ _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    rw [← hw, hj] at iso
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.2.2.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, act, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · show act.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hj, Category.comp_id, Category.id_comp]
  obtain ⟨σ, rfl⟩ : ∃ σ : ℂ →+* K, x = spMap σ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain rfl : σ.comp em = β :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_apply, hρ]
    exact GlobalTheory.T.determinantCondition_of_diagonalCMAction h₁ h₂ h₃ h₄ E H D t.pol u Hm χ act ty hAH hty hact K σ
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_tateIso_of_periodMap_genus_alt h₁ h₂ h₃ h₄ E H D D' f ν t.pol u Hm χ act Q hpq hgen hAH hpol.1 hΛ hpol.2.2.2.2.2
    (fun c n x => by
      rw [← hact, map_smul]
      exact congrArg (fun z => u.ex ((n : ℂ)⁻¹ • z)) (hQ c x).symm) K σ
  refine ⟨{ I with isom := fun n hn x y => weilIs_of_lbIso h₁.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn x y) },
    ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, hζ]
    exact (hI k hk).1
  · apply Over.OverMorphism.ext
    show (I.ev k _).left ≫ 𝟙 _ = spMap σ ≫ (t.pt i).left
    rw [Category.comp_id, hpt]
    exact (hI k hk).2 _

end GlobalTheory.PeriodObject
