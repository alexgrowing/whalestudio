import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMAdjoint

theorem adjoint_of_holUnif (hP : GlobalTheory.Published.PeriodComparison) {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) (u : HolUnif A L g) (h : Fin g → ℝ)
    {χ : u.Λ → ℂ} (hah : u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ) {ψ : LinearMap.BilinForm ℂ (HdR A)}
    (hψ : IsPolForm (dp0 ℂ) (𝟙 _) A L ψ) (α β : A ⟶ A) [IsMonHom α] [IsMonHom β] (m m' : Fin g → ℂ)
    (hm : ∀ j, m' j = starRingEnd ℂ (m j))
    (hα : ∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) (hβ : ∀ w, u.ex (fun j ↦ m' j * w j) = u.ex w ≫ β) (x y : HdR A) :
    ψ (push (dp0 ℂ) (𝟙 _) α x) y = ψ x (push (dp0 ℂ) (𝟙 _) β y) := by
  obtain ⟨ε, hP⟩ := hP
  obtain ⟨P, hspan, -, -, hnat, hform⟩ := hP A g hA hg L hL u
  have key : ∀ (δ : A ⟶ A) [IsMonHom δ] (n : Fin g → ℂ), (∀ w, u.ex (fun j ↦ n j * w j) = u.ex w ≫ δ) → ∀ z : u.Λ,
      ∃ z' : u.Λ, (z' : Fin g → ℂ) = (fun j ↦ n j * z.1 j) ∧ push (dp0 ℂ) (𝟙 _) δ (P z) = P z' := by
    intro δ _ n hδ z
    have hz : (fun j ↦ n j * z.1 j) ∈ u.Λ := by
      rw [← u.ker, hδ, (u.ker _).2 z.2, MonObj.one_comp]
    exact ⟨⟨_, hz⟩, rfl, hnat δ (LinearMap.mulLeft ℂ n) hδ z _ rfl⟩
  have e : ψ ∘ₗ push (dp0 ℂ) (𝟙 _) α = ψ.compl₂ (push (dp0 ℂ) (𝟙 _) β) := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨z, rfl⟩
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨w, rfl⟩
    obtain ⟨z', hz', ez⟩ := key α m hα z
    obtain ⟨w', hw', ew⟩ := key β m' hβ w
    rw [LinearMap.comp_apply, LinearMap.compl₂_apply, ez, ew, hform _ χ ψ hah hψ, hform _ χ ψ hah hψ, hz', hw']
    congr 3
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hm, RCLike.star_def, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  exact LinearMap.congr_fun₂ e x y

theorem exists_polForm_pull {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem ne_zero_of_isTotPos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x : F} (h : IsTotPos x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using h (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

theorem adjoint_of_scale {R O M : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing O] [AddCommGroup M] [Module R M]
    (ρ : O →+* Module.End R M) {ψ ψ₀ : LinearMap.BilinForm R M} {n : ℕ} (hn : n ≠ 0) {t a b : O}
    (ht : ∀ x z, (n : R) * ((2 : R) • ψ₀) x z = ψ x (ρ t z)) (adj : ∀ x z, ψ (ρ a x) z = ψ x (ρ b z)) (x z : M) :
    ψ₀ (ρ a x) z = ψ₀ x (ρ b z) := by
  have e := adj x (ρ t z)
  rw [← Module.End.mul_apply (ρ b), ← map_mul, mul_comm b, map_mul, Module.End.mul_apply, ← ht, ← ht] at e
  have e2 := mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) e
  simp only [LinearMap.smul_apply, smul_eq_mul] at e2
  exact mul_left_cancel₀ two_ne_zero e2

theorem half_form_adjoint : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      ∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h') := by
  intro hP hD _ E _ _ _ _ I _ d φ _ 𝔣 _ l _ Q _ _ y _ lam 𝔠 R _ _ X₀ X U p cm hX hF hcm _ _ _ _ c₀ ψ₀ _ hψ₀ a b hab h h'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.PureLift.exists_isPolForm hD.1 X₀.ab X₀.dim (L := X₀.diag U.c) (pull_isLB (X₀.isLB U.c) _)
  letI : Algebra R ℂ := R.subtype.toAlgebra
  have m := GlobalTheory.Published.AbelianDeRham.bcMor (R := R) (R' := ℂ) hX.grp
  have hBC : m.IsBC := (hD.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hX.grp).1
  obtain ⟨ψ', hψ', hc⟩ := exists_polForm_pull R.subtype hX m U.c hψ
  obtain ⟨χ, hχ⟩ := U.ah
  obtain ⟨α, _, eα, hα⟩ := hcm a
  obtain ⟨β, _, eβ, hβ⟩ := hcm b
  haveI := cm.hom
  have adj : ∀ x z : HdR X₀.A, ψ (act (dp0 R) (𝟙 _) cm a x) z = ψ x (act (dp0 R) (𝟙 _) cm b z) := by
    intro x z
    obtain ⟨x', hx⟩ := hBC.exists x
    obtain ⟨z', hz⟩ := hBC.exists z
    refine R.subtype_injective ?_
    rw [act_apply, act_apply, ← hc _ _ _ _ (hx.push m (cm.act a) α eα.symm) hz,
      ← hc _ _ _ _ hx (hz.push m (cm.act b) β eβ.symm)]
    exact adjoint_of_holUnif hP X.ab X.dim (pull_isLB (X.isLB U.c) _) U.u (fun j ↦ U.h (U.e j)) hχ hψ' α β _ _
      (fun j ↦ by rw [hab, IsCMField.complexEmbedding_complexConj]) hα hβ x' z'
  obtain ⟨n, t, hn, ht⟩ := GlobalTheory.T.polarization_forms_commensurable hD _ 𝔠 R X₀ c₀ U.c (ne_zero_of_isTotPos U.pos) _ ψ hψ₀ hψ
  have et : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) t) := by
    haveI := X₀.rm.hom
    rw [act_apply, act_apply]
    exact push_congr _ _ (hF t).symm
  exact adjoint_of_scale (act (dp0 R) (𝟙 _) cm) hn (fun x z ↦ (ht x z).trans (congrArg (fun T ↦ ψ x (T z)) et)) adj h h'

end GlobalTheory.CMAdjoint
