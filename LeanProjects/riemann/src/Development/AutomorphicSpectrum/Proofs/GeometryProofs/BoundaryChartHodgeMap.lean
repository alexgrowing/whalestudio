import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif

section Lin

variable {g : ℕ}

theorem hf_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x x' y : Fin g → ℂ) :
    hermForm Hm (x + x') y = hermForm Hm x y + hermForm Hm x' y := by
  simp [hermForm, add_dotProduct]

theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x y : Fin g → ℂ) :
    hermForm Hm (c • x) y = c * hermForm Hm x y := by
  simp [hermForm, smul_dotProduct]

theorem hf_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) :
    hermForm Hm x (y + y') = hermForm Hm x y + hermForm Hm x y' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hf_real_right (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (x y : Fin g → ℂ) :
    hermForm Hm x (r • y) = r * hermForm Hm x y := by
  have e : star (r • y) = (r : ℂ) • star y := by
    ext i
    simp
  simp [hermForm, e, Matrix.mulVec_smul, dotProduct_smul]

theorem real_smul_eq (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem hermForm_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤) (a a' : 𝓞 E)
    (ha : (a' : E) = IsCMField.complexConj E (a : E)) (x y : Fin g → ℂ) :
    hermForm R.Hm (R.B a x) y = hermForm R.Hm x (R.B a' y) := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => hermForm R.Hm (R.B a x) y - hermForm R.Hm x (R.B a' y)
  have hl : ∀ x x' y, D (x + x') y = D x y + D x' y := fun x x' y => by
    simp only [D, map_add, hf_add_left]
    ring
  have hr : ∀ x y y', D x (y + y') = D x y + D x y' := fun x y y' => by
    simp only [D, map_add, hf_add_right]
    ring
  have hc : ∀ (c : ℂ) x y, D (c • x) y = c * D x y := fun c x y => by
    simp only [D, map_smul, hf_smul_left]
    ring
  have hrr : ∀ (r : ℝ) x y, D x (r • y) = r * D x y := fun r x y => by
    have e : R.B a' (r • y) = r • R.B a' y := by
      rw [real_smul_eq, map_smul, real_smul_eq]
    simp only [D, e, hf_real_right]
    ring
  have h0l : ∀ y, D 0 y = 0 := fun y => by
    have := hc 0 0 y
    simpa using this
  have h0r : ∀ x, D x 0 = 0 := fun x => by
    have := hrr 0 x 0
    simpa using this
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    have h1 := R.im (a • l) l'
    have h2 := R.im l (a' • l')
    rw [R.act] at h1
    rw [R.act] at h2
    have h3 := R.adj a a' ha l l'
    simp only [D, Complex.sub_im, hermForm]
    rw [h1, h2, h3, sub_self]
  have s1 : ∀ l y, (D (R.P l) y).im = 0 := fun l y => by
    have hy : y ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add y y' _ _ h h' => simp [hr, h, h']
    | smul r y _ h => simp [hrr, h]
  have s2 : ∀ x y, (D x y).im = 0 := fun x y => by
    have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l y
    | zero => simp [h0l]
    | add x x' _ _ h h' => simp [hl, h, h']
    | smul r x _ h =>
      rw [real_smul_eq, hc]
      simp [h]
  have s3 : D x y = 0 := by
    refine Complex.ext ?_ (s2 x y)
    have := s2 (Complex.I • x) y
    rw [hc] at this
    simpa using this
  exact sub_eq_zero.1 s3

theorem bijective_of_countable {g' : ℕ} (h : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {K : Set (Fin g → ℂ)}
    {K' : Set (Fin g' → ℂ)} (hK : K.Countable) (hK' : K'.Countable) (hs : ∀ y, ∃ z, y - h z ∈ K)
    (hk : ∀ z, h z = 0 → z ∈ K') : Function.Bijective h := by
  refine ⟨(injective_iff_map_eq_zero h).2 fun z hz => ?_, fun y => ?_⟩
  · exact GlobalTheory.eq_zero_of_forall_smul_mem_countable hK' fun s => hk _ (by rw [map_smul, hz, smul_zero])
  · have h0 : (LinearMap.range h).mkQ y = 0 := by
      refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hK.image (LinearMap.range h).mkQ) fun s => ?_
      obtain ⟨z, hz⟩ := hs (s • y)
      refine ⟨_, hz, ?_⟩
      simp only [map_sub, map_smul, Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range h)).2 ⟨z, rfl⟩, sub_zero]
    have : y ∈ LinearMap.range h := by simpa using h0
    exact this

theorem herm_transport' {g' : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (hH : Hm.IsHermitian) : ∃ Hf : Matrix (Fin g') (Fin g') ℂ, Hf.IsHermitian ∧
      ∀ x y, hermForm Hf (h x) (h y) = hermForm Hm x y := by
  let A : Matrix (Fin g) (Fin g') ℂ := LinearMap.toMatrix' (h.symm : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hA : ∀ x, A.mulVec (h x) = x := fun x => by
    simp [A, LinearMap.toMatrix'_mulVec]
  refine ⟨A.transpose * Hm * A.transpose.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun x y => ?_⟩
  unfold hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.star_vecMul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.vecMul_transpose, hA, hA]

end Lin

section Pts

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A] {y : Sp ℂ ⟶ S} {φ : A.left ⟶ G.left}

def ptMap (hw : φ ≫ G.hom = A.hom ≫ y) (q : 𝟙_ (Over (Sp ℂ)) ⟶ A) : Over.mk y ⟶ G :=
  Over.homMk (q.left ≫ φ) (by
    have h : q.left ≫ A.hom = 𝟙 _ := Over.w q
    show (q.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, hw, ← Category.assoc, h, Category.id_comp])

@[simp] theorem ptMap_left (hw : φ ≫ G.hom = A.hom ≫ y) (q : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (ptMap hw q).left = q.left ≫ φ := rfl

theorem ptMap_mul (hp : IsGrpPullback A G y φ) (q q' : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    ptMap hp.1.w (q * q') = ptMap hp.1.w q * ptMap hp.1.w q' := by
  let ρ : Over.mk y ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y) := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (𝟙 _ ≫ y) = y
    simp)
  have e : ∀ a, ptMap hp.1.w a = ρ ≫ pushPt hp.1.w a := fun a =>
    Over.OverMorphism.ext (by simp [ρ, pushPt])
  have h := hp.2 (𝟙_ _) q q' (pushPt hp.1.w q) (pushPt hp.1.w q') rfl rfl
  rw [e q, e q', ← MonObj.comp_mul]
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, h]
  simp [ρ]

theorem ptMap_injective (hp : IsGrpPullback A G y φ) : Function.Injective (ptMap (y := y) hp.1.w) := fun q q' h =>
  Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun p => p.left) h) (by
    have h1 : q.left ≫ A.hom = 𝟙 _ := Over.w q
    have h2 : q'.left ≫ A.hom = 𝟙 _ := Over.w q'
    rw [h1, h2]))

theorem ptMap_surjective (hp : IsGrpPullback A G y φ) : Function.Surjective (ptMap (y := y) hp.1.w) := fun p => by
  have hw : p.left ≫ G.hom = 𝟙 _ ≫ y := by
    rw [Category.id_comp]
    exact Over.w p
  refine ⟨Over.homMk (hp.1.lift p.left (𝟙 _) hw) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
  exact hp.1.lift_fst _ _ _

theorem ptMap_one (hp : IsGrpPullback A G y φ) : ptMap hp.1.w (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = 1 := by
  have := ptMap_mul hp 1 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

end Pts

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isAH_reparam (u : HolUnif A L g) (X : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Hm Hf : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (hAH : u.IsAH Hm χ) (hHf : Hf.IsHermitian)
    (hf : ∀ x y, hermForm Hf x y = hermForm Hm (X x) (X y)) :
    ∃ (u₂ : HolUnif A L g) (χ₂ : u₂.Λ → ℂ), (∀ z, u₂.ex z = u.ex (X z)) ∧ (∀ z, z ∈ u₂.Λ ↔ X z ∈ u.Λ) ∧
      u₂.IsAH Hf χ₂ ∧ ∀ w v, u.IsDiff (X w) v → u₂.IsDiff w v := by
  refine ⟨GlobalTheory.holUnifReparam u X (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero),
    fun l => χ ⟨X l, l.2⟩, fun _ => rfl, fun _ => Iff.rfl, ⟨hHf, ?_, fun l => hAH.2.2.1 _, ?_⟩, ?_⟩
  · intro z hz
    have h := hAH.2.1 (X z) ((LinearEquiv.map_ne_zero_iff X).2 hz)
    have e := hf z z
    unfold hermForm at e
    rw [e]
    exact h
  · intro l i z hz
    have h := hAH.2.2.2 ⟨X l, l.2⟩ i (X z) hz
    have e1 := hf z l
    have e2 := hf l l
    unfold hermForm at e1 e2
    show u.fr i (X z) / 1 = χ ⟨X l, l.2⟩ * Complex.exp (Real.pi * (z ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ)))) * (u.fr i (X (z + l)) / 1)
    rw [div_one, div_one, map_add, h, e1, e2]
  · intro w v hv U h f
    rw [hv U h f]
    have key := X.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end Reparam

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_fibre_lift {R : Type} [CommRing R] {t : SAB H (Sp R)} {T : Scheme.{0}} {tt : SAB H T} {jj : Sp R ⟶ T}
    (m : SABMap t tt jj) {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B₀ : Set (Fin n → ℂ)}
    {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : Flat.FamExp t.G M B₀ ψ) {b : Fin n → ℂ} (hb : b ∈ B₀)
    {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ tt.G.left} {g' : ℕ} {L : LB A.left} (u' : HolUnif A L g')
    (hp : IsGrpPullback A tt.G (spMap (ψ b) ≫ jj) φ) :
    ∃ (φ' : A.left ⟶ t.G.left) (h : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), φ' ≫ m.φ = φ ∧
      (∀ z, (e.ex b (h z)).left = (u'.ex z).left ≫ φ') ∧ (∀ z, e.ex b (h z) = 1 ↔ u'.ex z = 1) ∧
      (e.per b).Countable ∧ e.ex b 0 = 1 ∧
      (1 : Over.mk (spMap (ψ b)) ⟶ t.G).left ≫ m.φ = (1 : Over.mk (spMap (ψ b) ≫ jj) ⟶ tt.G).left ∧
      ∀ z v, IsDerivAt0 (fun x => (e.ex b x).left) (h z) v →
        ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ' = v ∧ u'.IsDiff z v' := by
  have sq : φ ≫ tt.G.hom = (A.hom ≫ spMap (ψ b)) ≫ jj := by
    rw [Category.assoc]
    exact hp.1.w
  let φ' : A.left ⟶ t.G.left := m.cart.1.lift φ (A.hom ≫ spMap (ψ b)) sq
  have h1 : φ' ≫ m.φ = φ := m.cart.1.lift_fst _ _ sq
  have h2 : φ' ≫ t.G.hom = A.hom ≫ spMap (ψ b) := m.cart.1.lift_snd _ _ sq
  have hp' : IsGrpPullback A t.G (spMap (ψ b)) φ' := m.cart.cancel (hp.congr rfl h1.symm) h2
  let uu : (Fin g' → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => ptMap hp'.1.w (u'.ex z)
  have hadd : ∀ z w, uu (z + w) = uu z * uu w := fun z w => by
    simp only [uu]
    rw [u'.ex_add, ptMap_mul hp']
  have hol0 : IsHolTo Set.univ (fun z => (u'.ex z).left ≫ φ') :=
    GlobalTheory.HolTorsion.isHolTo_comp (Flat.PerGram.isHolTo_ex u') φ'
  obtain ⟨hf, -, hh⟩ := Flat.exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b)
    (Flat.ExpOnto.atPoint e hb) g' Set.univ (fun _ z => uu z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (Flat.ExpOnto.isHolTo_const_param (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (uu z).left) hol0)
  obtain ⟨hex, -, hder⟩ := hh 0 trivial
  have hex' : ∀ z, e.ex b (hf 0 z) = uu z := hex
  have hder' : ∀ z v, IsDerivAt0 (fun z => (uu z).left) z v ↔ IsDerivAt0 (fun z => (e.ex b z).left) (hf 0 z) v := hder
  obtain ⟨Γ₀, hΓ, hd, -, -⟩ := Flat.FamExp.per_discrete R t.G g n M B₀ ψ e b hb
  have hcount : (e.per b).Countable := by
    rw [← hΓ]
    haveI := hd
    have : Countable Γ₀ := countable_of_Lindelof_of_discrete
    exact Set.countable_coe_iff.1 this
  have hcount' : (u'.Λ : Set (Fin g' → ℂ)).Countable := by
    haveI := u'.discrete
    have : Countable u'.Λ := countable_of_Lindelof_of_discrete
    exact Set.countable_coe_iff.1 this
  have e0 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have one' : uu 0 = 1 := by
    simp only [uu]
    rw [(u'.ker 0).2 u'.Λ.zero_mem]
    exact ptMap_one hp'
  have hiff : ∀ z, e.ex b (hf 0 z) = 1 ↔ u'.ex z = 1 := fun z => by
    rw [hex']
    constructor
    · intro hz
      refine ptMap_injective hp' ?_
      rw [ptMap_one hp']
      exact hz
    · intro hz
      simp only [uu]
      rw [hz]
      exact ptMap_one hp'
  have hbij : Function.Bijective (hf 0) := by
    refine bijective_of_countable (hf 0) hcount hcount' (fun y => ?_) (fun z hz => ?_)
    · obtain ⟨q', hq'⟩ := ptMap_surjective hp' (e.ex b y)
      obtain ⟨z, rfl⟩ := u'.ex_onto q'
      refine ⟨z, ?_⟩
      show e.ex b (y - hf 0 z) = 1
      have h3 : e.ex b (y - hf 0 z) * e.ex b (hf 0 z) = e.ex b y := by
        rw [← e.add b hb, sub_add_cancel]
      have h4 : e.ex b (hf 0 z) = e.ex b y := (hex' z).trans hq'
      rw [h4] at h3
      exact mul_eq_right.1 h3
    · exact (u'.ker z).1 ((hiff z).1 (by rw [hz, e0]))
  refine ⟨φ', LinearEquiv.ofBijective (hf 0) hbij, h1, fun z => ?_, fun z => hiff z, hcount, e0, ?_, ?_⟩
  · exact congrArg (fun q => q.left) (hex' z)
  · have a1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ≫ φ' = (1 : Over.mk (spMap (ψ b)) ⟶ t.G).left :=
      congrArg (fun q => q.left) (ptMap_one hp')
    have a2 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ≫ φ = (1 : Over.mk (spMap (ψ b) ≫ jj) ⟶ tt.G).left :=
      congrArg (fun q => q.left) (ptMap_one hp)
    rw [← a1, Category.assoc, h1, a2]
  · intro z v H
    have hv := GlobalTheory.VerticalDeriv.isDerivAt0_vertical t.G.hom (spMap (ψ b)) (e := fun z => (e.ex b z).left)
      (fun z => Over.w (e.ex b z)) H
    have H1 := (hder' z v).2 H
    have l1 : hp'.1.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv ≫ φ' = v := hp'.1.lift_fst _ _ hv
    have l2 : hp'.1.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) :=
      hp'.1.lift_snd _ _ hv
    have H2 : IsDerivAt0 (fun z => (u'.ex z).left) z (hp'.1.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv) :=
      GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback hp'.1 (fun z => Over.w (u'.ex z)) hol0 l2 (by rw [l1]; exact H1)
    exact ⟨Over.homMk _ l2, l1, fun U h f => H2.2 U h f⟩

end Fibre

section Main

theorem exists_unif_of_interior : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (B₀ : Set (Fin n → ℂ)) (e : Flat.FamExp C.t.G C.M B₀ C.ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin C.g → ℂ)) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ), 1 ≤ D.p + D.q → b ∈ B₀ → 𝔐.Interior (spMap (C.ψ b) ≫ jj) → C.IsRiem b Hm → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ C.t.act.act a') → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ 𝔐.t.G.left) (u : HolUnif A (𝔐.t.PP.L.pull φ) C.g) (χ : u.Λ → ℂ), IsGrpPullback A 𝔐.t.G (spMap (C.ψ b) ≫ jj) φ ∧ u.IsAH Hm χ ∧ (∀ x, (u.ex x).left ≫ φ = (e.ex b x).left ≫ m.φ) ∧ (∀ x, x ∈ u.Λ ↔ x ∈ e.per b) ∧ (∀ (x : Fin C.g → ℂ) (v : Sp (DualNumber ℂ) ⟶ C.t.G.left), IsDerivAt0 (fun x => (e.ex b x).left) x v → ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = v ≫ m.φ ∧ u.IsDiff x v') ∧ ∀ a' a'' : 𝓞 E, (a'' : E) = IsCMField.complexConj E (a' : E) → ∀ x x', hermForm Hm (Bb a' x) x' = hermForm Hm x (Bb a'' x') := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 σ n a C jj m B₀ e b Bb Hm hD hb hint hR hact
  have hpol := HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S Ω K J y 𝔐 (spMap (C.ψ b) ≫ jj) hint
  obtain ⟨g', Λ, i₁, i₂, R', x, hF, -, -⟩ := GlobalTheory.T.interior_point_lattice_data hG.2.2.2.2.1 E H D l Xo c Y S Ω K J y 𝔐
    (spMap (C.ψ b) ≫ jj) hD hint hG Empty (fun i => i.elim) (fun i => i.elim)
  obtain ⟨A, iA, φ, u', χ', hp, hAH, hact', hinj, hmem, -⟩ := hF
  obtain ⟨φ', h, h1, hex, hiff, hcount, e0, hone, hder⟩ := exists_fibre_lift m e hb u' hp
  have hg : g' = C.g := by simpa using h.finrank_eq
  subst hg
  obtain ⟨Hf, hHf, hff⟩ := herm_transport' R'.Hm h R'.herm
  have hf2 : ∀ x y, hermForm Hf x y = hermForm R'.Hm (h.symm x) (h.symm y) := fun x y => by
    rw [← hff, h.apply_symm_apply, h.apply_symm_apply]
  obtain ⟨u, χ, hue, huΛ, huAH, hud⟩ := isAH_reparam u' h.symm R'.Hm Hf χ' hAH hHf hf2
  have hφ : ∀ x, (u.ex x).left ≫ φ = (e.ex b x).left ≫ m.φ := fun x => by
    have h3 := hex (h.symm x)
    rw [h.apply_symm_apply] at h3
    rw [hue]
    calc (u'.ex (h.symm x)).left ≫ φ = (u'.ex (h.symm x)).left ≫ φ' ≫ m.φ :=
          congrArg (fun q => (u'.ex (h.symm x)).left ≫ q) h1.symm
      _ = _ := by rw [h3, Category.assoc]
  have hper : ∀ x, x ∈ u.Λ ↔ x ∈ e.per b := fun x => by
    have h3 := hiff (h.symm x)
    rw [h.apply_symm_apply] at h3
    rw [huΛ, ← u'.ker, ← h3]
    rfl
  have hdv : ∀ x v, IsDerivAt0 (fun x => (e.ex b x).left) x v →
      ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ' = v ∧ u.IsDiff x v' := fun x v H => by
    obtain ⟨v', e1, e2⟩ := hder (h.symm x) v (by rw [h.apply_symm_apply]; exact H)
    exact ⟨v', e1, hud x v' e2⟩

  have hsq : spMap (dualMap (C.ψ b)) ≫ spMap (algebraMap C.R (DualNumber C.R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ b) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hT : ∀ u : Fin C.g → C.R, ∃ v : epsAt (spMap (C.ψ b)) ⟶ C.t.G,
      v.left = spMap (dualMap (C.ψ b)) ≫ (C.M.pt u).left := fun u =>
    ⟨Over.homMk (spMap (dualMap (C.ψ b)) ≫ (C.M.pt u).left) (by
      have hw := Over.w (C.M.pt u)
      show (spMap (dualMap (C.ψ b)) ≫ (C.M.pt u).left) ≫ C.t.G.hom =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ b)
      rw [Category.assoc, hw, ← hsq]
      simp), rfl⟩
  choose w hw using fun c : Fin C.g => hT (Pi.single c 1)
  have hvv : C.IsVal b (fun c => Pi.single c 1) w := fun c => hw c
  have he : ∀ c : Fin C.g, (fun k => C.ψ b ((Pi.single c 1 : Fin C.g → C.R) k)) = (Pi.single c 1 : Fin C.g → ℂ) :=
    fun c => by
      ext k
      by_cases h : k = c
      · subst h; simp
      · simp [Pi.single_apply, h]
  have hs : ∀ (Q : Matrix (Fin C.g) (Fin C.g) ℂ) c d,
      hermForm Q (Pi.single c 1) (Pi.single d 1) = Q c d := fun Q c d => by
    have : star (Pi.single d 1 : Fin C.g → ℂ) = Pi.single d 1 := by
      ext k
      by_cases h : k = d
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp [hermForm, this]
  have hG1 := (hR C.g _ w (Matrix.of fun c d => (Real.pi : ℂ) * hermForm Hm
    (fun k => C.ψ b ((Pi.single c 1 : Fin C.g → C.R) k)) (fun k => C.ψ b ((Pi.single d 1 : Fin C.g → C.R) k))) hvv).2
    (fun _ _ => rfl)
  have hZ : ∀ c, ((w c).left ≫ m.φ) ≫ 𝔐.t.G.hom =
      (epsAt (spMap (C.ψ b) ≫ jj)).hom := fun c => by
    have h3 : (w c).left ≫ C.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ b) := Over.w (w c)
    show ((w c).left ≫ m.φ) ≫ 𝔐.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (C.ψ b) ≫ jj
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, h3, Category.assoc]
  let vZ : Fin C.g → (epsAt (spMap (C.ψ b) ≫ jj) ⟶ 𝔐.t.G) := fun c => Over.homMk ((w c).left ≫ m.φ) (hZ c)
  have hG2 := (Flat.hodgeGram_iff_of_sabMap E H _ _ 𝔐.t C.t jj m (spMap (C.ψ b)) (spMap (C.ψ b) ≫ jj) C.g w vZ _ rfl
    (fun c => rfl)).1 hG1
  have hdw : ∀ c, IsDerivAt0 (fun x => (e.ex b x).left) (Pi.single c 1) (w c).left := fun c => by
    rw [hw c]
    exact e.diff b hb c
  have htan : ∀ c, IsTanAt 𝔐.t.G (spMap (C.ψ b) ≫ jj) (vZ c) := fun c => by
    show _ ≫ (w c).left ≫ m.φ = _
    have h3 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (w c).left = (e.ex b 0).left := (hdw c).1
    rw [e0] at h3
    rw [← hone, ← Category.assoc]
    exact congrArg (· ≫ m.φ) h3
  have hform := Fl.hodgeForm_of_isHodgeGram 𝔐.X 𝔐.t.G 𝔐.t.PP.L _ C.g vZ _ 𝔐.t.PP.isLB htan hG2
  choose v'' hv1 hv2 using fun c => hdv _ _ (hdw c)
  have hvφ : ∀ c, (v'' c).left ≫ φ = (vZ c).left := fun c => by
    rw [← h1, ← Category.assoc, hv1 c]
    rfl
  have hform2 : ∀ c d, HodgeForm 𝔐.t.G 𝔐.t.PP.L (spMap (C.ψ b) ≫ jj) (vZ c) (vZ d)
      (Real.pi * hermForm Hf (Pi.single c 1) (Pi.single d 1)) := fun c d =>
    ⟨𝔐.t.PP.isLB, htan c, htan d, A, iA, φ, C.g, u, Hf, χ, v'' c, v'' d, _, _, hp, huAH, hvφ c, hvφ d, hv2 c, hv2 d, rfl⟩
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists _ 𝔐.t.G ℂ (spMap (C.ψ b) ≫ jj)
  obtain ⟨f, hf, -, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H 𝔐.X 𝔐.t _ V Mz hpol
  have huq : ∀ c d c₁ c₂, HodgeForm 𝔐.t.G 𝔐.t.PP.L (spMap (C.ψ b) ≫ jj) (vZ c) (vZ d) c₁ →
      HodgeForm 𝔐.t.G 𝔐.t.PP.L (spMap (C.ψ b) ≫ jj) (vZ c) (vZ d) c₂ → c₁ = c₂ := fun c d c₁ c₂ a₁ a₂ => by
    obtain ⟨p, hp₁⟩ := Mz.onto _ (htan c)
    obtain ⟨q, hq₁⟩ := Mz.onto _ (htan d)
    have b₁ := hodgeInnerProduct_iff_hodgeForm.2 a₁
    have b₂ := hodgeInnerProduct_iff_hodgeForm.2 a₂
    rw [← hp₁, ← hq₁] at b₁ b₂
    exact ((hf q p _).1 b₁).trans ((hf q p _).1 b₂).symm
  have hHfm : Hf = Hm := by
    ext c d
    have h3 := huq c d _ _ (hform c d) (hform2 c d)
    simp only [Matrix.of_apply, he, hs] at h3
    exact (mul_left_cancel₀ (by exact_mod_cast Real.pi_ne_zero) h3).symm

  have hsub : ∀ p q, e.ex b p = e.ex b q → p - q ∈ e.per b := fun p q hpq => by
    show e.ex b (p - q) = 1
    have h3 : e.ex b (p - q) * e.ex b q = e.ex b p := by
      rw [← e.add b hb, sub_add_cancel]
    rw [hpq] at h3
    exact mul_eq_right.1 h3
  have hB : ∀ (a' : 𝓞 E) (y : Fin C.g → ℂ), Bb a' (h y) = h (R'.B a' y) := fun a' y => by
    have k1 : ∀ y, e.ex b (h (R'.B a' y)) = e.ex b (h y) ≫ C.t.act.act a' := fun y => by
      refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)
      · rw [Over.comp_left, hex, hex, Category.assoc, h1, hact' a' y, Category.assoc, Category.assoc]
        rw [m.act a', ← Category.assoc φ', h1]
      · rw [Over.w (e.ex b (h (R'.B a' y))), Over.w (e.ex b (h y) ≫ C.t.act.act a')]
    let Lm : (Fin C.g → ℂ) →ₗ[ℂ] (Fin C.g → ℂ) :=
      (Bb a').comp h.toLinearMap - h.toLinearMap.comp (R'.B a')
    have hL : ∀ y, Lm y ∈ e.per b := fun y => hsub _ _ ((hact a' (h y)).trans (k1 y).symm)
    have h0 : Lm y = 0 := GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun s => by
      rw [← map_smul]
      exact hL _
    exact sub_eq_zero.1 h0
  have hspan : Submodule.span ℝ (Set.range R'.P) = ⊤ := by
    have e1 : Set.range R'.P = (u'.Λ : Set (Fin C.g → ℂ)) := Set.ext fun p => (hmem p).symm
    rw [e1]
    exact u'.full
  refine ⟨A, iA, φ, u, χ, hp, hHfm ▸ huAH, hφ, hper, fun x v H => ?_, fun a' a'' ha x x' => ?_⟩
  · obtain ⟨v', e1, e2⟩ := hdv x v H
    exact ⟨v', by rw [← h1, ← Category.assoc, e1], e2⟩
  · obtain ⟨p, rfl⟩ := h.surjective x
    obtain ⟨q, rfl⟩ := h.surjective x'
    rw [hB, hB, ← hHfm, hff, hff]
    exact hermForm_adj R' hspan a' a'' ha p q

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif
