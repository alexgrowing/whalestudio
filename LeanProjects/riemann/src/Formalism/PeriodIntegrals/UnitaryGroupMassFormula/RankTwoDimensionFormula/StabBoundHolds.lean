import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfThree
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula.StabB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def hmat (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E :=
  M.map X.ιE.toRingHom

def gOf (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (hmat X (M : Matrix _ _ _)))
    (Matrix.toLin X.bas X.bas (hmat X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix _ _ _)))
    (by
      rw [← Matrix.toLin_mul, hmat, hmat, ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin_one])
    (by
      rw [← Matrix.toLin_mul, hmat, hmat, ← Matrix.map_mul, Units.inv_mul,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin_one])

theorem crd_gOf (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (gOf X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := by
  have hr : ⇑(X.bas.repr (gOf X M y)) = hmat X (M : Matrix _ _ _) *ᵥ ⇑(X.bas.repr y) := by
    show ⇑(X.bas.repr (Matrix.toLin X.bas X.bas (hmat X (M : Matrix _ _ _)) y)) = _
    rw [← LinearMap.toMatrix_mulVec_repr (v₁ := X.bas) (v₂ := X.bas), LinearMap.toMatrix_toLin]
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]
  rw [hr]
  simp [Matrix.mulVec, dotProduct, hmat, map_sum, crdOf]

theorem crd_injective : Function.Injective X.crd := by
  intro a b h
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.crd crdOf at h
  apply X.bas.repr.injective
  ext i
  exact X.ιE.symm.injective (congrFun h i)

theorem incl_mulVec {I : Formalism.MainNotions.S.AutInst} (M : Matrix (Fin I.n) (Fin I.n) I.E) (v : Fin I.n → I.E) :
    M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ incl I v = incl I (M *ᵥ v) := by
  unfold incl
  funext i
  exact (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) M v i).symm

theorem af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨p, hne, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hne⟩
  exact RingHom.domain_nontrivial (RestrictedProduct.evalRingHom (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v :
    Af F →+* v.adicCompletion F)

theorem incl_injective (I : Formalism.MainNotions.S.AutInst) : Function.Injective (incl I) := by
  haveI := af_nontrivial I.F
  have hi : Function.Injective (Formalism.UG.inclE (F := I.F) (Af I.F) : I.E →+* _) := RingHom.injective _
  intro a b h
  unfold incl at h
  funext i
  exact hi (congrFun h i)

theorem star_host (x : X.B.I.E) : star (X.ιE x) = X.ιE (star x) := by
  rw [X.ιE_conj]
  exact Formalism.BasicNotions.Examples₂.star_eq_conj _ _

theorem gOf_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    gOf X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hg : ∀ i, gOf X M (X.bas i) = ∑ k, hmat X (M : Matrix _ _ _) k i • X.bas k :=
    fun i => Matrix.toLin_self _ _ _ _
  have hU : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) = X.B.I.J := hM
  have key : ∀ i j, (VS D).hT (gOf X M (X.bas i)) (gOf X M (X.bas j)) = (VS D).hT (X.bas i) (X.bas j) := by
    intro i j
    rw [hg, hg, ← X.J_eq, ← congrFun (congrFun hU i) j]
    simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.map_smul, smul_eq_mul, ← X.J_eq,
      hmat, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, starRingEnd_apply, star_host,
      Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  intro x y
  rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  simp only [map_sum, LinearEquiv.map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.map_smul,
    smul_eq_mul, key]

def matOf (η : X.B.I.Gf) : GL (Fin X.B.I.n) X.B.I.E :=
  if h : ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat η = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) then h.choose else 1

theorem matOf_spec (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) :
    matOf X (η : X.B.I.Gf) ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (η : X.B.I.Gf) = (matOf X (η : X.B.I.Gf) : Matrix _ _ _).map
        (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  obtain ⟨γ, rfl⟩ := hη
  have hγ := γ.2
  unfold Gam at hγ
  have h1 := hγ.1
  unfold Formalism.MainNotions.LeviCoordinates.rr_GF at h1
  have h2 : (γ : X.B.I.Ginf × X.B.I.Gf) ∈ X.B.I.GFset := h1
  unfold Formalism.MainNotions.S.AutInst.GFset at h2
  obtain ⟨M, hM, -, hf⟩ := h2
  unfold matOf
  split_ifs with h
  · exact h.choose_spec
  · exact (h ⟨M, hM, hf⟩).elim

theorem gOf_fix (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) (v : (VS D).V)
    (hv : X.crd v ∈ fixSet X u) : gOf X (matOf X (η : X.B.I.Gf)) v = v := by
  apply crd_injective X
  rw [crd_gOf]
  apply incl_injective X.B.I
  rw [← incl_mulVec, ← (matOf_spec X u η hη).2]
  have hH := η.2
  unfold Hfin at hH
  unfold Formalism.L2.SG.PoincareInHH.HfinS at hH
  exact hH _ hv

theorem gOf_e (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) (a : Fin D.R.rS) :
    gOf X (matOf X (η : X.B.I.Gf)) (X.eX a) = X.eX a :=
  gOf_fix X u η hη _ (Or.inl (Or.inl ⟨a, rfl⟩))

theorem gOf_f (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) (a : Fin D.R.rS) :
    gOf X (matOf X (η : X.B.I.Gf)) (X.fY a) = X.fY a :=
  gOf_fix X u η hη _ (Or.inl (Or.inr ⟨a, rfl⟩))

theorem gOf_stabF (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) :
    gOf X (matOf X (η : X.B.I.Gf)) ∈ stabF D (X.Fu u) := by
  have he : ∀ i, gOf X (matOf X (η : X.B.I.Gf)) ((X.Fu u).e i) = (X.Fu u).e i := by
    intro i; rw [X.Fu_e]; exact gOf_e X u η hη i
  refine ⟨gOf_isom X _ (matOf_spec X u η hη).1, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => he i
  · rw [X.flagZVector]
    exact gOf_fix X u η hη _ (Or.inr rfl)

theorem latS_mul (u : D.what₂.Word) (η : Hfin X u) (hη : η ∈ (iotaF X u).range) (h : X.B.I.Gf) :
    latS X u ((η : X.B.I.Gf) * h) = gOf X (matOf X (η : X.B.I.Gf)) '' latS X u h := by
  set g := gOf X (matOf X (η : X.B.I.Gf)) with hg
  have hf := (matOf_spec X u η hη).2
  have key : ∀ w, X.B.I.fmat (η : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (g w)) = incl X.B.I (X.crd w) := by
    intro w
    rw [hg, crd_gOf, ← incl_mulVec, ← hf, Matrix.mulVec_mulVec]
    have e1 : X.B.I.fmat (η : X.B.I.Gf)⁻¹ * X.B.I.fmat (η : X.B.I.Gf) = 1 := by
      show X.B.I.fmat ((η : X.B.I.Gf)⁻¹ * (η : X.B.I.Gf)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e1, Matrix.one_mulVec]
  have main : ∀ w, X.B.I.fmat (((η : X.B.I.Gf) * h) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (g w)) =
      X.B.I.fmat (h * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd w) := by
    intro w
    have e : (((η : X.B.I.Gf) * h) * X.xu u)⁻¹ = (h * X.xu u)⁻¹ * (η : X.B.I.Gf)⁻¹ := by group
    rw [e]
    have ef : X.B.I.fmat ((h * X.xu u)⁻¹ * (η : X.B.I.Gf)⁻¹) =
        X.B.I.fmat (h * X.xu u)⁻¹ * X.B.I.fmat (η : X.B.I.Gf)⁻¹ := rfl
    rw [ef, ← Matrix.mulVec_mulVec, key]
  ext y
  constructor
  · intro hy
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    simp only [latS, Set.mem_ofPred_eq] at hy ⊢
    rwa [← main (g.symm y), g.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    simp only [latS, Set.mem_ofPred_eq] at hw ⊢
    rwa [main]

variable {T : D.host.E}

theorem fix_span (F0 : FlagG (VS D) D.R.rS T) (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hg : ∀ a, g (F0.e a) = F0.e a) : ∀ x ∈ F0.X, g x = x := by
  intro x hx
  unfold FlagG.X at hx
  have key := LinearMap.eqOn_span' (f := (g : (VS D).V →ₗ[D.host.E] (VS D).V)) (g := LinearMap.id)
    (s := Set.range F0.e) (by rintro _ ⟨a, rfl⟩; exact hg a) hx
  simpa using key

theorem perp_pres (F0 : FlagG (VS D) D.R.rS T) (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hiso : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : ∀ a, g (F0.e a) = F0.e a) :
    ∀ y ∈ perpS (VS D) F0.X, g y ∈ perpS (VS D) F0.X := by
  intro y hy
  unfold perpS at hy ⊢
  have hy' : ∀ x ∈ F0.X, (VS D).hT x y = 0 := hy
  have h2 : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hiso
  show ∀ x ∈ F0.X, (VS D).hT x (g y) = 0
  intro x hx
  have hgx : g x = x := fix_span F0 g hg x hx
  have h3 := h2 x y
  rw [hgx] at h3
  rw [h3]
  exact hy' x hx

def indQ (F0 : FlagG (VS D) D.R.rS T) (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hp : ∀ y ∈ perpS (VS D) F0.X, g y ∈ perpS (VS D) F0.X) (hX : ∀ x ∈ F0.X, g x = x) :
    WbQ D F0 →ₗ[D.host.E] WbQ D F0 :=
  Submodule.mapQ _ _ ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrict hp) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hx ⊢
    rw [LinearEquiv.coe_coe, hX _ hx]
    exact hx)

theorem indQ_mk (F0 : FlagG (VS D) D.R.rS T) (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hp : ∀ y ∈ perpS (VS D) F0.X, g y ∈ perpS (VS D) F0.X) (hX : ∀ x ∈ F0.X, g x = x)
    (x : perpS (VS D) F0.X) (hx : g x.1 ∈ perpS (VS D) F0.X) :
    indQ F0 g hp hX (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨g x.1, hx⟩ := by
  rfl

omit T in
theorem eq_of_ind (u : D.what₂.Word) (g1 g2 : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h1 : g1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (h2 : g2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf1 : ∀ a, g1 (X.fY a) = X.fY a) (hf2 : ∀ a, g2 (X.fY a) = X.fY a)
    (hq : ∀ x ∈ perpS (VS D) (X.Fu u).X, g1 x - g2 x ∈ (X.Fu u).X) : g1 = g2 := by
  have hfe : ∀ a b, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (X.eX a) (X.fY b), X.ef]
    split_ifs <;> simp
  have hzero : ∀ d ∈ (X.Fu u).X, (∀ b, (VS D).hT (X.fY b) d = 0) → d = 0 := by
    intro d hd hb
    unfold FlagG.X at hd
    rw [X.Fu_e, Submodule.mem_span_range_iff_exists_fun] at hd
    obtain ⟨c, rfl⟩ := hd
    have hc : ∀ b, c b = 0 := by
      intro b
      have := hb b
      simpa [map_sum, hfe] using this
    simp [hc]
  have hperp : ∀ x ∈ perpS (VS D) (X.Fu u).X, g1 x = g2 x := by
    intro x hx
    apply sub_eq_zero.1
    apply hzero _ (hq x hx)
    intro b
    have e1 := h1 (X.fY b) x
    have e2 := h2 (X.fY b) x
    rw [hf1 b] at e1
    rw [hf2 b] at e2
    rw [map_sub, e1, e2, sub_self]
  have hv' : ∀ v, v - ∑ a, (VS D).hT (X.eX a) v • X.fY a ∈ perpS (VS D) (X.Fu u).X := by
    intro v x hx
    unfold FlagG.X at hx
    rw [X.Fu_e, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    simp [map_sum, X.ef]
  apply LinearEquiv.ext
  intro v
  have hsplit : v = (v - ∑ a, (VS D).hT (X.eX a) v • X.fY a) + ∑ a, (VS D).hT (X.eX a) v • X.fY a := by abel
  rw [hsplit, map_add, map_add, hperp _ (hv' v)]
  congr 1
  simp [map_sum, hf1, hf2]

end PI.UnitaryDimensionFormula.StabB

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open StabB

theorem stabBound_holds : StabBound := by
  intro D X Y u _ Λ _ hfin
  set A : Set (Hfin X u) := {η | η ∈ (iotaF X u).range ∧ ∃ h h' : Hfin X u,
    latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V) ∧ latS X u (h' : X.B.I.Gf) = (Λ : Set (VS D).V) ∧
    ∃ κ ∈ Ku X u Y.hK, h' = η * h * κ} with hAdef
  have hgm : ∀ η ∈ A, Formalism.HermitianLatticesTheory.gmap (gOf X (matOf X (η : X.B.I.Gf))) Λ = Λ := by
    rintro η ⟨hη, h, h', hh, hh', κ, hκ, he⟩
    have hk : latS X u ((η : X.B.I.Gf) * (h : X.B.I.Gf) * (κ : X.B.I.Gf)) =
        latS X u ((η : X.B.I.Gf) * (h : X.B.I.Gf)) := kuStab D X u Y.hK _ ⟨κ, hκ⟩
    have e : latS X u (h' : X.B.I.Gf) =
        gOf X (matOf X (η : X.B.I.Gf)) '' latS X u (h : X.B.I.Gf) := by
      rw [he, Subgroup.coe_mul, Subgroup.coe_mul, hk, latS_mul X u η hη]
    apply SetLike.coe_injective
    calc ((Formalism.HermitianLatticesTheory.gmap (gOf X (matOf X (η : X.B.I.Gf))) Λ : Submodule _ _) : Set (VS D).V)
        = gOf X (matOf X (η : X.B.I.Gf)) '' latS X u (h : X.B.I.Gf) := by
          rw [hh, Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]; rfl
      _ = Λ := e.symm.trans hh'
  have hX : ∀ η ∈ A, ∀ x ∈ (X.Fu u).X, gOf X (matOf X (η : X.B.I.Gf)) x = x := fun η hA =>
    fix_span (X.Fu u) _ (fun a => by rw [X.Fu_e]; exact gOf_e X u η hA.1 a)
  have hp : ∀ η ∈ A, ∀ y ∈ perpS (VS D) (X.Fu u).X,
      gOf X (matOf X (η : X.B.I.Gf)) y ∈ perpS (VS D) (X.Fu u).X := fun η hA =>
    perp_pres (X.Fu u) _ (gOf_isom X _ (matOf_spec X u η hA.1).1)
      (fun a => by rw [X.Fu_e]; exact gOf_e X u η hA.1 a)
  let φ : A → autLz D (X.Fu u) Λ := fun η =>
    ⟨indQ (X.Fu u) _ (hp η.1 η.2) (hX η.1 η.2),
      ⟨_, gOf_stabF X u η.1 η.2.1, hgm η.1 η.2, fun x hx => indQ_mk (X.Fu u) _ _ _ x hx⟩⟩
  have hinj : Function.Injective φ := by
    intro η1 η2 h12
    have hfun : ∀ q, indQ (X.Fu u) _ (hp η1.1 η1.2) (hX η1.1 η1.2) q =
        indQ (X.Fu u) _ (hp η2.1 η2.2) (hX η2.1 η2.2) q :=
      fun q => congrFun (congrArg Subtype.val h12) q
    have hg : gOf X (matOf X (η1.1 : X.B.I.Gf)) = gOf X (matOf X (η2.1 : X.B.I.Gf)) := by
      apply eq_of_ind X u _ _ (gOf_isom X _ (matOf_spec X u _ η1.2.1).1)
        (gOf_isom X _ (matOf_spec X u _ η2.2.1).1) (gOf_f X u _ η1.2.1) (gOf_f X u _ η2.2.1)
      intro x hx
      have h3 := hfun (Submodule.Quotient.mk ⟨x, hx⟩)
      rw [indQ_mk _ _ _ _ _ (hp η1.1 η1.2 x hx), indQ_mk _ _ _ _ _ (hp η2.1 η2.2 x hx)] at h3
      have h4 := (Submodule.Quotient.eq _).1 h3
      simpa using h4
    have hM : ((matOf X (η1.1 : X.B.I.Gf) : GL (Fin X.B.I.n) X.B.I.E) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
        ((matOf X (η2.1 : X.B.I.Gf) : GL (Fin X.B.I.n) X.B.I.E) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
      have hl := congrArg LinearEquiv.toLinearMap hg
      have hl' : hmat X (matOf X (η1.1 : X.B.I.Gf) : Matrix _ _ _) =
          hmat X (matOf X (η2.1 : X.B.I.Gf) : Matrix _ _ _) :=
        (Matrix.toLin X.bas X.bas).injective hl
      exact Matrix.map_injective (by exact X.ιE.injective) hl'
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    have f1 := (matOf_spec X u _ η1.2.1).2
    have f2 := (matOf_spec X u _ η2.2.1).2
    change X.B.I.fmat (η1.1 : X.B.I.Gf) = X.B.I.fmat (η2.1 : X.B.I.Gf)
    rw [f1, f2, hM]
  have : Finite (autLz D (X.Fu u) Λ) := hfin.to_subtype
  have : Finite A := Finite.of_injective φ hinj
  refine ⟨A, Set.toFinite A, Nat.card_le_card_of_injective φ hinj, ?_⟩
  intro h h' hh hh' γ hγ κ hκ he
  exact ⟨hγ, h, h', hh, hh', κ, hκ, he⟩

end PI.UnitaryDimensionFormula
