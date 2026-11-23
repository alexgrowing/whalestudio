import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.PerSpan GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

theorem lie_equiv {S : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over (Sp ℂ)} [GrpObj G'] {z : Sp ℂ ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G z φ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (MV : LieModel G' (𝟙 (Sp ℂ)) V) (Mz : LieModel G z V') :
    ∃ Φ : V ≃ₗ[ℂ] V', ∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (epsAt (𝟙 (Sp ℂ))).hom (epsAt z).hom (by simp)
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (𝟙 (Sp ℂ)) z (Category.id_comp _).symm
  have h1 : (1 : Over.mk z ⟶ G).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G').left ≫ φ := by
    rw [← hρ₀, map_one]
  have tan : ∀ v : epsAt (𝟙 (Sp ℂ)) ⟶ G', IsTanAt G z (ρ v) ↔ IsTanAt G' (𝟙 _) v := by
    intro v
    unfold IsTanAt
    constructor
    · intro h
      refine hp.1.hom_ext ?_ ?_
      · rw [← h1, ← h, Category.assoc]
        exact congrArg _ (hρ v).symm
      · rw [Category.assoc, Over.w v, Over.w (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G')]
        exact TorusModel.fst_eps (𝟙 (Sp ℂ))
    · intro h
      rw [h1, ← h, Category.assoc]
      exact congrArg _ (hρ v)
  choose f hf using fun x => Mz.onto _ ((tan _).2 (MV.tan x))
  have hl : ∀ x, (Mz.pt (f x)).left = (MV.pt x).left ≫ φ := fun x => by
    rw [hf]
    exact hρ _
  let F : V →ₗ[ℂ] V' :=
    { toFun := f
      map_add' := fun x y => Mz.inj (by
        rw [Mz.add, hf, hf, hf, MV.add]
        exact map_mul ρ _ _)
      map_smul' := fun c x => Mz.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, Mz.smul, hl, hl, MV.smul, Category.assoc])) }
  refine ⟨LinearEquiv.ofBijective F ⟨fun x y h => ?_, fun y => ?_⟩, hl⟩
  · have h' : f x = f y := h
    refine MV.inj (ρ.injective ?_)
    exact (hf x).symm.trans ((congrArg Mz.pt h').trans (hf y))
  · obtain ⟨x, hx⟩ := MV.onto (ρ.symm (Mz.pt y)) ((tan _).1 (by rw [ρ.apply_symm_apply]; exact Mz.tan y))
    refine ⟨x, Mz.inj ?_⟩
    show Mz.pt (f x) = _
    rw [hf, hx]
    exact ρ.apply_symm_apply _

theorem torus_deriv {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)
    (MT : LieModel (splitTorus (Sp ℂ) X) (𝟙 _) (X →+ ℂ)) (hMT : IsCocharLie MT) (δ : X →+ ℂ) :
    IsDerivAt0 (fun w => (torusExp β w).left) (fun a => δ (β a)) (MT.pt δ).left := by
  obtain ⟨v, H⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_torusExp β) (fun a => δ (β a))
  have hv := GlobalTheory.VerticalDeriv.isDerivAt0_vertical (splitTorus (Sp ℂ) X).hom (𝟙 (Sp ℂ))
    (e := fun w => (torusExp β w).left) (fun w => Over.w (torusExp β w)) H
  let v' : epsAt (𝟙 (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X := Over.homMk v hv
  have h0 : torusExp β (0 : Fin d → ℂ) = 1 := by
    have := torusExp_add β (0 : Fin d → ℂ) 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ht : IsTanAt (splitTorus (Sp ℂ) X) (𝟙 _) v' := H.1.trans (congrArg (·.left) h0)
  obtain ⟨δ', hδ'⟩ := MT.onto v' ht
  have e : δ' = δ := by
    ext χ
    have H2 := GlobalTheory.FibreDeriv.isDerivAt0_comp H (pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)))
    have h3 := H2.2 ⊤ le_top ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))
    have h4 : (fun z => valAt' ((torusExp β z).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
        ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))) =
        fun z => Complex.exp (pairing β z χ) :=
      funext fun z => (valAt'_torusFst' _ _).trans (torusExp_hol_char β z χ)
    let Lc : (Fin d → ℂ) →L[ℂ] ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) • ContinuousLinearMap.proj a
    have hLc : ∀ w, Lc w = pairing β w χ := fun w => by simp [Lc, pairing]
    have h5 : fderiv ℂ (fun z => Complex.exp (pairing β z χ)) 0 (fun a => δ (β a)) = δ χ := by
      have : HasFDerivAt (fun z => Complex.exp (Lc z)) (Complex.exp (Lc 0) • Lc) 0 := Lc.hasFDerivAt.cexp
      simp only [hLc] at this
      rw [this.fderiv, ContinuousLinearMap.smul_apply, hLc, ← hLc 0, map_zero, Complex.exp_zero, one_smul]
      conv_rhs => rw [← β.sum_repr χ, map_sum]
      simp only [pairing, map_zsmul, zsmul_eq_mul]
    have h6 := hMT δ' χ
    rw [hδ'] at h6
    have h7 : (charVal v' χ).snd = δ' χ := by rw [h6]; simp
    rw [← h7, ← h5, ← h4]
    refine Eq.trans ?_ h3
    congr 1
    unfold charVal
    set g : Sp (DualNumber ℂ) ⟶ Spec (torusRing ZU X) :=
      v'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)) with hg
    have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom = Spec.preimage g := by
      conv_lhs => rw [← Spec.map_preimage g]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have h8 : g.appTop = g.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [← h, h8]
    rfl
  rw [← e, hδ', e]
  exact H

theorem torusExp_eq_one {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X) (w : Fin d → ℂ) :
    torusExp β w = 1 ↔ ∃ δ : X →+ ℤ, w = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ) := by
  have hT : ∀ χ : X, torusHom β w (Multiplicative.ofAdd χ) = expUnit (pairing β w χ) := fun χ => rfl
  have hE : torusExp β w =
      (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))).symm (torusHom β w) := rfl
  constructor
  · intro h1
    have hH : torusHom β w = 1 := by
      have h0 := congrArg (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))) h1
      rw [hE, MulEquiv.apply_symm_apply, map_one] at h0
      exact h0
    have hexp : ∀ a, Complex.exp (w a) = 1 := by
      intro a
      have h2 := congrArg (fun f => f (Multiplicative.ofAdd (β a))) hH
      simp only [hT, MonoidHom.one_apply, pairing_basis] at h2
      have h3 := gamma_expUnit (w a)
      rw [h2, Units.val_one, map_one] at h3
      exact h3.symm
    choose n hn using fun a => Complex.exp_eq_one_iff.1 (hexp a)
    refine ⟨(β.constr ℤ n).toAddMonoidHom, ?_⟩
    funext a
    rw [hn a]
    simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis]
    ring
  · rintro ⟨δ, rfl⟩
    have hH : torusHom β (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = 1 := by
      apply monoidHom_ext_basis β
      intro a
      rw [hT, pairing_basis, MonoidHom.one_apply]
      apply expUnit_eq_one
      show Complex.exp (2 * ↑Real.pi * Complex.I * (δ (β a) : ℂ)) = 1
      rw [mul_comm]
      exact Complex.exp_int_mul_two_pi_mul_I (δ (β a))
    rw [hE, hH, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem torus_lift (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, M.Lifts (ψ b) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) :
    letI := P.τ.addCommGroup
    ∃ (d : ℕ) (β : Module.Basis (Fin d) ℤ P.τ.X) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ (MT : LieModel (splitTorus (Sp ℂ) P.τ.X) (𝟙 _) (P.τ.X →+ ℂ)), IsCocharLie MT → ∀ δ : P.τ.X →+ ℂ,
        (Mz.pt (h fun a => δ (β a))).left = (MT.pt δ ≫ P.τ.i).left ≫ P.m.φ) ∧
      (∀ z, h z ∈ e.per b ↔ ∃ δ : P.τ.X →+ ℤ, z = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) ∧
      ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
        (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsGrpPullback A P.tB.G (𝟙 _) φ → IsAbLift e b P φ u ℓ →
        ∀ y, ℓ y = 0 ↔ ∃ z, y = h z := by
  letI := P.τ.grpB
  letI := P.τ.addCommGroup
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let β := Module.finBasis ℤ P.τ.X
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  let v : (Fin (Module.finrank ℤ P.τ.X) → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => ρ (torusExp β z ≫ P.τ.i)
  have vadd : ∀ z w, v (z + w) = v z * v w := fun z w => by
    show ρ (torusExp β (z + w) ≫ P.τ.i) = ρ (torusExp β z ≫ P.τ.i) * ρ (torusExp β w ≫ P.τ.i)
    rw [torusExp_add, MonObj.mul_comp]
    exact map_mul ρ _ _
  have vl : (fun z => (v z).left) = fun z => (torusExp β z).left ≫ P.τ.i.left ≫ P.m.φ := funext fun z => by
    rw [← Category.assoc]
    exact hρ _
  have vhol : IsHolTo Set.univ (fun z => (v z).left) := by
    rw [vl]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_torusExp β) _
  obtain ⟨h', -, hh⟩ := exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b)
    (famExpAtPoint e hb) _ Set.univ (fun _ z => v z) isOpen_univ subset_rfl (fun _ _ z w => vadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (v z).left) vhol)
  obtain ⟨hex, -, hder⟩ := hh 0 trivial
  have hex' : ∀ z, e.ex b (h' 0 z) = v z := hex
  have hder' : ∀ z w, IsDerivAt0 (fun z => (v z).left) z w ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h' 0 z) w := hder
  have hmono : Mono P.τ.i := by
    refine ⟨fun a a' haa => P.τ.isKernel.hom_ext haa (toUnit_unique _ _)⟩
  have hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1 := by
    intro z
    have h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η := P.τ.isKernel.w
    have h2 : z ≫ P.τ.i ≫ P.τ.q = 1 := by
      rw [h1, ← Category.assoc, Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    calc (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = (z ≫ P.τ.i ≫ P.τ.q) ≫ P.e.hom := by simp only [Category.assoc]
      _ = 1 := by rw [h2, MonObj.one_comp]
  refine ⟨_, β, h' 0, fun MT hMT δ => ?_, fun z => ?_, fun A _ φ g' u ℓ hA hl y => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (torus_deriv β MT hMT δ) (P.τ.i.left ≫ P.m.φ)
    rw [← vl] at d1
    have d2 := (hder' _ _).1 d1
    rw [Over.comp_left, Category.assoc]
    exact GlobalTheory.VerticalDeriv.isDerivAt0_unique (DiffL.isDerivAt0_pt e hb Mz hL _) d2
  · rw [← torusExp_eq_one]
    show e.ex b (h' 0 z) = 1 ↔ _
    rw [hex']
    refine (map_eq_one_iff ρ ρ.injective).trans ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [← cancel_mono P.τ.i, MonObj.one_comp]
      exact h1
    · show torusExp β z ≫ P.τ.i = 1
      rw [h1, MonObj.one_comp]
  · obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hA (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
    have hl' : ∀ y (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), ρ s = e.ex b y → ρ' (u.ex (ℓ y)) = s ≫ P.τ.q ≫ P.e.hom :=
      fun y s hs => Over.OverMorphism.ext ((hρ' _).trans (hl y s ((hρ s).symm.trans (congrArg (·.left) hs))))
    constructor
    · intro hy
      obtain ⟨Γ₀, hΓ, hd, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R t.G g n M B ψ e b hb
      have hcount : (e.per b).Countable := by
        rw [← hΓ]
        haveI := hd
        have : Countable Γ₀ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      have h0 : (LinearMap.range (h' 0)).mkQ y = 0 := by
        refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hcount.image (LinearMap.range (h' 0)).mkQ) fun c => ?_
        obtain ⟨s, hs⟩ := ρ.surjective (e.ex b (c • y))
        have h1 := hl' _ s hs
        rw [map_smul, hy, smul_zero, (u.ker 0).2 u.Λ.zero_mem] at h1
        have h2 : s ≫ P.τ.q ≫ P.e.hom = 1 := h1.symm.trans (map_one ρ')
        have h3 : s ≫ P.τ.q = 1 := by
          rw [← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]
          exact h2
        let τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X :=
          P.τ.isKernel.lift s (toUnit _) (by rw [h3, Hom.one_def]; rfl)
        have hτ : τ₀ ≫ P.τ.i = s := P.τ.isKernel.lift_fst _ _ _
        obtain ⟨w, hw⟩ := torusExp_surjective β τ₀
        have h4 : e.ex b (h' 0 w) = e.ex b (c • y) := by
          rw [hex', ← hs, ← hτ, ← hw]
        refine ⟨c • y - h' 0 w, ?_, ?_⟩
        · show e.ex b _ = 1
          have := e.add b hb (c • y - h' 0 w) (h' 0 w)
          rw [sub_add_cancel, h4] at this
          exact right_eq_mul.1 this
        · simp only [map_sub, map_smul, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range (h' 0))).2 ⟨w, rfl⟩, sub_zero]
      have : y ∈ LinearMap.range (h' 0) := by simpa using h0
      obtain ⟨z, hz⟩ := this
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      have hcount : (u.Λ : Set (Fin g' → ℂ)).Countable := by
        haveI := u.discrete
        have : Countable u.Λ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      refine GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun c => ?_
      rw [← map_smul, ← map_smul]
      refine (u.ker _).1 (ρ'.injective ?_)
      exact ((hl' _ _ (hex' (c • z)).symm).trans (hQ1 _)).trans (map_one ρ').symm

end LevelTowerAlt.Val
