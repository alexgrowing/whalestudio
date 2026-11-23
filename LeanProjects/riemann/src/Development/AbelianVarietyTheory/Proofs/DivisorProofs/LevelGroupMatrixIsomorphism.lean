import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoActCompare

theorem exists_glEquiv_of_surjective {A R M : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower A R M] (hs : Function.Surjective (algebraMap A R)) {r : ℕ}
    (φ : M ≃ₗ[A] (Fin r → R)) :
    ∃ θ : GL (Fin r) R ≃* (M ≃ₗ[A] M), (∀ g q, φ (θ g q) = g.1.mulVec (φ q)) ∧
      ∀ g, LinearEquiv.det ((θ g).extendScalarsOfSurjective hs) = Matrix.GeneralLinearGroup.det g := by
  let e : M ≃ₗ[R] (Fin r → R) := φ.extendScalarsOfSurjective hs
  let t : GL (Fin r) R ≃* ((Fin r → R) ≃ₗ[R] (Fin r → R)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin r → R))
  have ht : ∀ g v, t g v = g.1.mulVec v := fun g v => rfl
  let c : ((Fin r → R) ≃ₗ[R] (Fin r → R)) ≃* (M ≃ₗ[A] M) :=
    { toFun := fun f => (e ≪≫ₗ f ≪≫ₗ e.symm).restrictScalars A
      invFun := fun f => e.symm ≪≫ₗ f.extendScalarsOfSurjective hs ≪≫ₗ e
      left_inv := fun f => by
        ext1 v
        show e (e.symm (f (e (e.symm v)))) = f v
        simp
      right_inv := fun f => by
        ext1 v
        show e.symm (e (f (e.symm (e v)))) = f v
        simp
      map_mul' := fun f g => by
        ext1 v
        show e.symm (f (g (e v))) = e.symm (f (e (e.symm (g (e v)))))
        simp }
  refine ⟨t.trans c, fun g q => ?_, fun g => ?_⟩
  · show e (e.symm (t g (e q))) = _
    rw [e.apply_symm_apply, ht]
    rfl
  · have h : (((t.trans c) g).extendScalarsOfSurjective hs : M →ₗ[R] M) =
        (e.symm : (Fin r → R) →ₗ[R] M) ∘ₗ Matrix.toLin' g.1 ∘ₗ (e.symm.symm : M →ₗ[R] (Fin r → R)) := by
      ext1 v
      rfl
    ext1
    rw [LinearEquiv.coe_det, h, LinearMap.det_conj, LinearMap.det_toLin']
    rfl

theorem exists_glEquiv_pi {R ι : Type} [CommRing R] {k : ι → Type} [∀ i, CommRing (k i)] (c : R ≃+* ∀ i, k i)
    (r : ℕ) :
    ∃ θ : (∀ i, GL (Fin r) (k i)) ≃* GL (Fin r) R, ∀ g i a b, c ((θ g).1 a b) i = (g i).1 a b := by
  let m : Matrix (Fin r) (Fin r) R ≃+* ∀ i, Matrix (Fin r) (Fin r) (k i) :=
    c.mapMatrix.trans Matrix.piRingEquiv
  refine ⟨MulEquiv.piUnits.symm.trans (Units.mapEquiv m.toMulEquiv).symm, fun g i a b => ?_⟩
  show m (m.symm (fun j => (g j).1)) i a b = _
  rw [m.apply_symm_apply]

theorem exists_levGrp_equiv_pi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl E)), l.Mb = ∏ w ∈ Pg, w.asIdeal → ∀ (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (r : ℕ) (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)), ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l, (∀ (g : Formalism.L2.DIV.G0 Pg r) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb)), (∀ q, φ (ψ g q) = Y.mulVec (φ q)) ↔ ∀ w : ↥Pg, Y.map (Ideal.Quotient.factor (hle w)) = (g w).1) ∧ ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (LevelLiftConditions.levDet Dw l (ψ g)) = Matrix.GeneralLinearGroup.det (g w) := by
  intro E _ _ _ H Dw l Pg hP hle r φ
  obtain ⟨θ, h1, h2⟩ := exists_glEquiv_of_surjective (A := 𝓞 E) (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l)
    Ideal.Quotient.mk_surjective φ
  obtain ⟨η, h3⟩ := exists_glEquiv_pi (crt hP hle) r
  have h4 : ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), (η g).1.map (Ideal.Quotient.factor (hle w)) = (g w).1 :=
    fun g w => Matrix.ext fun a b => h3 g w a b
  refine ⟨η.trans θ, fun g Y => ?_, fun g w => ?_⟩
  · have h5 : ∀ q, φ ((η.trans θ) g q) = (η g).1.mulVec (φ q) := fun q => h1 (η g) q
    constructor
    · intro h w
      have : Y = (η g).1 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        obtain ⟨q, rfl⟩ := φ.surjective v
        exact ((h q).symm.trans (h5 q))
      rw [this]
      exact h4 g w
    · intro h q
      have : Y = (η g).1 := by
        refine Matrix.ext fun a b => (crt hP hle).injective (funext fun w => ?_)
        rw [h3 g w a b, ← h w]
        rfl
      rw [this]
      exact h5 q
  · have h6 : LevelLiftConditions.levDet Dw l ((η.trans θ) g) = Matrix.GeneralLinearGroup.det (η g) := h2 (η g)
    refine (congrArg _ h6).trans (Units.ext ?_)
    show Ideal.Quotient.factor (hle w) (η g).1.det = (g w).1.det
    rw [RingHom.map_det, ← h4 g w]
    rfl

end GlobalTheory.GeoActCompare
