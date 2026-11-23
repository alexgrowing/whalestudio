import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLocalLatticeCompletionIffCommMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentSelfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentNeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicUnitaryPointExtLocalComponentsStatement

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TwistPC

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ (J.mulVec y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A)
    (M : Matrix (Fin m) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J' (M.mulVec x) (M.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ M * J' * M) x y := by
  rw [hform_eq, hform_eq]
  have e : τ ∘ M.mulVec x = (M.map τ).mulVec (τ ∘ x) := by
    funext i; exact RingHom.map_mulVec τ M x i
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem comm_comm' (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F (Fv F v) E (Algebra.TensorProduct.comm F E (Fv F v) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_comm'' (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.comm F E (Fv F v) (Algebra.TensorProduct.comm F (Fv F v) E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_sigR' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F E (Fv F v) (Formalism.UG.sigR σ (Fv F v) x) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Algebra.TensorProduct.comm F E (Fv F v) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem locData (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r' → E)) (v : HeightOneSpectrum (𝓞 F))
    (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v)) (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v))
    (k1 : jv * jv' = 1) (k2 : jv' * jv = 1)
    (hiso : Formalism.UG.cT (Formalism.UG.sigR σ (Fv F v)) jv * J'.map (Formalism.UG.inclE (F := F) (Fv F v)) * jv =
      J.map (Formalism.UG.inclE (F := F) (Fv F v)))
    (hlat : jv.mulVec '' (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v)) =
      (Formalism.L2.Herm.locL v Λ' : Set (Fin r' → E ⊗[F] Fv F v))) :
    ∃ jl : GLoc σ J v ≃ₜ* GLoc σ J' v, IsLatticeConj Λ Λ' jl ∧ ∀ g,
      (GlobalTheory.AdelicU.matHom _ σ J' (jl g)).val =
        jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * (GlobalTheory.AdelicU.matHom _ σ J g).val *
          jv'.map (Algebra.TensorProduct.comm F E (Fv F v)) := by
  obtain ⟨cm, hcm⟩ : ∃ cm : E ⊗[F] Fv F v →+* Fv F v ⊗[F] E,
      cm = (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : Fv F v ⊗[F] E →+* E ⊗[F] Fv F v,
      cb = (Algebra.TensorProduct.comm F (Fv F v) E).toRingEquiv.toRingHom := ⟨_, rfl⟩
  have ecm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      X.map (Algebra.TensorProduct.comm F E (Fv F v)) = X.map cm := by
    intro m k X; subst hcm; rfl
  have bc1 : ∀ x, cb (cm x) = x := fun x => by subst hcm hcb; exact comm_comm' v x
  have bc2 : ∀ x, cm (cb x) = x := fun x => by subst hcm hcb; exact comm_comm'' v x
  have bcm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)), (X.map cm).map cb = X := by
    intro m k X; ext i l; exact bc1 _
  simp only [ecm]
  have hab : jv.map cm * jv'.map cm = 1 := by rw [← Matrix.map_mul, k1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hba : jv'.map cm * jv.map cm = 1 := by rw [← Matrix.map_mul, k2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (jv.map cm) * JR (F := F) (Fv F v) J' * jv.map cm =
      JR (F := F) (Fv F v) J := by
    have e := congrArg (fun X => X.map cm) hiso
    simp only [Matrix.map_mul] at e
    convert e using 3
    · ext i k; subst hcm; exact (comm_sigR' σ v _).symm
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry σ J J' v _ _ hab hba hJ
  refine ⟨φ, ?_, hφ⟩
  have injv : Function.Injective jv.mulVec := fun x y hxy => by
    have := congrArg jv'.mulVec hxy
    simpa [Matrix.mulVec_mulVec, k2] using this
  have hA : (jv.map cm).map cb = jv := bcm jv
  refine ⟨LinearEquiv.ofLinear (Matrix.mulVecLin (jv.map cm)) (Matrix.mulVecLin (jv'.map cm))
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hab])
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hba]), fun y y' => ?_, fun y => ?_, fun g y => ?_⟩
  · show GlobalTheory.AdelicU.hLin σ J' (Fv F v) ((jv.map cm).mulVec y) ((jv.map cm).mulVec y') = GlobalTheory.AdelicU.hLin σ J (Fv F v) y y'
    unfold GlobalTheory.AdelicU.hLin hR
    rw [hform_mulVec, hJ]
  · show (jv.map cm).mulVec y ∈ GlobalTheory.AdelicU.latLoc F Λ' v ↔ y ∈ GlobalTheory.AdelicU.latLoc F Λ v
    have ecb : ∀ {m : ℕ} (z : Fin m → Fv F v ⊗[F] E),
        (fun i => Algebra.TensorProduct.comm F (Fv F v) E (z i)) = cb ∘ z := by
      intro m z; subst hcb; rfl
    rw [GlobalTheory.T.mem_localLatticeCompletion_iff_comm_mem, GlobalTheory.T.mem_localLatticeCompletion_iff_comm_mem, ecb, ecb]
    have e : cb ∘ (jv.map cm).mulVec y = jv.mulVec (cb ∘ y) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hA]
    rw [e]
    have := injv.mem_set_image (s := (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v))) (a := cb ∘ y)
    rw [hlat] at this
    exact this
  · show (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val.mulVec ((jv.map cm).mulVec y) =
      (jv.map cm).mulVec ((GlobalTheory.AdelicU.matHom _ σ J g).val.mulVec y)
    rw [hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hba, Matrix.mul_one]

theorem assemble (v : HeightOneSpectrum (𝓞 F)) {r r' : ℕ} (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v))
    (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v)) (M : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)) :
    jv * M.map (Algebra.TensorProduct.comm F (Fv F v) E) * jv' =
      (jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * M * jv'.map (Algebra.TensorProduct.comm F E (Fv F v))).map
        (Algebra.TensorProduct.comm F (Fv F v) E) := by
  have e : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      (X.map (Algebra.TensorProduct.comm F E (Fv F v))).map (Algebra.TensorProduct.comm F (Fv F v) E) = X := by
    intro m k X; ext i l; exact comm_comm' v _
  rw [Matrix.map_mul, Matrix.map_mul, e, e]

end Gen

set_option maxHeartbeats 3000000 in

theorem isom_locComponents : ∀ (D : D7) (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V' (frameLat V) (frameLat V') j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ₀ → ∃ jl : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (jl v)) ∧ ∀ v g, Φ₀ (locFin V v g) = locFin V' v (jl v g) := by
  intro D V V' j Φ₀ hj hΦ
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  have key := fun v => locData D.sp.cm.sig V.gram V'.gram (frameLat V) (frameLat V') v
    (j.map (Formalism.UG.prV (E := D.host.E) v)) (j'.map (Formalism.UG.prV (E := D.host.E) v))
    (GlobalTheory.HeckeTrans.map_mul_one _ h1) (GlobalTheory.HeckeTrans.map_mul_one _ h2)
    (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).1.2 (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).2
  choose jl hjl hjm using key
  refine ⟨jl, hjl, fun v g => ?_⟩
  apply GlobalTheory.T.finiteAdelicUnitaryPoint_ext_localComponents
  intro u
  have hc := hΦ (locFin V v g)
  have e1 := congrArg (fun X => GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul X j') hc
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul, Matrix.mul_assoc, h1, Matrix.mul_one] at e1
  rw [e1, Matrix.map_mul, Matrix.map_mul]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V u g, GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V' u (jl u g), hjm]
    rw [← Matrix.mul_assoc]
    exact assemble (F := D.host.F) (E := D.host.E) u _ _ _
  · rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V hu, GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V' hu, Matrix.one_mul, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.TwistPC
