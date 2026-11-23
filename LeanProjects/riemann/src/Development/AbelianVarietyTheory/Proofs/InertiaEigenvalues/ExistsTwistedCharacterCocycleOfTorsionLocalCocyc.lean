import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases

section Gen1
variable {O : Type} [CommRing O]

def evOneQ (LL : Type) [Field LL] [Algebra O LL] : ((Fin 1 → LL) ⧸ stdG O LL 1) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL 1).mapQ (intO (O := O) LL) (LinearMap.proj (R := O) (φ := fun _ : Fin 1 => LL) 0) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u 0, rfl⟩)

variable {LL : Type} [Field LL] [Algebra O LL]

theorem evOneQ_mk (v : Fin 1 → LL) :
    evOneQ (O := O) LL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v 0) := rfl

theorem evOneQ_mem {lam : O} {a : ℕ} {q : (Fin 1 → LL) ⧸ stdG O LL 1} (h : lam ^ a • q = 0) :
    evOneQ LL q ∈ Xq LL lam a := by
  show (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] _)) (evOneQ LL q) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, h, map_zero]

def oneO : ↥(intO (O := O) LL) := ⟨1, 1, map_one (algebraMap O LL)⟩

theorem iotaC_oneO (lam : O) (a : ℕ) (q : (Fin 1 → LL) ⧸ stdG O LL 1) (h : evOneQ LL q ∈ Xq LL lam a) :
    iotaC LL lam a (oneO ⊗ₜ ⟨evOneQ LL q, h⟩) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) (oneO ⊗ₜ (evOneQ LL (Submodule.Quotient.mk v))) = _
    rw [evOneQ_mk, iotaG_tmul]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [constOne, oneO]

def oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) : ↥(latOne hinj ψ).T :=
  oneO

theorem actT_latOne_oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) (g : G) :
    actT (latOne hinj ψ) g (oneT hinj ψ) = ((ψ g : Oˣ) : O) • oneT hinj ψ := by
  apply Subtype.ext
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • (1 : LL) = ((ψ g : Oˣ) : O) • (1 : LL)
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

end Gen1

section Gen2
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem actTw_oneO (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (X : Type) [AddCommGroup X] [Module O X] (χ ψ : G →* Oˣ) (g : G) (x : X) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) X χ g (oneT hinj ψ ⊗ₜ x) = oneT hinj ψ ⊗ₜ ((((χ g)⁻¹ * ψ g : Oˣ) : O) • x) := by
  rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, actT_latOne_oneT, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, Units.val_mul, mul_smul]

theorem evOneQ_actD (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (g : G) (q : (Fin 1 → LL) ⧸ stdG O LL 1) :
    evOneQ LL (actD (stdLatG hinj N) g q) = N g 0 0 • evOneQ LL q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show evOneQ LL (Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g v)) = _
    rw [evOneQ_mk, evOneQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

end Gen2

section Gen3
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem liftC_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (hN : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0)
    (lam : O) (a : ℕ) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1) (hf : f ∈ divisibleCocycles (stdLatG hinj N))
    (htor : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (latOne hinj ψ) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaC LL lam a (z' g) = f g := by
  classical
  obtain ⟨hlc, hco⟩ := hf
  let F : ((Fin 1 → LL) ⧸ stdG O LL 1) → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a) :=
    fun q => if hq : lam ^ a • q = 0 then oneT hinj ψ ⊗ₜ ⟨evOneQ LL q, evOneQ_mem hq⟩ else 0
  refine ⟨fun g => oneT hinj ψ ⊗ₜ ⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩, ⟨?_, ?_⟩, ?_⟩
  · have hF : (fun g => oneT hinj ψ ⊗ₜ[O]
        (⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩ : ↥(Xq LL lam a))) = F ∘ f := by
      funext g
      simp only [F, Function.comp_apply, dif_pos (htor g)]
    rw [hF]
    exact hlc.comp F
  · intro g h
    beta_reduce
    rw [actTw_oneO, ← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hco g h, hN g]
    exact ((evOneQ LL).map_add _ _).trans (congrArg (evOneQ LL (f g) + ·) (evOneQ_actD hinj N g (f h)))
  · intro g
    exact iotaC_oneO lam a (f g) _

end Gen3

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locOC_chiRatO_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, Br.iota, mapM, chiRatO, twistM]

theorem chiT_one_eq_theta (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

theorem chiT_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = locOC C (chiRatO D.nd i c) g 0 0 := by
  rw [locOC_chiRatO_apply, chiT_one_eq_theta]
  congr 1
  simp only [chiT, MonoidHom.mul_apply]
  rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

end AtW

theorem liftC_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  intro D i w hw C lam _ θ c a f hf htor
  exact liftC_gen Subtype.val_injective (locOC C (chiRatO D.nd i c)) (chiT C θ 1) (chiT C θ c) (chiT_ratio C θ c)
    lam a f hf htor

end GlobalTheory.UseLoc.Cases

end
