import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.ReadC

section Gen
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    Formalism.WeaklyAdmissibleFiltrations.actT (latOne hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Formalism.WeaklyAdmissibleFiltrations.actT, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • x = ((ψ g : Oˣ) : O) • x
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ) (g : G) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g = (((χ g)⁻¹ * ψ g : Oˣ) : O) • LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul, Units.val_mul]

theorem actD_one (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (g : G) :
    actD (stdLatG hinj M) g = M g 0 0 • LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, actD,
    ← Submodule.Quotient.mk_smul]
  erw [Submodule.mapQ_apply]
  congr 1
  funext j
  fin_cases j
  simp [stdLatG, matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem equivG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O)) (g : G)
    (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) :
    iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u) =
      actD (stdLatG hinj M) g (iotaC LL lam a u) := by
  have h1 : tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u = (((χ g)⁻¹ * ψ g : Oˣ) : O) • u := by
    rw [actTw_latOne]; rfl
  rw [h1, actD_one, hM]
  exact (iotaC LL lam a).map_smul _ u

end Gen
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC
section Gen2
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem readG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O))
    (z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.IsCob (latOne hinj ψ) ↥(Xq LL lam a) χ z') :
    (fun g => iotaC LL lam a (z' g)) ∈ BD (stdLatG hinj M) := by
  obtain ⟨m, hm⟩ := hz
  refine ⟨iotaC LL lam a m, ?_⟩
  funext g
  have key := equivG hinj lam a ψ χ M hM g m
  rw [hm g]
  refine Eq.trans ?_ ((iotaC LL lam a).map_sub _ m).symm
  exact (congrArg (fun y => y - iotaC LL lam a m) key).symm

end Gen2
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem entry (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, mapM, chiRatO, twistM, Br.iota]

theorem ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    (chiT C θ 1 g)⁻¹ * chiT C θ c g = chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g := by
  have h1 : chiOC C 1 g = 1 := by simp [chiOC]
  simp only [chiT, MonoidHom.mul_apply, mul_inv_cancel, h1, one_mul]
  rw [mul_comm (chiOC C _ g) (θ g)]
  exact inv_mul_cancel_left _ _

theorem entry_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  rw [entry, ratio]

end GlobalTheory.UseLoc.Cases.ReadC

theorem GlobalTheory.UseLoc.Cases.readC_cob : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) :=
  fun D i w hw C lam θ c a z' hz =>
    ReadC.readG (LL := ↥C.LL.1) Subtype.val_injective lam a (chiT C θ c) (chiT C θ 1) (locOC C (chiRatO D.nd i c))
      (ReadC.entry_ratio C θ c) z' hz
