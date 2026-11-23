import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section

namespace GlobalTheory.UseLoc.Cases

theorem chiT_one_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

section GenRead

variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL] {k : ℕ}

def iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) :
    ↥(stdLatG (LL := LL) hinj M).T ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ (stdLatG (LL := LL) hinj N).T :=
  iotaW LL lam a k

theorem iotaL_tmul (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) (t : ↥(stdLatG (LL := LL) hinj M).T)
    (x : ↥(Xq LL lam a)) (s : LL) (hs : Submodule.Quotient.mk s = (x : LL ⧸ intO (O := O) LL)) :
    iotaL hinj M N lam a (t ⊗ₜ x) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := by
  obtain ⟨x, hx⟩ := x
  change Submodule.Quotient.mk s = x at hs
  subst hs
  rfl

theorem matRep_twistM_apply {G : Type} [Group G] (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (v : Fin k → LL) :
    matRep (mapM (algebraMap O LL) (twistM N θ)) g v = ((θ g : Oˣ) : O) • matRep (mapM (algebraMap O LL) N) g v := by
  have hM : (mapM (algebraMap O LL) (twistM N θ)) g =
      algebraMap O LL ((θ g : Oˣ) : O) • (mapM (algebraMap O LL) N) g := by
    ext p q
    simp [mapM, twistM, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((mapM (algebraMap O LL) (twistM N θ)) g).mulVec v = ((θ g : Oˣ) : O) • ((mapM (algebraMap O LL) N) g).mulVec v
  rw [hM, Matrix.smul_mulVec, algebraMap_smul]

theorem actD_iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (g : G) (y : ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a)) :
    actD (stdLatG hinj N) g (iotaL hinj (twistM N θ) N lam a y) =
      iotaL hinj (twistM N θ) N lam a (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul t x =>
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x : LL ⧸ intO (O := O) LL)
    rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, map_smul, iotaL_tmul hinj _ N lam a _ x s hs,
      iotaL_tmul hinj _ N lam a _ x s hs, ← Submodule.Quotient.mk_smul]
    change Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g (s • (t : Fin k → LL))) =
      Submodule.Quotient.mk ((((χ g)⁻¹ : Oˣ) : O) • s • matRep (mapM (algebraMap O LL) (twistM N θ)) g (t : Fin k → LL))
    congr 1
    rw [matRep_twistM_apply, LinearMap.map_smul, smul_comm _ s, ← mul_smul, hχ g, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [Algebra Qp LL]
    [TopologicalSpace (Fin k → LL)] [ContinuousAdd (Fin k → LL)] [ContinuousConstSMul LL (Fin k → LL)]

theorem readW_gen (PD : PeriodData G Qp K₀ K B BdR) (hinj : Function.Injective (algebraMap O LL))
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (z' : G → ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.InHfX PD (stdLatG (LL := LL) hinj (twistM N θ)) (stdLatG hinj N) ↥(Xq LL lam a) χ z') :
    (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) ∈ HfD PD (stdLatG (LL := LL) hinj N) := by
  obtain ⟨n, c, x, m, hc, hz⟩ := hz
  choose s hs using fun j => Submodule.Quotient.mk_surjective _ (x j : LL ⧸ intO (O := O) LL)
  have e : (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) =
      (∑ j, LinearMap.compLeft (stdLatG (LL := LL) hinj N).T.mkQ G (s j • fun g => (c j g : Fin k → LL))) +
        LinearMap.pi (fun g => actD (stdLatG (LL := LL) hinj N) g - LinearMap.id)
          (iotaL hinj (twistM N θ) N lam a m) := by
    funext g
    rw [hz g, map_add, map_sum, map_sub, ← actD_iotaL hinj N θ χ hχ lam a g m]
    simp only [Pi.add_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iotaL_tmul hinj _ N lam a _ (x j) (s j) (hs j)]
    rfl
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_sup_left (Submodule.mem_map_of_mem ?_))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.restrictScalars_mem O _ _).2 ((finiteCocycles PD _).smul_mem (s j) (hc j).2)

end GenRead

theorem chiT_one_inv_mul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = 1 := by
  rw [chiT_one_eq]
  simp

theorem readW_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  intro D i w hw C lam k N θ a z' hz
  exact readW_gen (Br.PD D.loc D.nbr i w hw) Subtype.val_injective N θ (chiT C θ 1) (chiT_one_inv_mul C θ) lam a z' hz

end GlobalTheory.UseLoc.Cases

end
