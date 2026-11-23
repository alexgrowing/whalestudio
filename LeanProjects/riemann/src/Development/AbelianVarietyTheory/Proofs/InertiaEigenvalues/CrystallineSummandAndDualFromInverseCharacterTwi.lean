import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJumpStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegCycPowerBlockCrysDeRhamJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensionalStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SummandJumps

open Matrix in

theorem exists_decomp_map {K L Γ : Type} [CommRing K] [CommRing L] (φ : K →+* L) {n r t : ℕ}
    (A : Γ → Matrix (Fin n) (Fin n) K) (B : Γ → Matrix (Fin r) (Fin r) K) (c : Γ → Fin t → K)
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (he : ∀ g u, e (A g *ᵥ u) = (B g *ᵥ (e u).1, fun j => c g j * (e u).2 j)) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)),
      ∀ g u, e' ((A g).map φ *ᵥ u) =
        ((B g).map φ *ᵥ (e' u).1, fun j => φ (c g j) * (e' u).2 j) := by
  classical
  let s := LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) K K
  let e0 : (Fin n → K) ≃ₗ[K] (Fin r ⊕ Fin t → K) := e.trans s.symm
  let P : Matrix (Fin r ⊕ Fin t) (Fin n) K := LinearMap.toMatrix' e0.toLinearMap
  let Q : Matrix (Fin n) (Fin r ⊕ Fin t) K := LinearMap.toMatrix' e0.symm.toLinearMap
  have hPQ : P * Q = 1 := by
    rw [← LinearMap.toMatrix'_comp]; simp
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix'_comp]; simp
  have hP : ∀ u, P *ᵥ u = Sum.elim (e u).1 (e u).2 := by
    intro u
    rw [LinearMap.toMatrix'_mulVec]
    funext x
    rcases x with x | x <;> rfl
  have hA : ∀ g, P * A g = fromBlocks (B g) 0 0 (diagonal (c g)) * P := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, he, fromBlocks_mulVec]
    funext x
    rcases x with x | x <;> simp [Matrix.mulVec_diagonal]
  have h1 : P.map φ * Q.map φ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ φ.map_zero φ.map_one]
  have h2 : Q.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ φ.map_zero φ.map_one]
  refine ⟨(Matrix.toLin'OfInv h2 h1).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) L L), fun g u => ?_⟩
  have h3 : P.map φ *ᵥ ((A g).map φ *ᵥ u) =
      fromBlocks ((B g).map φ) 0 0 (diagonal fun j => φ (c g j)) *ᵥ (P.map φ *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, hA, Matrix.map_mul,
      fromBlocks_map, Matrix.diagonal_map φ.map_zero, Matrix.map_zero _ φ.map_zero,
      Matrix.map_zero _ φ.map_zero]
  have h4 : ∀ v, (Matrix.toLin'OfInv h2 h1) v = P.map φ *ᵥ v := fun v => rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h4, h4, h3, fromBlocks_mulVec]
  ext x
  · simp [Function.comp_def]
    rfl
  · simp [Matrix.mulVec_diagonal]

theorem matRep_apply {Kf Γ : Type} [CommRing Kf] [Group Γ] {k : ℕ}
    (M : Γ →* Matrix (Fin k) (Fin k) Kf) (g : Γ) (v : Fin k → Kf) :
    matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem dual_equivariant {L Γ : Type} [Field L] [Group Γ] {r : ℕ}
    (W : Γ →* Matrix (Fin r) (Fin r) L) :
    GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.IsEquivariant (matRep W).dual (matRep (dualM W))
      (dotProductEquiv L (Fin r)).symm.toLinearMap := by
  intro g f
  obtain ⟨v, rfl⟩ := (dotProductEquiv L (Fin r)).surjective f
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun x => ?_
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    matRep_apply, dotProductEquiv_apply_apply]
  show v ⬝ᵥ (W g⁻¹).mulVec x = (W g⁻¹).transpose.mulVec v ⬝ᵥ x
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem pairing_twist {L Γ : Type} [Field L] [Group Γ] {r : ℕ}
    (W T : Γ →* Matrix (Fin r) (Fin r) L) (χ : Γ →* Lˣ)
    (hTW : ∀ g, T g = ((χ g : Lˣ) : L) • (W g⁻¹).transpose) (g : Γ) (x y : Fin r → L) :
    (dotProductEquiv L (Fin r)).toLinearMap (matRep W g x) (matRep T g y) =
      ((χ g ^ (1 : ℤ) : Lˣ) : L) * (dotProductEquiv L (Fin r)).toLinearMap x y := by
  show matRep W g x ⬝ᵥ matRep T g y = _ * (x ⬝ᵥ y)
  rw [matRep_apply, matRep_apply, hTW, Matrix.smul_mulVec, dotProduct_smul, zpow_one,
    smul_eq_mul, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    dotProduct_comm]

theorem twist_dual_apply {L Γ : Type} [Field L] [Group Γ] {r : ℕ}
    (W T : Γ →* Matrix (Fin r) (Fin r) L) (χ : Γ →* Lˣ)
    (hTW : ∀ g, T g = ((χ g : Lˣ) : L) • (W g⁻¹).transpose) (g : Γ) (x : Fin r → L) :
    matRep T g x = ((χ g : Lˣ) : L) • matRep (dualM W) g x := by
  rw [matRep_apply, matRep_apply, hTW, Matrix.smul_mulVec]; rfl

theorem charRep_one_apply {L Γ : Type} [Field L] [Group Γ] (χ : Γ →* Lˣ) (g : Γ) (x : L) :
    WeaklyAdmissibleFiltrations.charRep (χ ^ (1 : ℤ)) g x = ((χ g : Lˣ) : L) • x := by
  rw [zpow_one]; rfl

theorem exists_block {L Γ : Type} [Field L] [Group Γ] (t : ℕ) (χ : Γ →* Lˣ) :
    ∃ Z : Representation L Γ (Fin t → L), ∀ g v (c : Fin t),
      Z g v c = (((χ g)⁻¹ ^ (c : ℕ) : Lˣ) : L) * v c := by
  let Z : Γ →* Matrix (Fin t) (Fin t) L :=
    { toFun := fun g => Matrix.diagonal fun c : Fin t => (((χ g)⁻¹ ^ (c : ℕ) : Lˣ) : L)
      map_one' := by simp
      map_mul' := fun g h => by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext c
        rw [map_mul, mul_inv, mul_pow, Units.val_mul] }
  refine ⟨matRep Z, fun g v c => ?_⟩
  rw [matRep_apply]
  exact Matrix.mulVec_diagonal _ _ _

theorem exists_decomp_twist {O L Γ : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Group Γ]
    (ψ : O →+* L) (hψ : Function.Injective ψ) {n r t : ℕ}
    (σ : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (ε : Γ →* Oˣ)
    (key : ∀ c : ℕ, c < t → χ (c + 1) * (χ 1)⁻¹ = ε ^ (-(c : ℤ)))
    (hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := t) σ ρ χ e) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ g u,
      e' (((twistM ((Units.coeHom _).comp σ) (χ 1)⁻¹ g).map ψ).mulVec u) =
        (((twistM ((Units.coeHom _).comp ρ) (χ 1)⁻¹ g).map ψ).mulVec (e' u).1,
          fun c : Fin t => (((Units.map (ψ : O →* L) (ε g))⁻¹ ^ (c : ℕ) : Lˣ) : L) * (e' u).2 c) := by
  obtain ⟨e, he⟩ := hd
  let φ : FractionRing O →+* L := IsFractionRing.lift hψ
  have hφ : ∀ x, φ (algebraMap _ _ x) = ψ x := fun x => IsFractionRing.lift_algebraMap hψ x
  obtain ⟨e', he'⟩ := exists_decomp_map φ
    (fun g => (twistM ((Units.coeHom _).comp σ) (χ 1)⁻¹ g).map (algebraMap _ (FractionRing O)))
    (fun g => (twistM ((Units.coeHom _).comp ρ) (χ 1)⁻¹ g).map (algebraMap _ (FractionRing O)))
    (fun g (c : Fin t) => algebraMap _ (FractionRing O) (((ε g)⁻¹ ^ (c : ℕ) : Oˣ) : O)) e (by
      intro g u
      have h0 := he g u
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, matRep_apply] at h0
      have hsm : ∀ {k : ℕ} (a : O) (N : Matrix (Fin k) (Fin k) O),
          (a • N).map (algebraMap _ (FractionRing O)) =
            algebraMap _ (FractionRing O) a • N.map (algebraMap _ (FractionRing O)) := by
        intro k a N
        ext x y
        simp
      show e ((((((χ 1)⁻¹ g : Oˣ) : O) • ((Units.coeHom _).comp σ) g).map _).mulVec u) =
        ((((((χ 1)⁻¹ g : Oˣ) : O) • ((Units.coeHom _).comp ρ) g).map _).mulVec _, _)
      rw [hsm, hsm, Matrix.smul_mulVec, Matrix.smul_mulVec, map_smul]
      erw [h0]
      refine Prod.ext rfl (funext fun c => ?_)
      have hk := congrArg (fun χ : Γ →* Oˣ => χ g) (key c c.2)
      simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_neg, zpow_natCast] at hk
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, mul_comm (_ : Oˣ), hk]
      simp)
  refine ⟨e', fun g u => ?_⟩
  have h1 := he' g u
  simp only [Matrix.map_map, Function.comp_def, hφ] at h1
  refine h1.trans (Prod.ext rfl (funext fun c => ?_))
  show ψ _ * _ = _ * _
  rw [← map_inv (Units.map (ψ : O →* L)), ← map_pow (Units.map (ψ : O →* L))]
  rfl

theorem twist_dual_map {O L Γ : Type} [CommRing O] [Field L] [Group Γ] (ψ : O →+* L) {r : ℕ}
    (W : Γ →* Matrix (Fin r) (Fin r) O) (ε : Γ →* Oˣ) (g : Γ) :
    (twistM (dualM W) ε g).map ψ =
      ((Units.map (ψ : O →* L) (ε g) : Lˣ) : L) • ((W g⁻¹).map ψ).transpose := by
  ext x y
  exact map_mul ψ _ _

theorem local_core (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1)
    {n r t : ℕ} (M : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (W T : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1)
    (e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] ((Fin r → ↥LL.1) × (Fin t → ↥LL.1)))
    (he : ∀ g u, e ((M g).mulVec u) = ((W g).mulVec (e u).1, fun c : Fin t =>
      (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * (e u).2 c))
    (hTW : ∀ g, T g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (W g⁻¹).transpose) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) (matRep W) ∧ IsCrys (P.PD K) (matRep T)) ∧
    (IsDR (P.PD K) (matRep M) → IsDR (P.PD K) (matRep W) ∧ IsDR (P.PD K) (matRep T) ∧
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
        multV (P.PD K) (matRep W) τ a =
          multV (P.PD K) (matRep M) τ a - (if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0) ∧
        multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep W) τ (-a - 1)) := by
  obtain ⟨Z, hZ⟩ := exists_block t (cycLL (P.PD K) ↥LL.1)
  obtain ⟨-, -, zm⟩ := GlobalTheory.T.negCycPowerBlock_crys_deRham_jumps l P AI hT K LL t Z hZ
  obtain ⟨sd, sc, sm⟩ := GlobalTheory.T.directSum_deRham_crystalline_jumps_add l P AI hT K LL _ (matRep M) _ (matRep W) _ Z e
    (fun g v => by
      rw [matRep_apply, he, matRep_apply]
      exact Prod.ext rfl (funext fun c => (hZ g _ c).symm))
  constructor
  · intro hM
    have hW := (sc.1 hM).1
    refine ⟨hW, ?_⟩
    have h := (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.fontaineFormalism_iff l P).1
      (GlobalTheory.RegularRing.fontaineFormalism GlobalTheory.T.fontaineBcrisBasicTheorems_proof l P AI ⟨hT⟩) K LL
    have hq := h.2.2.2.2.1
    have ht := h.2.2.2.2.2.2.1
    have hd := h.2.2.2.2.2.2.2.1
    have hD : IsCrys (P.PD K) (matRep (dualM W)) :=
      hq _ (matRep W).dual _ (matRep (dualM W)) _ (dual_equivariant W)
        (LinearEquiv.surjective _) (hd _ _ hW)
    exact GlobalTheory.TwistCrys.isCrys_twist (P.PD K) ht hq (matRep (dualM W)) (matRep T)
      (WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥LL.1 ^ (1 : ℤ)))
      (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) LinearMap.id 1 rfl
      (charRep_one_apply _) (twist_dual_apply W T _ hTW) (GlobalTheory.T.cyc_zpow_crys_dR_jump_alt l P AI hT K LL 1).1 hD
  · intro hM
    have hW := (sd.1 hM).1
    obtain ⟨td, tm⟩ := GlobalTheory.T.galois_representation_hom_finite_dimensional l P AI hT K LL _ (matRep W) _ (matRep T)
      _ 1 (LinearEquiv.bijective _) (pairing_twist W T _ hTW) hW
    refine ⟨hW, td, fun τ a => ⟨?_, ?_⟩⟩
    · rw [sm τ a, zm τ a, add_sub_cancel_right]
    · have h1 := tm τ (-a - 1) hs
      rwa [show -(-a - 1) - 1 = a by ring] at h1

set_option maxHeartbeats 800000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e) → (IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π))))) ∧ (IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' a = multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' a - (if 0 ≤ a ∧ a < (D.R.t : ℤ) then 1 else 0) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' (-a - 1)) := by
  intro D i w hw hT LL' h r ρ π hd
  let ψ : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL
  have hψ : Function.Injective ψ :=
    (IntermediateField.inclusion_injective h).comp (Br.toLL_inj (D.nbr i w hw))
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hloc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw),
      mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw M) g =
        (M (j g)).map ψ := fun M g => rfl
  have hε : ∀ g, ψ (epsU D.nd i (j g) : (D.nd.O i)ˣ) =
      ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) := by
    intro g
    have h1 := congrArg (fun u : (Br.LL D.nbr i w hw)ˣ =>
      IntermediateField.inclusion h (u : Br.LL D.nbr i w hw))
      (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
    exact h1.trans ((IntermediateField.inclusion h).commutes _)
  have hε' : ∀ g, Units.map (ψ : D.nd.O i →* ↥LL'.1) (epsU D.nd i (j g)) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g := fun g => Units.ext (hε g)
  have key : ∀ c : ℕ, c < D.R.t →
      D.nd.chi i (c + 1) * (D.nd.chi i 1)⁻¹ = epsU D.nd i ^ (-(c : ℤ)) := by
    intro c hc
    rw [D.nd.chi_def i (c + 1) (by omega) hc, mul_inv_cancel_comm]
    push_cast
    rw [add_sub_cancel_right]
    rfl
  obtain ⟨e', he'⟩ := exists_decomp_twist ψ hψ (r π) (ρ π) (D.nd.chi i) (epsU D.nd i) key hd
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    have := (D.nbr i w hw).Kw.2
    have := LL'.2
    have h2 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun τ x => h ((D.nbr i w hw).LL_split τ x)) (Fintype.ofFinite _)).2
    rw [← h2]
    exact @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)
  refine local_core _ _ _ hT (D.nbr i w hw).Kw LL' hs _ _ _ e' (fun g u => ?_) (fun g => ?_)
  · have h1 := he' (j g) u
    rw [hε'] at h1
    have a1 := hloc (rTwO D.nd i r π) g
    have a2 := hloc (WpO D.nd i ρ π) g
    exact (congrArg (fun N => e' (Matrix.mulVec N u)) a1).trans (h1.trans
      (Prod.ext (congrArg (fun N => Matrix.mulVec N (e' u).1) a2.symm) rfl))
  · have h1 := twist_dual_map ψ (WpO D.nd i ρ π) (epsU D.nd i) (j g)
    rw [hε', ← map_inv j] at h1
    exact (hloc (T2O D.nd i ρ π) g).trans h1

end GlobalTheory.SummandJumps
