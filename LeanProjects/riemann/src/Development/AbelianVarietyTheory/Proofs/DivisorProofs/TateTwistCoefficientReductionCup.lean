import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedCup

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem cpush_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (a : CohomologyClass K I n) : cpush K (𝟙 I) n a = a := by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

def semiPre {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K') :
    SemiMap T K' where
  app U s := (ρ.app U s).comp ((u.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    change Sec.res g (ρ.app _ s (Sec.map (u.f s) a)) = ρ.app _ s (Sec.map (u.f s) (Sec.res g a))
    rw [ρ.nat, sec_map_res]
  comm U s t a := by
    change Sec.map (_ : _ ⟶ _) (ρ.app U s (Sec.map (u.f s) a)) = ρ.app U t (Sec.map (u.f t) (Sec.map (T.d s t) a))
    rw [ρ.comm, ← sec_map_comp, ← sec_map_comp, u.comm]

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (u : I ⟶ K)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x = Sec.map (u.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem semiPre_op {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K')
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) T n) :
    (semiPre u ρ).op.app E n x = ρ.op.app E n (cpush _ u n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n (zcomp α (Cocycle.ofHom u) (add_zero n))
  change _ = ρ.op.app E n (CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)))
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n _ β hβ]
  refine (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R (semiPre u ρ)).2 E n α β (fun p s h U y => ?_)
  rw [hβ p s h U y]
  change ρ.app U s (ev (α.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y) = _
  rw [ev_comp_ofHom]
  rfl

theorem semiMap_cup : ∀ (S R : Type) [CommRing S] [CommRing R] {I J T : Cx S} {I' J' K' : Cx R} (τ : Pair I J T) (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (σ : SemiMap T K'), (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b)) → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains S).obj E) I n) (b : CohomologyClass ((chains S).obj E) J m), σ.op.app E k (τ.cup E hk a b) = ν.cup E hk (ρ₁.op.app E n a) (ρ₂.op.app E m b) := by
  intro S R _ _ I J T I' J' K' τ ν ρ₁ ρ₂ σ hσ E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW S τ hk).1 α β
  obtain ⟨α', hα'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).1 E m β
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).1 E k γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW S τ hk).2 α β γ hγ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).2 E k γ γ' hγ',
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).2 E n α α' hα', (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).2 E m β β' hβ']
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 α' β' γ' ?_).symm
  intro N w h U x
  rw [hγ' N w h U x, hγ N w h U x, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, hσ, ← hα', ← hβ', Units.smul_def]

theorem reduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j),
    red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  intro Q q _ hqQ E n m i j a b
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp hqQ)⟩
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod Q) (res _ (tw Q i)) (res _ (tw Q j))
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod Q) τ hτ).1 (twPair Q i j) (𝟙 _) (𝟙 _)
  have hcup : cup Q a b = cpush _ u _ (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod Q) τ (twPair Q i j) (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
    rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_semiMap_of_tensorPairing Q (ZMod q) τ hτ (twPair q i j) (redMap Q q i) (redMap Q q j)
  have h1 := semiMap_cup (ZMod Q) (ZMod q) τ (twPair q i j) (redMap Q q i) (redMap Q q j) σ hσ E rfl a b
  rw [hcup]
  change (redMap Q q (i + j)).op.app E (n + m) (cpush _ u _ _) = (twPair q i j).cup E rfl _ _
  rw [← semiPre_op]
  change _ = (twPair q i j).cup E rfl ((redMap Q q i).op.app E n a) ((redMap Q q j).op.app E m b)
  rw [← h1]
  have hres := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q i
  have hresj := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q j
  have htw := GlobalTheory.T.isTateTwistResolution_tensor_flat Q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) hres.1 hresj.1 hresj.2.1 τ hτ
  have hflat := GlobalTheory.T.flat_tensor_of_flat_complexes (ZMod Q) τ hτ hres.2.1 hresj.2.1
  refine GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution Q q hqQ (i + j) _ htw hflat _ _ ?_ E (n + m) _
  intro U ζ
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [hσ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ ξ hξ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ j U ζ ξ hξ, (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 U ξ]
  change (redMap Q q (i + j)).app U 0 (Sec.map (u.f 0) _) = _
  rw [hu]
  change (redMap Q q (i + j)).app U 0 ((twPair Q i j).mul U 0 0 0 _ (resGen i ζ) (resGen j ζ)) = _
  rw [(GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique Q i j).1 U ζ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ (i + j) U ζ ξ hξ]

end GlobalTheory.EtC.RedCup

end
