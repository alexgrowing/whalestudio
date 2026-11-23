import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsReducedTorsionGeometricFibre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgHomLocalizationAugmentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTraceStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]

theorem exists_rep [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    (hfin : IsFinite ((𝟙 A) ^ n : A ⟶ A).left) (hflat : Flat ((𝟙 A) ^ n : A ⟶ A).left) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra O H), Module.Free O H ∧ Module.Finite O H ∧
      ∃ y : specO O H ⟶ A, y ^ n = 1 ∧ ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
        ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z := by
  obtain ⟨H, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 A) ^ n : A ⟶ A).left
    (CommRingCat.of O) (eSec A)
  letI : Algebra O H := φ.hom.toAlgebra
  haveI : Module.Finite O H := hφf
  haveI : Module.Flat O H := hφl
  have hpow : ∀ {T : Over (Sp O)} (z : T ⟶ A),
      z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have hy : y ≫ A.hom = (specO O H).hom := by
    rw [← Over.w ((𝟙 A) ^ n : A ⟶ A), ← Category.assoc, hpb.w, Category.assoc, he]
    exact Category.comp_id _
  let y' : specO O H ⟶ A := Over.homMk y hy
  refine ⟨H, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, GlobalTheory.UU.one_left]
    exact hpb.w
  · intro S _ _ z hz
    have hw : z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left =
        Spec.map (CommRingCat.ofHom (algebraMap O S)) ≫ eSec A := by
      rw [hpow, hz, GlobalTheory.UU.one_left]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec H := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap O S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : H ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

theorem isReduced_rep {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {H : Type} [CommRing H] [Algebra O H]
    [Module.Finite O H] {y : specO O H ⟶ A} (hy : y ^ n = 1)
    (hu : ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
      ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra O F] (hn : (n : F) ≠ 0) : _root_.IsReduced (F ⊗[O] H) := by
  refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
  let χ : H →ₐ[O] DualNumber F := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hz : (ptMap χ ≫ y) ^ n = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have h2 := TorsionReduced.eq_const_of_pow_eq_one hn.isUnit _ hz
  simp only [← Category.assoc] at h2
  rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h2
  have h4 := (hu _ _ hz).unique rfl h2.symm
  have h5 : ∀ a, (χ a).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f a) h4)
    simpa using this
  induction b with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, TrivSqZeroExt.snd_smul]
    exact smul_eq_zero_of_right f (h5 a)

theorem eq_one_of_affine {A : Over (Sp O)} [GrpObj A] {T : Over (Sp O)} (x : T ⟶ A)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (ρ : specO O S ⟶ T), ρ ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (T.left.affineOpenCover.f i ≫ T.hom)
  letI : Algebra O (T.left.affineOpenCover.X i) := ψ.hom.toAlgebra
  let ρ : specO O (T.left.affineOpenCover.X i) ⟶ T := Over.homMk (T.left.affineOpenCover.f i) hψ.symm
  have := (h _ ρ).trans (MonObj.comp_one ρ).symm
  exact congrArg (fun q => q.left) this

section Val
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']

def Val (x y : specO O S ⟶ A) (s : S) : Prop :=
  ∃ ζ, GlobalTheory.UU.CubWeil c n x y ζ ∧ (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ζ.val = s

variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}

theorem Val.exists (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ s, Val c n x y s := by
  obtain ⟨ζ, h, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hx hy
  exact ⟨_, ζ, h, rfl⟩

theorem Val.unique (h : Val c n x y s) (h' : Val c n x y s') : s = s' := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  rw [h.unique h']

theorem Val.isUnit (h : Val c n x y s) : IsUnit s := by
  obtain ⟨ζ, h, rfl⟩ := h
  exact ζ.isUnit.map _

theorem val_one_iff : Val c n x y 1 ↔ GlobalTheory.UU.CubWeil c n x y 1 := by
  refine ⟨fun ⟨ζ, h, e⟩ => ?_, fun h => ⟨1, h, map_one _⟩⟩
  have : ζ = 1 := Units.ext ((ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1 (e.trans (map_one _).symm))
  exact this ▸ h

theorem Val.mul_left (h : Val c n x y s) (h' : Val c n x' y s') : Val c n (x * x') y (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  exact ⟨_, h.mul_left h', map_mul _ _ _⟩

theorem Val.mul_right (h : Val c n x y s) (h' : Val c n x y' s') : Val c n x (y * y') (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  have := (h.symm.mul_left h'.symm).symm
  rw [mul_inv, inv_inv, inv_inv] at this
  exact ⟨_, this, map_mul _ _ _⟩

theorem Val.comp (h : Val c n x y s) (f : S →ₐ[O] S') : Val c n (ptMap f ≫ x) (ptMap f ≫ y) (f s) := by
  obtain ⟨ζ, h, rfl⟩ := h
  refine ⟨_, h.comp (ptMap f), ?_⟩
  exact congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))

theorem exists_matrix (c : CubicalStr A L) {H : Type} [CommRing H] [Algebra O H] {r : ℕ} (b : Module.Basis (Fin r) O H)
    {y : specO O H ⟶ A} (hy : y ^ n = 1) :
    ∃ D : Matrix (Fin r) (Fin r) O, ∀ (S : Type) [CommRing S] [Algebra O S] (φ ψ : H →ₐ[O] S),
      Val c n (ptMap φ ≫ y) (ptMap ψ ≫ y) (∑ i, ∑ j, algebraMap O S (D i j) * φ (b i) * ψ (b j)) := by
  have hz : ∀ χ : H →ₐ[O] H ⊗[O] H, (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨e, he⟩ := Val.exists (c := c) (hz Algebra.TensorProduct.includeLeft) (hz Algebra.TensorProduct.includeRight)
  refine ⟨fun i j => (b.tensorProduct b).repr e (i, j), fun S _ _ φ ψ => ?_⟩
  have h := he.comp (Algebra.TensorProduct.productMap φ ψ)
  rw [← Category.assoc, ← Category.assoc, TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap,
    Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right] at h
  convert h using 1
  conv_rhs => rw [← (b.tensorProduct b).sum_repr e]
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    _root_.mul_assoc]

end Val

theorem algHom_eq_of_isUnit_det {H S : Type} [CommRing H] [Algebra O H] [CommRing S] [Algebra O S] {r : ℕ}
    (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (hD : IsUnit D.det) (φ φ' : H →ₐ[O] S)
    (h : ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ' (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j)) : φ = φ' := by
  have key : ∀ ψ : H →ₐ[O] S,
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (ψ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
        ∑ j, (Matrix.vecMul (fun i => ψ (b i)) (D.map (algebraMap O S)) j) • Algebra.TensorProduct.basis S b j := by
    intro ψ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
  rw [key, key] at h
  have h1 := (Algebra.TensorProduct.basis S b).equivFun.symm.injective
    (((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).trans
      (h.trans ((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).symm))
  have hD' : IsUnit (D.map (algebraMap O S)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := hD.map (algebraMap O S)
    rwa [RingHom.map_det] at this
  have h2 := (Matrix.vecMul_injective_of_isUnit hD') h1
  exact AlgHom.toLinearMap_injective (b.ext fun i => congrFun h2 i)

end GlobalTheory.PerfectPairing

namespace GlobalTheory
open PerfectPairing in

theorem cubWeil_perfect_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  intro O K _ _ _ _ _ _ _ hinj A _ _ g hsm L c n hn hfin hflat hcard hK T x hx hT
  obtain ⟨H, _, _, _, _, y, hy, hu⟩ := exists_rep A n hfin hflat
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hred := isReduced_rep hy hu K hnK
  let b := Module.finBasis O H
  obtain ⟨D, hD⟩ := exists_matrix c b hy
  have hz : ∀ {S : Type} [CommRing S] [Algebra O S] (χ : H →ₐ[O] S), (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  let Γ : Subgroup (specO O K ⟶ A) := (powMonoidHom n).ker
  choose pt hpt using fun a : Γ => (hu K a.1 a.2).exists
  have hbij : Function.Bijective pt := by
    refine ⟨fun a a' e => Subtype.ext (by rw [← hpt, ← hpt, e]), fun χ => ⟨⟨ptMap χ ≫ y, hz χ⟩, ?_⟩⟩
    exact (hu K _ (hz χ)).unique (hpt _) rfl
  let X : Γ → Γ → K := fun a a' => ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)
  have hX : ∀ a a' : Γ, Val c n a.1 a'.1 (X a a') := fun a a' => by
    have := hD K (pt a) (pt a')
    rwa [hpt, hpt] at this
  have hr : Module.finrank O H = n ^ (2 * g) := by
    rw [← (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange O H K hred).2.1, ← Nat.card_eq_of_bijective pt hbij]
    exact hcard
  have hdet : IsUnit D.det := by
    refine GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace O H K Γ _ b D pt X ((n : O) ^ g) hinj hred hbij (fun _ _ => rfl)
      (fun a a' => (hX a a').isUnit.ne_zero) (fun a a' d => (hX _ _).unique ((hX a d).mul_left (hX a' d)))
      (fun a d d' => (hX _ _).unique ((hX a d).mul_right (hX a d'))) (fun a ha => Subtype.ext ?_) (fun h0 => ?_) ?_
      (GlobalTheory.pow_dvd_trace_torsion O A n H y g hsm hy hu)
    · refine hK a.1 a.2 fun z hz => val_one_iff.1 ?_
      have := hX a ⟨z, hz⟩
      rwa [ha] at this
    · have := congrArg (algebraMap O K) h0
      rw [map_pow, map_natCast, map_zero] at this
      exact pow_ne_zero g hnK this
    · rw [hr, Nat.cast_pow, mul_comm, pow_mul]
  refine eq_one_of_affine x fun S _ _ ρ => ?_
  obtain ⟨φ, hφ, -⟩ := hu S (ρ ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  obtain ⟨φ', hφ', -⟩ := hu S 1 (one_pow n)
  let l : S →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeLeft
  let m : H →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeRight
  have h1 := hD _ (l.comp φ) m
  have h2 := hD _ (l.comp φ') m
  rw [← TangentPow.ptMap_comp_ptMap, Category.assoc] at h1 h2
  rw [hφ, ← Category.assoc] at h1
  rw [hφ', MonObj.comp_one] at h2
  have e1 := h1.unique (val_one_iff.2 (hT _ _ _ (hz m)))
  have e2 := h2.unique (val_one_iff.2 (GlobalTheory.UU.cubWeil_one_left c (hz m)))
  rw [← hφ, ← hφ', algHom_eq_of_isUnit_det b D hdet φ φ' (e1.trans e2.symm)]

end GlobalTheory
