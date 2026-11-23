import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActionLevelMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeAssoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ecompose
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Fcompose
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LocalAlgebraInertPrime
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Nabladual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabfin
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.DualWeylModuleStable
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.SatakeDualWeyl.NablaRepApply
import Formalism.SatakeDualWeyl.DualWeylRepApply

namespace Formalism.UG.Final

private theorem mem_doubleCoset_one_iff_mem {G : Type} [Group G] (K : Subgroup G) (y : G) :
    y ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ y ∈ K := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, c, hc, rfl⟩
    simpa using K.mul_mem hh hc
  · intro hy
    exact ⟨y, hy, 1, K.one_mem, by simp⟩

private theorem quotient_out_mem_iff_eq_one {G : Type} [Group G] (K : Subgroup G) (x : G ⧸ K) :
    x.out ∈ K ↔ x = (QuotientGroup.mk (1 : G) : G ⧸ K) := by
  have hx : (QuotientGroup.mk x.out : G ⧸ K) = x := by
    first
      | exact QuotientGroup.out_eq' x
      | exact Quotient.out_eq x
  constructor
  · intro h
    rw [← hx]
    exact QuotientGroup.eq.mpr (by simpa using h)
  · intro h
    have h2 : (QuotientGroup.mk x.out : G ⧸ K) = QuotientGroup.mk 1 := hx.trans h
    simpa using QuotientGroup.eq.mp h2

theorem HeckeActMem : Formalism.UG.HeckeActMem := Formalism.UG.P.hecke_act_mem
theorem HeckeActMul : Formalism.UG.HeckeActMul := Formalism.UG.P.hecke_act_mul
theorem AdelicStabFinite : Formalism.UG.AdelicStabFinite := Formalism.UG.P.adelic_stabilizer_finite_holds
theorem AdelicStabFiniteL : Formalism.UG.AdelicStabFiniteL := Formalism.UG.P.adelic_stabilizer_finite_lattice_holds
theorem HeckeAssoc : Formalism.UG.HeckeAssoc := Formalism.UG.P.hecke_assoc
theorem BCMem : Formalism.UG.BCMem := by
  intro A B _ _ n _ _ σ σ' φ hφ J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  have hb : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl
  have hc : cT σ' ((g : Matrix n n A).map φ) = (cT σ (g : Matrix n n A)).map φ := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    exact (RingHom.congr_fun hφ _).symm
  rw [hb, hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
theorem RatPtsLe : Formalism.UG.RatPtsLe := by
  intro F E _ _ _ n _ _ σ J R _ _ x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  exact Formalism.UG.Final.BCMem E _ n (σ : E →+* E) (sigR σ R) (inclE (F := F) R)
    (RingHom.ext fun e => by simp [inclE, sigR]) J g hg
theorem GlEquivApply : Formalism.UG.GlEquivApply := by
  intro K _ n _ _ g x
  first
    | rfl
    | simp [glEquiv, Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply]
theorem HformGram : Formalism.UG.HformGram := by
  intro K _ _ n _ _ h x y
  have hx : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have hy : y = ∑ j, y j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, Finset.mul_sum, hform, gram]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem HermBridge : Formalism.UG.HermBridge := by
  intro K _ _ n _ _ h g
  have hgl : ∀ x, glEquiv g x = Matrix.mulVec (g : Matrix n n K) x := fun x => Formalism.UG.Final.GlEquivApply K n g x
  have hent : ∀ i j, (cT (starRingEnd K) (g : Matrix n n K) * gram h * (g : Matrix n n K)) i j
      = h (glEquiv g (Pi.single i 1)) (glEquiv g (Pi.single j 1)) := by
    intro i j
    rw [Formalism.UG.Final.HformGram K n h, hgl, hgl]
    simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  constructor
  · intro hu
    have hu' : cT (starRingEnd K) (g : Matrix n n K) * gram h * (g : Matrix n n K) = gram h := hu
    let h' : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K :=
      (h.comp ((glEquiv g : (n → K) ≃ₗ[K] (n → K)) : (n → K) →ₗ[K] (n → K))).compl₂
        ((glEquiv g : (n → K) ≃ₗ[K] (n → K)) : (n → K) →ₗ[K] (n → K))
    have hh' : ∀ x y, h' x y = h (glEquiv g x) (glEquiv g y) := fun x y => rfl
    have hgram : gram h' = gram h := by
      ext i j
      show h' (Pi.single i 1) (Pi.single j 1) = h (Pi.single i 1) (Pi.single j 1)
      rw [hh', ← hent, hu']
      try rfl
    intro x y
    show h (glEquiv g x) (glEquiv g y) = h x y
    rw [← hh', Formalism.UG.Final.HformGram K n h', hgram, ← Formalism.UG.Final.HformGram K n h]
  · intro hB
    show cT (starRingEnd K) (g : Matrix n n K) * gram h * (g : Matrix n n K) = gram h
    ext i j
    rw [hent]
    exact hB _ _
theorem HermBridgeSurj : Formalism.UG.HermBridgeSurj := by
  intro K _ _ n _ _ h u _
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩
  simp [glEquiv]
theorem CartanDecomp : Formalism.UG.CartanDecomp := Formalism.UG.P.cartan_decomposition_holds
theorem CartanUnique : Formalism.UG.CartanUnique := Formalism.UG.P.cartan_decomposition_unique_holds
theorem ClassSetFiniteL : Formalism.UG.ClassSetFiniteL := Formalism.UG.P.lattice_class_set_finite_local_holds
theorem ClassSetFinite : Formalism.UG.ClassSetFinite := Formalism.UG.P.lattice_class_set_finite_holds
theorem HeckeConvMem : Formalism.UG.HeckeConvMem := Formalism.UG.P.hecke_convolution_mem_holds
theorem ConvCount : Formalism.UG.ConvCount := Formalism.UG.P.convolution_count_holds
theorem LevelAfLStd : Formalism.UG.LevelAfLStd := Formalism.UG.P.level_subgroup_finite_adelic_standard
theorem HeckeCommGL : Formalism.UG.HeckeCommGL := Formalism.UG.P.hecke_algebra_GL_commutative
theorem SatakeTj : Formalism.UG.SatakeTj := Formalism.UG.P.satake_transform_hecke_operator_Tj
theorem SatakeInert : Formalism.UG.SatakeInert := Formalism.UG.P.satake_inert
theorem SatMul : Formalism.UG.SatMul := Formalism.UG.P.satake_mul
theorem SphericalExistsU : Formalism.UG.SphericalExistsU := Formalism.UG.P.exists_spherical_function_unitary
theorem GLintComm : Formalism.UG.GLintComm := Formalism.UG.P.GL_integral_hecke_commute
theorem LocInert : Formalism.UG.LocInert := Formalism.UG.P.local_algebra_inert_prime
theorem DosetIndMem : Formalism.UG.DosetIndMem := by
  intro G _ K k _ g
  show (∀ a b : K, ∀ x : G, dosetInd k K g ((a : G) * x * b) = dosetInd k K g x) ∧
    ∃ S : Finset G, ∀ x : G, dosetInd k K g x ≠ 0 → ∃ s ∈ S, ∃ a b : K, x = (a : G) * s * b
  refine ⟨fun a b x => ?_, ⟨{g}, fun x hx => ?_⟩⟩
  · by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)
    · have hm : (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
        obtain ⟨h, hh, c, hc, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
        exact DoubleCoset.mem_doubleCoset.mpr
          ⟨(a : G) * h, K.mul_mem a.2 hh, c * b, K.mul_mem hc b.2, by simp only [mul_assoc]⟩
      simp [dosetInd, Set.indicator_apply, hx, hm]
    · have hm : (a : G) * x * b ∉ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
        intro hm
        apply hx
        obtain ⟨h, hh, c, hc, he⟩ := DoubleCoset.mem_doubleCoset.mp hm
        refine DoubleCoset.mem_doubleCoset.mpr
          ⟨(a : G)⁻¹ * h, K.mul_mem (K.inv_mem a.2) hh, c * (b : G)⁻¹, K.mul_mem hc (K.inv_mem b.2), ?_⟩
        have hx' : x = (a : G)⁻¹ * ((a : G) * x * b) * (b : G)⁻¹ := by group
        rw [hx', he]
        simp only [mul_assoc]
      simp [dosetInd, Set.indicator_apply, hx, hm]
  · have hm : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
      by_contra h
      apply hx
      simp [dosetInd, Set.indicator_apply, h]
    obtain ⟨h, hh, c, hc, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hm
    exact ⟨g, Finset.mem_singleton_self g, ⟨h, hh⟩, ⟨c, hc⟩, rfl⟩
theorem HeckeUnit : Formalism.UG.HeckeUnit := by
  intro G _ K k _ f hf
  obtain ⟨hbi, -⟩ := hf
  refine ⟨?_, ?_⟩
  · funext g
    unfold conv
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)]
    · have hmem : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (quotient_out_mem_iff_eq_one K _).mpr rfl
      have h1 : dosetInd k K 1 (QuotientGroup.mk 1 : G ⧸ K).out = 1 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).mpr hmem]
      simp only [h1, one_mul]
      have h2 := hbi ⟨_, K.inv_mem hmem⟩ 1 g
      simpa using h2
    · intro x hx
      have hn : x.out ∉ K := fun h => hx ((quotient_out_mem_iff_eq_one K x).mp h)
      have h0 : dosetInd k K 1 x.out = 0 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).not.mpr hn]
      simp only [h0, zero_mul]
  · funext g
    unfold conv
    rw [finsum_eq_single _ (QuotientGroup.mk g : G ⧸ K)]
    · have hq : (QuotientGroup.mk ((QuotientGroup.mk g : G ⧸ K).out) : G ⧸ K) = QuotientGroup.mk g := by
        first
          | exact QuotientGroup.out_eq' _
          | exact Quotient.out_eq _
      have hk : ((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * g ∈ K := QuotientGroup.eq.mp hq
      have h1 : dosetInd k K 1 (((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * g) = 1 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).mpr hk]
      simp only [h1, mul_one]
      have h2 := hbi 1 ⟨_, K.inv_mem hk⟩ g
      simpa using h2
    · intro x hx
      have hn : x.out⁻¹ * g ∉ K := by
        intro h
        apply hx
        have hq : (QuotientGroup.mk x.out : G ⧸ K) = QuotientGroup.mk g := QuotientGroup.eq.mpr h
        rw [← hq]
        first
          | exact (QuotientGroup.out_eq' x).symm
          | exact (Quotient.out_eq x).symm
      have h0 : dosetInd k K 1 (x.out⁻¹ * g) = 0 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).not.mpr hn]
      simp only [h0, mul_zero]
theorem HeckeActOne : Formalism.UG.HeckeActOne := by
  intro G _ Γ K k _ W _ _ ρ φ hφ
  funext g
  have hright : ∀ c : K, φ (g * c) = φ g := by
    intro c
    have h2 := hφ 1 g c
    simpa using h2
  unfold hAct
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)]
  · have hmem : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (quotient_out_mem_iff_eq_one K _).mpr rfl
    have h1 : dosetInd k K 1 (QuotientGroup.mk 1 : G ⧸ K).out = 1 := by
      simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).mpr hmem]
    simp only [h1, one_smul]
    exact hright ⟨_, hmem⟩
  · intro x hx
    have hn : x.out ∉ K := fun h => hx ((quotient_out_mem_iff_eq_one K x).mp h)
    have h0 : dosetInd k K 1 x.out = 0 := by
      simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).not.mpr hn]
    simp only [h0, zero_smul]
theorem HeckeBasis : Formalism.UG.HeckeBasis := by
  intro G _ K k _
  classical
  have hout : ∀ f ∈ Hecke k K, ∀ g : G, (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = f g := by
    intro f hf g
    obtain ⟨hbi, -⟩ := hf
    obtain ⟨h, hh, c, hc, he⟩ :=
      (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).mp (Quotient.out_eq _).symm
    rw [he]
    exact hbi ⟨h, hh⟩ ⟨c, hc⟩ g
  have hfin : ∀ f : Hecke k K, (Function.support fun c : ClassSet K K => (f : G → k) (Quotient.out c)).Finite := by
    intro f
    obtain ⟨-, S, hS⟩ := f.2
    apply (S.finite_toSet.image (DoubleCoset.mk K K)).subset
    intro c hc
    obtain ⟨s, hs, a, b, he⟩ := hS _ hc
    refine ⟨s, hs, ?_⟩
    have h1 : DoubleCoset.mk K K s = DoubleCoset.mk K K (Quotient.out c) :=
      (DoubleCoset.eq K K s _).mpr ⟨a, a.2, b, b.2, he⟩
    rw [h1]
    exact Quotient.out_eq c
  have hinv : ∀ φ : ClassSet K K →₀ k, (fun g => φ (DoubleCoset.mk K K g)) ∈ Hecke k K := by
    intro φ
    show (∀ a b : K, ∀ g : G, φ (DoubleCoset.mk K K ((a : G) * g * b)) = φ (DoubleCoset.mk K K g)) ∧
      ∃ S : Finset G, ∀ g : G, φ (DoubleCoset.mk K K g) ≠ 0 → ∃ s ∈ S, ∃ a b : K, g = (a : G) * s * b
    refine ⟨fun a b g => ?_, ⟨φ.support.image Quotient.out, fun g hg => ?_⟩⟩
    · congr 1
      exact ((DoubleCoset.eq K K g _).mpr ⟨a, a.2, b, b.2, rfl⟩).symm
    · refine ⟨Quotient.out (DoubleCoset.mk K K g),
        Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hg), ?_⟩
      obtain ⟨h, hh, c, hc, he⟩ :=
        (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).mp (Quotient.out_eq _).symm
      refine ⟨⟨h⁻¹, K.inv_mem hh⟩, ⟨c⁻¹, K.inv_mem hc⟩, ?_⟩
      rw [he]
      group
  refine ⟨{ toFun := fun f => Finsupp.ofSupportFinite (fun c => (f : G → k) (Quotient.out c)) (hfin f)
            map_add' := ?_
            map_smul' := ?_
            invFun := fun φ => ⟨fun g => φ (DoubleCoset.mk K K g), hinv φ⟩
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro f₁ f₂
    ext c
    simp [Finsupp.ofSupportFinite_coe]
  · intro r f
    ext c
    simp [Finsupp.ofSupportFinite_coe]
  · intro f
    apply Subtype.ext
    funext g
    show (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = (f : G → k) g
    exact hout f f.2 g
  · intro φ
    ext c
    show φ (DoubleCoset.mk K K (Quotient.out c)) = φ c
    rw [show DoubleCoset.mk K K (Quotient.out c) = c from Quotient.out_eq c]
  · intro f g
    show (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = (f : G → k) g
    exact hout f f.2 g
private theorem Tj_eq_dosetInd_diagJ {L : Type} [Field L] (O : Subring L) (ϖ : L) (k : Type) [CommRing k]
    (n j : ℕ) (d : GL (Fin n) L) (hd : (d : Matrix (Fin n) (Fin n) L) = diagJ n ϖ j) :
    Tj k n O ϖ j = dosetInd k (GLint (Fin n) O) d := by
  unfold Tj dosetInd
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, Units.ext (by simp [h, hd])⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by simp [hd]⟩

theorem TjMem : Formalism.UG.TjMem := by
  intro L _ O ϖ k _ n j hϖ
  have hdet : (diagJ n ϖ j).det ≠ 0 := by
    simp only [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by split_ifs <;> simp [hϖ]
  rw [Tj_eq_dosetInd_diagJ O ϖ k n j (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) rfl]
  exact Formalism.UG.Final.DosetIndMem _ _ k _
theorem InclInj : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  have hinj : Function.Injective (inclE (F := F) (E := E) R) := by
    first
      | exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F R).injective
      | exact Algebra.TensorProduct.includeLeft_injective (R := F) (A := E) (B := R) (algebraMap F R).injective
  intro g h hgh
  apply Units.ext
  ext i j
  apply hinj
  exact congrArg (fun u : GL n (TensorProduct F E R) => (u : Matrix n n (TensorProduct F E R)) i j) hgh
theorem SigExists : Formalism.UG.SigExists := Formalism.UG.P.signature_exists
theorem SigConj : Formalism.UG.SigConj := by
  intro n _ _ J p q e P hP g
  have hmul : ∀ A B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      cT (starRingEnd ℂ) (A * B) = cT (starRingEnd ℂ) B * cT (starRingEnd ℂ) A := by
    intro A B
    ext i j
    simp [cT, Matrix.mul_apply, mul_comm]
  have hone : cT (starRingEnd ℂ) (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    simp only [cT]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hPPi : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := Units.mul_inv P
  have hCiC : cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← hmul, hPPi, hone]
  show cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = J.reindex e e ↔
    cT (starRingEnd ℂ) ((P⁻¹ * g * P : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q *
      ((P⁻¹ * g * P : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q
  rw [← hP]
  simp only [Units.val_mul, hmul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) (cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)),
    hCiC, Matrix.one_mul, ← Matrix.mul_assoc (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), hPPi, Matrix.one_mul]
  constructor
  · intro h
    have h2 := congrArg (fun Z => cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (Z * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) h
    simpa only [Matrix.mul_assoc] using h2
  · intro h
    have h2 := congrArg (fun Z => cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Z *
      ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) h
    simp only [← Matrix.mul_assoc, hCiC, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, hPPi, Matrix.mul_one] at h2
    exact h2
theorem SphericalExists : Formalism.UG.SphericalExists := Formalism.UG.P.exists_spherical_function
theorem SplitIso : Formalism.UG.SplitIso := Formalism.UG.P.split_unitary_group_iso
theorem StabFinite : Formalism.UG.StabFinite := Formalism.UG.P.UG_stabilizer_finite
theorem StabStd : Formalism.UG.StabStd := by
  intro A R _ _ _ n _ _ hι
  have hL : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, ∃ r : R, algebraMap R A r = x i := by
    intro x
    simp [stdLat, Submodule.mem_pi]
  have hfwd : ∀ g0 : GL n R, ∀ x : n → A, x ∈ stdLat (n := n) (A := A) R →
      Matrix.mulVec ((bc (algebraMap R A) g0 : GL n A) : Matrix n n A) x ∈ stdLat (n := n) (A := A) R := by
    intro g0 x hx
    rw [hL] at hx ⊢
    choose r hr using hx
    intro i
    refine ⟨∑ j, (g0 : Matrix n n R) i j * r j, ?_⟩
    simp [Matrix.mulVec, dotProduct, bc, hr]
  apply le_antisymm
  · intro g hg
    have hginv : g⁻¹ ∈ stabGL (stdLat (n := n) (A := A) R) := (stabGL _).inv_mem hg
    have hcol : ∀ h : GL n A, h ∈ stabGL (stdLat (n := n) (A := A) R) →
        ∀ i j, ∃ r : R, algebraMap R A r = (h : Matrix n n A) i j := by
      intro h hh i j
      have he : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
        rw [hL]
        intro k
        by_cases hk : k = j
        · subst hk
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [hk]⟩
      have h2 := (hh _).1 he
      rw [hL] at h2
      obtain ⟨r, hr⟩ := h2 i
      refine ⟨r, ?_⟩
      rw [hr]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    choose M hM using hcol g hg
    choose N hN using hcol g⁻¹ hginv
    have hinj : ∀ X Y : Matrix n n R, X.map (algebraMap R A) = Y.map (algebraMap R A) → X = Y := by
      intro X Y hXY
      ext i j
      exact hι (congrFun (congrFun hXY i) j)
    have hMg : (Matrix.of M).map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j
      simp [hM]
    have hNg : (Matrix.of N).map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      simp [hN]
    refine MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, hinj _ _ ?_, hinj _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hMg, hNg, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hMg, hNg, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · apply Units.ext
      exact hMg
  · intro g hg
    obtain ⟨g0, rfl⟩ := MonoidHom.mem_range.mp hg
    intro x
    constructor
    · exact hfwd g0 x
    · intro hx
      have h2 := hfwd g0⁻¹ _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul] at h2
      simpa using h2
theorem DefSig : Formalism.UG.DefSig := Formalism.UG.P.definite_form_signature
theorem StdFormDef : Formalism.UG.StdFormDef := Formalism.UG.P.standard_hermitian_form_definite
theorem TjCosets : Formalism.UG.TjCosets := Formalism.UG.P.Tj_double_coset_decomposition
theorem TjEq : Formalism.UG.TjEq := by
  intro L _ O ϖ k _ n j d hd
  exact Tj_eq_dosetInd_diagJ O ϖ k n j d hd
theorem TjIndep : Formalism.UG.TjIndep := by
  intro L _ O ϖ u k _ n j hu hu' hu0
  let d : Fin n → O := fun i => if (i : ℕ) < j then ⟨u, hu⟩ else 1
  let d' : Fin n → O := fun i => if (i : ℕ) < j then ⟨u⁻¹, hu'⟩ else 1
  have hdd : ∀ i, d i * d' i = 1 := by
    intro i
    simp only [d, d']
    split_ifs
    · exact Subtype.ext (mul_inv_cancel₀ hu0)
    · exact mul_one 1
  have hd'd : ∀ i, d' i * d i = 1 := fun i => by rw [mul_comm]; exact hdd i
  let D0 : GL (Fin n) O := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hdd]; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd'd]; exact Matrix.diagonal_one⟩
  let Dg : GL (Fin n) L := bc O.subtype D0
  have hD : (Dg : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then u else 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha : (a : ℕ) < j <;> simp [Dg, D0, d, bc, ha]
    · simp [Dg, D0, bc, hab]
  have hdiag : diagJ n (u * ϖ) j = diagJ n ϖ j * (Dg : Matrix (Fin n) (Fin n) L) := by
    rw [hD]
    simp only [diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> ring
  have hDmem : Dg ∈ GLint (Fin n) O := MonoidHom.mem_range.mpr ⟨D0, rfl⟩
  unfold Tj
  congr 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, Dg * b, (GLint (Fin n) O).mul_mem hDmem hb, ?_⟩
    rw [h, hdiag, Units.val_mul]
    simp only [Matrix.mul_assoc]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, Dg⁻¹ * b, (GLint (Fin n) O).mul_mem ((GLint (Fin n) O).inv_mem hDmem) hb, ?_⟩
    rw [h, hdiag, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Dg : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
theorem UJTransport : Formalism.UG.UJTransport := by
  intro A B _ _ n _ _ σ σ' φ hφ J
  have hmem : ∀ g : GL n A, g ∈ UJ σ J → bc (φ : A →+* B) g ∈ UJ σ' (J.map φ) :=
    fun g hg => Formalism.UG.Final.BCMem A B n σ σ' (φ : A →+* B) hφ J g hg
  have hψ : ((φ.symm : B ≃+* A) : B →+* A).comp σ' = σ.comp ((φ.symm : B ≃+* A) : B →+* A) := by
    apply RingHom.ext
    intro b
    apply φ.injective
    have h1 := RingHom.congr_fun hφ (φ.symm b)
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 ⊢
    rw [h1]
  have hmem' : ∀ h : GL n B, h ∈ UJ σ' (J.map φ) → bc ((φ.symm : B ≃+* A) : B →+* A) h ∈ UJ σ J := by
    intro h hh
    have := Formalism.UG.Final.BCMem B A n σ' σ ((φ.symm : B ≃+* A) : B →+* A) hψ (J.map φ) h hh
    have hJ : (J.map φ).map ((φ.symm : B ≃+* A) : B →+* A) = J := by
      ext i j
      simp
    rw [hJ] at this
    exact this
  refine ⟨{ toFun := fun g => ⟨bc (φ : A →+* B) g, hmem g g.2⟩
            invFun := fun h => ⟨bc ((φ.symm : B ≃+* A) : B →+* A) h, hmem' h h.2⟩
            left_inv := fun g => ?_
            right_inv := fun h => ?_
            map_mul' := fun g h => ?_ }, fun g => rfl⟩
  · apply Subtype.ext
    apply Units.ext
    ext i j
    simp [bc]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    simp [bc]
  · apply Subtype.ext
    simp
theorem SplitPts : Formalism.UG.SplitPts := Formalism.UG.P.split_group_points
theorem KpqSubgroupCompact : Formalism.UG.KpqSubgroupCompact := Formalism.UG.P.maximal_compact_subgroup_compact
theorem DwActMul : Formalism.UG.DwActMul := by
  intro R _ r n g h
  refine ⟨?_, ?_⟩
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [dwAct, Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, mul_inv_rev, Units.val_mul, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [dwAct, Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite MvPolynomial.C, ite_mul]
theorem WeylGLStableLocal : Formalism.UG.WeylGLStableLocal := Formalism.UG.P.weyl_module_GL_stable_local
theorem WeylGLStable : Formalism.UG.WeylGLStable := Formalism.UG.P.weyl_module_GL_stable

end Formalism.UG.Final
