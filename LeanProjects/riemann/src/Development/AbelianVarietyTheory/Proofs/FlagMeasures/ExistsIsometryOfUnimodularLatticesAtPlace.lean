import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.HermitianLatticesTheory
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.GenusSelfDual GlobalTheory.LocalIsomAt

namespace GlobalTheory.Mass.UnimodLoc

section Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem exists_factor [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    {A N : Matrix (Fin n) (Fin n) E} (hA : ∀ a b, cc (A a b) = A b a)
    (h1 : ∀ i j, A i j ∈ semiLoc v) (h2 : ∀ i j, N i j ∈ semiLoc v) (hAN : A * N = 1) :
    ∃ P : GL (Fin n) (LocAlg v), P.1 ∈ (locOrder v).toSubring.matrix ∧
      (P⁻¹).1 ∈ (locOrder v).toSubring.matrix ∧ A.map (locEmb v) = P.1ᵀ * P.1.map (locConj v) :=
  exists_eq_transpose_mul_map_locConj v (N := N.map (locEmb v))
    (fun i j => (locEmb_mem_locOrder_iff v _).2 (h1 i j))
    (fun i j => (locEmb_mem_locOrder_iff v _).2 (h2 i j))
    (by rw [← Matrix.map_mul, hAN, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun i j => by
      change locConj v (locEmb v (A i j)) = locEmb v (A j i)
      rw [locConj_locEmb, hA])

theorem exists_unitary [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    {A N A' N' : Matrix (Fin n) (Fin n) E} (hA : ∀ a b, cc (A a b) = A b a) (hA' : ∀ a b, cc (A' a b) = A' b a)
    (h1 : ∀ i j, A i j ∈ semiLoc v) (h2 : ∀ i j, N i j ∈ semiLoc v) (hAN : A * N = 1)
    (h1' : ∀ i j, A' i j ∈ semiLoc v) (h2' : ∀ i j, N' i j ∈ semiLoc v) (hAN' : A' * N' = 1)
    (T : GL (Fin n) E) (hT : A' = T.1ᵀ * A * T.1.map cc) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᵀ * A * γ.map cc = A ∧ ∀ i j, ((T⁻¹).1 * γ) i j ∈ semiLoc v := by
  obtain ⟨P, hP, hPi, hPA⟩ := exists_factor v hA h1 h2 hAN
  obtain ⟨Q, hQ, hQi, hQA⟩ := exists_factor v hA' h1' h2' hAN'
  have hd : A.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hAN).ne_zero
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal :=
    ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)), Ideal.absNorm_mem _⟩
  let T' : GL (Fin n) (LocAlg v) := Matrix.GeneralLinearGroup.map (locEmb v) T
  have hT' : T'.1ᵀ * A.map (locEmb v) * T'.1.map (locConj v) = Q.1ᵀ * 1 * Q.1.map (locConj v) := by
    rw [Matrix.mul_one, ← hQA, hT, Matrix.map_mul, Matrix.map_mul]
    rfl
  let u : GL (Fin n) (LocAlg v) := T' * Q⁻¹ * P
  have hu : u.1ᵀ * A.map (locEmb v) * u.1.map (locConj v) = A.map (locEmb v) := by
    have e : (T' * Q⁻¹).1ᵀ * A.map (locEmb v) * (T' * Q⁻¹).1.map (locConj v) = 1 := by
      rw [Units.val_mul, UnramifiedHermitian.congr_mul, hT', ← UnramifiedHermitian.congr_mul, Units.mul_inv]
      simp
    rw [Units.val_mul, UnramifiedHermitian.congr_mul, e, Matrix.mul_one, ← hPA]
  haveI : IsArtinianRing (LocAlg v) := IsArtinianRing.of_finite (v.adicCompletion (maximalRealSubfield E)) _
  obtain ⟨lam, hlam, hlu⟩ := (infinite_norm_one E).exists_notMem_finite
    (finite_not_isUnit_one_add_smul (locEmb v) u.1)
  obtain ⟨γ, hγ, hγX⟩ := exists_unitary_congr_pi (T := Unit) (A := fun _ => LocAlg v) (fun _ => locEmb v)
    (IsCMField.complexConj E : E →+* E) (fun _ => locConj v) (fun _ => locConj_locEmb v)
    (IsCMField.complexConj_apply_apply E) (fun _ => locConj_locConj v) A
    (Matrix.ext fun a b => hA b a) hd (fun _ => (locOrder v).toSubring) (fun _ z => locConj_mem v)
    (fun z => by
      obtain ⟨x, hx⟩ := exists_sub_mem_locOrder ({v} : Finset _)
        (fun w => (Finset.mem_singleton.1 w.2).symm ▸ z ())
      exact ⟨x, fun _ => hx ⟨v, Finset.mem_singleton_self v⟩⟩)
    (fun x => by
      obtain ⟨k, s, hk, hx⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic x)).exists_nsmul_eq (𝓞 E)
      exact ⟨k, Nat.pos_of_ne_zero hk, fun _ => by rw [← map_nsmul, hx]; exact locEmb_mem_locOrder v s⟩)
    p hp0 (fun _ => exists_inv_one_add v hp) (fun _ => u) (fun _ => T') (fun _ => hu) lam hlam
    (fun _ => not_not.1 hlu)
  refine ⟨γ, hγ, fun i j => (locEmb_mem_locOrder_iff v _).1 ?_⟩
  have h3 : (T'⁻¹).1 * (γ.map (locEmb v) * (u⁻¹).1) * T'.1 ∈ (locOrder v).toSubring.matrix := hγX ()
  have h4 := mul_mem (mul_mem h3 hQi) hP
  have e : (T'⁻¹).1 * (γ.map (locEmb v) * (u⁻¹).1) * T'.1 * (Q⁻¹).1 * P.1 = ((T⁻¹).1 * γ).map (locEmb v) := by
    have e1 : (u⁻¹).1 * (T'.1 * (Q⁻¹).1 * P.1) = 1 := Units.inv_mul u
    have e2 : (T'⁻¹).1 = (T⁻¹).1.map (locEmb v) := rfl
    rw [Matrix.map_mul, ← e2]
    calc _ = (T'⁻¹).1 * γ.map (locEmb v) * ((u⁻¹).1 * (T'.1 * (Q⁻¹).1 * P.1)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.mul_one]
  rw [e] at h4
  exact h4 i j

end Mat

section Lat

variable {K V : Type} [Field K] [NumberField K] [IsCMField K] [StarRing K] (hst : ∀ x : K, star x = cc x)
  (v : HeightOneSpectrum (𝓞 (maximalRealSubfield K))) {P : Ideal (𝓞 K)} (hP : P.IsPrime)
  (hPv : P.comap (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = v.asIdeal)

include hst hP hPv

theorem mem_loc_iff {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ loc (K := K) P L ↔ ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) s • x ∈ L := by
  constructor
  · rintro ⟨s, hs, hx⟩
    have key : ∀ s ∈ hcompl (K := K) P, s ∉ P ∧ IsCMField.ringOfIntegersComplexConj K s ∉ P := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem s h => exact ⟨h.1, h.2 _ (hst _).symm⟩
      | one => rw [map_one, and_self]; exact (Ideal.ne_top_iff_one _).1 hP.ne_top
      | mul a b _ _ ha hb =>
        rw [map_mul]
        exact ⟨fun h => (hP.mem_or_mem h).elim ha.1 hb.1, fun h => (hP.mem_or_mem h).elim ha.2 hb.2⟩
    obtain ⟨m, hm⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff K
      (IsCMField.ringOfIntegersComplexConj K s * s)).1 (by ext; simp [mul_comm])
    refine ⟨m, ?_, ?_⟩
    · rw [← hPv, Ideal.mem_comap, hm]
      exact fun h => (hP.mem_or_mem h).elim (key s hs).2 (key s hs).1
    · rw [hm, mul_smul]
      exact L.smul_mem _ hx
  · rintro ⟨s, hs, hx⟩
    rw [← hPv, Ideal.mem_comap] at hs
    refine ⟨_, Submonoid.subset_closure ⟨hs, fun t ht => ?_⟩, hx⟩
    have : t = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) s :=
      RingOfIntegers.ext (ht.trans ((hst _).trans (cc_algebraMap s)))
    rwa [this]

theorem mem_locR_iff (z : K) : z ∈ locR (K := K) P ↔ z ∈ semiLoc v := by
  rw [locR, mem_loc_iff hst v hP hPv, mem_semiLoc_iff]
  simp only [GlobalTheory.LocalLattice.mem_one_ringOfIntegers_iff]
  rfl

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_basis (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ x, x ∈ loc (K := K) P L ↔ ∀ i, b.repr x i ∈ semiLoc v := by
  let e := (Module.finBasis K V).equivFun
  let L₀ : Submodule (𝓞 K) (Fin (Module.finrank K V) → K) := L.map (e.toLinearMap.restrictScalars (𝓞 K))
  have hL₀ : ReciprocityTheory.MultiplicativeHeights.IsLattice L₀ := by
    refine ⟨hL.fg.map _, ?_⟩
    have : (L₀ : Set _) = e.toLinearMap '' (L : Set V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨g, hg⟩ := exists_frame v hL₀
  refine ⟨Module.Basis.ofEquivFun (e.trans (Matrix.toLin'OfInv (Units.mul_inv g) (Units.inv_mul g))), fun x => ?_⟩
  rw [mem_loc_iff hst v hP hPv]
  refine Iff.trans ?_ (hg (e x))
  refine exists_congr fun s => and_congr_right fun _ => ⟨fun h => ⟨_, h, ?_⟩, ?_⟩
  · exact map_smul (e.toLinearMap.restrictScalars (𝓞 K)) _ _
  · rintro ⟨y, hy, h⟩
    have := e.injective (h.trans (map_smul (e.toLinearMap.restrictScalars (𝓞 K)) _ x).symm)
    exact this ▸ hy

omit hP hPv [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem form_eq (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : V) :
    h y x = herm (Matrix.of fun i j => h (b j) (b i)) (b.equivFun x) (b.equivFun y) := by
  conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y]
  simp only [herm, map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, Matrix.of_apply, Finset.mul_sum, starRingEnd_apply, hst]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit hst hP hPv [IsCMField K] [FiniteDimensional K V] in
theorem mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ dualAt h P L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) P := by
  simp [dualAt, Submodule.mem_iInf]

omit [FiniteDimensional K V] in
theorem gram (h : V →ₗ⋆[K] V →ₗ[K] K) (hn : h.Nondegenerate) {n : ℕ} (b : Module.Basis (Fin n) K V)
    (L : Submodule (𝓞 K) V) (hb : ∀ x, x ∈ loc (K := K) P L ↔ ∀ i, b.repr x i ∈ semiLoc v)
    (hu : IsUnimodularAt h P L) :
    (∀ i j, h (b j) (b i) ∈ semiLoc v) ∧ ∃ N : Matrix (Fin n) (Fin n) K, (∀ i j, N i j ∈ semiLoc v) ∧
      (Matrix.of fun i j => h (b j) (b i)) * N = 1 := by
  have hm : ∀ x, x ∈ loc (K := K) P L ↔ ∀ y ∈ loc (K := K) P L, h y x ∈ semiLoc v := fun x => by
    conv_lhs => rw [← hu, mem_dualAt]
    simp only [mem_locR_iff hst v hP hPv]
  have hbi : ∀ i, b i ∈ loc (K := K) P L := fun i => (hb _).2 fun j => by
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => (hm _).1 (hbi i) _ (hbi j), ?_⟩
  set A : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => h (b j) (b i) with hA
  have hd : A.det ≠ 0 := fun h0 => by
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    refine hc0 (b.equivFun.symm.map_eq_zero_iff.1 (hn.2 _ fun y => ?_))
    rw [form_eq hst h b, ← hA, LinearEquiv.apply_symm_apply, herm_eq_dotProduct, hc, zero_dotProduct]
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv _ hd.isUnit⟩
  have := (hb _).1 ((hm (b.equivFun.symm (Pi.single i 1 ᵥ* A⁻¹))).2 fun y hy => by
    rw [form_eq hst h b, ← hA, LinearEquiv.apply_symm_apply, herm_eq_dotProduct, Matrix.vecMul_vecMul,
      Matrix.nonsing_inv_mul _ hd.isUnit, Matrix.vecMul_one, single_dotProduct, one_mul]
    exact cc_mem_semiLoc v ((hb y).1 hy i)) j
  rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  simpa using this

theorem exists_isom [Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K)]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate) (L L' : Submodule (𝓞 K) V)
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L')
    (hu : IsUnimodularAt h P L) (hu' : IsUnimodularAt h P L') :
    ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  obtain ⟨b, hb⟩ := exists_basis hst v hP hPv L hL
  obtain ⟨b', hb'⟩ := exists_basis hst v hP hPv L' hL'
  obtain ⟨h1, N, h2, hN⟩ := gram hst v hP hPv h hn b L hb hu
  obtain ⟨h1', N', h2', hN'⟩ := gram hst v hP hPv h hn b' L' hb' hu'
  let T : GL (Fin (Module.finrank K V)) K :=
    ⟨b.toMatrix b', b'.toMatrix b, b.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip b⟩
  obtain ⟨γ, hγ, hγT⟩ := exists_unitary v (A := Matrix.of fun i j => h (b j) (b i))
    (A' := Matrix.of fun i j => h (b' j) (b' i)) (fun i j => (hst _).symm.trans (hs.eq _ _))
    (fun i j => (hst _).symm.trans (hs.eq _ _)) h1 h2 hN h1' h2' hN' T (by
      ext i j
      rw [← Published.herm_col, Matrix.of_apply, form_eq hst h b]
      rfl)
  have hγd : γ.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hγ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact (Matrix.isUnit_det_of_right_inverse hN).ne_zero this.symm
  let g : V ≃ₗ[K] V := (b.equivFun.trans
    (Matrix.toLinearEquiv' γ (Matrix.invertibleOfIsUnitDet γ hγd.isUnit))).trans b.equivFun.symm
  have hg : ∀ x, b.equivFun (g x) = γ *ᵥ b.equivFun x := fun x => b.equivFun.apply_symm_apply _
  have hgi : ∀ x y, h (g x) (g y) = h x y := fun x y => by
    rw [form_eq hst h b, form_eq hst h b y x, hg, hg, herm_mulVec, hγ]
  have hle : ∀ x ∈ loc (K := K) P L, g x ∈ loc (K := K) P L' := fun x hx => (hb' _).2 fun i => by
    have e : b'.repr (g x) i = ((b'.toMatrix b * γ) *ᵥ b.equivFun x) i := by
      rw [← Matrix.mulVec_mulVec, ← hg]
      exact (congrFun (b.toMatrix_mulVec_repr b' (g x)) i).symm
    rw [e, Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hγT i j) ((hb x).1 hx j)
  refine ⟨g, hgi, le_antisymm ?_ fun z hz => ⟨g.symm z, ?_, g.apply_symm_apply z⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  · rw [← hu, SetLike.mem_coe, mem_dualAt]
    intro y hy
    rw [← hgi, g.apply_symm_apply]
    rw [← hu', mem_dualAt] at hz
    exact hz _ (hle y hy)

end Lat

theorem exists_isom_of_isUnimodularAt : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L L' : Submodule (𝓞 K) V), Submodule.IsLattice K L → Submodule.IsLattice K L' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P L → IsUnimodularAt h P L' → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  intro K V _ _ _ _ _ _ _ _ h hc hs hn L L' hL hL' P hP hu hu'
  obtain ⟨_, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff K star).1 ⟨hc.2.1, by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 P hP
    refine ⟨algebraMap (𝓞 K) K θ, fun e => e2 ?_⟩
    rw [show t = θ from RingOfIntegers.ext (e1.trans e), sub_self]
    exact zero_mem _⟩
  have hst' : ∀ x : K, star x = cc x := congrFun hst
  haveI := Formalism.L2.Pj.unramBridge_holds K fun Q hQ => by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 Q hQ
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ = t :=
      RingOfIntegers.ext (e1.trans (hst' _)).symm
    rwa [this]
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  exact exists_isom hst' (w.under (𝓞 (maximalRealSubfield K))) hP.isPrime rfl h hs hn L L' hL hL' hu hu'

end GlobalTheory.Mass.UnimodLoc
