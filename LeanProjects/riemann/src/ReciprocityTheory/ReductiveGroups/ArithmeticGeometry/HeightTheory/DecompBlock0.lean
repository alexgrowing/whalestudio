import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FracFieldPositiveRowsOmega
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable abbrev sub0 (x : Fin (d.N + 1) → K) : KTp K d.D d.N →ₐ[K] KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v)

set_option synthInstance.maxHeartbeats 400000 in

theorem finYX4 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI := d.algLE h c
    letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c))) := by
  letI := d.algLE h c
  letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
  letI := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    classical
    obtain ⟨e, -, -, hsp⟩ := hd.a4
    refine ⟨⟨Finset.univ.image (fun k : Fin d.del => algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))), ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨q, hq, p, hp⟩ := hsp (fun c' => if hc : c' = c then hc ▸ y else 0)
    have hpc : d.sH c q * y = ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      have h1 := hp c
      first
        | (simp only [dif_pos (rfl : c = c)] at h1; exact h1)
        | simpa using h1
    have hq0 := hq c
    have hKT : ∀ r : KTp K d.D d.N, d.KTtoS h c (algebraMap _ _ r) = d.sH c r := fun r => by
      simp [Data.KTtoS]
    have hy : y = ∑ k, (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (p k) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) •
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_div₀, hKT,
        div_mul_eq_mul_div, ← Finset.sum_div, ← hpc]
      first
        | exact (mul_div_cancel_left₀ y hq0).symm
        | field_simp
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact Module.Finite.of_equiv_equiv d.eLX4 (d.eEX4 c)
    (RingHom.ext fun q => (d.fieldEquiv_compat_liftY h c q).symm)

set_option synthInstance.maxHeartbeats 400000 in
theorem decomp_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ (L E : Type) (_ : Field L) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (eL : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (eE : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) E)),
      (∀ q : KTf K d.D d.N, eE (d.KTtoS h c q) = VariableBasisExtension.liftY (eL q)) ∧
      (∀ r : Ω c, ∃ e : E, eE (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap (MvPolynomial (Fin (d.N + 1)) E) (FractionRing (MvPolynomial (Fin (d.N + 1)) E))
          (MvPolynomial.C e)) ∧
      ∀ l : L, ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x P = P) ∧ (∀ x, d.sub0 x Q = Q) ∧
        eL.symm (algebraMap (MvPolynomial (Fin (d.N + 1)) L)
            (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (MvPolynomial.C l)) =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q := by
  letI := d.algLE h c
  refine ⟨d.FracFieldPositiveRowsBase, d.FracFieldPositiveRowsOmega c, inferInstance, inferInstance, inferInstance,
    FractionFieldVariableLift.finiteDimensional_of_liftY (σ := Fin (d.N + 1)) (d.finYX4 hd h c), d.eLX4, d.eEX4 c,
    fun q => d.fieldEquiv_compat_liftY h c q, fun r => ?_, fun l => ?_⟩
  · refine ⟨algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (MvPolynomial.C r), ?_⟩
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq, d.eEX4_algebraMap, FractionFieldVariableLift.hE_C]
    simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := d.PolyRingPositiveRowsBase) l
    have hfix : ∀ (x : Fin (d.N + 1) → K) (p : d.PolyRingPositiveRowsBase),
        d.sub0 x (MvPolynomial.rename Subtype.val p) = MvPolynomial.rename Subtype.val p := by
      intro x p
      have hc : (d.sub0 x).comp (MvPolynomial.rename (R := K)
          (Subtype.val : {v : TVar d.D d.N // v.1 ≠ 0} → TVar d.D d.N)) =
          MvPolynomial.rename Subtype.val := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [Data.sub0, v.2]
      exact AlgHom.congr_fun hc p
    refine ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.rename Subtype.val q, ?_,
      fun x => hfix x p, fun x => hfix x q, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hq
        (MvPolynomial.rename_injective _ Subtype.val_injective (h0.trans (map_zero _).symm))
    · rw [RingEquiv.symm_apply_eq, map_div₀ d.eLX4, d.eLX4_algebraMap, d.eLX4_algebraMap,
        FractionFieldVariableLift.hL_rename, FractionFieldVariableLift.hL_rename]
      simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
      exact map_div₀ ((algebraMap (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) _).comp MvPolynomial.C) _ _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
