import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataForms
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SizeWindowBrackets.JointCSlopeExists
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K]

theorem plEquiv_eq_plOf (w : HeightOneSpectrum (𝓞 K)) : plEquiv K w = Formalism.LFunctionChainParameters.LBrDiv.plOf w := rfl

theorem prW_eq_prBelow (w : HeightOneSpectrum (𝓞 K)) :
    prW w = Formalism.LFunctionChainParameters.LChain2.prBelow (plEquiv K w) := rfl

theorem eW_eq_ramE (w : HeightOneSpectrum (𝓞 K)) :
    (eW w : ℝ) = Formalism.LFunctionChainParameters.LChain2.ramE (plEquiv K w) := rfl

theorem eW_eq_eWL (w : HeightOneSpectrum (𝓞 K)) : eW w = Formalism.BasicNotions.eWL K w := rfl

theorem lW_eq_ell (w : HeightOneSpectrum (𝓞 K)) : lW w = Formalism.LFunctionChainParameters.slopeLatticeData.ell (plEquiv K w) := rfl

theorem lW_eq_lw (w : HeightOneSpectrum (𝓞 K)) : lW w = Formalism.LFunctionChainParameters.LBrDiv.lw w := rfl

theorem lW_mul_eW (w : HeightOneSpectrum (𝓞 K)) :
    lW w * (eW w : ℝ) = Formalism.LFunctionChainParameters.LChain2.lE (plEquiv K w) := rfl

theorem lW_eq_lw₂ (w : HeightOneSpectrum (𝓞 K)) : lW w = Formalism.BasicNotions.lw K w := rfl

theorem plEquiv_symm_eq_hs (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) :
    (plEquiv K).symm p = Formalism.L2.GlobalTheoryTheory.Arith.hs p := rfl

theorem hs_plEquiv (w : HeightOneSpectrum (𝓞 K)) : Formalism.L2.GlobalTheoryTheory.Arith.hs (plEquiv K w) = w := rfl

theorem prW_eq_pOf (w : HeightOneSpectrum (𝓞 K)) : prW w = Formalism.L2.GlobalTheoryTheory.Arith.pOf w := by
  unfold Formalism.L2.GlobalTheoryTheory.Arith.pOf
  have hdvd : ringChar (𝓞 K ⧸ w.asIdeal) ∣ prW w := by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_prW_mem w
  rcases (Nat.dvd_prime (prW_prime w)).1 hdvd with h | h
  · exfalso
    have : Nontrivial (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
    exact CharP.ringChar_ne_one h
  · exact h.symm

theorem prW_eq_resCharW (w : HeightOneSpectrum (𝓞 K)) : prW w = Formalism.BasicNotions.Examples₂.PlacesToy.resCharW w :=
  (eq_prW_of_mem w (Formalism.BasicNotions.Examples₂.PlacesToy.resCharW_prime w) (Formalism.BasicNotions.Examples₂.PlacesToy.resCharW_mem w)).symm

theorem owToK_eq_rlocToK (w : HeightOneSpectrum (𝓞 K)) :
    owToK w = Formalism.LFunctionChainParameters.LJC.rlocToK (plEquiv K w) := rfl

theorem owAlgebra_eq_rlocAlgebra (w : HeightOneSpectrum (𝓞 K)) :
    (owAlgebra w : Algebra (Ow w) K) = Formalism.LFunctionChainParameters.LJC.rlocAlgebra (plEquiv K w) := rfl

theorem owModule_eq_rlocModule (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V] :
    owModule w V = Formalism.LFunctionChainParameters.LJC.rlocModule (plEquiv K w) V := rfl

theorem rlocModule_eq_rlocModule (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) (V : Type) [AddCommGroup V] [Module K V] :
    Formalism.L2.Col.rlocModule V p = Formalism.LFunctionChainParameters.LJC.rlocModule p V := rfl

section Len
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem lenW_eq_lenAt (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A B = Formalism.LFunctionChainParameters.slopeLatticeData.lenAt (plEquiv K w) A B := by
  have h1 : Formalism.LFunctionChainParameters.slopeLatticeData.lenAt (plEquiv K w) A B = Formalism.LFunctionChainParameters.slopeLatticeData.lenAt (plEquiv K w) A (A ⊓ B) := by
    unfold Formalism.LFunctionChainParameters.slopeLatticeData.lenAt
    have : (A ⊓ B).comap A.subtype = B.comap A.subtype := by
      ext x; simp
    rw [this]
  rw [h1, ← lenW_inf]
  exact (@Formalism.LFunctionChainParameters.slopeLatticeData.length_at_span K V _ _ _ _ (plEquiv K w) (owModule w V) (owTowerO w V) A
    (A ⊓ B) inf_le_left).symm

theorem lenW_eq_lenLoc (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A B = Formalism.BasicNotions.DV.lenLoc w B A := lenW_eq_lenAt w A B

theorem scalW_symm_eq_locScal (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) (c : K) (L : Submodule (𝓞 K) V) :
    scalW ((plEquiv K).symm p) c L =
      @Formalism.LFunctionChainParameters.slopeLatticeData.locScal K V _ _ _ _ _ p (Formalism.L2.Col.rlocModule V p) c L :=
  scalW_eq_locScal _ c L

theorem lenW_symm_eq_lenAt (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V) :
    lenW ((plEquiv K).symm p) A B = Formalism.LFunctionChainParameters.slopeLatticeData.lenAt p A B := lenW_eq_lenAt _ A B

theorem lenW_ne_top (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (hA : A.FG) {d : 𝓞 K}
    (hd : d ≠ 0) (h : ∀ x ∈ A, d • x ∈ B) : lenW w A B ≠ ⊤ := by
  rw [lenW_eq_length]
  exact Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal A B hA (mem_nonZeroDivisors_of_ne_zero hd) h)

theorem lenW_eq_lenUW_mul (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (hA : A.FG) {d : 𝓞 K}
    (hd : d ≠ 0) (h : ∀ x ∈ A, d • x ∈ B) :
    ∃ n : ℕ, lenW w A B = n ∧ (n : ℚ) = lenUW w A B * (eW w : ℚ) := by
  refine ⟨(lenW w A B).toNat, (ENat.natCast_toNat (lenW_ne_top w hA hd h)).symm, (lenUW_mul_eW w A B).symm⟩

theorem unitRule_lenUW_real (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.BasicNotions.unitRule K w ((lenUW w A B : ℚ) : ℝ) = ((lenW w A B).toNat : ℝ) := by
  have h := lenUW_mul_eW w A B
  have h' : ((lenUW w A B : ℚ) : ℝ) * (eW w : ℝ) = ((lenW w A B).toNat : ℝ) := by exact_mod_cast h
  unfold Formalism.BasicNotions.unitRule
  rw [mul_comm]
  exact h'

theorem lenUW_eq_lenUnit (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenUW w A B =
      Formalism.BasicNotions.lenUnit (O := Ow w) (prW w) (atW w A ⧸ (atW w B).comap (atW w A).subtype) := by
  unfold lenUW Formalism.BasicNotions.lenUnit lenW
  rw [length_ow_quot_prW, ENat.toNat_natCast]

end Len

section Rec
variable [StarRing K]

theorem mem_intW_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ Formalism.BasicNotions.intW (Formalism.BasicNotions.Examples₂.placesOf K) w ↔ x ∈ (algebraMap (Ow w) K).range := by
  rw [mem_range_ow_iff]
  show (0 : WithTop ℤ) ≤ Formalism.BasicNotions.Examples₂.PlacesToy.valW w x ↔ _
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [Formalism.BasicNotions.Examples₂.PlacesToy.valW_of_ne w hx]
    have h0 : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg, ← WithZero.log_one,
      WithZero.log_le_log h0 one_ne_zero]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_locW_iff (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.BasicNotions.locW (Formalism.BasicNotions.Examples₂.placesOf K) w L ↔ x ∈ atW w L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      obtain ⟨r', hr'⟩ := (mem_intW_iff w r.1).1 r.2
      have : r • x = r' • x := by
        rw [ow_smul_def, hr']; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hr : algebraMap (Ow w) K r ∈ Formalism.BasicNotions.intW (Formalism.BasicNotions.Examples₂.placesOf K) w :=
        (mem_intW_iff w _).2 ⟨r, rfl⟩
      have : r • x = (⟨algebraMap (Ow w) K r, hr⟩ : Formalism.BasicNotions.intW (Formalism.BasicNotions.Examples₂.placesOf K) w) • x := rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx

end Rec

theorem mem_locW_D (D : Formalism.BasicNotions.D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V]
    [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V]
    (A : Submodule (𝓞 D.what₂.LL) V) (y : V) :
    y ∈ Formalism.BasicNotions.locW D.what₂.places w A ↔ y ∈ atW (D.plEq w) A := by
  rw [D.mem_locW_iff, mem_atW_iff]; rfl

theorem eW_D (D : Formalism.BasicNotions.D7) (w : D.what₂.places.Pl) : eW (D.plEq w) = D.what₂.places.ramIdx w :=
  (D.ram_eq w).symm

theorem prW_D (D : Formalism.BasicNotions.D7) (w : D.what₂.places.Pl) : prW (D.plEq w) = D.what₂.places.resChar w := by
  refine (eq_prW_of_mem _ (D.what₂.places.resChar_prime w) ?_).symm
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem unitRule_lenUW (D : Formalism.BasicNotions.D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V]
    [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V] (A B : Submodule (𝓞 D.what₂.LL) V) :
    Formalism.BasicNotions.Rows.unitRule D.what₂.places w (lenUW (D.plEq w) A B) =
      ((lenW (D.plEq w) A B).toNat : ℚ) := by
  unfold Formalism.BasicNotions.Rows.unitRule
  rw [← eW_D, mul_comm, lenUW_mul_eW]

open Formalism.BasicNotions (vAdd)

theorem valuation_ow_unit (w : HeightOneSpectrum (𝓞 K)) (u : (Ow w)ˣ) :
    w.valuation K (algebraMap (Ow w) K u) = 1 := by
  have h1 : w.valuation K (algebraMap (Ow w) K u) ≤ 1 := (mem_range_ow_iff w _).1 ⟨_, rfl⟩
  have h2 : w.valuation K (algebraMap (Ow w) K (u⁻¹ : (Ow w)ˣ)) ≤ 1 :=
    (mem_range_ow_iff w _).1 ⟨_, rfl⟩
  have h3 : w.valuation K (algebraMap (Ow w) K u) *
      w.valuation K (algebraMap (Ow w) K (u⁻¹ : (Ow w)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  apply le_antisymm h1
  calc (1 : WithZero (Multiplicative ℤ)) = w.valuation K (algebraMap (Ow w) K u) *
        w.valuation K (algebraMap (Ow w) K (u⁻¹ : (Ow w)ˣ)) := h3.symm
    _ ≤ w.valuation K (algebraMap (Ow w) K u) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

theorem vAdd_unifW {w : HeightOneSpectrum (𝓞 K)} {ϖ : 𝓞 K} (h : IsUnifW w ϖ) :
    vAdd w (algebraMap (𝓞 K) K ϖ) = 1 := by
  unfold Formalism.BasicNotions.vAdd
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have h0 : ϖ ≠ 0 := fun h' => h.2 (h' ▸ Ideal.zero_mem _)
  have hne : w.intValuation ϖ ≠ 0 := w.intValuation_ne_zero ϖ h0
  have h1 : w.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (w.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h.1)
  have h2 : ¬ w.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h' => h.2 ((w.intValuation_le_pow_iff_mem ϖ 2).1 h')
  rw [← WithZero.log_le_iff_le_exp hne] at h1 h2
  push_cast at h1 h2
  omega

theorem exists_emultiplicity_eq_vAdd (w : HeightOneSpectrum (𝓞 K)) {ϖ : Ow w} (hϖ : Irreducible ϖ)
    {r : Ow w} (hr : r ≠ 0) :
    ∃ n : ℕ, emultiplicity ϖ r = n ∧ vAdd w (algebraMap (Ow w) K r) = n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_, ?_⟩
  · rw [emultiplicity_eq_of_associated_right (associated_unit_mul_left (ϖ ^ n) (u : Ow w) u.isUnit),
      emultiplicity_pow_self_of_prime hϖ.prime]
  · obtain ⟨ϖ0, h0⟩ := exists_isUnifW w
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible (Ow w) h0.irreducible hϖ
    have hval : w.valuation K (algebraMap (Ow w) K ϖ) = w.valuation K (algebraMap (𝓞 K) K ϖ0) := by
      rw [← hv, map_mul, map_mul, valuation_ow_unit, mul_one, ← IsScalarTower.algebraMap_apply]
    have h1 := vAdd_unifW h0
    unfold Formalism.BasicNotions.vAdd at h1 ⊢
    rw [map_mul, map_mul, valuation_ow_unit, one_mul, map_pow, map_pow, hval, WithZero.log_pow,
      nsmul_eq_mul]
    have h2 : WithZero.log (w.valuation K (algebraMap (𝓞 K) K ϖ0)) = -1 := by omega
    rw [h2]
    ring

section Det
variable {V : Type} [AddCommGroup V] [Module K V]

theorem repr_coe (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] (S : Submodule (Ow w) V)
    (b : Module.Basis ι (Ow w) S) (bK : Module.Basis ι K V) (hb : ∀ i, bK i = (b i : V)) (s : S) (i : ι) :
    bK.repr (s : V) i = algebraMap (Ow w) K (b.repr s i) := by
  have h1 : (s : V) = ∑ j, algebraMap (Ow w) K (b.repr s j) • bK j := by
    conv_lhs => rw [← b.sum_repr s]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb]; rfl
  rw [h1, bK.repr_sum_self]

theorem length_quot_map (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule (Ow w) V) (b : Module.Basis ι (Ow w) S) (bK : Module.Basis ι K V)
    (hb : ∀ i, bK i = (b i : V)) (f : V →ₗ[K] V) (hf : S.map (f.restrictScalars (Ow w)) ≤ S)
    (hdet : LinearMap.det f ≠ 0) :
    ∃ n : ℕ, Module.length (Ow w) (S ⧸ (S.map (f.restrictScalars (Ow w))).comap S.subtype) = n ∧
      vAdd w (LinearMap.det f) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  let fS : S →ₗ[Ow w] S := (f.restrictScalars (Ow w)).restrict (fun x hx => hf ⟨x, hx, rfl⟩)
  let u : Matrix ι ι (Ow w) := LinearMap.toMatrix b b fS
  have hu : (algebraMap (Ow w) K).mapMatrix u = LinearMap.toMatrix bK bK f := by
    ext i j
    have h1 : u i j = b.repr (fS (b j)) i := LinearMap.toMatrix_apply b b fS i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h1, LinearMap.toMatrix_apply, hb,
      ← repr_coe w S b bK hb]
    rfl
  have hdu : algebraMap (Ow w) K u.det = LinearMap.det f := by
    rw [RingHom.map_det, hu, LinearMap.det_toMatrix]
  have hu0 : u.det ≠ 0 := fun h => hdet (by rw [← hdu, h, map_zero])
  obtain ⟨n, hn1, hn2⟩ := exists_emultiplicity_eq_vAdd w hϖ hu0
  refine ⟨n, ?_, by rw [← hdu]; exact hn2⟩
  rw [← hn1, ← Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.index_det ϖ hϖ u hu0]
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ b.equivFun ?_)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨b.equivFun ⟨z, hz⟩, ?_⟩
    have h1 : fS ⟨z, hz⟩ = x := Subtype.ext hzx
    have h2 := LinearMap.toMatrix_mulVec_repr b b fS ⟨z, hz⟩
    rw [h1] at h2
    exact h2
  · rintro ⟨z, rfl⟩
    refine ⟨fS (b.equivFun.symm z), ⟨_, (b.equivFun.symm z).2, rfl⟩, ?_⟩
    have h2 := LinearMap.toMatrix_mulVec_repr b b fS (b.equivFun.symm z)
    have h3 : (⇑(b.repr (b.equivFun.symm z)) : ι → Ow w) = z := b.equivFun.apply_symm_apply z
    rw [h3] at h2
    exact h2.symm

end Det

theorem length_map_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M)
    (X Y : Submodule R M) :
    Module.length R (X.map (e : M →ₗ[R] M) ⧸
      (Y.map (e : M →ₗ[R] M)).comap (X.map (e : M →ₗ[R] M)).subtype) =
    Module.length R (X ⧸ Y.comap X.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (e.submoduleMap X) ?_)).symm
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := hy
    have hxz : x = z := e.injective (hxy.trans hzy.symm)
    subst hxz
    exact ⟨⟨x, hx⟩, hz, Subtype.ext hxy⟩

section Local
variable {V : Type} [AddCommGroup V] [Module K V]

theorem lidx_local (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule (Ow w) V) (b : Module.Basis ι (Ow w) S) (bK : Module.Basis ι K V)
    (hb : ∀ i, bK i = (b i : V)) (γ : V ≃ₗ[K] V) (T : Submodule (Ow w) V)
    (hT : S.map ((γ : V →ₗ[K] V).restrictScalars (Ow w)) = T) :
    ((Module.length (Ow w) (S ⧸ (S ⊓ T).comap S.subtype)).toNat : ℤ) -
      ((Module.length (Ow w) (T ⧸ (S ⊓ T).comap T.subtype)).toNat : ℤ) =
      vAdd w (LinearMap.det (γ : V →ₗ[K] V)) := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis bK
  let G : Matrix ι ι K := LinearMap.toMatrix bK bK (γ : V →ₗ[K] V)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (Ow w))
    (Finset.univ.image (fun p : ι × ι => G p.1 p.2))
  have c0 : (c : Ow w) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  let cK : K := algebraMap (Ow w) K c
  have cK0 : cK ≠ 0 := fun h => c0 (algebraMap_ow_injective w (by rw [map_zero]; exact h))
  let f : V →ₗ[K] V := cK • (γ : V →ₗ[K] V)
  let g : V →ₗ[K] V := cK • (LinearMap.id : V →ₗ[K] V)
  have hfb : ∀ j, f (b j : V) ∈ S := by
    intro j
    have h1 : f (b j : V) = ∑ i, (cK * G i j) • bK i := by
      show cK • γ (b j : V) = _
      rw [← hb j, ← bK.sum_repr (γ (bK j)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hG : G i j = bK.repr (γ (bK j)) i := LinearMap.toMatrix_apply _ _ _ _ _
      rw [smul_smul, hG]
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hc (G i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2 : (cK * G i j) • bK i = r • (b i : V) := by
      rw [ow_smul_def, hr, Algebra.smul_def, hb]
    rw [h2]
    exact S.smul_mem r (b i).2
  have hf : S.map (f.restrictScalars (Ow w)) ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x = ∑ j, (b.repr ⟨x, hx⟩ j) • (b j : V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    show f x ∈ S
    rw [h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [LinearMap.map_smul_of_tower]
    exact S.smul_mem _ (hfb j)
  have hg : S.map (g.restrictScalars (Ow w)) ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact S.smul_mem (c : Ow w) hx
  have hdγ : LinearMap.det (γ : V →ₗ[K] V) ≠ 0 := (LinearEquiv.isUnit_det' γ).ne_zero
  have hdg : LinearMap.det g = cK ^ Module.finrank K V := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdg0 : LinearMap.det g ≠ 0 := by rw [hdg]; exact pow_ne_zero _ cK0
  have hdf : LinearMap.det f = LinearMap.det g * LinearMap.det (γ : V →ₗ[K] V) := by
    rw [hdg, LinearMap.det_smul]
  have hdf0 : LinearMap.det f ≠ 0 := by rw [hdf]; exact mul_ne_zero hdg0 hdγ
  obtain ⟨n1, hl1, hv1⟩ := length_quot_map w S b bK hb f hf hdf0
  obtain ⟨n2, hl2, hv2⟩ := length_quot_map w S b bK hb g hg hdg0
  have hv : vAdd w (LinearMap.det (γ : V →ₗ[K] V)) = (n1 : ℤ) - n2 := by
    rw [hdf, Formalism.BasicNotions.Examples₂.PlacesToy.vAdd_mul w hdg0 hdγ, hv2] at hv1
    omega
  let γR : V ≃ₗ[Ow w] V := γ.restrictScalars (Ow w)
  have hTγ : S.map (γR : V →ₗ[Ow w] V) = T := hT
  have hC : (S.map (g.restrictScalars (Ow w))).map (γR : V →ₗ[Ow w] V) =
      S.map (f.restrictScalars (Ow w)) := by
    rw [← Submodule.map_comp]
    congr 1
    ext x
    show γ (cK • x) = cK • γ x
    rw [map_smul]
  have hl3 : Module.length (Ow w) (T ⧸ (S.map (f.restrictScalars (Ow w))).comap T.subtype) = n2 := by
    rw [← hl2, ← length_map_equiv γR S (S.map (g.restrictScalars (Ow w))), hC]
    subst hT
    rfl
  have hCT : S.map (f.restrictScalars (Ow w)) ≤ T := by
    rw [← hC, ← hTγ]
    exact Submodule.map_mono hg
  have e1 := Formalism.HermitianLatticesTheory.indexBasic_len_add (S.map (f.restrictScalars (Ow w))) (S ⊓ T) S
    (le_inf hf hCT) inf_le_left
  have e2 := Formalism.HermitianLatticesTheory.indexBasic_len_add (S.map (f.restrictScalars (Ow w))) (S ⊓ T) T
    (le_inf hf hCT) inf_le_right
  rw [hl1] at e1
  rw [hl3] at e2
  have t1 : Module.length (Ow w) (↥(S ⊓ T) ⧸ (S.map (f.restrictScalars (Ow w))).comap (S ⊓ T).subtype) +
      Module.length (Ow w) (S ⧸ (S ⊓ T).comap S.subtype) ≠ ⊤ := by
    rw [← e1]; exact ENat.natCast_ne_top _
  have t2 : Module.length (Ow w) (↥(S ⊓ T) ⧸ (S.map (f.restrictScalars (Ow w))).comap (S ⊓ T).subtype) +
      Module.length (Ow w) (T ⧸ (S ⊓ T).comap T.subtype) ≠ ⊤ := by
    rw [← e2]; exact ENat.natCast_ne_top _
  obtain ⟨hx, ha⟩ := WithTop.add_ne_top.mp t1
  obtain ⟨-, ha'⟩ := WithTop.add_ne_top.mp t2
  have f1 := congrArg ENat.toNat e1
  have f2 := congrArg ENat.toNat e2
  rw [ENat.toNat_natCast, ENat.toNat_add hx ha] at f1
  rw [ENat.toNat_natCast, ENat.toNat_add hx ha'] at f2
  rw [hv]
  omega

end Local

section Main
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_basis_atW (w : HeightOneSpectrum (𝓞 K)) {A : Submodule (𝓞 K) V} (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι (Ow w) (atW w A)) (bK : Module.Basis ι K V),
      ∀ i, bK i = (b i : V) := by
  have := atW_finite w hfg
  have := atW_free w hfg
  let b := Module.Free.chooseBasis (Ow w) (atW w A)
  have hli : LinearIndependent (Ow w) (fun i => ((b i : atW w A) : V)) :=
    b.linearIndependent.map' (atW w A).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atW w A) : V)) :=
    (LinearIndependent.iff_fractionRing (Ow w) K).1 hli
  have hs : Submodule.span (Ow w) (Set.range fun i => ((b i : atW w A) : V)) = atW w A := by
    have h1 : (Set.range fun i => ((b i : atW w A) : V)) = (atW w A).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have key : ∀ S : Set V, Submodule.span (Ow w) S = atW w A → Submodule.span K S = ⊤ := fun S hS => by
    rw [← hsp, ← span_atW w A, ← hS, Submodule.span_span_of_tower]
  exact ⟨_, inferInstance, b, Module.Basis.mk hliK (key _ hs).ge, fun i => Module.Basis.mk_apply _ _ i⟩

theorem lidxW_eq_vAdd_det (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V)
    (hfg : A.FG) (hsp : Submodule.span K (A : Set V) = ⊤)
    (h : (atW w A).map ((γ : V →ₗ[K] V).restrictScalars (Ow w)) = atW w B) :
    lidxW w A B = vAdd w (LinearMap.det (γ : V →ₗ[K] V)) := by
  classical
  obtain ⟨ι, _, b, bK, hb⟩ := exists_basis_atW w hfg hsp
  rw [← lidx_local w (atW w A) b bK hb γ (atW w B) h]
  unfold lidxW lenW
  rw [atW_inf]

theorem lidxUW_eq_vAdd_det (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V)
    (hfg : A.FG) (hsp : Submodule.span K (A : Set V) = ⊤)
    (h : (atW w A).map ((γ : V →ₗ[K] V).restrictScalars (Ow w)) = atW w B) :
    lidxUW w A B = (vAdd w (LinearMap.det (γ : V →ₗ[K] V)) : ℚ) / (eW w : ℚ) := by
  unfold lidxUW
  rw [lidxW_eq_vAdd_det w A B γ hfg hsp h]

theorem bridge_lidx_det_holds : Formalism.BasicNotions.bridge_lidx_det := by
  intro K V _ _ _ _ _ _ _ w A B γ hA h
  rw [← lidxW_eq_lidx]
  refine lidxW_eq_vAdd_det w A B γ hA.fg hA.span_eq_top ?_
  rw [← atW_map]
  apply Submodule.restrictScalars_injective (𝓞 K)
  rw [atW_restrictScalars, atW_restrictScalars]
  exact h

end Main

end Formalism.L2.Col
