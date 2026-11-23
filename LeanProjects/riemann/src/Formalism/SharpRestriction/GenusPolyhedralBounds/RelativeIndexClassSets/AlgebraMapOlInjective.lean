import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference
import Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev Idx (D : D7) (j N : ℕ) : Type := Fin (WeightFamilies.dimY D j + 1) × Fin N

abbrev Pol (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Type :=
  MvPolynomial (Idx D j N) (X.Ol la)

abbrev gI (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Ideal (Pol X la N) :=
  Formalism.DV.gaussIdeal (Idx D j N) (X.Ol la)

instance gI_isPrime (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : (gI X la N).IsPrime :=
  Formalism.DV.GaussP.gaussIdeal_isPrime _ _

def Op (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Type :=
  Localization.AtPrime (gI X la N)

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

instance Op.commRing : CommRing (Op X la N) := inferInstanceAs (CommRing (Localization.AtPrime (gI X la N)))
instance Op.isDomain : IsDomain (Op X la N) := Formalism.DV.GaussP.isDomain_A _ _
instance Op.isDVR : IsDiscreteValuationRing (Op X la N) := Formalism.DV.GaussP.isDVR _ _
instance Op.algPol : Algebra (Pol X la N) (Op X la N) :=
  inferInstanceAs (Algebra (Pol X la N) (Localization.AtPrime (gI X la N)))
instance Op.isLoc : IsLocalization.AtPrime (Op X la N) (gI X la N) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (gI X la N)) (gI X la N))
instance Op.algOl : Algebra (X.Ol la) (Op X la N) :=
  inferInstanceAs (Algebra (X.Ol la) (Localization.AtPrime (gI X la N)))
instance Op.towPol : IsScalarTower (X.Ol la) (Pol X la N) (Op X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Pol X la N) (Localization.AtPrime (gI X la N)))
instance Op.isLocalHom : IsLocalHom (algebraMap (X.Ol la) (Op X la N)) := Formalism.DV.GaussP.isLocalHom_A _ _
instance Op.flat : Module.Flat (X.Ol la) (Op X la N) := Formalism.DV.GaussP.flat_A _ _

theorem Op.algebraMap_injective : Function.Injective (algebraMap (X.Ol la) (Op X la N)) :=
  Formalism.DV.GaussP.algebraMap_injective _ _

theorem Op.maximalIdeal_eq : IsLocalRing.maximalIdeal (Op X la N) =
    Ideal.map (algebraMap (X.Ol la) (Op X la N)) (IsLocalRing.maximalIdeal (X.Ol la)) :=
  Formalism.DV.GaussP.maximalIdeal_eq _ _

theorem Op.irreducible_map {ϖ : X.Ol la} (h : Irreducible ϖ) :
    Irreducible (algebraMap (X.Ol la) (Op X la N) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, Op.maximalIdeal_eq, h.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

def Kp : Type := FractionRing (Op X la N)

instance Kp.field : Field (Kp X la N) := inferInstanceAs (Field (FractionRing (Op X la N)))
instance Kp.algOp : Algebra (Op X la N) (Kp X la N) :=
  inferInstanceAs (Algebra (Op X la N) (FractionRing (Op X la N)))
instance Kp.isFrac : IsFractionRing (Op X la N) (Kp X la N) :=
  inferInstanceAs (IsFractionRing (Op X la N) (FractionRing (Op X la N)))
instance Kp.torsionFreeOp : Module.IsTorsionFree (Op X la N) (Kp X la N) := inferInstance
instance Kp.algOl : Algebra (X.Ol la) (Kp X la N) :=
  ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (X.Ol la) (Op X la N))).toAlgebra
instance Kp.towOp : IsScalarTower (X.Ol la) (Op X la N) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem Kp.algebraMap_Ol_injective : Function.Injective (algebraMap (X.Ol la) (Kp X la N)) :=
  (IsFractionRing.injective (Op X la N) (Kp X la N)).comp (Op.algebraMap_injective X la N)

instance Kp.algKl : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la) (Kp.algebraMap_Ol_injective X la N)).toAlgebra
instance Kp.towKl : IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (A := X.Ol la) (K := X.Kl la) (Kp.algebraMap_Ol_injective X la N) x).symm

def Rp : Type := Kp X la N ⊗[X.Kl la] X.Vl la

instance Rp.commRing : CommRing (Rp X la N) := inferInstanceAs (CommRing (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algKp : Algebra (Kp X la N) (Rp X la N) :=
  inferInstanceAs (Algebra (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algOp : Algebra (Op X la N) (Rp X la N) :=
  inferInstanceAs (Algebra (Op X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOp : IsScalarTower (Op X la N) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (Op X la N) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algKl : Algebra (X.Kl la) (Rp X la N) :=
  inferInstanceAs (Algebra (X.Kl la) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towKl : IsScalarTower (X.Kl la) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Kl la) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algOl : Algebra (X.Ol la) (Rp X la N) :=
  inferInstanceAs (Algebra (X.Ol la) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlKp : IsScalarTower (X.Ol la) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlOp : IsScalarTower (X.Ol la) (Op X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Op X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlKl : IsScalarTower (X.Ol la) (X.Kl la) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N ⊗[X.Kl la] X.Vl la))

instance Rp.torsionFreeOp : Module.IsTorsionFree (Op X la N) (Rp X la N) where
  isSMulRegular r hr := by
    have h0 : algebraMap (Op X la N) (Kp X la N) r ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact hr.ne_zero
    intro x y hxy
    simp only [← algebraMap_smul (Kp X la N) r] at hxy
    exact smul_right_injective _ h0 hxy

def bcV : X.Vl la →ₐ[X.Kl la] Rp X la N :=
  (Algebra.TensorProduct.includeRight : X.Vl la →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] X.Vl la)

theorem bcV_apply (v : X.Vl la) : bcV X la N v = ((1 : Kp X la N) ⊗ₜ[X.Kl la] v : Kp X la N ⊗[X.Kl la] X.Vl la) := rfl

theorem bcV_isBaseChange : IsBaseChange (Kp X la N) (bcV X la N).toLinearMap :=
  TensorProduct.isBaseChange (X.Kl la) (X.Vl la) (Kp X la N)

def emb : X.Forms →+* Rp X la N :=
  (bcV X la N).toRingHom.comp (Algebra.TensorProduct.includeRight : X.Forms →ₐ[B.KO] X.Kl la ⊗[B.KO] X.Forms).toRingHom

theorem emb_apply (F : X.Forms) : emb X la N F =
    ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F) : Kp X la N ⊗[X.Kl la] X.Vl la) := rfl

theorem emb_eq_bcV (F : X.Forms) : emb X la N F = bcV X la N (X.bc la F) := rfl

def Vw (u : WeightFamilies.Wt D j) : Submodule (Kp X la N) (Rp X la N) :=
  Submodule.span (Kp X la N) (Set.range fun F : B.Cusp j u => emb X la N (X.inc u F))

theorem emb_mem_Vw (u : WeightFamilies.Wt D j) (F : B.Cusp j u) : emb X la N (X.inc u F) ∈ Vw X la N u :=
  Submodule.subset_span ⟨F, rfl⟩

theorem emb_smul (a : B.KO) (F : X.Forms) :
    emb X la N (a • F) = algebraMap B.KO (X.Kl la) a • emb X la N F := by
  rw [emb_eq_bcV, emb_eq_bcV, map_smul (X.bc la), ← algebraMap_smul (X.Kl la) a (X.bc la F), map_smul]

theorem Vw_eq_span_image (u : WeightFamilies.Wt D j) {s : Set (B.Cusp j u)} (hs : Submodule.span B.KO s = ⊤) :
    Vw X la N u = Submodule.span (Kp X la N) ((fun F : B.Cusp j u => emb X la N (X.inc u F)) '' s) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (Set.image_subset_range _ _))
  rintro _ ⟨F, rfl⟩
  have hF : F ∈ Submodule.span B.KO s := hs ▸ Submodule.mem_top
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    simp only [map_smul, emb_smul]
    rw [← algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a)]
    exact Submodule.smul_mem _ _ hx

instance Vw.finiteDimensional (u : WeightFamilies.Wt D j) : FiniteDimensional (Kp X la N) ↥(Vw X la N u) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B.KO) (M := B.Cusp j u)
  rw [Vw_eq_span_image X la N u hs]
  exact FiniteDimensional.span_of_finite _ (s.finite_toSet.image _)

theorem Vw_mul_le (u u' : WeightFamilies.Wt D j) : Vw X la N u * Vw X la N u' ≤ Vw X la N (wadd u u') := by
  unfold Vw
  rw [Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨F, rfl⟩, _, ⟨G, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  exact ⟨H, by simp only [← hH, map_mul]⟩

theorem mul_mem_Vw {u u' : WeightFamilies.Wt D j} {x y : Rp X la N} (hx : x ∈ Vw X la N u) (hy : y ∈ Vw X la N u') :
    x * y ∈ Vw X la N (wadd u u') :=
  Vw_mul_le X la N u u' (Submodule.mul_mem_mul hx hy)

def Tv (p : Idx D j N) : Op X la N := algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X p)

end

def addL (u wL : WeightFamilies.Wt D j) (n : ℕ) : WeightFamilies.Wt D j := wadd u (wsmul n wL)

theorem wadd_addL (u wL : WeightFamilies.Wt D j) (n : ℕ) : wadd wL (addL u wL n) = addL u wL (n + 1) := by
  unfold addL wadd wsmul
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; ring
  · funext τ i; ring
  · ring

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def sec (i : Fin (WeightFamilies.dimY D j + 1)) : Rp X la N :=
  ∑ k, (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) • emb X la N (X.inc wL (w k))

theorem sec_mem_Vw (i : Fin (WeightFamilies.dimY D j + 1)) : sec X la w i ∈ Vw X la N wL :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N wL (w k))

def secPow (α : Fin (WeightFamilies.dimY D j) → ℕ) : Rp X la N := ∏ i, sec X la w i.succ ^ α i

theorem sec_pow_mul_mem (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : Rp X la N}
    (hv : v ∈ Vw X la N (addL u wL n)) : sec X la w i ^ m * v ∈ Vw X la N (addL u wL (n + m)) := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact mul_mem_Vw X la N (sec_mem_Vw X la w i) ih

def Mon (u : WeightFamilies.Wt D j) (a n : ℕ) : Submodule (Kp X la N) (Rp X la N) :=
  ⨆ (α : Fin (WeightFamilies.dimY D j) → ℕ) (_ : ∑ i, α i = a),
    (Vw X la N (addL u wL n)).map (LinearMap.mulLeft (Kp X la N) (secPow X la w α))

theorem sec_pow_mul_mem_Mon (u : WeightFamilies.Wt D j) (a n m : ℕ) {x : Rp X la N} (hx : x ∈ Mon X la w u a n) :
    sec X la w 0 ^ m * x ∈ Mon X la w u a (n + m) := by
  have h : Mon X la w u a n ≤
      (Mon X la w u a (n + m)).comap (LinearMap.mulLeft (Kp X la N) (sec X la w 0 ^ m)) := by
    refine iSup₂_le fun α hα => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    show sec X la w 0 ^ m * (secPow X la w α * v) ∈ Mon X la w u a (n + m)
    rw [mul_left_comm]
    exact Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hα
      (Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la N) (secPow X la w α))
        (sec_pow_mul_mem X la w 0 u n m hv)))
  exact h hx

def Fil (u : WeightFamilies.Wt D j) (a : ℕ) : Submodule (Kp X la N) (Rp X la N) where
  carrier := {f | f ∈ Vw X la N u ∧ ∃ k, a ≤ k ∧ sec X la w 0 ^ k * f ∈ Mon X la w u a (k - a)}
  zero_mem' := ⟨Submodule.zero_mem _, a, le_rfl, by rw [mul_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, k, hk, hfk⟩ ⟨hg, k', hk', hgk⟩
    refine ⟨Submodule.add_mem _ hf hg, k + k', by omega, ?_⟩
    rw [mul_add]
    refine Submodule.add_mem _ ?_ ?_
    · have := sec_pow_mul_mem_Mon X la w u a (k - a) k' hfk
      rwa [← mul_assoc, ← pow_add, add_comm k' k, show k - a + k' = k + k' - a by omega] at this
    · have := sec_pow_mul_mem_Mon X la w u a (k' - a) k hgk
      rwa [← mul_assoc, ← pow_add, show k' - a + k = k + k' - a by omega] at this
  smul_mem' := by
    rintro c f ⟨hf, k, hk, hfk⟩
    exact ⟨Submodule.smul_mem _ c hf, k, hk, by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hfk⟩

theorem mem_Fil {u : WeightFamilies.Wt D j} {a : ℕ} {f : Rp X la N} : f ∈ Fil X la w u a ↔
    f ∈ Vw X la N u ∧ ∃ k, a ≤ k ∧ sec X la w 0 ^ k * f ∈ Mon X la w u a (k - a) := Iff.rfl

theorem Fil_le_Vw (u : WeightFamilies.Wt D j) (a : ℕ) : Fil X la w u a ≤ Vw X la N u := fun _ h => h.1

end

end Formalism.MainNotions.Gaps.EtaleWeightGaps
