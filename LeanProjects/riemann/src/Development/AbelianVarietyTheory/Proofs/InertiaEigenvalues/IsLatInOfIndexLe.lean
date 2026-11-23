import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.ExportFromInputs

section Algebra

theorem sIdx_map {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') (hf : Function.Injective f) (l : ℕ) (M N : Submodule R W) :
    sIdx l (M.map f) (N.map f) = sIdx l M N := by
  simp only [sIdx_eq_signedLength_div, signedLength, relLength_map_of_injective f hf]

theorem isLatIn_map {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] (f : W →ₗ[R] W') {M V : Submodule R W} (h : IsLatIn M V) :
    IsLatIn (M.map f) (V.map f) := by
  refine ⟨h.1.map f, Submodule.map_mono h.2.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hy⟩ := h.2.2 x hx
  exact ⟨c, hc, c • x, hy, map_smul _ _ _⟩

theorem isLatIn_smul {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W]
    {M V : Submodule R W} (h : IsLatIn M V) {c : R} (hc : c ≠ 0) :
    IsLatIn (M.map (c • LinearMap.id)) V := by
  refine ⟨h.1.map _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact V.smul_mem c (h.2.1 hx)
  · obtain ⟨d, hd, hy⟩ := h.2.2 x hx
    exact ⟨c * d, mul_ne_zero hc hd, d • x, hy, (mul_smul c d x).symm⟩

theorem isLatIn_of_span {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module (FractionRing R) W]
    [Module R W] [IsScalarTower R (FractionRing R) W] {L : Submodule R W} {V : Submodule (FractionRing R) W}
    (hfg : L.FG) (h : Submodule.span (FractionRing R) (L : Set W) = V) : IsLatIn L (V.restrictScalars R) := by
  refine ⟨hfg, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← h]; exact Submodule.subset_span hx
  · rw [← h, Submodule.restrictScalars_mem] at hx
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) (FractionRing R)
      (L : Set W) x hx
    rw [Submodule.span_eq] at hc
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩

theorem span_of_isLatIn {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module (FractionRing R) W]
    [Module R W] [IsScalarTower R (FractionRing R) W] {L : Submodule R W} {V : Submodule (FractionRing R) W}
    (h : IsLatIn L (V.restrictScalars R)) : Submodule.span (FractionRing R) (L : Set W) = V := by
  refine le_antisymm (Submodule.span_le.2 h.2.1) fun x hx => ?_
  obtain ⟨c, hc, hx⟩ := h.2.2 x hx
  have hc' : algebraMap R (FractionRing R) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hc
  have : x = (algebraMap R (FractionRing R) c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul (FractionRing R) c x, inv_smul_smul₀ hc']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem map_baseChange {O R W W' : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup W] [Module O W]
    [AddCommGroup W'] [Module O W'] (f : W →ₗ[O] W') (T : Submodule O W) :
    (T.baseChange R).map (f.baseChange R) = (T.map f).baseChange R := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by simp⟩

theorem torsionFree_tensor {O R W : Type} [CommRing O] [IsDomain O] [CommRing R] [IsDomain R] [Algebra O R]
    [AddCommGroup W] [Module (FractionRing O) W] [Module O W] [IsScalarTower O (FractionRing O) W]
    (c : R) (x : R ⊗[O] W) (hc : c ≠ 0) (hx : c • x = 0) : x = 0 := by
  haveI : Module.Flat O W := Module.Flat.trans O (FractionRing O) W
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := W)
    (LinearMap.mulLeft O c) (mul_right_injective₀ hc)
  apply hinj
  have : ∀ y : R ⊗[O] W, (LinearMap.mulLeft O c).rTensor W y = c • y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => simp [TensorProduct.smul_tmul']
    | add a b ha hb => rw [map_add, ha, hb, smul_add]
  rw [this, hx, map_zero]

section Tower

variable {O R S W : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra R S] [Algebra O S]
  [IsScalarTower O R S] [AddCommGroup W] [Module O W]

theorem cancel_one_tmul (x : R ⊗[O] W) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W ((1 : S) ⊗ₜ[R] x) =
      LinearMap.rTensor W (IsScalarTower.toAlgHom O R S).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp [Algebra.smul_def]
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]

theorem span_rTensor (L : Submodule R (R ⊗[O] W)) :
    Submodule.span S ((LinearMap.rTensor W (IsScalarTower.toAlgHom O R S).toLinearMap) '' (L : Set (R ⊗[O] W))) =
      (L.baseChange S).map (TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, cancel_one_tmul v⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (cancel_one_tmul v).symm⟩

theorem baseChange_tower (T : Submodule O W) :
    T.baseChange S = ((T.baseChange R).baseChange S).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W).toLinearMap := by
  rw [Submodule.baseChange_eq_span (p := T) (A := R), Submodule.baseChange_span, Submodule.map_span,
    Submodule.baseChange_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨v, hv, by simp⟩

end Tower

theorem index_extend {O R S W : Type} [CommRing O] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra O R] [Algebra R S] [Algebra O S]
    [IsScalarTower O R S] [AddCommGroup W] [Module O W] (hinj : Function.Injective (algebraMap R S))
    [Module.Finite R S] (l : ℕ) {V T : Submodule O W} {L : Submodule R (R ⊗[O] W)} {e : ℝ}
    (hT : IsLatIn (T.baseChange R) (V.baseChange R)) (hL : IsLatIn L (V.baseChange R))
    (h : sIdx l (T.baseChange R) L ≤ e) (M : Submodule S (S ⊗[O] W)) (hM : IsLatIn M (V.baseChange S)) :
    sIdx l M (Submodule.span S
      ((LinearMap.rTensor W (IsScalarTower.toAlgHom O R S).toLinearMap) '' (L : Set (R ⊗[O] W)))) ≤
      sIdx l M (T.baseChange S) + e := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsLocalHom (algebraMap R S) := Algebra.IsIntegral.isLocalHom _ _
  rw [span_rTensor]
  have h1 := isLatIn_map (TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W).toLinearMap
    (isLatIn_baseChange S hinj hT)
  have h2 := isLatIn_map (TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W).toLinearMap
    (isLatIn_baseChange S hinj hL)
  have h3 := (sIdx_baseChange R S hinj _ l _ _ _ hT hL).2
  rw [← sIdx_map _ (TensorProduct.AlgebraTensorModule.cancelBaseChange O R S S W).injective] at h3
  rw [← baseChange_tower] at h1 h2 h3
  rw [← baseChange_tower] at h1
  rw [(sIdx_add_and_mono S _ l _ _ _ _ hM h1 h2).1]
  linarith

theorem index_unscale {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (htf : ∀ (c : R) (w : W), c ≠ 0 → c • w = 0 → w = 0) (l : ℕ) {V B T L : Submodule R W}
    (hB : IsLatIn B V) (hT : IsLatIn T V) (hL : IsLatIn L V) {c : R} (hc : c ≠ 0) {e : ℝ}
    (h : sIdx l B (L.map (c • LinearMap.id)) ≤ sIdx l B (T.map (c • LinearMap.id)) + e) : sIdx l T L ≤ e := by
  have hi : Function.Injective (c • (LinearMap.id : W →ₗ[R] W)) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    exact htf c w hc hw
  rw [(sIdx_add_and_mono R _ l _ _ _ _ hB (isLatIn_smul hT hc) (isLatIn_smul hL hc)).1, sIdx_map _ hi] at h
  linarith

theorem isLatIn_of_index_le {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) (hl0 : (l : R) ≠ 0) (hl : ¬ IsUnit (l : R)) {V B T : Submodule R W} {C : ℝ}
    (hB : IsLatIn B V) (hfg : T.FG) (hle : T ≤ V) (H : ∀ T', IsLatIn T' V → T ≤ T' → sIdx l B T' ≤ C) :
    IsLatIn T V := by
  let P : ℕ → Submodule R W := fun n => B.map ((l : R) ^ n • LinearMap.id)
  have hP : ∀ n, IsLatIn (P n) V := fun n => isLatIn_smul hB (pow_ne_zero n hl0)
  have hL : ∀ n, IsLatIn (T ⊔ P n) V := fun n =>
    ⟨hfg.sup (hP n).1, sup_le hle (hP n).2.1, fun x hx =>
      ((hP n).2.2 x hx).imp fun c hc => ⟨hc.1, Submodule.mem_sup_right hc.2⟩⟩
  have hstep : ∀ n, P (n + 1) ≤ Ideal.span {(l : R)} • P n := by
    rintro n _ ⟨x, hx, rfl⟩
    show (l : R) ^ (n + 1) • x ∈ _
    rw [pow_succ', mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ⟨x, hx, rfl⟩
  have hanti : ∀ n, T ⊔ P (n + 1) ≤ T ⊔ P n := fun n =>
    sup_le_sup_left ((hstep n).trans Submodule.smul_le_right) _
  by_contra hT
  have hne : ∀ n, ¬ T ⊔ P n ≤ T ⊔ P (n + 1) := by
    intro n h
    have h1 : P n ≤ T := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(l : R)}) (hP n).1 ?_
        (le_sup_right.trans (h.trans (sup_le_sup_left (hstep n) _)))
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, Ideal.span_singleton_le_iff_mem]
      exact hl
    exact hT ⟨hfg, hle, fun x hx => ((hP n).2.2 x hx).imp fun c hc => ⟨hc.1, h1 hc.2⟩⟩
  set e : ℝ := ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) with he
  have hepos : 0 < e := by
    rw [he, Nat.cast_pos, Nat.pos_iff_ne_zero, Ne, ENat.toNat_eq_zero, not_or,
      IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ⟨hl, hl0⟩
  have hone : ∀ n, 1 / e ≤ sIdx l (T ⊔ P n) (T ⊔ P (n + 1)) := by
    intro n
    rw [sIdx_eq_signedLength_div, ← he]
    refine div_le_div_of_nonneg_right ?_ hepos.le
    have h1 := relLength_ne_top_of_isLatIn (hL n) (hL (n + 1))
    have h2 : relLength (T ⊔ P (n + 1)) (T ⊔ P n) = 0 := relLength_eq_zero_iff.2 (hanti n)
    have h3 : relLength (T ⊔ P n) (T ⊔ P (n + 1)) ≠ 0 := fun h => hne n (relLength_eq_zero_iff.1 h)
    have h4 : (relLength (T ⊔ P n) (T ⊔ P (n + 1))).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero, not_or]; exact ⟨h3, h1⟩
    rw [signedLength, h2]
    have : (1 : ℤ) ≤ ((relLength (T ⊔ P n) (T ⊔ P (n + 1))).toNat : ℤ) := by omega
    simpa using Nat.one_le_iff_ne_zero.2 h4
  have hgrow : ∀ n : ℕ, sIdx l B (T ⊔ P 0) + n * (1 / e) ≤ sIdx l B (T ⊔ P n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [(sIdx_add_and_mono R _ l _ _ _ _ hB (hL n) (hL (n + 1))).1]
      have := hone n
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - sIdx l B (T ⊔ P 0)) / (1 / e))
  rw [div_lt_iff₀ (by positivity)] at hn
  have := hgrow n
  have := H _ (hL n) le_sup_left
  linarith

end Algebra

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

open GlobalTheory.TwistInputsTest

theorem charZero_O (i : X.Tw) : CharZero (X.O i) := by
  haveI : CharZero (FractionRing (X.O i)) :=
    (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance
  exact (RingHom.charZero_iff (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))).2 inferInstance

theorem card_ne_zero (i : X.Tw) : ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) ≠ 0 := by
  haveI := charZero_O (X := X) i
  exact Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

theorem AO_apply (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x := rfl

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  have he : eG Y i j b = act Y i j b (Y.eAlg i b) := rfl
  rw [he, ← Module.End.mul_apply, ← map_mul, Y.eAlg_idem]

theorem zO_eq (i : X.Tw) (j : ℕ) (b : Bool) (z : MonoidAlgebra (X.O i) (G0g N))
    (hz : MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom z =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) : zO Y i j b z = AO Y i j b := by
  ext x
  rw [AO_apply, ← algebraMap_smul (FractionRing (X.O i)), map_natCast]
  unfold zO
  rw [hz, map_smul]
  rfl

theorem central_of_map (i : X.Tw) (b : Bool) (z : MonoidAlgebra (X.O i) (G0g N))
    (hz : MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom z =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) (x : MonoidAlgebra (X.O i) (G0g N)) :
    z * x = x * z := by
  apply MonoidAlgebra.map_injective (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom
    (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hz' : MonoidAlgebra.mapRingHom (G0g N) (algebraMap (X.O i) (FractionRing (X.O i))) z =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := hz
  show MonoidAlgebra.mapRingHom (G0g N) (algebraMap (X.O i) (FractionRing (X.O i))) (z * x) =
    MonoidAlgebra.mapRingHom (G0g N) (algebraMap (X.O i) (FractionRing (X.O i))) (x * z)
  rw [map_mul, map_mul, hz', smul_mul_assoc, mul_smul_comm, Y.eAlg_central]

theorem zO_mem (i : X.Tw) (j : ℕ) (b : Bool) (L : Submodule (X.O i) (Y.Fm i j b))
    (hL : ∀ g, L.map ((Y.actG i j b g).toLinearMap.restrictScalars (X.O i)) ≤ L)
    (z : MonoidAlgebra (X.O i) (G0g N)) (x : Y.Fm i j b) (hx : x ∈ L) : zO Y i j b z x ∈ L := by
  have h : ∀ z, zO Y i j b z x = act Y i j b
    (MonoidAlgebra.mapRingHom (G0g N) (algebraMap (X.O i) (FractionRing (X.O i))) z) x := fun _ => rfl
  rw [h]
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add]; exact L.add_mem hf hg
  | single g r =>
    have : act Y i j b (MonoidAlgebra.mapRingHom (G0g N) (algebraMap (X.O i) (FractionRing (X.O i)))
        (MonoidAlgebra.single g r)) x = r • Y.actG i j b g x := by
      simp [act]
    rw [this]
    exact L.smul_mem r (hL g ⟨x, hx, rfl⟩)

def fam (i : X.Tw) (z : Bool → MonoidAlgebra (X.O i) (G0g N)) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) :
    RFam Y i :=
  ⟨Mall Y i, fun _ b => z b, fun j b => Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i), S⟩

theorem isLatIn_B (i : X.Tw) (j : ℕ) (b : Bool) (hfg : (Mall Y i j b).FG)
    (hsp : Submodule.span (FractionRing (X.O i)) (Mall Y i j b : Set (Y.Fm i j b)) = Fm0 Y i j b) :
    IsLatIn (Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i)) ((V0 Y i j b).restrictScalars (X.O i)) := by
  refine ⟨hfg.of_le inf_le_left, inf_le_right, fun x hx => ?_⟩
  obtain ⟨c, hc, h⟩ := (isLatIn_of_span hfg hsp).2.2 x (goodPart_le_typeSubspace Y i j b hx)
  exact ⟨c, hc, h, Submodule.smul_mem _ c hx⟩

theorem map_AO (i : X.Tw) (j : ℕ) (b : Bool) (T : Submodule (X.O i) (Y.Fm i j b)) :
    T.map (AO Y i j b) = (T.map (eO Y i j b)).map (((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • LinearMap.id) := by
  rw [← Submodule.map_comp]; rfl

theorem abHyp_fam (E : ExpDat Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool)
    (z : Bool → MonoidAlgebra (X.O i) (G0g N))
    (hz : MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom (z b) =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (h3 : IsotypicPartsInternalDirectSum Y E) (h5 : GroupAlgebraIntegrality Y) (h11 : GoodLatticePoints Y)
    (hF : FullRk Y E i j b (SgJ Y E i j b)) (hS : BasisOf Y i j b (SgJ Y E i j b) (S j b)) :
    ABHyp Y i (fam Y i z S) j b := by
  obtain ⟨hG, hfg, hsp, hhk, ht2, -⟩ := h3 i hi j hj b
  have hcomm := ((h5 i hi b).2 j hj).1
  have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ hz
  have hB := isLatIn_B Y i j b hfg hsp
  have hAV : ∀ x ∈ Fm0 Y i j b, AO Y i j b x ∈ V0 Y i j b := fun x hx =>
    ((V0 Y i j b).restrictScalars (X.O i)).smul_mem _ ⟨x, hx, rfl⟩
  have hAM : (Mall Y i j b).map (AO Y i j b) ≤ Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨?_, goodPart_le_typeSubspace Y i j b (hAV x hx.2)⟩, hAV x hx.2⟩
    rw [← zO_eq Y i j b _ hz]
    exact zO_mem Y i j b _ hG _ x hx.1
  have he : ∀ k P, HkIdx i k P → ∀ x, eG Y i j b (Y.hkF i j b k P x) = Y.hkF i j b k P (eG Y i j b x) :=
    fun k P h x => act_comm Y i j b _ (fun g x => LinearMap.congr_fun (hcomm g k P h) x) _ x
  have hspA : Submodule.span (FractionRing (X.O i))
      (((Mall Y i j b).map (AO Y i j b) : Submodule (X.O i) (Y.Fm i j b)) : Set (Y.Fm i j b)) = V0 Y i j b := by
    rw [map_AO]
    apply span_of_isLatIn
    apply isLatIn_smul _ (card_ne_zero i)
    exact isLatIn_map (eO Y i j b) (isLatIn_of_span hfg hsp)
  unfold ABHyp
  rw [hA]
  refine ⟨hfg, hhk, hAM.trans inf_le_left, ?_, hAM, ?_, hS.2.1, ?_, central_of_map Y i b _ hz, ?_, ?_,
    h11 i hi j hj b⟩
  · show IsLatIn _ ((Submodule.span (FractionRing (X.O i))
      (((Mall Y i j b).map (AO Y i j b) : Submodule (X.O i) (Y.Fm i j b)) : Set (Y.Fm i j b))).restrictScalars _)
    rw [hspA]; exact hB
  · rintro k P h _ ⟨x, hx, rfl⟩
    refine ⟨hhk k P h ⟨x, hx.1, rfl⟩, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx.2
    refine ⟨Y.hkF i j b k P y, ?_, he k P h y⟩
    refine (mem_typeSubspace_iff_unipotent_character Y i j b _).2 fun u => ?_
    have := LinearMap.congr_fun (hcomm u k P h) y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, (mem_typeSubspace_iff_unipotent_character Y i j b y).1 hy u, map_smul]
  · refine Eq.trans ?_ (span_of_isLatIn hB).symm
    rw [← hF.2.2, ← hS.2.2, Submodule.span_span_of_tower]
    rfl
  · intro k P h
    ext x
    show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b (Y.hkF i j b k P x) =
      hkO Y i j b k P (((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x)
    rw [map_smul, he k P h]; rfl
  · have : ∀ a : Y.Dat i j b, ∃ c : ℕ, a ∈ S j b → ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) →
        ClsQ (D := D) Q → Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
        ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((Mall Y i j b).subtype.rTensor _) := by
      intro a
      by_cases ha : a ∈ S j b
      · obtain ⟨c, hc⟩ := ht2 a (hS.1 ha)
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h ha⟩
    choose c hc using this
    refine ⟨(S j b).sup c, fun Q M h1 h2 h4 a ha h6 => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := c) ha)
    show ((X.l i : X.O i) ^ (S j b).sup c) • Y.thU i j b Q M a ∈ _
    have ha' : a ∈ S j b := ha
    rw [show (S j b).sup c = d + c a by rw [add_comm]; exact hd, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hc a ha' Q M h1 h2 h4 h6)

theorem natCast_l_ne_zero (i : X.Tw) (k : ℕ) : ((X.l i : ℕ) : X.Ok i k) ≠ 0 ∧ ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) := by
  haveI := charZero_O (X := X) i
  haveI : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  haveI := X.Ok_fin i k
  haveI : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap (X.O i) (X.Ok i k))]
  refine ⟨(map_ne_zero_iff _ (X.Ok_inj i k)).2 (Nat.cast_ne_zero.2 (X.lPrime i).out.ne_zero), fun h => ?_⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 (X.O_l i) ((isUnit_map_iff _ _).1 h)

theorem export_at (E : ExpDat Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool)
    (S : Finset (Y.Dat i j b)) (h3 : IsotypicPartsInternalDirectSum Y E) (h7 : admT4 Y E)
    (hF : FullRk Y E i j b (SgJ Y E i j b)) (hS : BasisOf Y i j b (SgJ Y E i j b) S)
    (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (hψ : TwOK i k Q ψ) (hu : UnrG ψ)
    (e : ℝ)
    (H : ∀ T : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b),
      IsLatIn T (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) →
      (ThPsi Y i j b k Q ψ (SgJ Y E i j b)).map ((AO Y i j b).baseChange (X.Ok i k)) ≤ T →
      sIdx (X.l i) ((Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) T ≤
        sIdx (X.l i) (Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i))
          ((Th Y i j b (SgJ Y E i j b)).map (AO Y i j b)) + e) :
    IdxAt Y i j b (SgJ Y E i j b) k Q ψ e ∧
      IsLatIn (eThPsi Y i j b k Q ψ (SgJ Y E i j b)) (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
      InclAt Y i j b (SgJ Y E i j b) k Q ψ := by
  obtain ⟨-, hfg, hsp, -, -, hty⟩ := h3 i hi j hj b
  haveI : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  haveI := X.Ok_fin i k
  haveI : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := Algebra.IsIntegral.isLocalHom _ _
  have hB := isLatIn_B Y i j b hfg hsp
  have hBk := isLatIn_baseChange (X.Ok i k) (X.Ok_inj i k) hB
  have hincl : InclAt Y i j b (SgJ Y E i j b) k Q ψ :=
    Submodule.map_mono (h7 i hi j hj b k Q ψ hψ _ subset_rfl)
  have htf : ∀ (c : X.Ok i k) (w : X.Ok i k ⊗[X.O i] Y.Fm i j b), c ≠ 0 → c • w = 0 → w = 0 :=
    torsionFree_tensor
  have hc := card_ne_zero (X := X) i
  have hck : algebraMap (X.O i) (X.Ok i k) (D.what₂.restRowsFiniteGroupCard : ℕ) ≠ 0 := (map_ne_zero_iff _ (X.Ok_inj i k)).2 hc
  have hmap : ∀ T : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b),
      T.map ((AO Y i j b).baseChange (X.Ok i k)) = (T.map ((eO Y i j b).baseChange (X.Ok i k))).map
        (algebraMap (X.O i) (X.Ok i k) (D.what₂.restRowsFiniteGroupCard : ℕ) • LinearMap.id) := by
    intro T
    rw [← Submodule.map_comp, AO, LinearMap.baseChange_smul, algebraMap_smul]
    rfl

  have hXfg : (eThPsi Y i j b k Q ψ (SgJ Y E i j b)).FG :=
    (((Y.MtLat_fg i j b k Q ψ).map _).map _).of_le hincl
  have hXle : eThPsi Y i j b k Q ψ (SgJ Y E i j b) ≤
      ((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) := by
    have h1 : ThPsi Y i j b k Q ψ (SgJ Y E i j b) ≤
        ((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :=
      Submodule.span_le.2 (Set.iUnion₂_subset fun a ha => hty k Q ψ hψ hu a ha)
    refine (Submodule.map_mono h1).trans ?_
    rw [map_baseChange]
    rfl
  have hle : (ThPsi Y i j b k Q ψ (SgJ Y E i j b)).map ((AO Y i j b).baseChange (X.Ok i k)) ≤
      eThPsi Y i j b k Q ψ (SgJ Y E i j b) := by
    rw [hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem _ _ hx
  have hX : IsLatIn (eThPsi Y i j b k Q ψ (SgJ Y E i j b))
      (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) :=
    isLatIn_of_index_le (X.l i) (natCast_l_ne_zero i k).1 (natCast_l_ne_zero i k).2 hBk hXfg hXle
      fun T hT h => H T hT (hle.trans h)

  have hA : IsLatIn ((Th Y i j b (SgJ Y E i j b)).map (AO Y i j b)) ((V0 Y i j b).restrictScalars (X.O i)) := by
    refine isLatIn_of_span ?_ hF.2.2
    rw [← hS.2.2]
    exact Submodule.fg_span (S.finite_toSet.image _)
  have hY : IsLatIn (eTh Y i j b (SgJ Y E i j b)) ((V0 Y i j b).restrictScalars (X.O i)) := by
    have h1 := hA
    rw [map_AO] at h1
    have hinj : Function.Injective (((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) •
        (LinearMap.id : Y.Fm i j b →ₗ[X.O i] Y.Fm i j b)) := by
      haveI : Module.IsTorsionFree (X.O i) (Y.Fm i j b) :=
        Module.IsTorsionFree.trans_faithfulSMul (X.O i) (FractionRing (X.O i)) (Y.Fm i j b)
      exact smul_right_injective _ hc
    refine ⟨Submodule.fg_of_fg_map_injective _ hinj h1.1, ?_, fun x hx => ?_⟩
    · refine Submodule.map_mono (f := eO Y i j b) (p' := (Fm0 Y i j b).restrictScalars (X.O i)) ?_
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_typeSubspace_iff_unipotent_character Y i j b _).2 (E.theta_base_equivariant i j b a ha)
    · obtain ⟨c, hc0, y, hy, h⟩ := h1.2.2 x hx
      exact ⟨c, hc0, h ▸ Submodule.smul_mem _ _ hy⟩
  have hYk := isLatIn_baseChange (X.Ok i k) (X.Ok_inj i k) hY
  have hbound := H _ (by rw [hmap]; exact isLatIn_smul hX hck) le_rfl
  rw [← (sIdx_baseChange (X.O i) (X.Ok i k) (X.Ok_inj i k) _ (X.l i) _ _ _ hB hA).2, ← map_baseChange (AO Y i j b),
    hmap, hmap, map_baseChange] at hbound
  have hfin := index_unscale htf (X.l i) hBk hYk hX hck hbound
  refine ⟨?_, hX, hincl⟩
  intro O' _ _ _ _ _ _ hinj hfin' M hM
  exact index_extend hinj (X.l i) hYk hX hfin M hM

theorem psiAt_comp {Γ Δ A : Type} [Group Γ] [Group Δ] [CommGroup A] (b : Bool) (χ : Δ →* A) (f : Γ →* Δ) :
    psiAt b (χ.comp f) = (psiAt b χ).comp f := by
  cases b <;> rfl

theorem export_at_setting (bkP : BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (h2 : TwistingCharacterExistence Y bkP N0) (h3 : IsotypicPartsInternalDirectSum Y E)
    (h5 : GroupAlgebraIntegrality Y) (h7 : admT4 Y E) (h10 : TwistedSeriesSpecialisation Y) (h11 : GoodLatticePoints Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) :
    TwistTheoremAtIndex Y bkP E N0 i := by
  classical
  intro hs eps' he hF S hS A
  choose z hz using fun b => (h5 i hi b).1
  have hAB := fun j hj b => abHyp_fam Y E i hi j hj b z (hz b) S h3 h5 h11 (hF j hj b) (hS j hj b)
  obtain ⟨Q, k, ψ', hok, ha, hc, hd, M, χ, hχ, epsB, h0, hsum, H⟩ :=
    h2 i hi hs eps' he (fam Y i z S) hAB (levs Y i S ∪ A)
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, _ := fun j hj b => by
    obtain ⟨htw, hu, hdis⟩ := twOK_of_psiOk i _ Q k ψ' hok b
    refine export_at Y E i hi j hj b (S j b) h3 h7 (hF j hj b) (hS j hj b) k Q _ htw hu (epsB j b) ?_
    intro T hT hle
    obtain ⟨-, hfg, hsp, -⟩ := h3 i hi j hj b
    have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ (hz b)
    have hTh : (fam Y i z S).Th j b = (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b) := by
      rw [← (hS j hj b).2.2, RFam.Th, hA]; rfl
    rw [← hTh]
    refine H j hj b T ?_ fun a ha => ?_
    · have : Submodule.span (FractionRing (X.O i)) ((fam Y i z S).B j b : Set (Y.Fm i j b)) = V0 Y i j b :=
        span_of_isLatIn (isLatIn_B Y i j b hfg hsp)
      rw [this]; exact hT
    · have ha' : a ∈ S j b := ha
      rw [hχ, psiAt_comp] at htw hle
      have hlev : Disjoint Q (Y.lev i j b a) := by
        refine hdis.mono_right (le_trans ?_ Finset.subset_union_left)
        intro v hv
        simp only [levs, Finset.mem_biUnion]
        exact ⟨j, hj, b, Finset.mem_univ _, a, ha', hv⟩
      rw [hA]
      refine hle ⟨_, ?_, rfl⟩
      refine Submodule.span_mono ?_ (h10 i hi j hj b k Q M _ htw a hlev)
      exact Set.biUnion_subset_biUnion_left (Set.singleton_subset_iff.2 ((hS j hj b).1 ha'))
  exact ⟨Q, k, ψ', hok, ⟨epsB, h0, hsum, fun j hj b => (key j hj b).1⟩, fun j hj b => (key j hj b).2, ha, hc, hd⟩

end GlobalTheory.ExportFromInputs

theorem GlobalTheory.export_of_inputs :
    ∀ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : Formalism.MainNotions.IntegralHeckeForms.XD D), Formalism.MainNotions.IntegralHeckeForms.Stmt D bkP E := by
  rintro D bkP E N0 ⟨-, h2, h3, -, h5, h7, -, -, h10, h11⟩ i hi
  exact GlobalTheory.ExportFromInputs.export_at_setting D.nexp _ E N0 h2 h3 h5 h7 h10 h11 i hi

end
