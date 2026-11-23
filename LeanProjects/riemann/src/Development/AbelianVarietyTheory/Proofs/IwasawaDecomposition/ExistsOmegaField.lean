import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeightsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegralStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedData

variable {D : D7}

def rowP (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  toEAf D e * ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

theorem rowPairing_add (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x y : Fin W.rank → D.host.E) (a : Fin W.rank) :
    rowP W β e (x + y) a = rowP W β e x a + rowP W β e y a := by
  simp only [rowP, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem rowPairing_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (a : Fin W.rank) :
    rowP W β e 0 a = 0 := by
  simp only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem rowPairing_smul (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (c : D.host.E) (x : Fin W.rank → D.host.E)
    (a : Fin W.rank) : rowP W β e (c • x) a = eToEAf D (D.sp.cm.sig c) * rowP W β e x a := by
  simp only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem uMat_eq (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (β : GL (Fin W.rank) (EAf D)) (e : AE D)
    (X : Fin V.rank → Fin W.rank → D.host.E) (b : Fin V.rank) (a : Fin W.rank) :
    FWT.uMat V W βV β e X b a = ∑ b', (βV⁻¹).val b b' * rowP W β e (X b') a := by
  simp only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eToEAf_int (c : 𝓞 D.host.E) : eToEAf D (c : D.host.E) = (oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

theorem exists_sig (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

theorem rowP_int (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (x : Fin W.rank → D.host.E) (hx : x ∈ latG W 1) (a : Fin W.rank) :
    rowP W β e x a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]
    exact mul_mem (GlobalTheory.T.conj_principalFractional_integral_idempotentSum D e P he hP c hc) (GlobalTheory.T.selfDual_vector_pairs_integral_frame_columns D W β Λ hβ v hv a)
  | zero => rw [rowPairing_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [rowPairing_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc'⟩ := exists_sig c
    rw [show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]
    exact mul_mem (Subtype.prop _) hx

theorem residue_rowPairing_eq_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (a : Fin W.rank)
    (hi : ∀ x, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : x ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) : resS D.host.F PP ⟨_, hi x⟩ = 0 := by
  refine Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c', hc', e'⟩ := hJ c hc
    have : (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a
      rw [map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']
    rw [this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]
  · have : (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
      rw [map_add, rowPairing_add]
    rw [this, map_add, hx, hy, add_zero]

theorem redM_uMat (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) (X : Fin V.rank → Fin W.rank → D.host.E)
    (hi : ∀ b a, rowP W β e (X b) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IsIntM (FWT.uMat V W βV β e X) ∧ ∀ PP b a, redM PP (FWT.uMat V W βV β e X) b a =
      ∑ b', resS D.host.F PP ⟨_, hβ b b'⟩ * resS D.host.F PP ⟨_, hi b' a⟩ := by
  have h : IsIntM (FWT.uMat V W βV β e X) := fun b a => by
    rw [uMat_eq V W hV]
    exact sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)
  refine ⟨h, fun PP b a => ?_⟩
  rw [redM, dif_pos (h b a)]
  simp only [← map_mul, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finset_sum]
  exact uMat_eq V W hV βV β e X b a

theorem omega_congr {a b : ℕ} (Pg Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → y PP = y' PP) :
    omegaK Pg y * omegaQ Q r ξ k y = omegaK Pg y' * omegaQ Q r ξ k y' := by
  classical
  have h1 : omegaK Pg y = omegaK Pg y' := by
    unfold omegaK
    refine if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl
  have h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
    have e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
        ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
      forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]
    unfold omegaQ
    by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dif_pos c, dif_pos (e.1 c)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit := Units.ext (by
        rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])
      rw [this]
    · rw [dif_neg c, dif_neg (fun c' => c (e.2 c'))]
  rw [h1, h2]

theorem exists_omega_field (Pg Q : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
      (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), omegaK Pg y * omegaQ Q r ξ k y ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩
  · unfold omegaK
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold omegaQ
    split_ifs
    · refine prod_mem fun PP _ => zpow_mem (h _ ?_) _
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2
      rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
    · exact zero_mem _

set_option maxHeartbeats 800000 in

theorem exists_datum (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x z : Fin V.rank → La) (h : ∀ b, z b - x b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) :
    redM PP (FWT.uMat V W βV β e fun b => ι (z b)) = redM PP (FWT.uMat V W βV β e fun b => ι (x b)) := by
  have key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩ := fun b' a => by
    have h2 := residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')
    have : (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a
      rw [← rowPairing_add, ← LinearMap.map_add, sub_add_cancel]
    rw [this, RingHom.map_add, h2, zero_add]
  funext b a
  exact ((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans
    ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans
      ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)

theorem adForms_ext {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

theorem exists_phi {F : Face D A} (hR : R.Char F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' →
      (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
      ∀ J : Ideal (𝓞 D.host.E),
        (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) →
        ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M',
          PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

set_option maxHeartbeats 1000000 in

theorem exists_thAd {F : Face D A} (hR : R.Char F) (t : T0) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) {Cl : Type} (h : Cl → GA D (Vc D i)) {J' : Subgroup (Bridge.Gf (Vc D i))}
    (hle : J' ≤ levJ R i t) (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)))
    (v₀ : (R.MW i (sg0 D A)).Vec) : ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.models.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_ext _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y)) (hrange.le (LinearMap.mem_range_self _ y'))
      fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]

theorem latEmb_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

set_option maxHeartbeats 2000000 in

theorem exists_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hfw hpb hfin hG i hV
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨pd, l₂, c₁, h1, h2, hc⟩ := GlobalTheory.TupleCover.exists_covers_of_char T R F hT hR hpb hG i
  choose Mφ hMφ hφ using fun t => exists_phi R i hR hV t (iotaW T i) (latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hR.lev i t
  have := c₁.fin
  obtain ⟨c', hc'⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  have h3 : c₁.F ≤ c'.F := le_sup_left.trans hc'
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t => ((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc'
  have hle : T.Q.c.F ≤ c'.F := h1.trans h3
  have hLL := h2.trans h3
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ := hc c' hle h3
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coeffExt_rationalForms_values_field D G Pl0 T0 A T R F κ v₀ hR hfw hpb i c'.F jL (inC c') hjL
  obtain ⟨lev, hlev⟩ := GlobalTheory.T.exists_level_at_each_index D G Pl0 T0 A T R F κ v₀ hR hfw hpb i
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    (GlobalTheory.SplitReps.reps_exist R i F hR c'.F).2 hV (T.Q.Xo ((i : ℕ) + 1)) c' id dδ
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad t) (hbad t).2.2.2.2
    fun PP hPP => (hrep t).1.2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => exists_thAd R i hR t c0' (h t) (hrep t).1.2.2.1 (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hLL,
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    ⟨GlobalTheory.T.level_coefficient_compatibility D G Pl0 T0 A T R F κ v₀ hR hfw hpb i _ lev hlev,
      GlobalTheory.T.level_coefficient_compatibility D G Pl0 T0 A T R F κ v₀ hR hfw hpb i _ lev hlev⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinnedData
