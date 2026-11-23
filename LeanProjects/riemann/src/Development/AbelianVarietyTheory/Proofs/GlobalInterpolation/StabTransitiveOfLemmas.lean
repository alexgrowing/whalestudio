import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerCompletions
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

namespace GlobalTheory.StabOrbit

open scoped TensorProduct Pointwise Matrix
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J :=
    (show HR R σ J from k).2
  have e : (fun i => sigR R σ (((HA.mat R σ J k).1 *ᵥ x) i)) =
      (fun i => sigR R σ (x i)) ᵥ* Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec _ _ _ i
  rw [hR, hR, hform_eq_dot, hform_eq_dot, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hk]

theorem hR_rat (a : R) (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => a ⊗ₜ[F] z i) = a ⊗ₜ[F] hE σ J x z := by
  simp [hR, hE, Formalism.UG.hform, sigR, JR, inclR, TensorProduct.tmul_sum]

theorem hR_add (x y z : Fin M → R ⊗[F] E) : hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z :=
  hLin_add_left σ J R y z x

theorem hR_smul (c : R ⊗[F] E) (x y : Fin M → R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y :=
  hLin_smul_left σ J R c y x

theorem hR_map {R' : Type} [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') (x y : Fin M → R ⊗[F] E) :
    hR R' σ J (fun i => Algebra.TensorProduct.map φ (AlgHom.id F E) (x i))
      (fun i => Algebra.TensorProduct.map φ (AlgHom.id F E) (y i)) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) (hR R σ J x y) := by
  have hσ : ∀ z, sigR R' σ (Algebra.TensorProduct.map φ (AlgHom.id F E) z) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp [hR, Formalism.UG.hform, hσ, JR, inclR]

end Form

section Length

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem qR_eq_iff (R : Type) [CommRing R] [Algebra F R] (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (y : Fin M → R ⊗[F] E) (b : R) : qR R σ J y = b ↔ hR R σ J y y = b ⊗ₜ[F] (1 : E) := by
  rw [SelfDualLatticeCompare.hR_self R h hJ]
  exact ⟨fun e => e ▸ rfl, fun e =>
    Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective e⟩

end Length

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (v : HeightOneSpectrum (𝓞 F))

theorem mem_OEv_iff (z : Fv F v ⊗[F] E) : z ∈ SelfDualLatticeActions.OEv E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun τ => ?_)
    let ψ : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _
        fun a => by
          change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
          rw [absBar_algebraMap]
          exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z) ?_
    refine IsIntegral.map_of_comp_eq ψ (finEmb F v τ).toRingHom (RingHom.ext fun a => ?_) hz
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ SelfDualLatticeActions.OEv E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : IsIntegral (v.adicCompletionIntegers F) ((1 : Fv F v) ⊗ₜ[F] (x : E)) :=
      (show IsIntegral ℤ (x : E) from x.2).map_of_comp_eq (algebraMap ℤ _)
        (inclR (F := F) (E := E) (Fv F v)) (RingHom.ext_int _ _)
    have h2 := h1.smul (⟨a, ha⟩ : v.adicCompletionIntegers F)
    convert h2 using 1
    change _ ↔ IsIntegral _ (a • ((1 : Fv F v) ⊗ₜ[F] (x : E)))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

def latMax (L : Submodule (𝓞 E) (Fin M → E)) : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M) where
  carrier := latLoc F L v
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' := fun c _ hy => (latLoc F L v).smul_mem ⟨c.1, (mem_OEv_iff v _).1 c.2⟩ hy

theorem isSelfDualLat_latMax (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin M → E)}
    (hL : SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L) : SelfDualLatticeActions.IsSelfDualLat v σ J (latMax v L) := by
  classical
  have hl : Submodule.IsLattice E L := ⟨hL.1, hL.2.1⟩
  have hsd : IsSelfDualAt σ J L v := by
    refine (SelfDual.forall_isSelfDualAt_iff hJ.2 hl).2 (fun y => (hL.2.2 y).trans ?_) v
    exact forall₂_congr fun x _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hl
  have hcol : ∀ j, (fun i => (S.map (inclR (F := F) (Fv F v))) i j) ∈ latMax v L := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  have hsum := SelfDual.eq_sum_col (SelfDual.map_mul_eq_one (F := F) (Fv F v) h1)
  refine ⟨?_, eq_top_iff.2 fun y _ => ?_, fun y => ?_⟩
  · refine Submodule.fg_iff_exists_fin_generating_family.2
      ⟨k, fun j i => (S.map (inclR (F := F) (Fv F v))) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcol j
    · rw [hsum y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_OEv_iff v _).2
        ((SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : SelfDualLatticeActions.OEv E v)
        (Submodule.subset_span ⟨j, rfl⟩)
  · rw [hsum y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · change y ∈ latLoc F L v ↔ _
    rw [hsd]
    simp only [Submodule.mem_top, true_and, mem_OEv_iff]
    exact Iff.rfl

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

omit [NumberField E] in
theorem vecLoc_actVec (v : HeightOneSpectrum (𝓞 F)) (k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) :
    vecLoc v (SelfDualLatticeOrthogonalParts.actVec σ J k y) = SelfDualLatticeActions.act v σ J (projFinLoc σ J v k) (vecLoc v y) :=
  funext fun i => RingHom.map_mulVec
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom _ y i

theorem exists_stab_act_eq (H : SelfDualLatticeActions.SelfDualLatticeLemmas) (h : IsCMExt F E σ)
    (hu : SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E) (hM : 1 ≤ M) (hJ : IsHermND σ J)
    {L : Submodule (𝓞 E) (Fin M → E)} (hL : SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L) {β : F}
    (hβ : β = 1 ∨ β = -1) {y y' : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E (L : Set (Fin M → E))) (hy' : y' ∈ latHat F E (L : Set (Fin M → E)))
    (qy : qR (Af F) σ J y = algebraMap F (Af F) β) (qy' : qR (Af F) σ J y' = algebraMap F (Af F) β) :
    ∃ k ∈ SelfDualLatticeOrthogonalParts.stabHat σ J (L : Set (Fin M → E)), SelfDualLatticeOrthogonalParts.actVec σ J k y = y' := by
  haveI : Submodule.IsLattice E L := ⟨hL.1, hL.2.1⟩
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ SelfDualLatticeActions.latStab v σ J (latMax v L),
      SelfDualLatticeActions.act v σ J g (vecLoc v y) = vecLoc v y' := fun v => by
    obtain ⟨u, hu'⟩ : ∃ u : (v.adicCompletionIntegers F)ˣ,
        ((u : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) β := by
      rcases hβ with rfl | rfl
      · exact ⟨1, by simp⟩
      · exact ⟨-1, by simp⟩
    have hs : ∀ z ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J z = algebraMap F (Af F) β →
        vecLoc v z ∈ SelfDualLatticeActions.sphere v σ J (latMax v L) (u : v.adicCompletionIntegers F) := by
      intro z hz qz
      refine ⟨(mem_latHat_iff hL.1 z).1 hz v, (qR_eq_iff _ h hJ _ _).2 ?_⟩
      refine (hR_map (Af F) σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) z z).trans ?_
      rw [(qR_eq_iff _ h hJ _ _).1 qz, Algebra.TensorProduct.map_tmul, AlgHom.commutes, hu']
      rfl
    exact ((H F E σ h M J hM hJ v (fun w _ => hu w) _ (isSelfDualLat_latMax v hJ hL)).2.2 u).2.2.1
      _ (hs y hy qy) _ (hs y' hy' qy')
  choose g hg hgy using hloc
  obtain ⟨k, hk, -⟩ := existsUnique_projFinLoc_eq σ J L g (Filter.Eventually.of_forall fun v => hg v)
  refine ⟨k, fun z => ?_, funext fun i => LatticeLocalGlobal.ext_components _ _ fun v => ?_⟩
  · simp only [mem_latHat_iff hL.1, vecLoc_actVec, hk]
    exact forall_congr' fun v => hg v _
  · have := vecLoc_actVec v k y
    rw [hk, hgy] at this
    exact congrFun this i

omit [NumberField E] in
theorem latHat_mono {S T : Set (Fin M → E)} (h : S ⊆ T) : latHat F E S ≤ latHat F E T :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

omit [NumberField E] in

theorem proj_mem {L : Submodule (𝓞 E) (Fin M → E)} (hL : SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L) {β : F}
    (hβ : β = 1 ∨ β = -1) {x : Fin M → E} (hx : x ∈ L) (hq : hE σ J x x = algebraMap F E β)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (L : Set (Fin M → E))) :
    y - (inclR (Af F) (algebraMap F E β) * hR (Af F) σ J (SelfDualLatticeOrthogonalParts.ratVec F x) y) • SelfDualLatticeOrthogonalParts.ratVec F x ∈
      latHat F E (SelfDualLatticeOrthogonalParts.perpPart σ J L x) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    have hb : IsIntegral ℤ (algebraMap F E β) ∧ algebraMap F E β * algebraMap F E β = 1 := by
      rcases hβ with rfl | rfl
      · exact ⟨by rw [map_one]; exact isIntegral_one, by simp⟩
      · exact ⟨by rw [map_neg, map_one]; exact isIntegral_one.neg, by simp⟩
    have hc : IsIntegral ℤ (algebraMap F E β * hE σ J x z) := hb.1.mul ((hL.2.2 z).1 hz x hx)
    refine AddSubgroup.subset_closure ⟨a, ha, z - (algebraMap F E β * hE σ J x z) • x,
      ⟨L.sub_mem hz (L.smul_mem (⟨_, hc⟩ : 𝓞 E) hx), ?_⟩, funext fun i => ?_⟩
    · have : ∀ c : E, hE σ J x (z - c • x) = hE σ J x z - c * hE σ J x x := fun c => by
        simp only [hE, hform_eq_dot, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
      rw [this, hq]
      linear_combination (-hE σ J x z) * hb.2
    · have := hR_rat (Af F) σ J a x z
      unfold SelfDualLatticeOrthogonalParts.ratVec
      rw [this]
      generalize algebraMap F E β = b
      simp [inclR, TensorProduct.tmul_sub]
  | zero =>
    have := hR_smul (Af F) σ J 0 (SelfDualLatticeOrthogonalParts.ratVec F x) 0
    rw [zero_smul, zero_mul] at this
    rw [this, mul_zero, zero_smul, sub_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [hR_add, mul_add, add_smul, ← sub_add_sub_comm]
    exact add_mem hy hz
  | neg y _ hy =>
    have := hR_smul (Af F) σ J (-1) (SelfDualLatticeOrthogonalParts.ratVec F x) y
    rw [neg_one_smul, neg_one_mul] at this
    rw [this, mul_neg, neg_smul, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub]
    exact neg_mem hy

omit [NumberField E] in

theorem mem_latHat_perp_iff {L : Submodule (𝓞 E) (Fin M → E)} (hL : SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L)
    {β : F} (hβ : β = 1 ∨ β = -1) {x : Fin M → E} (hx : x ∈ L) (hq : hE σ J x x = algebraMap F E β)
    (y : Fin M → Af F ⊗[F] E) :
    y ∈ latHat F E (SelfDualLatticeOrthogonalParts.perpPart σ J L x) ↔
      y ∈ latHat F E (L : Set (Fin M → E)) ∧ hR (Af F) σ J (SelfDualLatticeOrthogonalParts.ratVec F x) y = 0 := by
  refine ⟨fun hy => ⟨latHat_mono (fun _ h => h.1) hy, ?_⟩, fun hy => ?_⟩
  · induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, z, hz, rfl⟩ := hy
      exact (hR_rat (Af F) σ J a x z).trans (by rw [hz.2, TensorProduct.tmul_zero])
    | zero => simpa using hR_smul (Af F) σ J 0 (SelfDualLatticeOrthogonalParts.ratVec F x) 0
    | add y z _ _ hy hz => rw [hR_add, hy, hz, add_zero]
    | neg y _ hy => rw [← neg_one_smul (Af F ⊗[F] E) y, hR_smul, hy, mul_zero]
  · simpa [hy.2] using proj_mem hL hβ hx hq hy.1

omit [NumberField E] in

theorem stab_inf_eq {L : Submodule (𝓞 E) (Fin M → E)} (hL : SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L)
    {β : F} (hβ : β = 1 ∨ β = -1) {x : Fin M → E} (hx : x ∈ L) (hq : hE σ J x x = algebraMap F E β) :
    SelfDualLatticeOrthogonalParts.stabHat σ J (L : Set (Fin M → E)) ⊓ SelfDualLatticeOrthogonalParts.stabVec σ J x =
      SelfDualLatticeOrthogonalParts.stabHat σ J (SelfDualLatticeOrthogonalParts.perpPart σ J L x) ⊓ SelfDualLatticeOrthogonalParts.stabVec σ J x := by
  have key : ∀ k ∈ SelfDualLatticeOrthogonalParts.stabHat σ J (SelfDualLatticeOrthogonalParts.perpPart σ J L x) ⊓ SelfDualLatticeOrthogonalParts.stabVec σ J x,
      ∀ y ∈ latHat F E (L : Set (Fin M → E)),
        SelfDualLatticeOrthogonalParts.actVec σ J k y ∈ latHat F E (L : Set (Fin M → E)) := by
    rintro k ⟨hk, hkx⟩ y hy
    have h1 := proj_mem hL hβ hx hq hy
    have h2 := latHat_mono (S := SelfDualLatticeOrthogonalParts.perpPart σ J L x) (T := L) (fun _ h => h.1) h1
    have h3 := latHat_mono (S := SelfDualLatticeOrthogonalParts.perpPart σ J L x) (T := L) (fun _ h => h.1) ((hk _).1 h1)
    have h4 := (SelfDualLatticeOrthogonalParts.mem_stabVec σ J x k).1 hkx
    unfold SelfDualLatticeOrthogonalParts.actVec at h3 h4 ⊢
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h4] at h3
    have := add_mem h3 (sub_mem hy h2)
    rwa [sub_sub_cancel, sub_add_cancel] at this
  apply le_antisymm
  · refine fun k hk => ⟨fun y => ?_, hk.2⟩
    have h4 := (SelfDualLatticeOrthogonalParts.mem_stabVec σ J x k).1 hk.2
    have h5 : hR (Af F) σ J (SelfDualLatticeOrthogonalParts.actVec σ J k (SelfDualLatticeOrthogonalParts.ratVec F x)) (SelfDualLatticeOrthogonalParts.actVec σ J k y) = _ :=
      hR_act (Af F) σ J k _ _
    rw [h4] at h5
    rw [mem_latHat_perp_iff hL hβ hx hq, mem_latHat_perp_iff hL hβ hx hq, h5]
    exact and_congr_left' (hk.1 y)
  · refine fun k hk => ⟨fun y => ⟨key k hk y, fun hy => ?_⟩, hk.2⟩
    have := key k⁻¹ (inv_mem hk) _ hy
    rwa [← SelfDualLatticeOrthogonalParts.actVec_mul, inv_mul_cancel, SelfDualLatticeOrthogonalParts.actVec_one] at this

end Global

theorem stabTransitive_of_lemmas (H : SelfDualLatticeActions.SelfDualLatticeLemmas) : SelfDualLatticeOrthogonalParts.StabTransitive := by
  intro F E _ _ _ _ _ σ h hu M J hJ L hL β hβ x hx hq
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exfalso
      have h0 : algebraMap F E β = 0 := by rw [← hq]; simp [hE, Formalism.UG.hform]
      rcases hβ with rfl | rfl <;> simp at h0
    · exact hM
  have hxL : SelfDualLatticeOrthogonalParts.ratVec F x ∈ latHat F E (L : Set (Fin M → E)) :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩
  have hxx : hR (Af F) σ J (SelfDualLatticeOrthogonalParts.ratVec F x) (SelfDualLatticeOrthogonalParts.ratVec F x) =
      algebraMap F (Af F) β ⊗ₜ[F] (1 : E) := by
    refine (hR_rat (Af F) σ J 1 x x).trans ?_
    rw [hq, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : ∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ SelfDualLatticeOrthogonalParts.stabHat σ J (L : Set (Fin M → E)), SelfDualLatticeOrthogonalParts.actVec σ J k (SelfDualLatticeOrthogonalParts.ratVec F x) = y :=
    fun y hy qy => exists_stab_act_eq H h hu hM hJ hL hβ hxL hy ((qR_eq_iff _ h hJ _ _).2 hxx) qy
  refine ⟨h1, Set.ext fun g => ⟨fun hg => ?_, ?_⟩, stab_inf_eq hL hβ hx hq⟩
  · obtain ⟨k, hk, e⟩ := h1 _ hg ((qR_eq_iff _ h hJ _ _).2 ((hR_act (Af F) σ J g⁻¹ _ _).trans hxx))
    refine ⟨g * k, (SelfDualLatticeOrthogonalParts.mem_stabVec σ J x _).2 ?_, k⁻¹, inv_mem hk, mul_inv_cancel_right g k⟩
    rw [SelfDualLatticeOrthogonalParts.actVec_mul, e, ← SelfDualLatticeOrthogonalParts.actVec_mul, mul_inv_cancel, SelfDualLatticeOrthogonalParts.actVec_one]
  · rintro ⟨s, hs, k, hk, rfl⟩
    change SelfDualLatticeOrthogonalParts.actVec σ J (s * k)⁻¹ _ ∈ latHat F E (L : Set (Fin M → E))
    rw [mul_inv_rev, SelfDualLatticeOrthogonalParts.actVec_mul, (SelfDualLatticeOrthogonalParts.mem_stabVec σ J x _).1 (inv_mem hs)]
    exact (inv_mem hk _).1 hxL

end GlobalTheory.StabOrbit
