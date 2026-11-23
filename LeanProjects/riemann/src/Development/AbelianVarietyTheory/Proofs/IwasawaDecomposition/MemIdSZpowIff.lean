import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InTypeIsoSortedPos
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem int_mulVec (S : Subring R) {M : Matrix (Fin n) (Fin n) R} (hM : ∀ i j, M i j ∈ S) {z : Fin n → R}
    (hz : ∀ i, z i ∈ S) (i : Fin n) : (M *ᵥ z) i ∈ S :=
  S.sum_mem (t := Finset.univ) fun j _ => mul_mem (hM i j) (hz j)

theorem exists_adapted (S : Subring R) {ε : R} (hε : ε * ε = ε) (hεS : ε ∈ S) {u u' : Fin n → R} (hu : ∀ i, u' i * u i = 1)
    (b : GL (Fin n) R) (hb : ε • (b.1 - 1) = b.1 - 1)
    (hD : GlobalTheory.DivDual.Dv (fun z => ∀ i, z i ∈ S) (· ∈ S) ε u b.1) :
    ∃ k : GL (Fin n) R, (∀ i j, k.1 i j ∈ S) ∧ (∀ i j, (k⁻¹).1 i j ∈ S) ∧
      ∀ z : Fin n → R, (∀ i, ((b⁻¹).1 *ᵥ z) i ∈ S) ↔ ∀ i, (ε * u' i + (1 - ε)) * ((k⁻¹).1 *ᵥ z) i ∈ S := by
  classical
  obtain ⟨B, h1, h2, h3, h4⟩ := hD
  have h1ε : 1 - ε ∈ S := sub_mem (one_mem _) hεS
  set M : Matrix (Fin n) (Fin n) R := ε • B + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) with hM
  have hMv : ∀ z, M *ᵥ z = ε • B *ᵥ z + (1 - ε) • z := fun z => by
    rw [hM, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  have hsingle : ∀ j i : Fin n, (Pi.single j 1 : Fin n → R) i ∈ S := fun j i => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have mix : ∀ z w : Fin n → R, (∀ i, z i ∈ S) → (∀ i, w i ∈ S) → ∀ i, (ε • z + (1 - ε) • w) i ∈ S :=
    fun z w hz hw i => add_mem (mul_mem hεS (hz i)) (mul_mem h1ε (hw i))
  have e1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε, mul_one, sub_self]
  have e2 : (1 - ε) * ε = 0 := by rw [mul_comm, e1]
  have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  have hMmix : ∀ z w : Fin n → R, M *ᵥ (ε • z + (1 - ε) • w) = ε • B *ᵥ z + (1 - ε) • w := fun z w => by
    rw [hMv, mulVec_add, mulVec_smul, mulVec_smul]
    simp only [smul_add, smul_smul, hε, e1, e2, e3, zero_smul, add_zero, zero_add]
  have hMS : ∀ i j, M i j ∈ S := fun i j => by
    have := h1 _ (hsingle j) i
    rw [mulVec_single_one] at this
    exact add_mem this (mul_mem h1ε (by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _))
  choose c hc hce using fun j => h2 _ (hsingle j)
  set M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (ε • c j + (1 - ε) • (Pi.single j 1 : Fin n → R)) i with hM'
  have hMM : M * M' = 1 := by
    ext i j
    have := congrFun (hMmix (c j) (Pi.single j 1)) i
    rw [← hce, ← add_smul, add_sub_cancel, one_smul] at this
    rw [Matrix.one_apply, ← Pi.single_apply (M := R) j 1 i, ← this]
    rfl
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hbv : ∀ z, b.1 *ᵥ z = ε • b.1 *ᵥ z + (1 - ε) • z := fun z => by
    have := congrArg (· *ᵥ z) hb
    simp only [smul_mulVec, sub_mulVec, one_mulVec] at this
    rw [sub_smul, one_smul, smul_sub] at *
    linear_combination (exp := 1) -this
  have hDw : ∀ z w : Fin n → R, ∀ i, (ε * u' i + (1 - ε)) * (ε • (fun i => u i * z i) + (1 - ε) • w) i =
      (ε • z + (1 - ε) • w) i := fun z w i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ε * ε * z i) * hu i + (z i - u' i * w i - u i * z i + w i) * hε
  refine ⟨⟨M, M', hMM, hMM'⟩, hMS, fun i j => mix _ _ (hc j) (hsingle j) i, fun z => ⟨fun hz i => ?_, fun hz i => ?_⟩⟩
  · obtain ⟨w, hw, e⟩ := h3 _ hz
    have ez : z = M *ᵥ (ε • (fun i => u i * w i) + (1 - ε) • ((b⁻¹).1 *ᵥ z)) := by
      rw [hMmix, ← e, ← hbv, mulVec_mulVec, Units.mul_inv, one_mulVec]
    show _ * (M' *ᵥ z) i ∈ S
    have : M' *ᵥ z = ε • (fun i => u i * w i) + (1 - ε) • ((b⁻¹).1 *ᵥ z) := by
      conv_lhs => rw [ez]
      rw [mulVec_mulVec, hMM', one_mulVec]
    rw [this, hDw]
    exact mix _ _ hw hz i
  · set w : Fin n → R := fun i => (ε * u' i + (1 - ε)) * (M' *ᵥ z) i with hw
    have hz' : ∀ i, w i ∈ S := hz
    obtain ⟨y, hy, e⟩ := h4 w hz'
    have e4 : M' *ᵥ z = ε • (fun i => u i * w i) + (1 - ε) • w := by
      funext i
      simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(ε * ε * (M' *ᵥ z) i)) * hu i + ((M' *ᵥ z) i * (u i + u' i - 2)) * hε
    have ez : z = b.1 *ᵥ (ε • y + (1 - ε) • w) := by
      rw [hbv, mulVec_add, mulVec_smul, mulVec_smul]
      simp only [smul_add, smul_smul, hε, e1, e2, e3, zero_smul, add_zero, zero_add]
      rw [e, ← hMmix, ← e4, mulVec_mulVec, hMM, one_mulVec]
    rw [ez, mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact mix _ _ hy hz' i

end Ring

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_approx (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥)
    (u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hu : ∀ i, u i ∈ Formalism.L2.Herm.intAf F E) :
    ∃ v ∈ Formalism.UG.CS.globLat x (stdLat E n), ∀ i, ∃ t ∈ idS F J, u i = pullV x v i + (t : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have hxu : (x⁻¹).1 *ᵥ (x.1 *ᵥ u) = u := by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have h1 : x.1 *ᵥ u ∈ Submodule.span (Formalism.L2.Herm.intAf F E)
      ((fun v : Fin n → E => fun i => iA F E (v i)) '' (Formalism.UG.CS.globLat x (stdLat E n) : Set (Fin n → E))) := by
    rw [Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
      (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x _]
    rw [mem_latS_std, hxu]
    exact hu
  rw [← hxu]
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ Formalism.UG.CS.globLat x (stdLat E n), ∀ i, ∃ t ∈ idS F J,
    ((x⁻¹).1 *ᵥ z) i = pullV x v i + (t : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ h1
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, fun i => ⟨0, zero_mem _, (add_zero _).symm⟩⟩
  · refine ⟨0, zero_mem _, fun i => ⟨0, zero_mem _, ?_⟩⟩
    rw [mulVec_zero, show pullV x 0 = 0 from map_zero (pullVAdd x)]
    simp
  · rintro a b _ _ ⟨v, hv, h⟩ ⟨w, hw, h'⟩
    refine ⟨v + w, add_mem hv hw, fun i => ?_⟩
    obtain ⟨t, ht, e⟩ := h i
    obtain ⟨t', ht', e'⟩ := h' i
    refine ⟨t + t', add_mem ht ht', ?_⟩
    rw [mulVec_add, Pi.add_apply, e, e', pullV_add, Subring.coe_add]
    ring
  · rintro c a _ ⟨v, hv, h⟩
    obtain ⟨b, hb⟩ := Formalism.L2.DIV.cmpS_surj (F := F) J hJ (Ideal.Quotient.mk _ c)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : c - oToS F E b ∈ idS F J := Ideal.Quotient.eq.1 hb.symm
    refine ⟨b • v, Submodule.smul_mem _ b hv, fun i => ?_⟩
    obtain ⟨t, ht, e⟩ := h i
    refine ⟨(c - oToS F E b) * ⟨_, (mem_globLat x v).1 hv i⟩ + c * t,
      add_mem (Ideal.mul_mem_right _ _ hb') (Ideal.mul_mem_left _ _ ht), ?_⟩
    rw [Subring.smul_def, mulVec_smul, Pi.smul_apply, e, pullV_osmul, iA_coe, smul_eq_mul]
    push_cast
    ring

def resI (F : Type) [Field F] [NumberField F] [Algebra F E] (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ J :=
  ((RingEquiv.ofBijective (cmpS F J) (Formalism.L2.DIV.cmpS_bij (F := F) J hJ)).symm : _ →+* 𝓞 E ⧸ J).comp
    (Ideal.Quotient.mk (idS F J))

omit [StarRing E] in
theorem resI_oToS (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (a : 𝓞 E) : resI F J hJ (oToS F E a) = Ideal.Quotient.mk J a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F J) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

omit [StarRing E] in
theorem resI_eq_zero (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (t : Formalism.L2.Herm.intAf F E) : resI F J hJ t = 0 ↔ t ∈ idS F J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold resI
  rw [RingHom.comp_apply]
  exact map_eq_zero_iff _ (RingEquiv.injective _)

def coordMod (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (J : Fin n → Ideal (𝓞 E)) (hJ : ∀ i, J i ≠ ⊥) :
    Formalism.UG.CS.globLat x (stdLat E n) →ₗ[𝓞 E] ∀ i, 𝓞 E ⧸ J i where
  toFun v i := resI F (J i) (hJ i) ⟨pullV x v.1 i, (mem_globLat x v.1).1 v.2 i⟩
  map_add' v w := by
    funext i
    rw [Pi.add_apply, ← map_add]
    congr 1
    exact Subtype.ext (pullV_add x v.1 w.1 i)
  map_smul' a v := by
    funext i
    show _ = Ideal.Quotient.mk (J i) a * _
    rw [← resI_oToS (F := F) (J i) (hJ i), ← map_mul]
    congr 1
    exact Subtype.ext (pullV_osmul x a v.1 i)

theorem coordMod_surj (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (J : Fin n → Ideal (𝓞 E)) (hJ : ∀ i, J i ≠ ⊥) :
    Function.Surjective (coordMod x J hJ) := by
  intro c
  choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)
  obtain ⟨v, hv, h⟩ := exists_approx x (∏ i, J i) (Finset.prod_ne_zero_iff.2 fun i _ => hJ i)
    (fun i => iA F E (algebraMap (𝓞 E) E (a i))) fun i => iA_mem (a i)
  refine ⟨⟨v, hv⟩, funext fun i => ?_⟩
  obtain ⟨t, ht, e⟩ := h i
  have ht' : t ∈ idS F (J i) := Ideal.map_mono (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))) ht
  have e' : oToS F E (a i) = ⟨pullV x v i, (mem_globLat x v).1 hv i⟩ + t := Subtype.ext e
  rw [← ha, ← resI_oToS (F := F) (J i) (hJ i), e', map_add, (resI_eq_zero _ _ t).2 ht', add_zero]
  rfl

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F}

theorem IdemOf.mem_idS_zpow_iff (h : IdemOf F Q ε) {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (d : ℤ)
    (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ d.toNat) ↔ (ε * iA F E (((ϖ : E) ^ d)⁻¹) + (1 - ε)) * a ∈ Formalism.L2.Herm.intAf F E := by
  rw [add_mul, add_mem_cancel_right (mul_mem h.one_sub_mem a.2)]
  obtain ⟨m, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [Int.toNat_natCast, zpow_natCast]
    exact h.mem_idS_pow_iff h1 h2 m a
  · rw [Int.toNat_neg_natCast, _root_.zpow_neg, inv_inv, zpow_natCast]
    refine iff_of_true ?_ (mul_mem (mul_mem h.mem ?_) a.2)
    · unfold idS
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
    · rw [map_pow]; exact pow_mem (iA_mem ϖ) m

theorem quot_equiv (h : IdemOf F Q ε) {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (d : Fin n → ℤ)
    (y b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hb : ε • (b.1 - 1) = b.1 - 1)
    (hD : GlobalTheory.DivDual.Dv (fun z => ∀ i, z i ∈ Formalism.L2.Herm.intAf F E) (· ∈ Formalism.L2.Herm.intAf F E) ε
      (fun i => iA F E ((ϖ : E) ^ d i)) b.1) :
    Nonempty ((Formalism.UG.CS.globLat y (stdLat E n) ⧸ (Formalism.UG.CS.globLat (y * b) (stdLat E n) ⊓
      Formalism.UG.CS.globLat y (stdLat E n)).comap (Formalism.UG.CS.globLat y (stdLat E n)).subtype) ≃ₗ[𝓞 E]
        ∀ i, 𝓞 E ⧸ Q.asIdeal ^ (d i).toNat) := by
  obtain ⟨k, k1, k2, hk⟩ := exists_adapted _ h.1 h.mem (u' := fun i => iA F E (((ϖ : E) ^ d i)⁻¹))
    (fun i => by rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ (IdemOf.unif_ne h2)), map_one]) b hb hD
  have pm : ∀ (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) v, pullV (y * g) v = (g⁻¹).1 *ᵥ pullV y v := fun g v => by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hN : Formalism.UG.CS.globLat y (stdLat E n) = Formalism.UG.CS.globLat (y * k) (stdLat E n) := by
    ext v
    rw [mem_globLat, mem_globLat, pm]
    refine ⟨int_mulVec _ k2, fun hv => ?_⟩
    have := int_mulVec _ k1 hv
    rwa [mulVec_mulVec, Units.mul_inv, one_mulVec] at this
  have hJ : ∀ i, Q.asIdeal ^ (d i).toNat ≠ ⊥ := fun i => pow_ne_zero _ Q.ne_bot
  rw [hN]
  refine ⟨(Submodule.quotEquivOfEq _ _ ?_).trans ((coordMod (y * k) _ hJ).quotKerEquivOfSurjective (coordMod_surj _ _ hJ))⟩
  ext v
  rw [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply, and_iff_left v.2, mem_globLat, pm, hk, ← pm,
    LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun i => ?_
  exact (((resI_eq_zero _ (hJ i) _).trans (h.mem_idS_zpow_iff h1 h2 (d i)
    ⟨pullV (y * k) v.1 i, (mem_globLat _ v.1).1 v.2 i⟩))).symm

end Lat

section Lists

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def posPart (d : List ℤ) : List ℕ := (d.map Int.toNat).filter fun a => 0 < a

theorem pi_equiv_posPart (P : Ideal (𝓞 E)) {n : ℕ} (d : List ℤ) (hd : d.length = n) :
    Nonempty ((∀ i : Fin n, 𝓞 E ⧸ P ^ (d.getD i.1 0).toNat) ≃ₗ[𝓞 E] inType P (posPart d)) := by
  obtain ⟨e⟩ := GlobalTheory.InertTypeIso.iso_filter_pos P (d.map Int.toNat)
  have hl : (d.map Int.toNat).length = n := by rw [List.length_map, hd]
  suffices h : (∀ i : Fin n, 𝓞 E ⧸ P ^ (d.getD i.1 0).toNat) ≃ₗ[𝓞 E] inType P (d.map Int.toNat) from ⟨h.trans e⟩
  refine (LinearEquiv.piCongrLeft' (𝓞 E) _ (finCongr hl.symm)).trans (LinearEquiv.piCongrRight fun i => ?_)
  refine Submodule.quotEquivOfEq _ _ ?_
  congr 1
  have hi : i.1 < d.length := i.2.trans_eq (List.length_map _)
  simp [List.getElem?_eq_getElem hi]

theorem posPart_pos (d : List ℤ) : ∀ a ∈ posPart d, 0 < a := fun a ha => by
  simpa using (List.mem_filter.1 ha).2

theorem posPart_pairwise {d : List ℤ} (h : d.Pairwise fun a b => b ≤ a) : (posPart d).Pairwise (· ≥ ·) := by
  refine List.Pairwise.filter _ ?_
  rw [List.pairwise_map]
  exact h.imp fun h => Int.toNat_le_toNat h

theorem count_posPart (d : List ℤ) {a : ℤ} (ha : 0 < a) : (posPart d).count a.toNat = d.count a := by
  unfold posPart
  rw [List.count_filter (by simpa using ha), List.count_eq_countP, List.countP_map, List.count_eq_countP]
  refine List.countP_congr fun x _ => ?_
  simp only [Function.comp_apply, beq_iff_eq]
  omega

theorem count_neg {d : List ℤ} (h : (d.map Neg.neg).reverse = d) (a : ℤ) : d.count (-a) = d.count a := by
  conv_lhs => rw [← h]
  rw [List.count_reverse]
  exact List.count_map_of_injective d _ neg_injective a

theorem eq_of_posPart_eq {d d' : List ℤ} (h : d.Pairwise fun a b => b ≤ a) (h' : d'.Pairwise fun a b => b ≤ a)
    (hl : d.length = d'.length) (s : (d.map Neg.neg).reverse = d) (s' : (d'.map Neg.neg).reverse = d')
    (e : posPart d = posPart d') : d = d' := by
  have c1 : ∀ a : ℤ, a ≠ 0 → d.count a = d'.count a := fun a ha => by
    rcases lt_or_gt_of_ne ha with ha | ha
    · rw [← count_neg s, ← count_neg s', ← count_posPart d (neg_pos.2 ha), ← count_posPart d' (neg_pos.2 ha), e]
    · rw [← count_posPart d ha, ← count_posPart d' ha, e]
  have p1 : (d.filter fun a => ¬ (a == 0)).Perm (d'.filter fun a => ¬ (a == 0)) := by
    rw [List.perm_iff_count]
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [List.count_eq_zero_of_not_mem (by simp), List.count_eq_zero_of_not_mem (by simp)]
    · rw [List.count_filter (by simpa using ha), List.count_filter (by simpa using ha), c1 a ha]
  have c0 : d.count 0 = d'.count 0 := by
    have a1 := List.length_eq_countP_add_countP (fun a : ℤ => a == 0) (l := d)
    have a2 := List.length_eq_countP_add_countP (fun a : ℤ => a == 0) (l := d')
    have a3 := p1.length_eq
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter] at a3
    rw [List.count_eq_countP, List.count_eq_countP]
    omega
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) h h' (List.perm_iff_count.2 fun a => ?_)
  by_cases ha : a = 0
  · rw [ha, c0]
  · exact c1 a ha

end Lists

end GlobalTheory.InertNbr
