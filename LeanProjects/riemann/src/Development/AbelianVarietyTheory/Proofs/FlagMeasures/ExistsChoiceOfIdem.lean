import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint

open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem sig_sig (z : I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (sigR I.cm.sig (Af I.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show star (star a) ⊗ₜ b = _
    rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sig_hAf (x y : Fin I.n → I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (hAf I x y) = hAf I y x := by
  unfold hAf hform
  simp only [map_sum, map_mul, sig_sig]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  have h2 : sigR I.cm.sig (Af I.F) (I.J.map (inclE (F := I.F) (Af I.F)) j i) =
      I.J.map (inclE (F := I.F) (Af I.F)) i j := by
    rw [Matrix.map_apply, Matrix.map_apply, ← h]
    rfl
  rw [h2]
  ring

def sigI (I : AutInst) : IntAf I.F I.E →+* IntAf I.F I.E :=
  ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun z =>
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2 z.1 z.2

theorem coe_sigI (z : IntAf I.F I.E) : (sigI I z : I.E ⊗[I.F] Af I.F) = sigR I.cm.sig (Af I.F) z := rfl

theorem sigI_sigI (z : IntAf I.F I.E) : sigI I (sigI I z) = z := Subtype.ext (sig_sig _)

def hI (x y : I.Lf) : IntAf I.F I.E :=
  ⟨hAf I x y, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 y.2 x x.2⟩

theorem coe_hI (x y : I.Lf) : (hI x y : I.E ⊗[I.F] Af I.F) = hAf I x y := rfl

theorem sigI_hI (x y : I.Lf) : sigI I (hI x y) = hI y x := Subtype.ext (sig_hAf _ _)

theorem hI_add (x y z : I.Lf) : hI x (y + z) = hI x y + hI x z := by
  apply Subtype.ext
  show hAf I x (y.1 + z.1) = hAf I x y + hAf I x z
  simp only [hAf, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hI_smul (a : IntAf I.F I.E) (x y : I.Lf) : hI x (a • y) = a * hI x y := by
  apply Subtype.ext
  show hAf I x ((a : I.E ⊗[I.F] Af I.F) • y.1) = a * hAf I x y
  unfold hAf hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem ker_of_card {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {p N : ℕ} (hp : p ≠ 0)
    (r : R →+* ZMod p) (c : M →ₛₗ[r] (Fin N → ZMod p)) (hs : Function.Surjective c)
    (hc : Nat.card (M ⧸ (RingHom.ker r • (⊤ : Submodule R M))) = p ^ N) (y : M) :
    c y = 0 ↔ y ∈ RingHom.ker r • (⊤ : Submodule R M) := by
  set S : Submodule R M := RingHom.ker r • (⊤ : Submodule R M) with hS
  have hle : S ≤ LinearMap.ker c := fun y h => by
    refine Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [LinearMap.mem_ker, map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]
  refine ⟨fun h => ?_, fun h => hle h⟩
  haveI : NeZero p := ⟨hp⟩
  haveI : Finite (M ⧸ S) := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp)
  have hb : Function.Bijective (S.liftQ c hle) := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨fun t => ?_, by rw [hc, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
    obtain ⟨y, rfl⟩ := hs t
    exact ⟨S.mkQ y, rfl⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero]
  exact h

theorem exists_frame_of_dual {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (hn : I.n = N) (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (r : IntAf I.F I.E →+* ZMod p)
    (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (b b' : Fin N → I.Lf)
    (hb : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0) :
    ∃ fr : PlFrame I N p w, fr.r = r ∧ ∀ y i, fr.c y i = r (hI (b' i) y) := by
  let c : I.Lf →ₛₗ[r] (Fin N → ZMod p) :=
    { toFun := fun y i => r (hI (b' i) y)
      map_add' := fun x y => funext fun i => by rw [hI_add, map_add]; rfl
      map_smul' := fun a y => funext fun i => by rw [hI_smul, map_mul]; rfl }
  have hs : Function.Surjective c := fun t => by
    choose s hs using ZMod.ringHom_surjective r
    refine ⟨∑ j, s (t j) • b j, ?_⟩
    rw [map_sum]
    funext i
    have : ∀ j, c (b j) i = if i = j then 1 else 0 := fun j => hb i j
    simp [map_smulₛₗ, hs, this]
  have hk := ker_eq_extId hp.ne_zero r hr
  have hc := GlobalTheory.AdelicLattice.card_quot_extId I p w hp hw
  rw [← hk] at hc
  replace hc := hc.trans (congrArg (p ^ ·) hn)
  refine ⟨⟨r, fun a _ => hr a, c, hs, fun y => ?_⟩, rfl, fun _ _ => rfl⟩
  rw [ker_of_card hp.ne_zero r c hs hc, hk]
  exact Submodule.mem_smul_top_iff _ _ y

theorem conj_reduction {p : ℕ} {w w' : HeightOneSpectrum (𝓞 I.E)} (hc : IsConj I w w')
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (a : 𝓞 I.E) :
    (r.comp (sigI I)) (psi I.F I.E a) = 0 ↔ a ∈ w'.asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have e : sigI I (psi I.F I.E a) = psi I.F I.E (st a) := rfl
  rw [RingHom.comp_apply, e, hr]
  exact hc (st a) a (by rw [hst, star_star])

theorem mem_span_iff {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (S : Set I.Lf) (y : I.Lf) :
    (∃ s ∈ Submodule.span (IntAf I.F I.E) S, y - s ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)) ↔
      fr.c y ∈ Submodule.span (ZMod p) (fr.c '' S) := by
  haveI : RingHomSurjective fr.r := ⟨ZMod.ringHom_surjective _⟩
  rw [← Submodule.map_span, Submodule.mem_map]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← fr.c_eq_zero_iff, map_sub, sub_eq_zero, eq_comm]

theorem glue_mod {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (U : Finset ι) (𝔞 : ι → Ideal R)
    (ε : ι → R) (h2 : ∀ u, 1 - ε u ∈ 𝔞 u) (h3 : ∀ u v, u ≠ v → ε u ∈ 𝔞 v) (T : Submodule R M) (y : M) (s : ι → M)
    (hs : ∀ u ∈ U, s u ∈ T) (hs' : ∀ u ∈ U, y - s u ∈ 𝔞 u • (⊤ : Submodule R M)) :
    ∃ t ∈ T, ∀ u ∈ U, y - t ∈ 𝔞 u • (⊤ : Submodule R M) := by
  refine ⟨∑ v ∈ U, ε v • s v, sum_mem fun v hv => T.smul_mem _ (hs v hv), fun u hu => ?_⟩
  rw [← Finset.add_sum_erase _ _ hu]
  have e : y - (ε u • s u + ∑ v ∈ U.erase u, ε v • s v) =
      (y - s u) + (1 - ε u) • s u - ∑ v ∈ U.erase u, ε v • s v := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  exact sub_mem (add_mem (hs' u hu) (Submodule.smul_mem_smul (h2 u) Submodule.mem_top))
    (sum_mem fun v hv => Submodule.smul_mem_smul (h3 v u (Finset.ne_of_mem_erase hv)) Submodule.mem_top)

theorem mem_mod_iff {m : ℕ} (hm : 1 ≤ m) (hrad : (Ideal.span {(m : 𝓞 I.E)}).IsRadical)
    (T : Submodule (IntAf I.F I.E) I.Lf) (y : I.Lf) :
    (∃ s ∈ T, ∃ z ∈ I.Lf, y.1 = s.1 + (m : I.E ⊗[I.F] Af I.F) • z) ↔
      ∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal →
        ∃ s ∈ T, y - s ∈ extId I u.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) := by
  have crt := GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I m hm hrad
  constructor
  · rintro ⟨s, hs, z, hz, e⟩ u hu
    refine ⟨s, hs, (Submodule.mem_smul_top_iff _ _ _).2 ?_⟩
    exact (crt _ (y - s).2).2 ⟨z, hz, by rw [Submodule.coe_sub, e, add_sub_cancel_left]⟩ u hu
  · intro H
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : m ≠ 0)
    have hfin : {u : HeightOneSpectrum (𝓞 I.E) | (m : 𝓞 I.E) ∈ u.asIdeal}.Finite :=
      (Ideal.finite_factors h0).subset fun u hu => Ideal.dvd_span_singleton.2 hu
    choose! s hs hs' using H
    choose ε h1 h2 h3 h4 using GlobalTheory.RowLev.exists_prime_idempotent I
    obtain ⟨t, hT, key⟩ := glue_mod hfin.toFinset (fun u => extId I u.asIdeal) ε h2 (fun u v h => h3 u v h.symm) T y s
      (fun v hv => hs v (hfin.mem_toFinset.1 hv)) (fun v hv => hs' v (hfin.mem_toFinset.1 hv))
    obtain ⟨z, hz, e⟩ := (crt _ (y - t).2).1
      fun u hu => (Submodule.mem_smul_top_iff _ _ _).1 (key u (hfin.mem_toFinset.2 hu))
    have e' : y.1 - t.1 = (m : I.E ⊗[I.F] Af I.F) • z := e
    exact ⟨t, hT, z, hz, sub_eq_iff_eq_add'.1 e'⟩

theorem entry_eq {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (b : Fin N → I.Lf)
    (hb : ∀ j, fr.c (b j) = Pi.single j 1) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin N) (Fin N) (ZMod p)}
    (hM : fr.ActsAs x M) (i j : Fin N) : M i j = fr.c (latEnd hx (b j)) i := by
  have := hM (b j) (mulVec_mem hx (b j).2)
  rw [hb, Matrix.mulVec_single_one] at this
  exact (congrFun this i).symm

theorem hI_latEnd {x : I.Gf} (hx : x ∈ I.Kset) (y z : I.Lf) :
    hI (latEnd hx y) z = hI y (latEnd (x := x⁻¹) ((Ksub I).inv_mem hx) z) := by
  apply Subtype.ext
  have := GlobalTheory.Mem.RowsBundle.hAf_inv_mulVec x⁻¹ y.1 z.1
  rw [inv_inv] at this
  exact this

theorem rows_unitri {R : Type} [CommRing R] {N : ℕ} (A B : Matrix (Fin N) (Fin N) R) (h : B * A = 1) (t : ℕ)
    (hB : ∀ i : Fin N, t ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0) :
    ∀ i : Fin N, t ≤ i.1 → A i i = 1 ∧ ∀ j, j < i → A i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    intro hi
    have key : ∀ j, j ≤ i → A i j = (1 : Matrix (Fin N) (Fin N) R) i j := fun j hj => by
      rw [← h, Matrix.mul_apply, Finset.sum_eq_single i, (hB i hi).1, one_mul]
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with h1 | h1
        · rw [(hB i hi).2 l h1, zero_mul]
        · rw [(ih l h1 (hi.trans h1.le)).2 j (hj.trans_lt h1), mul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    exact ⟨by rw [key i le_rfl, Matrix.one_apply_eq], fun j hj => by rw [key j hj.le, Matrix.one_apply_ne hj.ne']⟩

theorem exists_choice_of_idem (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hrad : ∀ k, (Ideal.span {((g k : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g k)
    {f : ℕ} (hf : 0 < f)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (ε : IntAf I.F I.E) (h1 : ε * ε = ε) (h2 : ε * sigI I ε = 0)
    (h3 : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε - sigI I ε ∈ extId I v.asIdeal) :
    ∃ w : ∀ _ : Fin 2, Fin f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin f) w ∧
      ∀ k v, 1 - ε ∈ extId I (w k v).asIdeal := by
  obtain ⟨cj, hc, hconj, hmem⟩ := GlobalTheory.Mem.RowsBundle.exists_conj_involution I
  have hsig := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2
  have hsig' : ∀ u z, z ∈ extId I u.asIdeal → sigI I z ∈ extId I (cj u).asIdeal := fun u z hz => by
    obtain ⟨z', h, e⟩ := hsig u (cj u) ((hconj _ _).2 rfl) z hz
    rwa [show sigI I z = z' from Subtype.ext e.symm]
  have hpr : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → (extId I v.asIdeal).IsPrime := by
    intro k v hv
    haveI : Fact (g k).Prime := ⟨hg k⟩
    obtain ⟨r, hr⟩ := exists_reduction (F := I.F) (g k) (hg k) v (hsp k v hv)
    rw [← ker_eq_extId (hg k).ne_zero r hr]
    exact RingHom.ker_isPrime r
  let Pl : Fin 2 → Type := fun k =>
    {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ 1 - ε ∈ extId I v.asIdeal}
  have hn : ∀ k (v v' : Pl k), v'.1 ≠ cj v.1 := fun k v v' e => by
    have a1 := hsig' _ _ v.2.2
    rw [← e, map_sub, map_one] at a1
    have a2 := Ideal.add_mem _ v'.2.2 (Ideal.mul_mem_left _ ε a1)
    rw [mul_sub, h2, mul_one, sub_zero, sub_add_cancel] at a2
    exact (hpr k _ v'.2.1).ne_top ((Ideal.eq_top_iff_one _).2 a2)
  have hcov : ∀ k (u : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal →
      ∃ v : Pl k, u = v.1 ∨ u = cj v.1 := fun k u hu => by
    have h0 : ε * (1 - ε) ∈ extId I u.asIdeal := by rw [mul_sub, h1, mul_one, sub_self]; exact zero_mem _
    rcases (hpr k u hu).mem_or_mem h0 with h | h
    · refine ⟨⟨cj u, hmem _ _ hu, ?_⟩, Or.inr (hc u).symm⟩
      have a1 := hsig' _ _ (Ideal.add_mem _ (h3 k u hu) h)
      rwa [show 1 - ε - sigI I ε + ε = 1 - sigI I ε by ring, map_sub, map_one, sigI_sigI] at a1
    · exact ⟨⟨u, hu, h⟩, Or.inl rfl⟩
  have hP : ∀ k, Nat.card (Pl k) = f := fun k =>
    (GlobalTheory.Mem.RowsBundle.meets_iff_card cj hc _ (hmem (g k)) hf (hcard k) (fun v : Pl k => v.1) (fun v => v.2.1)
      Subtype.val_injective (hn k)).1 (hcov k)
  have e : ∀ k, Fin f ≃ Pl k := fun k =>
    haveI : Finite (Pl k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  refine ⟨fun k v => (e k v).1, ⟨hg, hne, hrad, fun k v => ⟨(e k v).2.1, hsp k _ (e k v).2.1⟩,
    fun k => Subtype.val_injective.comp (e k).injective, fun k v v' h => hn k _ _ ((hconj _ _).1 h),
    fun k u hu => ?_⟩, fun k v => (e k v).2.2⟩
  obtain ⟨v, hv⟩ := hcov k u hu
  obtain ⟨v, rfl⟩ := (e k).surjective v
  exact ⟨v, hv.imp id (hconj _ _).2⟩

end GlobalTheory.RowIndex
