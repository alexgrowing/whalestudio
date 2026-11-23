import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueCoprimeConjugation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleBranchingIffIsBranching
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

noncomputable section

namespace UpperTheory.GalS

theorem om_gen_inj {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k))
    {γ : GE D.nd} (hγ : TameGenAt (D.nd.plOm.1 w) γ) {x y : Fb (D.host.g k) (D.host.g_prime k)} (hx : x ≠ 0) (hy : y ≠ 0)
    (e : P.om k w x γ = P.om k w y γ) : x = y := by
  by_contra hne
  obtain ⟨σ, hσ, hd⟩ := P.om_inj k w hw x y hx hy hne
  obtain ⟨U, hU, hUx⟩ := P.om_open k w x hx
  obtain ⟨V, hV, hVy⟩ := P.om_open k w y hy
  have inv : ∀ z, z ≠ 0 → ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), P.om k w z a * P.om k w z a⁻¹ = 1 := fun z hz a ha => by
    rw [← P.om_mul k w z hz a ha _ (inv_mem ha), mul_inv_cancel, P.om_one k w z hz]
  let K : Subgroup (GE D.nd) :=
    { carrier := {s | s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) ∧ P.om k w x s = P.om k w y s}
      one_mem' := ⟨one_mem _, by rw [P.om_one k w x hx, P.om_one k w y hy]⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [P.om_mul k w x hx a ha.1 b hb.1, P.om_mul k w y hy a ha.1 b hb.1, ha.2, hb.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have h1 := inv x hx a ha.1
        have h2 := inv y hy a ha.1
        rw [ha.2] at h1
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)⟩ }
  have hK : Subgroup.closure (insert γ (wildSet D.nd (D.nd.plOm.1 w))) ≤ K := by
    rw [Subgroup.closure_le]
    rintro s (rfl | hs)
    · exact ⟨hγ.1, e⟩
    · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hs, by rw [P.om_wild k w hw x hx s hs, P.om_wild k w hw y hy s hs]⟩
  have hO : IsOpen {s : GE D.nd | σ⁻¹ * s ∈ (U : Set (GE D.nd)) ∩ V} := (hU.inter hV).preimage (continuous_mul_left σ⁻¹)
  obtain ⟨s, hs1, hs2⟩ := mem_closure_iff.1 (hγ.2 hσ) _ hO (by simp [U.one_mem, V.one_mem])
  have hs := hK hs2
  have hi : σ⁻¹ * s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := mul_mem (inv_mem hσ) hs.1
  have e1 := P.om_mul k w x hx σ hσ _ hi
  have e2 := P.om_mul k w y hy σ hσ _ hi
  rw [mul_inv_cancel_left, hUx _ hs1.1 hi, mul_one] at e1
  rw [mul_inv_cancel_left, hVy _ hs1.2 hi, mul_one] at e2
  exact hd (e1.symm.trans (hs.2.trans e2))

theorem om_pow {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) {γ : GE D.nd}
    (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) {x : Fb (D.host.g k) (D.host.g_prime k)} (hx : x ≠ 0) (n : ℕ) (h : x ^ n = 1) :
    P.om k w x γ ^ n = 1 := by
  have h1 : P.om k w 1 γ = 1 := by
    have a := P.tameInertiaChar_mul_root k w 1 1 one_ne_zero one_ne_zero γ hγ
    have b := P.om_mul k w 1 one_ne_zero γ hγ _ (inv_mem hγ)
    rw [mul_inv_cancel, P.om_one k w 1 one_ne_zero] at b
    rw [mul_one] at a
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one b.symm) (a.symm.trans (mul_one _).symm)
  have h2 : ∀ m : ℕ, P.om k w (x ^ m) γ = P.om k w x γ ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ m ih => rw [pow_succ, pow_succ, P.tameInertiaChar_mul_root k w _ _ (pow_ne_zero _ hx) hx γ hγ, ih]
  rw [← h2, h, h1]

theorem card_rootsBar {p : ℕ} [Fact p.Prime] (a : (ZMod p)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]

theorem nc_of_roots {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k))
    (y : D.naut.LP w) (hm : D.naut.mono0 y) (hdeg : (D.naut.items₂ k w y).natDegree = D.naut.lpDim y)
    (hle : D.naut.lpDim y ≤ D.R.nV)
    (hnz : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y), x ≠ 0)
    (hrep : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ x, x ::ₘ {x} ≤ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y) → x ^ (D.host.g k - 1) = 1) :
    Nc D.nd D.naut y := by
  classical
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨fun σ hσ hwild => ?_, hm, fun γ hγ z hz => ?_⟩
  · rw [P.inertiaCharpoly_eigenvalues k w hw _ hdeg σ hσ,
      Multiset.map_congr rfl (fun x hx => by rw [P.om_wild k w hw x (hnz x hx) σ hwild, C_1]),
      Multiset.map_const', Multiset.prod_replicate, card_rootsBar, hdeg]
  · rw [P.inertiaCharpoly_eigenvalues k w hw _ hdeg γ hγ.1, thr_split (D.host.g_prime k) hw (D.nd.g_split k) (DiscreteGroups.sglob.DzType.big_of_le_nV D k hle)] at hz
    set M := Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y) with hM
    have e : (M.map fun x => X - C (P.om k w x γ)).prod = ((M.map fun x => P.om k w x γ).map fun c => X - C c).prod := by
      rw [Multiset.map_map]; rfl
    rw [e, ← count_roots, roots_multiset_prod_X_sub_C] at hz
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.count_pos.1 (by omega : 0 < Multiset.count z (M.map fun x => P.om k w x γ)))
    rw [Multiset.count_map_eq_count _ _ (fun a ha b hb h => om_gen_inj P k w hw hγ (hnz a ha) (hnz b hb) h) x hx] at hz
    rw [GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw]
    exact om_pow P k w hγ.1 (hnz x hx) _ (hrep x (Multiset.le_count_iff_replicate_le.1 hz))

theorem nc_of_label {D : D7} (P : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ P) (h1 : SumRepresentations.adm1 D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (PI : D.naut.AV i) (τ : (P.lz k).Irr D.R.r) (hτ : τ ∈ P.kty i PI k v) (hsq : Squarefree ((P.lz k).lab τ))
    (hroot : ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k)))
    (w : PlE D.host) (hw : w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w) :
    Nc D.nd D.naut (D.naut.locV i PI w) := by
  classical
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  obtain ⟨Pa, -, -, hr, hs, -⟩ := h1 i PI
  have hdim : ∀ w, IsSplitPl D.host w → D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := fun w h => by
    rw [← hs w h, GlobalTheory.InertialTypesCmp.lpDim_isoLoc, hr]
  have hne : (P.lz k).lab τ ≠ 0 := ((P.lz k).lab_spec τ).1.ne_zero
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have hrep : ∀ x, 2 ≤ (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).count x →
      x ^ (D.host.g k - 1) = 1 := by
    intro x hx
    unfold Formalism.CyclotomicNorms.rootsBar at hx
    have hnd := nodup_roots ((PerfectField.separable_iff_squarefree.2 hsq).map
      (f := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))))
    rw [Polynomial.map_mul, roots_mul (by
        rw [← Polynomial.map_mul]
        exact Polynomial.map_ne_zero (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero)),
      Multiset.count_add, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C] at hx
    have h1 := Multiset.nodup_iff_count_le_one.1 hnd x
    have h2 : x ∈ D.R.t • ({algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))} : Multiset _) :=
      Multiset.count_pos.1 (by omega)
    rw [Multiset.mem_singleton.1 (Multiset.mem_of_mem_nsmul h2), ← map_pow, ZMod.pow_card_sub_one_eq_one u.ne_zero, map_one]
  rcases hw with rfl | hc
  · refine nc_of_roots P k _ (D.naut.plGw_over k v) _ hm0 ?_ (hdim _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)).le (by rw [hlab]; exact hroot0)
      (fun x hx => hrep x (Multiset.le_count_iff_replicate_le.2 (by rw [hlab] at hx; exact hx)))
    rw [hdim _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
      ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    rfl
  · obtain ⟨hw, hs'⟩ := GlobalTheory.TypeAbove.conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    refine nc_of_roots P k w hw _ hm (hdeg.trans (hdim w hs').symm) (hdim w hs').le ?_ fun x hx => ?_
    · rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz)
    · rw [hroots] at hx
      have h2 := Multiset.le_count_iff_replicate_le.2 (show Multiset.replicate 2 x ≤ _ from hx)
      rw [← inv_inv x, Multiset.count_map_eq_count' _ _ inv_injective] at h2
      have h3 := hrep _ h2
      rwa [inv_pow, inv_eq_one] at h3

end UpperTheory.GalS
