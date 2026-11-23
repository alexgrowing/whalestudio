import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne

open Polynomial GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.GreenSeries

section Generic
open GlobalTheory.BadShare GlobalTheory.BadShare.Basic
variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def levGen (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (hN : 0 < N) : Lev g N := ⟨false, 0, 0, by omega, ψ, hψ, fun _ => 1⟩

theorem levGen_mem_iff (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (hN : 0 < N) (x : GG g N) :
    (levGen ψ hψ hN).Mem x ↔ Formalism.MainNotions.ArithmeticCylinders.IsUniUp (x : Matrix (Fin N) (Fin N) (ZMod g)) := by
  simp only [Lev.Mem, IsUp, levGen, Formalism.MainNotions.ArithmeticCylinders.IsUniUp, Bool.false_eq_true, false_implies, and_true]
  constructor
  · rintro ⟨h1, h2⟩ a b
    exact ⟨h2 a b, fun h => h ▸ h1 a⟩
  · intro h
    exact ⟨fun a => (h a a).2 rfl, fun a b hb => (h a b).1 hb⟩

theorem inner_sum (M : Matrix (Fin N) (Fin N) (ZMod g)) (a : Fin N) :
    (∑ b : Fin N, if (b : ℕ) = a + 1 then M a b else 0) = Formalism.MainNotions.ArithmeticCylinders.entN M a (a + 1) := by
  unfold Formalism.MainNotions.ArithmeticCylinders.entN
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a + 1, h.2⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro e; exact hb (Fin.ext e)
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]; intro e; exact h ⟨a.2, e ▸ b.2⟩

theorem levGen_chi (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (hN : 0 < N) (x : GG g N) :
    (levGen ψ hψ hN).chi x =
      ψ (∑ i ∈ Finset.range (N - 1), Formalism.MainNotions.ArithmeticCylinders.entN (x : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1)) := by
  simp only [Lev.chi, Lev.Edge, levGen, Bool.false_eq_true, if_false, Units.val_one, one_mul]
  congr 1
  rw [Finset.sum_congr rfl fun a _ => inner_sum (x : Matrix (Fin N) (Fin N) (ZMod g)) a,
    Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN (x : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1)) N]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.add_sub_cancel]
  have : Formalism.MainNotions.ArithmeticCylinders.entN (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) m (m + 1) = 0 := by
    unfold Formalism.MainNotions.ArithmeticCylinders.entN; rw [dif_neg]; omega
  rw [this, add_zero]

theorem coeff_eU (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (hN : 0 < N) (x : GG g N) :
    (Formalism.MainNotions.ArithmeticCylinders.eU g N ψ).coeff x = (levGen ψ hψ hN).e x := by
  have hc : Nat.card {u // (levGen ψ hψ hN).Mem u} =
      (Finset.univ.filter fun u : GG g N => Formalism.MainNotions.ArithmeticCylinders.IsUniUp (u : Matrix (Fin N) (Fin N) (ZMod g))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext u; simp [levGen_mem_iff]
  simp only [Lev.e, eps, hc, levGen_chi, levGen_mem_iff, Formalism.MainNotions.ArithmeticCylinders.eU, Formalism.MainNotions.ArithmeticCylinders.eDat]
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, div_eq_inv_mul, Fintype.card_subtype]

end Generic

theorem genericOfWh : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), 0 < N → ∀ (V : FDRep ℂ (GlobalTheory.BadShare.GG g N))
    (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → wh ψ (fun x => V.character x) ≠ 0 → GlobalTheory.BadShare.IsGeneric V.ρ := by
  intro g _ N hN V ψ hψ hw
  let Lv := levGen ψ hψ hN
  have hrk : (GlobalTheory.BadShare.rk V.ρ Lv.e : ℂ) = wh ψ (fun x => V.character x) := by
    rw [GlobalTheory.BadShare.Basic.rk_eq_sum_trace V.ρ (GlobalTheory.BadShare.Basic.isProj_e Lv).1]
    unfold wh tr
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [coeff_eU ψ hψ hN]; rfl
  have hpos : GlobalTheory.BadShare.rk V.ρ Lv.e ≠ 0 := fun h => hw (by rw [← hrk, h]; simp)
  have hne : LinearMap.range (GlobalTheory.BadShare.op V.ρ Lv.e) ≠ ⊥ := by
    intro h; apply hpos; unfold GlobalTheory.BadShare.rk; rw [h]; simp
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Lv, rfl, _, hx0, fun u hu => ?_⟩
  have hm : Lv.Mem u := ⟨hu, fun h => absurd h (by simp [Lv, levGen])⟩
  have key : ∀ γ, Lv.e (u⁻¹ * γ) = Lv.chi u * Lv.e γ := by
    intro γ
    simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps]
    by_cases hγ : Lv.Mem γ
    · have h2 : Lv.Mem (u⁻¹ * γ) := GlobalTheory.BadShare.Basic.mem_mul Lv (GlobalTheory.BadShare.Basic.mem_inv Lv hm) hγ
      rw [if_pos h2, if_pos hγ, GlobalTheory.BadShare.Basic.chi_mul Lv (GlobalTheory.BadShare.Basic.mem_inv Lv hm) hγ,
        GlobalTheory.BadShare.Basic.chi_inv Lv hm]
      have := GlobalTheory.BadShare.Basic.chi_ne Lv u
      have := GlobalTheory.BadShare.Basic.chi_ne Lv γ
      field_simp
    · have h2 : ¬ Lv.Mem (u⁻¹ * γ) := fun h => hγ (by simpa using GlobalTheory.BadShare.Basic.mem_mul Lv hm h)
      rw [if_neg h2, if_neg hγ, mul_zero]
  calc V.ρ u (GlobalTheory.BadShare.op V.ρ Lv.e y) = ∑ γ, Lv.e γ • V.ρ (u * γ) y := by
        simp [GlobalTheory.BadShare.op, map_mul, Module.End.mul_apply]
    _ = ∑ γ, Lv.e (u⁻¹ * γ) • V.ρ γ y :=
        Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun γ => by simp
    _ = Lv.chi u • GlobalTheory.BadShare.op V.ρ Lv.e y := by
        simp [key, GlobalTheory.BadShare.op, Finset.smul_sum, mul_smul]

theorem wh_mul_const {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) (c : ℂ) :
    wh ψ (fun x => χ x * c) = wh ψ χ * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_zero_one {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  unfold wh tr Formalism.MainNotions.ArithmeticCylinders.eU Formalism.MainNotions.ArithmeticCylinders.eDat
  simp [Formalism.MainNotions.ArithmeticCylinders.IsUniUp]

theorem whHcL : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ L : List (Pc g),
    (∀ p ∈ L, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) → wh ψ (hcL L (degL L)) = 1 := by
  intro g _ ψ hψ L
  induction L with
  | nil => intro _; exact wh_zero_one ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have ihL := ih fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have hcl : IsClass (hcL L (degL L)) := (GlobalTheory.charDec _ _).2.2.1 (GlobalTheory.gl_list_product_perm_char g L [] _ rfl
      (fun q hq => by
        obtain ⟨-, ⟨V, -, hV⟩, -⟩ := (hL q (List.mem_cons_of_mem _ hq)).1
        exact ⟨V, hV⟩)).1
    have hpc : IsClass p.2 := GlobalTheory.GLq.isClass_of_isIrr hp.1.2.1
    rw [hcL_cons, hc, GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) _ (by simp [degL])]
    · have : (fun x => wh ψ (fun y => p.2 x * hcL L (degL L) y)) = fun x => p.2 x := by
        funext x
        have h1 : (fun y => p.2 x * hcL L (degL L) y) = fun y => hcL L (degL L) y * p.2 x := by
          funext y; ring
        rw [h1, wh_mul_const, ihL, one_mul]
      rw [this]
      exact GlobalTheory.GLq.wh_cusp_eq_one g ψ hψ p.1 p.2 hp.1 hp.2
    · intro y x z
      simp only [hpc x z]
    · intro x y z
      simp only [hcl y z]

theorem degHcL : ∀ (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (Q : List ((ZMod g)[X] × Pc g)),
    (∀ p ∈ Q, p.2.1 = p.1.natDegree ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) →
    ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f →
    hcL (Q.map Prod.snd) (degL (Q.map Prod.snd)) 1 * (GlobalTheory.BadShare.torusCard g f : ℂ) =
      ∏ i ∈ Finset.range (degL (Q.map Prod.snd)), ((g : ℂ) ^ (i + 1) - 1) := by
  intro g _ f Q hQ hf
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hdpos : ∀ p ∈ Q, 0 < p.2.1 := by
    intro p hp
    have hm : p.1 ∈ UniqueFactorizationMonoid.normalizedFactors f := by
      rw [← hf]; exact Multiset.mem_coe.2 (List.mem_map_of_mem hp)
    rw [(hQ p hp).1]
    exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hm).natDegree_pos
  have hd := GlobalTheory.GLq.HcDeg.hc_degree g (Q.map Prod.snd) _ rfl
  have e1 : ((Q.map Prod.snd).map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)) =
      Q.map fun p => p.2.2 1 * ((g : ℂ) ^ p.1.natDegree - 1) := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp]
    rw [(hQ p hp).2, ← (hQ p hp).1]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (hdpos p hp)]
  have e2 : (GlobalTheory.BadShare.torusCard g f : ℂ) = (Q.map fun p => (g : ℂ) ^ p.1.natDegree - 1).prod := by
    unfold GlobalTheory.BadShare.torusCard GlobalTheory.BadShare.degType
    rw [← hf, Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe, Nat.cast_list_prod, List.map_map, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast; rfl
  have e3 : ((Q.map Prod.snd).map fun p => p.2 1) = Q.map fun p => p.2.2 1 := by
    rw [List.map_map]; rfl
  have hne : (Q.map fun p => p.2.2 1).prod ≠ 0 := by
    intro h
    rw [List.prod_eq_zero_iff] at h
    obtain ⟨p, hp, h0⟩ := List.mem_map.1 h
    rw [(hQ p hp).2, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, hi, h1⟩ := h0
    have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have : (g : ℂ) ^ i = 1 := sub_eq_zero.1 h1
    have h2 : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact this
    have h3 := Nat.cast_injective h2
    have h4 : 1 < g ^ i := Nat.one_lt_pow (by omega) hg1
    omega
  rw [e1, List.prod_map_mul, e3, GlobalTheory.GLq.HcDeg.prod_Icc_eq_range] at hd
  rw [e2]
  apply mul_right_cancel₀ hne
  rw [← hd]
  ring

theorem labelsOfEq : ∀ (g : ℕ) [Fact g.Prime] (Q Q' : List ((ZMod g)[X] × Pc g)) (n : ℕ),
    (∀ p ∈ Q ++ Q', IsCusp p.2.2) → (∀ p ∈ Q ++ Q', ∀ q ∈ Q ++ Q', p.2 = q.2 → p.1 = q.1) →
    (Q.map Prod.fst).Nodup → degL (Q.map Prod.snd) = n → degL (Q'.map Prod.snd) = n →
    hcL (Q.map Prod.snd) n = hcL (Q'.map Prod.snd) n →
    (↑(Q.map Prod.fst) : Multiset (ZMod g)[X]) = ↑(Q'.map Prod.fst) := by
  intro g _ Q Q' n hc hinj hnd h1 h2 he
  have hc1 : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact hc q (List.mem_append_left _ hq)
  have hc2 : ∀ p ∈ Q'.map Prod.snd, IsCusp p.2 := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact hc q (List.mem_append_right _ hq)
  have hnd2 : (Q.map Prod.snd).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => Prod.ext ?_ hxy) (List.Nodup.of_map _ hnd)
    exact hinj x (List.mem_append_left _ hx) y (List.mem_append_left _ hy) hxy
  have hip := (GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ (Q'.map Prod.snd) n h1 h2 hc1 hc2)
  have hperm : (Q.map Prod.snd).Perm (Q'.map Prod.snd) := by
    by_contra hp
    have a := hip.1 hp
    rw [← he, hip.2 hnd2] at a
    exact one_ne_zero a
  let h : Pc g → (ZMod g)[X] := fun s => if hs : ∃ p ∈ Q ++ Q', p.2 = s then hs.choose.1 else 0
  have hh : ∀ p ∈ Q ++ Q', h p.2 = p.1 := by
    intro p hp
    have hs : ∃ q ∈ Q ++ Q', q.2 = p.2 := ⟨p, hp, rfl⟩
    simp only [h, dif_pos hs]
    exact hinj _ hs.choose_spec.1 p hp hs.choose_spec.2
  have k1 : Q.map Prod.fst = (Q.map Prod.snd).map h := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (hh p (List.mem_append_left _ hp)).symm
  have k2 : Q'.map Prod.fst = (Q'.map Prod.snd).map h := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (hh p (List.mem_append_right _ hp)).symm
  rw [k1, k2]
  exact Multiset.coe_eq_coe.2 (hperm.map h)

theorem monic_of_factor {g : ℕ} [Fact g.Prime] {f P : (ZMod g)[X]}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors f) : P.Monic := by
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor P hP]
  exact monic_normalize (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).ne_zero

theorem prod_factors_of_monic {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} (hf : f.Monic) :
    (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
  have hm : (UniqueFactorizationMonoid.normalizedFactors f).prod.Monic := by
    have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f) id fun P hP =>
      monic_of_factor hP
    rwa [Multiset.map_id] at this
  exact eq_of_monic_of_associated hm hf (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)

theorem isPrimeLab_of_factor {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {P : (ZMod g)[X]}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors f) : IsPrimeLab P.natDegree P := by
  have hi := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  refine ⟨monic_of_factor hP, hi, fun h => h0 ?_, rfl⟩
  · obtain ⟨c, hc⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    rw [hc, mul_coeff_zero, h, zero_mul]

theorem green_series : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GreenSeriesSt := by
  intro hG g _ N
  obtain ⟨L⟩ := GlobalTheory.GLq.LabelModel.inhab g
  have H : ∀ d, ∃ τ : (ZMod g)[X] → Gn g d → ℂ, 0 < d →
      (∀ P, IsPrimeLab d P → IsCuspOf L P (τ P) ∧ τ P 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) ∧
      (∀ P P', IsPrimeLab d P → IsPrimeLab d P' → τ P = τ P' → P = P') := by
    intro d
    by_cases hd : 0 < d
    · obtain ⟨τ, h1, h2, -⟩ := hG.green g L d hd
      exact ⟨τ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hd⟩
  choose τ hτ using H
  let Q : (ZMod g)[X] → List ((ZMod g)[X] × Pc g) := fun f =>
    (UniqueFactorizationMonoid.normalizedFactors f).toList.map fun P => (P, ⟨P.natDegree, τ P.natDegree P⟩)
  refine ⟨fun f => hcL ((Q f).map Prod.snd) N, fun hN => ?_⟩
  have hfst : ∀ f, (((Q f).map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f := by
    intro f; simp [Q, Function.comp_def]
  have hmemQ : ∀ f, ∀ p ∈ Q f, p.1 ∈ UniqueFactorizationMonoid.normalizedFactors f ∧
      p.2 = ⟨p.1.natDegree, τ p.1.natDegree p.1⟩ := by
    intro f p hp
    simp only [Q, List.mem_map, Multiset.mem_toList] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    exact ⟨hP, rfl⟩
  have hpos : ∀ {P : (ZMod g)[X]} {d}, IsPrimeLab d P → 0 < d := fun h => h.2.2.2 ▸ h.2.1.natDegree_pos
  have hQ : ∀ f ∈ GlobalTheory.BadShare.sqSet g N, ∀ p ∈ Q f, p.2.1 = p.1.natDegree ∧ IsCusp p.2.2 ∧
      p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1) ∧ IsPrimeLab p.1.natDegree p.1 := by
    intro f hf p hp
    obtain ⟨h1, h2⟩ := hmemQ f p hp
    have hl := isPrimeLab_of_factor (GlobalTheory.BadShare.mem_sqSet.1 hf).2.2.2 h1
    obtain ⟨⟨-, hc, -⟩, hd⟩ := (hτ _ (hpos hl)).1 p.1 hl
    rw [h2]
    exact ⟨rfl, hc, hd, hl⟩
  have hdeg : ∀ f ∈ GlobalTheory.BadShare.sqSet g N, degL ((Q f).map Prod.snd) = N := by
    intro f hf
    obtain ⟨hm, hn, -, -⟩ := GlobalTheory.BadShare.mem_sqSet.1 hf
    have e1 : degL ((Q f).map Prod.snd) = (((Q f).map Prod.fst).map natDegree).sum := by
      unfold degL
      simp [Q, List.map_map, Function.comp_def]
    rw [e1, ← Multiset.sum_coe, ← Multiset.map_coe, hfst, ← hn]
    conv_rhs => rw [← prod_factors_of_monic hm]
    rw [natDegree_multiset_prod_of_monic _ fun P hP => monic_of_factor hP]
  have hinj : ∀ f ∈ GlobalTheory.BadShare.sqSet g N, ∀ f' ∈ GlobalTheory.BadShare.sqSet g N,
      ∀ p ∈ Q f ++ Q f', ∀ q ∈ Q f ++ Q f', p.2 = q.2 → p.1 = q.1 := by
    intro f hf f' hf' p hp q hq he
    have hp' : ∃ F ∈ GlobalTheory.BadShare.sqSet g N, p ∈ Q F := by
      rcases List.mem_append.1 hp with h | h; exacts [⟨f, hf, h⟩, ⟨f', hf', h⟩]
    have hq' : ∃ F ∈ GlobalTheory.BadShare.sqSet g N, q ∈ Q F := by
      rcases List.mem_append.1 hq with h | h; exacts [⟨f, hf, h⟩, ⟨f', hf', h⟩]
    obtain ⟨F, hF, hpF⟩ := hp'
    obtain ⟨F', hF', hqF⟩ := hq'
    have lp := (hQ F hF p hpF).2.2.2
    have lq := (hQ F' hF' q hqF).2.2.2
    rw [(hmemQ F p hpF).2, (hmemQ F' q hqF).2] at he
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 he
    have h3 : HEq (τ p.1.natDegree q.1) (τ q.1.natDegree q.1) := by rw [h1]
    have h4 : τ p.1.natDegree p.1 = τ p.1.natDegree q.1 := eq_of_heq (h2.trans h3.symm)
    exact (hτ _ (hpos lp)).2 p.1 q.1 lp (h1 ▸ lq) h4
  have hnd : ∀ f ∈ GlobalTheory.BadShare.sqSet g N, ((Q f).map Prod.fst).Nodup := by
    intro f hf
    rw [← Multiset.coe_nodup, hfst]
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (GlobalTheory.BadShare.mem_sqSet.1 hf).1.ne_zero).1 (GlobalTheory.BadShare.mem_sqSet.1 hf).2.2.1
  have ψne : (ZMod.stdAddChar (N := g)) ≠ 1 := fun h1 => by
    have h2 : (ZMod.stdAddChar (N := g)) 1 = ZMod.stdAddChar (N := g) 0 := by rw [h1]; simp
    exact one_ne_zero (ZMod.injective_stdAddChar h2)
  refine ⟨fun f hf f' hf' he => ?_, fun f hf => ?_⟩
  · have hc : ∀ p ∈ Q f ++ Q f', IsCusp p.2.2 := fun p hp => by
      rcases List.mem_append.1 hp with h | h
      exacts [(hQ f hf p h).2.1, (hQ f' hf' p h).2.1]
    have := labelsOfEq g (Q f) (Q f') N hc (hinj f hf f' hf') (hnd f hf) (hdeg f hf) (hdeg f' hf') he
    rw [hfst, hfst] at this
    rw [← prod_factors_of_monic (GlobalTheory.BadShare.mem_sqSet.1 hf).1, this,
      prod_factors_of_monic (GlobalTheory.BadShare.mem_sqSet.1 hf').1]
  · have hcL' : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hQ f hf q hq).2.1
    have hch : IsChar (hcL ((Q f).map Prod.snd) N) :=
      (GlobalTheory.gl_list_product_perm_char g _ [] N (hdeg f hf).symm fun p hp => by
        obtain ⟨-, ⟨V, -, hV⟩, -⟩ := hcL' p hp; exact ⟨V, hV⟩).1
    have hnd' : ((Q f).map Prod.snd).Nodup := by
      have := hnd f hf
      rw [List.nodup_iff_injective_get] at this ⊢
      intro i j hij
      have hi : i.1 < (Q f).length := by simpa using i.2
      have hj : j.1 < (Q f).length := by simpa using j.2
      have e := hinj f hf f hf ((Q f).get ⟨i, hi⟩) (List.mem_append_left _ (List.get_mem _ _))
        ((Q f).get ⟨j, hj⟩) (List.mem_append_left _ (List.get_mem _ _)) (by simpa using hij)
      have := @this ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ (by simpa using e)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    have hip := (GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ N (hdeg f hf) (hdeg f hf) hcL' hcL').2 hnd'
    obtain ⟨V, hVs, hV⟩ := (GlobalTheory.charDec _ _).2.2.2.1 hch hip
    have hVc : V.character = hcL ((Q f).map Prod.snd) N := funext hV
    refine ⟨V, hVs, hVc, ?_, ?_⟩
    · refine genericOfWh g N hN V _ ψne ?_
      have hw := whHcL g _ ψne ((Q f).map Prod.snd) fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact ⟨(hQ f hf q hq).2.1, (hQ f hf q hq).2.2.1⟩
      rw [hdeg f hf] at hw
      have : (fun x => V.character x) = hcL ((Q f).map Prod.snd) N := hVc
      rw [this, hw]; exact one_ne_zero
    · have hd := degHcL g f (Q f) (fun p hp => ⟨(hQ f hf p hp).1, (hQ f hf p hp).2.2.1⟩) (hfst f)
      rw [hdeg f hf, ← hVc, FDRep.char_one] at hd
      apply Nat.cast_injective (R := ℂ)
      rw [Nat.cast_mul, hd, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos)]
      push_cast; rfl

end GlobalTheory.GreenSeries
