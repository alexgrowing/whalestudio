import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisAvgInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOInvSmulNsmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulAddSmulAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdemEqSingle
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

open GlobalTheory.PlaceModel GlobalTheory.SeeSaw

variable {D : D7} {S T : HSp D}

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem comb_sum_single {ι : Type} [Fintype ι] (ψ : AddChar (AF D.host.F) ℂ) (x : ι → WO S T) (a : ι → ℂ)
    (f : WO S T → ℂ) :
    comb ψ S T (∑ i, Finsupp.single (x i) (a i)) f = ∑ i, a i • heisO ψ S T (x i) f := by
  rw [comb_eq_linearCombination, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.linearCombination_single _ _ _

theorem isFinComb_sum_single {ι : Type} [Fintype ι] (x : ι → WO S T) (a : ι → ℂ)
    (hx : ∀ i, (x i).map (infPart D) = 0) : IsFinComb (∑ i, Finsupp.single (x i) (a i)) := by
  classical
  intro u hu
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hi)]
  exact hx i

theorem map_infPart_add_neg {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + -y).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show infPart D (x i j + -y i j) = 0
  rw [map_add, map_neg, h1, h2, neg_zero, add_zero]

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  linear_combination -h

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplO_skew S T x x
  have hh := half_mul_two D
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - symplO S T x x * hh

theorem heisL_cancel (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ (-x) f) = f := by
  rw [heisL_heisL, symplOH, symplO_neg_right, symplO_self, neg_zero, mul_zero, AddChar.map_zero_eq_one, one_smul,
    add_neg_cancel]
  funext w
  change ψ (symplOH S T w 0) * f (w + 0) = f w
  rw [symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem lamE_two_nsmul {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ)
    {u : WO S T} (hu : u ∈ Λ) : lamE ψ S T e (2 • u) = 1 := by
  have h := hΛ _ (he u hu) _ (hc _ (Λ.nsmul_mem hu 2))
  rw [← h]
  unfold lamE symplOH
  congr 1
  rw [two_nsmul u, smul_add e, symplO_add_left]
  have hh := half_mul_two D
  linear_combination (symplO S T (e • u) (cA D e • (u + u))) * hh

theorem lamE_half {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) {e' : AE D} (he' : e' * cA D e' = 0) {u : WO S T}
    (hu : IsHalf e' u) : lamE ψ S T e u = 1 := by
  have h : e' • u = u := (isHalf_iff S T).1 hu
  have h1 : e • u = e' • (e • u) := by rw [smul_comm, h]
  have h2 : cA D e' • (cA D e • u) = 0 := by
    rw [smul_comm, ← h, smul_smul (cA D e'), mul_comm, he', zero_smul, smul_zero]
  unfold lamE symplOH
  rw [h1, symplO_smul, h2, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]

theorem finite_Qm {V : Type} [AddCommGroup V] {Λ : AddSubgroup V} {m : ℕ} {R : Set V} (hR : R.Finite)
    (h : ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + m • u) : Finite (Qm m Λ) := by
  classical
  haveI : Finite R := hR
  refine Finite.of_surjective
    (fun r : R => if hr : (r : V) ∈ Λ then (QuotientAddGroup.mk (⟨r, hr⟩ : Λ) : Qm m Λ) else 0) fun q => ?_
  obtain ⟨r, hr, u, hu, ht⟩ := h _ (repm_mem q)
  have hrΛ : r ∈ Λ := by
    have := Λ.sub_mem (repm_mem q) (Λ.nsmul_mem hu m)
    rwa [ht, add_sub_cancel_right] at this
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [dif_pos hrΛ]
  rw [← mk_repm q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine mem_mLat.2 ⟨u, hu, ?_⟩
  change m • u = -r + repm q
  rw [ht]; abel

theorem decomp_of_lam (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    (lam : WO S T → ℂ) (hlam : ∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y))
    (hlm : ∀ l ∈ Λ, lam (m • l) = 1) [Fintype (Qm m Λ)] (f : WO S T → ℂ) (hf : ∀ l ∈ Λ, heisO ψ S T (m • l) f = f) :
    ∃ (u : Qm m Λ → WO S T) (c : Qm m Λ → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, IsFinComb (c i)) ∧
      (∀ i, ∀ b ∈ Λ, lam b • heisO ψ S T b (comb ψ S T (c i) f) = comb ψ S T (c i) f) ∧
      f = ∑ i, heisO ψ S T (u i) (comb ψ S T (c i) f) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Qm m Λ → WO S T, ∀ a, s a = incA D ((m : D.host.E)⁻¹) • repm a := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = (Fintype.card (Qm m Λ) : ℂ) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hsinf : ∀ a, (s a).map (infPart D) = 0 := fun a => by
    rw [hs]; exact map_infPart_smul _ (hinf _ (repm_mem a))
  have hcomb : ∀ a, comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) (N⁻¹ • heisL S T ψ (-s a) f) := by
    intro a
    rw [comb_sum_single]
    refine Finset.sum_congr rfl fun q _ => ?_
    change _ = lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)
    rw [map_smul, heisL_heisL, smul_smul, smul_smul]
    rfl
  refine ⟨s, fun a => ∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a))), hsinf,
    fun a => isFinComb_sum_single _ _ fun q => map_infPart_add_neg (hinf _ (repm_mem q)) (hsinf a), fun a b hb => ?_, ?_⟩
  · rw [hcomb]
    refine heisAvg_invariant D ψ S T Λ m lam hlam _ (fun l hl => ?_) b hb
    change lam (m • l) • heisL S T ψ (m • l) (N⁻¹ • heisL S T ψ (-s a) f) = _
    have h1 : ψ (symplO S T (m • l) (-s a)) = 1 := by
      rw [symplO_neg_right, ← symplO_skew, hs, symplO_inv_smul_nsmul hm]
      exact hΛ _ (repm_mem a) _ hl
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [hlm l hl, one_smul, map_smul, heisL_comm, h1, one_smul, h2]
  · have h3 : ∀ a, heisO ψ S T (s a) (comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
        (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f) =
        ∑ q : Qm m Λ, ψ (symplO S T (s a) (repm q)) • ((lam (repm q) * N⁻¹) • heisL S T ψ (repm q) f) := by
      intro a
      rw [hcomb]
      change heisL S T ψ (s a) (∑ q : Qm m Λ, lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, heisL_comm, heisL_cancel, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    simp only [h3]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hs, charSum_selfAnn D ψ S T Λ m hm hinf hΛ hmax, ← hN, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 (repm_zero_mem (m := m) (Λ := Λ))
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [← hl', hlm l hl, h2, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem theta_eq_sum_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) := by
  intro D ψ θ S T sS sT LS LT f₀ hS hT hv f hf
  have hψ := hv.1
  obtain ⟨k, hk, hfk⟩ := Formalism.IndefR.Fin.latLevel_of (Formalism.IndefR.Fin.latSelfDual D) ψ hψ S T LS LT hS hT f hf
  obtain ⟨-, -, hmod, hdual⟩ := Formalism.IndefR.Fin.latSelfDual D ψ hψ S T LS LT hS hT
  have hinf := fun u (hu : u ∈ latO S T LS LT fun _ => True) => Formalism.IndefR.Fin.latAll_inf S T LS LT hu
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) (2 * k) (by omega)
  change ∀ u ∈ latO S T LS LT fun _ => True, _ at hfk
  generalize latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at hfk hmod hdual hinf hRc ⊢
  haveI : Finite (Qm (2 * k) Λ) := finite_Qm hR hRc
  letI : Fintype (Qm (2 * k) Λ) := Fintype.ofFinite _
  obtain ⟨e, h1, h2, hi, hi', h, hh, h3⟩ := GlobalTheory.TwoPlaceIdem.exists_idem_half D
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1 := fun x hx => (hdual x (hinf x hx)).1 hx
  have hr : ∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z := fun u hu =>
    ⟨h • u, hmod h hh u hu, by rw [← h3, two_mul, add_smul, two_nsmul]⟩
  have hl2 : ∀ u ∈ Λ, lamE ψ S T e (2 • u) = 1 := fun u hu => lamE_two_nsmul hΛ (hmod e hi) (hmod _ hi') hu
  obtain ⟨u, c, hu, hc, hfix, hsum⟩ := decomp_of_lam ψ Λ (2 * k) (by omega) hinf hΛ (fun x hx h => (hdual x hx).2 h)
    (lamE ψ S T e) (lamE_add_of_lattice D ψ S T Λ e h1 h2 hΛ (hmod e hi) (hmod _ hi') hr)
    (fun l hl => by rw [mul_nsmul']; exact hl2 _ (Λ.nsmul_mem hl k)) f
    (fun l hl => by rw [mul_nsmul]; exact hfk _ (Λ.nsmul_mem hl 2))
  let ι := (Fintype.equivFin (Qm (2 * k) Λ)).symm
  refine ⟨_, fun i => u (ι i), fun i => c (ι i), fun i => hu _, fun i => hc _, fun i => ⟨fun b hb => ?_, fun e' he' b hb hb' => ?_⟩, ?_⟩
  · have := hfix (ι i) _ (Λ.nsmul_mem hb 2)
    rwa [hl2 b hb, one_smul] at this
  · have := hfix (ι i) b hb
    rwa [lamE_half e he'.2.1 hb', one_smul] at this
  · exact hsum.trans (Equiv.sum_comp ι fun q => heisO ψ S T (u q) (comb ψ S T (c q) f)).symm

end GlobalTheory.FinDecomp

end

theorem _root_.GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) :=
  GlobalTheory.FinDecomp.theta_eq_sum_latVac
