import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings

noncomputable section

namespace GlobalTheory.Survey.EmbeddingValuationsAnti

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings GlobalTheory.HeightCounting

theorem v_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.v := by
  have hk := R.m_add_three_le_k
  have step : ∀ (n : ℕ) (h : n + 1 < R.k - 1), P.v ⟨n + 1, h⟩ < P.v ⟨n, by omega⟩ := fun n h =>
    (P.u_gt_v ⟨n + 1, h⟩).trans (P.v_gt_u ⟨n, by omega⟩)
  have key : ∀ (d n : ℕ) (h : n + d + 1 < R.k - 1), P.v ⟨n + d + 1, h⟩ < P.v ⟨n, by omega⟩ := by
    intro d
    induction d with
    | zero => intro n h; exact step n h
    | succ d ih => intro n h; exact (step (n + d + 1) (by omega)).trans (ih n (by omega))
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have : a < b := hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt this
  exact key d a hb

theorem b_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.b := by
  have ht : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
  have step : ∀ (n : ℕ) (h : n + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + 1, h⟩ := fun n h => by
    have h1 := P.gap_be ⟨n, by omega⟩
    have h2 := P.gap_eb ⟨n, by omega⟩ h
    simp only at h2
    linarith
  have key : ∀ (d n : ℕ) (h : n + d + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + d + 1, h⟩ := by
    intro d
    induction d with
    | zero => intro n h; exact step n h
    | succ d ih => intro n h; exact (ih n (by omega)).trans (step (n + d + 1) (by omega))
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have : a < b := hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt this
  exact key d a hb

theorem neg_b_lt_v {R : Ranks} (P : HCParam R) (i : Fin (R.k - 1)) (j : Fin R.m) : -P.b j < P.v i := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 : P.u ⟨R.k - 1, by omega⟩ < P.v ⟨R.k - 2, by omega⟩ := by
    have := P.v_gt_u ⟨R.k - 2, by omega⟩
    have e : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext (by simp; omega)
    simpa [e] using this
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i := (v_strictAnti P).antitone (by
    have := i.2; show i.1 ≤ R.k - 2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (by show 0 ≤ j.1; omega)
  linarith

theorem nodup_hcSigma {R : Ranks} (P : HCParam R) : (hcSigma P).Nodup := by
  unfold hcSigma
  rw [Multiset.nodup_add]
  refine ⟨?_, ?_, ?_⟩
  · refine Multiset.Nodup.map (fun a b h => (v_strictAnti P).injective ?_) Finset.univ.nodup
    exact_mod_cast h
  · refine Multiset.Nodup.map (fun a b h => (b_strictMono P).injective ?_) Finset.univ.nodup
    have := neg_injective h
    exact_mod_cast this
  · rw [Multiset.disjoint_left]
    intro z h1 h2
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 h1
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h2
    have : -P.b j = P.v i := by exact_mod_cast hj
    exact (neg_b_lt_v P i j).ne this

theorem emb_injective (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem embTau_injective (D : D7) : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext (emb_injective D h))

theorem embTau_ne_bar (D : D7) (τ τ' : D.what₂.Tau) : embTauBar D τ ≠ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ' := by
  intro h
  have hc : embTauBar D τ = D.host.emb (D.R.cc * (D.eTau τ : D.R.GG)) := by
    refine RingHom.ext fun x => ?_
    simp only [embTauBar, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau, embPsi, Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply, map_mul]
    rw [← D.host.conjE_apply D.host.φ₀]
    rfl
  rw [hc] at h
  have h1 := emb_injective D h
  have hn : D.R.cc ∉ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  apply hn
  have h2 : D.R.cc =
      ((D.eTau τ' : D.R.Psi) : D.R.GG) *
        ((D.eTau τ : D.R.Psi) : D.R.GG)⁻¹ := by
    rw [← h1]; group
  rw [h2]
  exact (D.R.Psi).mul_mem (D.eTau τ').2 ((D.R.Psi).inv_mem (D.eTau τ).2)

open Classical in

def perturbedSide {D : D7} (S : RowSide D) : RowSide D where
  locR σ w := if ∃ k v, D.naut.plGw k v = w then S.locR σ w else D.naut.lpZero w
  satR := S.satR
  lab_eq k σ v := by rw [if_pos ⟨k, v, rfl⟩]; exact S.lab_eq k σ v

def LabelsOnly (D : D7) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧ D.naut.ralg π ∧
  (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG π w)) ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
    D.naut.unr (D.naut.locG π w)) ∧
  (∀ τ : D.what₂.Tau, D.naut.infG π (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = hcSigma (D.hc τ) ∧
    D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z))

end GlobalTheory.Survey.EmbeddingValuationsAnti

end
