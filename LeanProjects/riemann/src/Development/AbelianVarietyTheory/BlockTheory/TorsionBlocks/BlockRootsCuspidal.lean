import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

open Polynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRootsCuspidal

def IsBlockRoots {F : Type} [Monoid F] (g : ℕ) (B : Multiset (ℕ × ℕ)) (Rt : Multiset F) : Prop :=
  ∃ M : Multiset ((ℕ × ℕ) × Multiset F),
    M.map Prod.fst = B ∧
    (∀ p ∈ M, Multiset.card p.2 = p.1.1 ∧ p.2.map (fun x => x ^ g) = p.2) ∧
    (M.map fun p => p.1.2 • p.2).sum = Rt

def labelRoots (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) :
    Multiset (Formalism.BasicNotions.Fb (D.host.g k) (D.host.g_prime k)) :=
  @Formalism.CyclotomicNorms.rootsBar (D.host.g k) ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)

def BlockRootsAt (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  IsBlockRoots (D.host.g k) (D.ntypes.bc σ) (labelRoots D σ k v)

def TameAt (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (lam : D.what₂.places.Pl) : Prop :=
  Matrix.charpoly
      ((D.ntypes.rbar σ lam (D.ntypes.tg k v) :
          GL (Fin D.R.r) (Formalism.BasicNotions.Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam))) :
        Matrix (Fin D.R.r) (Fin D.R.r)
          (Formalism.BasicNotions.Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam))) =
    ((labelRoots D σ k v).map fun x =>
      X - C (D.ntypes.iota k v lam (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar lam) x))).prod ∧
  ∃ φ : Formalism.MainNotions.N.GE D.nd,
    D.ntypes.rbar σ lam (φ * D.ntypes.tg k v * φ⁻¹) =
      D.ntypes.rbar σ lam (D.ntypes.tg k v) ^ D.host.g k

def LabelsAndTameInertia (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ σ : D.what₂.FT, D.nd.goodRow σ → ∀ (k : Fin 2) (v : D.nd.PlG k),
    BlockRootsAt D σ k v ∧
    (D.ntypes.cuspidal σ → ∀ lam : D.what₂.places.Pl, D.what₂.places.resChar lam ≠ D.host.g k →
      TameAt D σ k v lam)

theorem IsBlockRoots.le_one {F : Type} [Monoid F] {g : ℕ} {B : Multiset (ℕ × ℕ)} {Rt : Multiset F}
    (h : IsBlockRoots g B Rt) (hR : Rt.Nodup) : ∀ p ∈ B, 0 < p.1 → p.2 ≤ 1 := by
  classical
  obtain ⟨M, rfl, hM, rfl⟩ := h
  intro p hp h0
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
  have hc := (hM q hq).1
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (hc ▸ h0)
  have hle : q.1.2 • q.2 ≤ (M.map fun p => p.1.2 • p.2).sum :=
    Multiset.single_le_sum (fun _ _ => Multiset.zero_le _) _ (Multiset.mem_map_of_mem _ hq)
  have h1 := Multiset.count_le_of_le x hle
  have h2 := Multiset.nodup_iff_count_le_one.1 hR x
  rw [Multiset.count_nsmul] at h1
  have h3 := Multiset.one_le_count_iff_mem.2 hx
  nlinarith

theorem blockRootsAt_of_cuspidal (D : Formalism.BasicNotions.D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k)
    (h : D.ntypes.cuspidal σ) : BlockRootsAt D σ k v := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hdeg : ((D.nd.lab k σ v).map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))).natDegree
      = D.R.r := by
    rw [natDegree_map]; exact (D.nd.lab_monic k σ v).2
  have hcard := IsAlgClosed.card_roots_eq_natDegree
    (p := (D.nd.lab k σ v).map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))))
  refine ⟨{((D.R.r, 1), labelRoots D σ k v)}, ?_, ?_, ?_⟩
  · rw [Multiset.map_singleton]; exact h.symm
  · intro p hp
    rw [Multiset.mem_singleton] at hp
    subst hp
    refine ⟨hcard.trans hdeg, ?_⟩
    have := roots_map_of_injective_of_card_eq_natDegree
      (f := frobenius (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.host.g k)) (RingHom.injective _) hcard
    rw [Polynomial.map_map, RingHom.ext_zmod ((frobenius _ _).comp _)
      (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))] at this
    exact this
  · simp

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRootsCuspidal
