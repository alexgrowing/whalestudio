import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
open Matrix

namespace GlobalTheory.BesselChar

theorem unip_pi_iff {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S))
    (M : Matrix (Fin n) (Fin n) (ι → S)) :
    GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i))
      (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  constructor
  · rintro ⟨⟨T, hT, e⟩, h2⟩ i
    set φ := Pi.evalRingHom (fun _ => S) i
    refine ⟨⟨T.map φ, fun j l hjl => by simp [Matrix.map_apply, hT j l hjl], ?_⟩, fun y hy => ?_⟩
    · have := congrArg (fun X => X.map φ) e
      simpa only [Matrix.map_mul, Matrix.map_add _ (map_add φ)] using this
    · let y' : Fin n → ι → S := fun k => Pi.single i (y k)
      have hy' : K *ᵥ y' = 0 := by
        funext j i'
        by_cases hi : i' = i
        · subst hi
          have h1 := congr_fun (mulVec_map φ K y') j
          have h0 : (fun k => φ (y' k)) = y := by
            funext k; simp [φ, y']
          rw [h0, hy] at h1
          simpa [φ] using h1.symm
        · show (∑ k, K j k * y' k) i' = 0
          rw [Finset.sum_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [y', Pi.single_apply, hi]
      obtain ⟨a, ha⟩ := h2 y' hy'
      refine ⟨fun l => φ (a l), ?_⟩
      have h0 : (fun k => φ (y' k)) = y := by
        funext k; simp [φ, y']
      have h1 := mulVec_map φ M y'
      have h3 := mulVec_map φ E a
      rw [h0] at h1
      rw [h1, h3, ha]
      funext k
      simp only [Pi.add_apply, map_add]
      rw [show φ (y' k) = y k from congr_fun h0 k]
  · intro h
    choose hc hv using h
    choose T hT e using hc
    refine ⟨⟨Matrix.of fun j l i => T i j l, fun j l hjl => by funext i; exact hT i j l hjl, ?_⟩, fun y hy => ?_⟩
    · ext k l i
      have h1 := congr_fun (congr_fun (e i) k) l
      have hT' : (Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i) = T i := by
        ext j l; rfl
      have h2 : ((M * E).map (Pi.evalRingHom (fun _ => S) i)) k l
          = ((E + E * Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i)) k l := by
        rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hT']
        exact h1
      simpa using h2
    · have hyi : ∀ i, K.map (Pi.evalRingHom (fun _ => S) i) *ᵥ (fun k => y k i) = 0 := by
        intro i
        have := mulVec_map (Pi.evalRingHom (fun _ => S) i) K y
        refine this.trans ?_
        rw [hy]; rfl
      choose a ha using fun i => hv i _ (hyi i)
      refine ⟨fun l i => a i l, ?_⟩
      funext k i
      have h1 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) M y) k
      have h3 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) E (fun l i => a i l)) k
      have h4 := congr_fun (ha i) k
      simp only [Pi.evalRingHom_apply] at h1 h3
      show (M *ᵥ y) k i = y k i + (E *ᵥ fun l i => a i l) k i
      rw [← h1, ← h3, h4]
      rfl

end GlobalTheory.BesselChar
