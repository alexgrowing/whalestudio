import Mathlib

namespace GlobalTheory

open MvPolynomial in

theorem _root_.GlobalTheory.etale_mvPolynomial_map_of_etale {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by
  letI := g.toAlgebra
  letI : Algebra (MvPolynomial N B) (MvPolynomial N A) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Etale.isStableUnderBaseChange B A (MvPolynomial N B) (MvPolynomial N A) hg

open MvPolynomial in

theorem etale_eval₂Hom_option_of_bijective {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N)
    (hg : (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f n)) : (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  let ι : MvPolynomial (Fin (d+1)) k →+* MvPolynomial N (MvPolynomial (Fin 1) k) :=
    eval₂Hom (C.comp C) (fun j => (e j).elim (C (X 0)) X)
  let κ : MvPolynomial N (MvPolynomial (Fin 1) k) →+* MvPolynomial (Fin (d+1)) k :=
    eval₂Hom (eval₂Hom C (fun _ => X (e.symm none))) (fun i => X (e.symm (some i)))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        simp [ι, κ]
    · intro j
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n) =
      (MvPolynomial.eval₂Hom f n).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t))).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

end GlobalTheory
