import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

section Push

variable (S : Thick (dp0 R) s) {A : Type} [CommRing A] (a : S.B →+* A) {JA : Ideal A} (θ : DividedPowers JA)
  (ha : IsDPMorphism S.δ θ a)

include ha in
theorem push_ker : RingHom.ker S.π ≤ RingHom.ker ((Ideal.Quotient.mk JA).comp a) := fun b hb ↦
  Ideal.Quotient.eq_zero_iff_mem.2 (ha.1 (Ideal.mem_map_of_mem _ ((S.ker b).1 hb)))

def pushRed : S.B₀ →+* A ⧸ JA := RingHom.liftOfSurjective S.π S.surj ⟨_, push_ker S a θ ha⟩

theorem pushRed_π (b : S.B) : pushRed S a θ ha (S.π b) = Ideal.Quotient.mk JA (a b) :=
  RingHom.liftOfSurjective_comp_apply S.π S.surj ⟨_, push_ker S a θ ha⟩ b

variable (hn : IsNilDP θ)

def push : Thick (dp0 R) s where
  B := A
  alg := (a.comp (algebraMap R S.B)).toAlgebra
  J := JA
  δ := θ
  nil := hn
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := A ⧸ JA
  π := Ideal.Quotient.mk JA
  surj := Ideal.Quotient.mk_surjective
  ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
  x := spMap (pushRed S a θ ha) ≫ S.x
  w := by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ pushRed_π S a θ ha _

def pushHom : S ⟶ push S a θ ha hn where
  φ := { a with commutes' := fun _ ↦ rfl }
  φ₀ := pushRed S a θ ha
  comm := pushRed_π S a θ ha
  dp := ha
  pt := rfl

def pushDesc {V : Thick (dp0 R) s} (φ : S ⟶ V) (G : A →+* V.B) (hG : IsDPMorphism θ V.δ G)
    (e : G.comp a = (φ.φ : S.B →+* V.B)) : push S a θ ha hn ⟶ V where
  φ := { G with commutes' := fun r ↦ (DFunLike.congr_fun e _).trans (φ.φ.commutes r) }
  φ₀ := Ideal.Quotient.lift JA (V.π.comp G) fun _ hc ↦ (V.ker _).2 (hG.1 (Ideal.mem_map_of_mem _ hc))
  comm := fun _ ↦ rfl
  dp := hG
  pt := by
    change spMap _ ≫ spMap (pushRed S a θ ha) ≫ S.x = V.x
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← φ.pt]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    obtain ⟨b, rfl⟩ := S.surj b
    rw [RingHom.comp_apply, pushRed_π, φ.comm]
    exact congrArg V.π (DFunLike.congr_fun e b)

end Push

theorem exists_trunc (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P), InN κ P ∧ IsLev P.δ n ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V), ∃! ψ : P ⟶ V, i ≫ ψ = φ := by
  obtain ⟨A, _, a, JA, θ, ha, hlev, hext, hsurj, huniv⟩ := ring_trunc κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, hext, hlev, ?_⟩
  intro V hV φ
  obtain ⟨G, hG, hGa⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ?_, ?_⟩
  · refine Thick.hom_ext fun b ↦ ?_
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · intro ψ hψ
    refine Thick.hom_ext fun x ↦ ?_
    obtain ⟨b, rfl⟩ := hsurj x
    have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
    rw [hψ] at h1
    have h2 : G (a b) = φ.φ b := DFunLike.congr_fun hGa b
    exact h1.symm.trans h2.symm

theorem exists_adj_one (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : P.B), InN κ P ∧ IsLev P.δ n ∧ y ∈ P.J ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : V.B), z ∈ V.J →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ψ.φ y = z := by
  obtain ⟨A, _, a, JA, θ, y, ha, hlev, hext, hy, huniv⟩ := ring_adj κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, y, hext, hlev, hy, ?_⟩
  intro V hV φ z hz
  obtain ⟨G, ⟨hG, hGa, hGy⟩, huniq⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp z hz
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ⟨?_, hGy⟩, ?_⟩
  · refine Thick.hom_ext fun b ↦ ?_
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · rintro ψ ⟨hψ, hψy⟩
    let g : A →+* V.B := ψ.φ.toRingHom
    have hcomp : g.comp a = (φ.φ : S.B →+* V.B) := by
      refine RingHom.ext fun b ↦ ?_
      have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
      rw [hψ] at h1
      exact h1.symm
    have heq : g = G := huniq g ⟨ψ.dp, hcomp, hψy⟩
    refine Thick.hom_ext fun x ↦ ?_
    exact DFunLike.congr_fun heq x

theorem exists_adj' (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k := by
  induction d with
  | zero =>
    obtain ⟨P, i, hP, hlev, huniv⟩ := exists_trunc S hS n hn
    refine ⟨P, i, Fin.elim0, hP, hlev, fun k ↦ Fin.elim0 k, ?_⟩
    intro V hV φ z _
    obtain ⟨ψ, hψ, huniq⟩ := huniv V hV φ
    exact ⟨ψ, ⟨hψ, fun k ↦ Fin.elim0 k⟩, fun ψ' h ↦ huniq ψ' h.1⟩
  | succ d ih =>
    obtain ⟨P, i, y, hP, hlev, hy, huniv⟩ := ih
    obtain ⟨Q, j, w, hQ, hlevQ, hw, hunivQ⟩ := exists_adj_one P hP n hn
    refine ⟨Q, i ≫ j, Fin.cons w (fun k ↦ j.φ (y k)), hQ, hlevQ, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simpa using hw
      · simp only [Fin.cons_succ]
        exact j.dp.ideal_comp (Ideal.mem_map_of_mem _ (hy k))
    · intro V hV φ z hz
      obtain ⟨ψ₁, ⟨hψ₁, hψ₁y⟩, huniq₁⟩ := huniv V hV φ (fun k ↦ z k.succ) (fun k ↦ hz k.succ)
      obtain ⟨ψ, ⟨hψ, hψw⟩, huniq⟩ := hunivQ V hV ψ₁ (z 0) (hz 0)
      refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
      · rw [Category.assoc, hψ, hψ₁]
      · intro k
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · simpa using hψw
        · simp only [Fin.cons_succ]
          rw [← Thick.comp_φ, hψ]
          exact hψ₁y k
      · rintro ψ' ⟨hψ', hψ'y⟩
        have h1 : j ≫ ψ' = ψ₁ := by
          refine huniq₁ (j ≫ ψ') ⟨?_, fun k ↦ ?_⟩
          · rw [← Category.assoc]
            exact hψ'
          · rw [Thick.comp_φ]
            have := hψ'y k.succ
            simpa only [Fin.cons_succ] using this
        refine huniq ψ' ⟨h1, ?_⟩
        have := hψ'y 0
        simpa only [Fin.cons_zero] using this

end FubiniStudyChowHeightFormula₂.Adr
