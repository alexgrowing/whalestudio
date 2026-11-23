import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.GlobalPf

def gam {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) : T ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V (by simp)

def Affine : Prop := ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K) {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens),
  IsAffineOpen V → BC q i k (gam p V) → Eqv _ (sch.map (pullback.fst p (Spec.map k) ∣_ V)) (tw q i)

def LocEt : Prop := ∀ {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p] (x : X),
  ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
    ∃ c : CommRingCat.of (MvPolynomial (Fin n) T) ⟶ Γ(X, V), Et c ∧
      CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T) ≫ c = gam p V

theorem Global_of (hZ : ZarLocal) (hA : Affine) (hL : LocEt) : Global := by
  intro H q i T K k hG X p _
  refine hZ H (ZMod q) (tw q i) (pullback.fst p (Spec.map k)) fun x => ?_
  obtain ⟨U, n, hx, hU⟩ := hL p x
  refine ⟨U, hx, fun V hV hVU => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hU V hV hVU
  have hb := hG n _ c hc
  rw [hcg] at hb
  exact hA q i k p V hV hb

end LateralTheory.E.GlobalPf

end
