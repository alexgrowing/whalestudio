import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelEqParahoricCategory
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem cbe_iff {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {r h' κ s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) (hκ : κ ∈ J) :
    s ∈ Loc.Cbe J (r * h' * κ) ↔ r⁻¹ * s * r ∈ Loc.Cbe J h' := by
  constructor
  · rintro ⟨hs1, hs2⟩
    refine ⟨(Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem ((Loc.R1 k n c).inv_mem hr) hs1) hr, ?_⟩
    have h2 : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J := hs2
    show h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J
    have e : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ = κ * ((r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹) * κ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hκ h2) (inv_mem hκ)
  · rintro ⟨hs1, hs2⟩
    have hs1' : s ∈ Loc.R1 k n c := by
      have := (Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem hr hs1) ((Loc.R1 k n c).inv_mem hr)
      rwa [show r * (r⁻¹ * s * r) * r⁻¹ = s by group] at this
    refine ⟨hs1', ?_⟩
    have h2 : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J := hs2
    show (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J
    have e : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ = κ⁻¹ * (h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹) * κ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hκ) h2) hκ

theorem red_conj {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (δ : GLint E n P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ y ∈ stdAt E n P, redV P (g y) = A.1.mulVec (redV P y)) :
    ∀ y ∈ stdAt E n P, redV P ((δ.1 * g * δ.1⁻¹) y) =
      (GlobalTheory.TopStep.redGL n P δ * A * (GlobalTheory.TopStep.redGL n P δ)⁻¹).1.mulVec (redV P y) := by
  intro y hy
  have h1 : δ.1⁻¹ y ∈ stdAt E n P := ((δ⁻¹).2 y).2 hy
  have h2 : g (δ.1⁻¹ y) ∈ stdAt E n P := (hg _).2 h1
  show redV P (δ.1 (g (δ.1⁻¹ y))) = _
  rw [GlobalTheory.TopStep.redV_redGL δ h2, hA _ h1]
  have h3 := GlobalTheory.TopStep.redV_redGL δ⁻¹ hy
  have e : (δ⁻¹).1 y = δ.1⁻¹ y := rfl
  rw [e] at h3
  rw [h3, map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem inX_mem_lamYat_iff {X : Fields} {Pr : Primes X} {R : Ranks} (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : Sp X.E (R.N j)) :
    Loc.inX X.E (R.N j) (cOf R j) x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ stdAt X.E (R.N j) P := by
  unfold lamYat
  rw [if_pos hP]
  exact ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
    GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩

theorem lamRow_tup {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu mu' : Tup X.F X.E X.K S) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (f : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) :
    lamRow Ch mu true j P f = lamRow Ch mu' true j P f := by
  unfold lamRow
  simp only [if_pos hP, if_true]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem loc_match : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  intro X Pr R Ch sel S mu mu' cst cst' L L' G m2 _ _ _ hs hs' hok hok' j hj b b' w r κ hr hκ he
  have hP : w.1 ∈ Pr.vGs := w.2
  have hjm : j < R.m := by rw [hok.hm]; omega
  have hG := hok.grpG j b w
  have hG' := hok'.grpG j b' w
  have hC := hok.chrG j b w
  have hC' := hok'.chrG j b' w
  have hint := hok.int j b ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hint' := hok'.int j b' ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hst := hok.stabG j b ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hst' := hok'.stabG j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hpsi := fun a ha => hok.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  have hpsi' := fun a ha => hok'.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  rw [hs] at hG hC hint
  rw [hs'] at hG' hC' hint'
  unfold chiInv at hC hC'
  rw [hs] at hC
  rw [hs'] at hC'
  generalize L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = h at hG hC hint hst he
  generalize L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ = h' at hG' hC' hint' hst' he
  subst he

  have hκs := jat_le_stab_lamY true j w.1 hP κ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j w.1) := by
    have := mul_mem (mul_mem hst (inv_mem hκs)) (inv_mem hst')
    rwa [show r * h' * κ * κ⁻¹ * h'⁻¹ = r by group] at this
  obtain ⟨γ, hγ⟩ := GlobalTheory.QNormal.exists_res hr
  have hγint : γ ∈ GLint X.E (R.N j) w.1 := by
    intro y
    rw [← inX_mem_lamYat_iff (Pr := Pr) j hP, ← inX_mem_lamYat_iff (Pr := Pr) j hP, ← hγ y]
    exact hrs _
  set γg : GLint X.E (R.N j) w.1 := ⟨γ, hγint⟩ with hγg
  refine ⟨GlobalTheory.TopStep.redGL (R.N j) w.1 γg⁻¹, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    have e : γ = 1 := by
      refine LinearEquiv.ext fun y => GlobalTheory.QNormal.inX_injective (c := cOf R j) ?_
      rw [← hγ y]
      rfl
    have e2 : γg = 1 := Subtype.ext e
    rw [e2, inv_one, map_one]
  · intro hbar
    rw [hG, hG']
    constructor
    · rintro ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩
      refine ⟨γ⁻¹ * g * γ, ⟨r⁻¹ * r₁ * r, (cbe_iff _ hr hκ).1 hr₁, GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres⟩, ?_⟩
      intro y hy
      exact red_conj γg⁻¹ (hint ⟨r₁, hr₁, hres⟩) hred y hy
    · rintro ⟨g', ⟨r₁', hr₁', hres'⟩, hred'⟩
      have hγ' : ∀ y, r⁻¹ (Loc.inX X.E (R.N j) (cOf R j) y) = Loc.inX X.E (R.N j) (cOf R j) (γ⁻¹ y) := by
        intro y
        show r.symm _ = _
        rw [LinearEquiv.symm_apply_eq, hγ]
        show _ = Loc.inX X.E (R.N j) (cOf R j) (γ (γ.symm y))
        rw [LinearEquiv.apply_symm_apply]
      have hmem : r * r₁' * r⁻¹ ∈ Loc.Cbe (Jat (Pr := Pr) true j w.1) (r * h' * κ) := by
        refine (cbe_iff _ hr hκ).2 ?_
        rwa [show r⁻¹ * (r * r₁' * r⁻¹) * r = r₁' by group]
      refine ⟨γ * g' * γ⁻¹, ⟨r * r₁' * r⁻¹, hmem, fun y => GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ' hres' y⟩, ?_⟩
      intro y hy
      have e : ∀ (Q A : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Q * (Q⁻¹ * A * Q⁻¹⁻¹) * Q⁻¹ = A := by
        intro Q A
        group
      have := red_conj γg (hint' ⟨r₁', hr₁', hres'⟩) hred' y hy
      rw [map_inv, e] at this
      exact this
  · intro hbar hbar' hx
    obtain ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩ := (hG hbar.1).1 hbar.2
    have hgint := hint ⟨r₁, hr₁, hres⟩
    have hr₁' := (cbe_iff _ hr hκ).1 hr₁
    have hres' := GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres
    have hred' : ∀ y ∈ stdAt X.E (R.N j) w.1, redV w.1 ((γ⁻¹ * g * γ) y) = hbar'.1.1.mulVec (redV w.1 y) := by
      intro y hy
      rw [hx]
      exact red_conj γg⁻¹ hgint hred y hy
    have e1 := hC hbar g r₁ hr₁ hres hred
    have e2 := hC' hbar' (γ⁻¹ * g * γ) (r⁻¹ * r₁ * r) hr₁' hres' hred'
    refine Units.ext ?_
    rw [e1, e2, GlobalTheory.Proof.level_eq_parahoric_category.n1Arg_conj_eq hr hr₁.1]

    have hr₁s : r₁ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) := by
      have h1 : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁.2
      have h2 := jat_le_stab_lamY true j w.1 hP _ h1
      have h3 := mul_mem (mul_mem hst h2) (inv_mem hst)
      rw [show r * h' * κ * ((r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹) * (r * h' * κ)⁻¹ = r₁ by group] at h3
      unfold lamYat at h3
      rw [if_pos hP] at h3
      exact h3
    have hq := GlobalTheory.TopStep.qOf_ne_zero (P := w.1) (E := X.E)
    have hia := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r₁ hr₁s
    have ea : ((qOf w.1 : ℕ) : X.E) * Loc.n1Arg r₁ / ((qOf w.1 : ℕ) : X.E) = Loc.n1Arg r₁ := by
      field_simp
    have p1 := hpsi _ hia
    have p2 := hpsi' _ hia
    rw [ea] at p1 p2
    rw [p1, p2]
    congr 1

    rw [lamRow_tup Ch mu mu' j hP]
    have ht : h'⁻¹ * (r⁻¹ * r₁ * r) * h'⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁'.2
    rw [inv_inv] at ht
    have e : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ) = κ⁻¹ * (h'⁻¹ * (r⁻¹ * r₁ * r) * h') * κ := by group
    rw [e]
    generalize h'⁻¹ * (r⁻¹ * r₁ * r) * h' = t at ht ⊢
    have LM := GlobalTheory.SymLevelMul.lamRow_mul Ch mu' j w.1 hjm hP
    have hκi : κ⁻¹ ∈ Jat (Pr := Pr) (R := R) true j w.1 := inv_mem hκ
    rw [LM _ (mul_mem hκi ht) _ hκ, LM _ hκi _ ht]
    have e3 : lamRow Ch mu' true j w.1 t.toLinearMap =
        lamRow Ch mu' true j w.1 t.toLinearMap * lamRow Ch mu' true j w.1 (κ⁻¹ : AutY X R j).toLinearMap *
          lamRow Ch mu' true j w.1 κ.toLinearMap := by
      conv_lhs => rw [show t = t * κ⁻¹ * κ by group]
      rw [LM _ (mul_mem ht hκi) _ hκ, LM _ ht _ hκi]
    linear_combination -e3

end GlobalTheory.Mem.Col2.IdxEx.LocMatch
