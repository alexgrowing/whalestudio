import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivSupOfIsotypicPartsInternalDirectSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTripleForOfOff

noncomputable section

namespace GlobalTheory.TwInputs.EigModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.Triple (heckeVal satake muBase)

variable {D : D7}

theorem heckeVal_mul (μ δ : HChar D.host.E) (π : D.naut.CG D.R.r) (k : ℕ) (P : PlE D.host) :
    heckeVal (μ * δ) π k P = (((δ.val P : ℂˣ) : ℂ)⁻¹) ^ k * heckeVal μ π k P := by
  have e : satake (μ * δ) π P = (satake μ π P).map fun a => ((δ.val P : ℂˣ) : ℂ)⁻¹ • a := by
    rw [satake, satake, Multiset.map_map]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [HChar.val_mul, Units.val_mul, mul_inv, Function.comp_apply, smul_eq_mul]
    ring
  rw [heckeVal, heckeVal, e, ← Multiset.pow_smul_esymm, smul_eq_mul]
  ring

variable {cf : CharFrame D} {Rw : RowSide D} {Sb : Finset (PlE D.host)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}

theorem eig_eq_heckeVal (h : EigTrue D cf Rw Sb eig) (j : Fin D.R.m) {σ} (h1 : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h2 : D.nd.goodRow σ) {π} (hπ : GlobalTheory.EigTie.IsRowPar Rw σ π) {P} (hP : IsSplitPl D.host P) (hS : P ∉ Sb) {k}
    (hk : 1 ≤ k) (hk' : k ≤ D.R.r) :
    D.what₂.embLL (eig (j.1 + 1) σ k P : D.what₂.LL) = heckeVal (cf.mu0 j) π k P := by
  rw [(h j σ h1 h2 P hP hS).2 k hk hk', heckeVal, satake, hπ.2 P hP]

theorem eig_twist (h : EigTrue D cf Rw Sb eig) (l : ℕ) (j : Fin D.R.m) {σ} (h1 : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h2 : D.nd.goodRow σ) {π} (hπ : GlobalTheory.EigTie.IsRowPar Rw σ π) {P} (hP : IsSplitPl D.host P) (hS : P ∉ Sb) {k}
    (hk : 1 ≤ k) (hk' : k ≤ D.R.r) :
    ((((cf.delAt l).val P : ℂˣ) : ℂ)⁻¹) ^ k * D.what₂.embLL (eig (j.1 + 1) σ k P : D.what₂.LL) =
      heckeVal (muBase cf l j) π k P := by
  rw [eig_eq_heckeVal h j h1 h2 hπ hP hS hk hk', muBase, heckeVal_mul]

theorem eig_top (h : EigTrue D cf Rw Sb eig) (hR : RowParam D Rw) (j : Fin D.R.m) {σ} (h1 : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h2 : D.nd.goodRow σ) {P} (hP : IsSplitPl D.host P) (hS : P ∉ Sb) :
    ∃ π, GlobalTheory.EigTie.IsRowPar Rw σ π ∧
      D.what₂.embLL (eig (j.1 + 1) σ D.R.r P : D.what₂.LL) = (satake (cf.mu0 j) π P).prod := by
  obtain ⟨π, hπ⟩ := hR (j.1 + 1) (by omega) j.2 σ h1 h2
  refine ⟨π, hπ, ?_⟩
  rw [eig_eq_heckeVal h j h1 h2 hπ hP hS (GlobalTheory.GalChar.odd_r D.R).pos le_rfl,
    GlobalTheory.Triple.heckeVal_top _ _ _ (by rw [hπ.2 P hP]; exact (h j σ h1 h2 P hP hS).1)]

theorem eig_unique {eig'} (h : EigTrue D cf Rw Sb eig) (h' : EigTrue D cf Rw Sb eig') (j : Fin D.R.m) {σ}
    (h1 : D.what₂.isot (j.1 + 1) σ ≠ ⊥) (h2 : D.nd.goodRow σ) {P} (hP : IsSplitPl D.host P) (hS : P ∉ Sb) {k}
    (hk : 1 ≤ k) (hk' : k ≤ D.R.r) : eig (j.1 + 1) σ k P = eig' (j.1 + 1) σ k P :=
  Subtype.ext (D.what₂.embLL.injective
    (((h j σ h1 h2 P hP hS).2 k hk hk').trans ((h' j σ h1 h2 P hP hS).2 k hk hk').symm))

theorem exists_eig (hR : RowParam D Rw) (hS : ∀ k, placesOver D.host.E (D.host.g k) ⊆ (Sb : Set (PlE D.host)))
    (hv : ∀ (j : Fin D.R.m) σ π, D.what₂.isot (j.1 + 1) σ ≠ ⊥ → D.nd.goodRow σ → GlobalTheory.EigTie.IsRowPar Rw σ π →
      ∀ k P, IsSplitPl D.host P → P ∉ Sb → ∃ x : ↥D.LL0, D.what₂.embLL (x : D.what₂.LL) = heckeVal (cf.mu0 j) π k P) :
    ∃ eig, EigTrue D cf Rw Sb eig := by
  have H : ∀ (j : ℕ) σ k P, ∃ x : ↥D.LL0, ∀ j' : Fin D.R.m, j'.1 + 1 = j → D.what₂.isot (j'.1 + 1) σ ≠ ⊥ → D.nd.goodRow σ →
      IsSplitPl D.host P → P ∉ Sb → ∃ π, GlobalTheory.EigTie.IsRowPar Rw σ π ∧
        D.what₂.embLL (x : D.what₂.LL) = heckeVal (cf.mu0 j') π k P := by
    intro j σ k P
    by_cases h : ∃ j' : Fin D.R.m, j'.1 + 1 = j ∧ D.what₂.isot (j'.1 + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ ∧ IsSplitPl D.host P ∧ P ∉ Sb
    · obtain ⟨j', e, h1, h2, h3, h4⟩ := h
      obtain ⟨π, hπ⟩ := hR (j'.1 + 1) (by omega) j'.2 σ h1 h2
      obtain ⟨x, hx⟩ := hv j' σ π h1 h2 hπ k P h3 h4
      refine ⟨x, fun j'' e' _ _ _ _ => ⟨π, hπ, ?_⟩⟩
      obtain rfl : j'' = j' := Fin.ext (by omega)
      exact hx
    · exact ⟨0, fun j' e h1 h2 h3 h4 => (h ⟨j', e, h1, h2, h3, h4⟩).elim⟩
  choose eig heig using H
  refine ⟨eig, fun j σ h1 h2 P hP hP' => ⟨?_, fun k _ _ => ?_⟩⟩
  · obtain ⟨π, hπ⟩ := hR (j.1 + 1) (by omega) j.2 σ h1 h2
    rw [← hπ.2 P hP]
    exact hπ.1.unr P fun k hk => hP' (hS k hk)
  · obtain ⟨π, hπ, e⟩ := heig (j.1 + 1) σ k P j rfl h1 h2 hP hP'
    rw [e, heckeVal, satake, hπ.2 P hP]

theorem eigOcc_scalar (S : RatDat D.ntw) (θ) (c : ℕ → ℕ → PlE D.host → ↥D.LL0)
    (hne : ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≠ ⊥) :
    EigOcc D S θ (fun j k P => ((c j k P : ↥D.LL0) : D.what₂.LL) • 1) Sb (fun j _ k P => c j k P) := by
  intro j h1 h2 σ _ _
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (hne j h1 h2)
  exact ⟨x, hx, h0, fun k P _ _ _ _ => rfl⟩

theorem not_eigOcc (S : RatDat D.ntw) (θ) (hL) {j} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {σ} (ho : D.what₂.isot j σ ≠ ⊥)
    (hg : D.nd.goodRow σ) (hb : goodL D S θ j = ⊥) : ¬ EigOcc D S θ hL Sb eig := fun h =>
  let ⟨x, hx, h0, _⟩ := h j h1 h2 σ ho hg
  h0 (by rwa [hb, Submodule.mem_bot] at hx)

theorem meetsReference_of_meetsAll (h : MeetsAll D) : GlobalTheory.TripTie.MeetsP0 D := fun i _ j _ b W => h i j b W

theorem sig_all_of (hN : NoFormsOff D) (hM : MeetsAll D) (hC : CommAll D)
    (hall : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, GlobalTheory.EigTie.IsEigSys D.nexp i j b ev →
      ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, HkIdx i k P → GlobalTheory.EigTie.sigEv s k P = ev k P) :
    D.nexp.sig_all := by
  intro i j b x ev hx he hk
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · let W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
      Eigsp D.nexp i j b ev ⊓ LinearMap.ker (eG D.nexp i j b - LinearMap.id)
    have mW : ∀ y, y ∈ W ↔ (∀ k P, HkIdx i k P → D.nexp.hkF i j b k P y = ev k P • y) ∧ eG D.nexp i j b y = y := by
      intro y
      simp only [W, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hxW : x ∈ W := (mW x).2 ⟨fun k P h => hk k P h.1 h.2.1 h.2.2.1 h.2.2.2, he⟩
    have hst : GStable D.nexp i j b W := by
      intro g y hy
      obtain ⟨a, c⟩ := (mW y).1 hy
      refine (mW _).2 ⟨fun k P h => by rw [hC i j hj b k P h, a k P h, map_smul], ?_⟩
      have e := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
        (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
        (D.nexp.eAlg_central i b (MonoidAlgebra.of _ _ g))
      rw [map_mul, map_mul, MonoidAlgebra.lift_of] at e
      have e2 := LinearMap.congr_fun e y
      change eG D.nexp i j b (D.nexp.actG i j b g y) = D.nexp.actG i j b g (eG D.nexp i j b y) at e2
      rw [e2, c]
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1
      (hM i j b W ((Submodule.ne_bot_iff _).2 ⟨x, hxW, hx⟩) hst fun y hy => ((mW y).1 hy).2)
    obtain ⟨a, c⟩ := (mW y).1 hy1
    obtain ⟨s, e1, e2, e3⟩ := hall i j hj b ev ⟨y, ⟨y, hy2, c⟩, hy0, a⟩
    exact ⟨s, e1, e2, fun k P p q r t => e3 k P ⟨p, q, r, t⟩⟩
  · exact absurd ((hN i j hj b).elim x 0) hx

section Laws

open GlobalTheory.SupLaw.Model

variable (D) (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

theorem noFormsOff : NoFormsOff (GlobalTheory.SupLaw.Model.rec D A s) := fun i j hj _ =>
  haveI : IsEmpty (Pt D j) := ⟨fun y => hj y.2⟩
  inferInstanceAs (Subsingleton (Pt D j → KK D i))

theorem meetsAll : MeetsAll (GlobalTheory.SupLaw.Model.rec D A s) := fun i j b W hW _ _ => by
  have := goodFiltration_eq_top D A s i j b
  intro h
  apply hW
  rw [← h]
  exact (inf_eq_left.2 (this ▸ le_top)).symm

theorem commAll (t) : CommAll (GlobalTheory.SupLaw.Model.rec D (scal D t) s) := fun i j _ b k P _ g x =>
  ((transl D i j g).map_smul (t i k) x).symm

theorem fullAll : FullAll (GlobalTheory.SupLaw.Model.rec D A s) := fun i j _ b => by
  rw [eq_top_iff]
  intro f _
  obtain ⟨c, hc⟩ := exists_pow D i j f
  have hl : ((D.ntw.l i : KK D i)) ^ c ≠ 0 := pow_ne_zero _ (GlobalTheory.TwAll.Model.l_ne_zero D.nth i)
  have h2 := Submodule.smul_mem (Submodule.span (KK D i)
    ((LinearMap.range (intF D i j) : Submodule (D.ntw.O i) (Pt D j → KK D i)) : Set (Pt D j → KK D i)))
    (((D.ntw.l i : KK D i)) ^ c)⁻¹ (Submodule.subset_span hc)
  have e : ((D.ntw.l i : D.ntw.O i) ^ c) • (show Pt D j → KK D i from f) = ((D.ntw.l i : KK D i)) ^ c • (show Pt D j → KK D i from f) := by
    rw [← algebraMap_smul (KK D i), map_pow, map_natCast]
  rw [e, smul_smul, inv_mul_cancel₀ hl, one_smul] at h2
  exact h2

theorem all_laws : ∃ (D' : D7) (_ : D'.ntw.Tw ≃ D.ntw.Tw),
    (∀ i, ∀ j ∈ Finset.Icc 1 D'.R.m, ∀ b, Nontrivial (D'.nexp.Fm i j b)) ∧
    NoFormsOff D' ∧ MeetsAll D' ∧ CommAll D' ∧ FullAll D' :=
  ⟨GlobalTheory.SupLaw.Model.rec D (scal D fun _ k => k) fun _ _ => 1, Equiv.refl _, fun i j hj b => nontrivial_fm D _ _ i j hj b,
    noFormsOff D _ _, meetsAll D _ _, commAll D _ _, fullAll D _ _⟩

theorem not_commAll (i : D.ntw.Tw) (k P) (hP : HkIdx (D := D) i k P) (g : G0g D.nd) (hg : g ≠ 1) :
    ¬ CommAll (GlobalTheory.SupLaw.Model.rec D (fun i j _ _ => unitOp D i j 1 1) s) := fun h => by
  have h1 := congrFun (h i 1 (one_mem_range D) true k P hP g (fun _ => 1)) ⟨1, one_mem_range D⟩
  simp [unitOp, transl, hg] at h1

end Laws

end GlobalTheory.TwInputs.EigModel

end
