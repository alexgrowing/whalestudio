import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkVal

open GlobalTheory.FlagAmple.PlkLoc GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.FlagBundle GlobalTheory.FlagEmb GlobalTheory.QCoh.Qcqs

section Stalk

variable {X : Scheme.{0}}

theorem top_le_preimage_stalk (y : X) {K : Type} [CommRing K] (ψ : X.presheaf.stalk y →+* K) {N : X.Opens}
    (hy : y ∈ N) : ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk y) ⁻¹ᵁ N := by
  intro p _
  have h : (X.fromSpecStalk y) (spMap ψ p) ∈ {z | z ⤳ y} := Scheme.range_fromSpecStalk ▸ ⟨_, rfl⟩
  exact h.mem_open N.isOpen hy

theorem appLE_stalk_top (y : X) {K : Type} [CommRing K] (ψ : X.presheaf.stalk y →+* K) {N : X.Opens}
    (hy : y ∈ N) (h : Γ(X, N)) :
    ((spMap ψ ≫ X.fromSpecStalk y).appLE N ⊤ (top_le_preimage_stalk y ψ hy)).hom h =
      fnOn ⊤ (ψ (X.presheaf.germ N y hy h)) := by
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hy]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  have e2 := congrArg (fun χ => χ.hom (X.presheaf.germ N y hy h))
    (Scheme.ΓSpecIso_inv_naturality (R := X.presheaf.stalk y) (S := .of K) (CommRingCat.ofHom ψ))
  refine Eq.trans ?_ (congrArg (resG (Sp K) (le_top : (⊤ : (Sp K).Opens) ≤ ⊤)) e2.symm)
  rfl

end Stalk

section Stalk2

variable {X : Scheme.{0}} [IsIntegral X]

theorem appLE_stalk (y : X) {K : Type} [CommRing K] (ψ : X.presheaf.stalk y →+* K) {W' : X.Opens}
    {W : (Sp K).Opens} (e : W ≤ (spMap ψ ≫ X.fromSpecStalk y) ⁻¹ᵁ W') (h : Γ(X, W')) (s : X.presheaf.stalk y)
    (hg : genericPoint X ∈ W') (hs : algebraMap _ X.functionField s = fnOf W' hg h) :
    ((spMap ψ ≫ X.fromSpecStalk y).appLE W' W e).hom h = fnOn W (ψ s) := by
  obtain ⟨N, hyN, h', rfl⟩ := X.presheaf.exists_germ_eq s
  have hN := top_le_preimage_stalk y ψ hyN
  have e2 : W ≤ (spMap ψ ≫ X.fromSpecStalk y) ⁻¹ᵁ (N ⊓ W') := fun p hp => ⟨hN trivial, e hp⟩
  have hres : resG X (inf_le_right : N ⊓ W' ≤ W') h = resG X inf_le_left h' := fn_ext fun hg' => by
    rw [fnOf_resG, fnOf_resG, ← hs, algebraMap_germ hyN]
  calc ((spMap ψ ≫ X.fromSpecStalk y).appLE W' W e).hom h
      = ((spMap ψ ≫ X.fromSpecStalk y).appLE (N ⊓ W') W e2).hom (resG X inf_le_right h) :=
        (appLE_resG _ inf_le_right e2 h).symm
    _ = ((spMap ψ ≫ X.fromSpecStalk y).appLE (N ⊓ W') W e2).hom (resG X inf_le_left h') := by rw [hres]
    _ = ((spMap ψ ≫ X.fromSpecStalk y).appLE N W (le_top.trans hN)).hom h' := appLE_resG _ inf_le_left e2 h'
    _ = resG _ (le_top : W ≤ ⊤) (((spMap ψ ≫ X.fromSpecStalk y).appLE N ⊤ hN).hom h') :=
        (resG_appLE _ hN le_top h').symm
    _ = fnOn W (ψ (X.presheaf.germ N y hyN h')) := by rw [appLE_stalk_top, resG_fnOn]

end Stalk2

section Tri

theorem prod_castLE {M : Type} [CommMonoid M] {n i : ℕ} (h : i ≤ n) (f : Fin n → M) :
    ∏ a : Fin i, f (Fin.castLE h a) = ∏ a : Fin n, if (a : ℕ) < i then f a else 1 := by
  rw [← Finset.prod_filter]
  have e : (Finset.univ.filter fun a : Fin n => (a : ℕ) < i) = Finset.univ.map (Fin.castLEEmb h) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  rw [e, Finset.prod_map]
  rfl

theorem sum_castLE {M : Type} [AddCommMonoid M] {n i : ℕ} (h : i ≤ n) (f : Fin n → M)
    (hf : ∀ a : Fin n, i ≤ (a : ℕ) → f a = 0) : ∑ a : Fin n, f a = ∑ a : Fin i, f (Fin.castLE h a) := by
  have e : (Finset.univ.filter fun a : Fin n => (a : ℕ) < i) = Finset.univ.map (Fin.castLEEmb h) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  calc ∑ a : Fin n, f a = ∑ a : Fin n, if (a : ℕ) < i then f a else 0 :=
        Finset.sum_congr rfl fun a _ => by
          split_ifs with ha
          · rfl
          · exact hf a (not_lt.1 ha)
    _ = ∑ a : Fin i, f (Fin.castLE h a) := by
      rw [← Finset.sum_filter, e, Finset.sum_map]
      rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem plkFn_mul_tri {K : Type} [CommRing K] (T M : Mat Dw.mult K) (hT : ∀ τ i l, i < l → T τ i l = 0)
    (x : Step Dw) :
    plkFn (T * M) x = (∏ a : Fin (x.2.1 : ℕ), T x.1 (Fin.castLE x.2.1.2.le a) (Fin.castLE x.2.1.2.le a)) • plkFn M x := by
  funext q
  let A : Matrix (Fin (x.2.1 : ℕ)) (Fin (x.2.1 : ℕ)) K :=
    Matrix.of fun l m => T x.1 (Fin.castLE x.2.1.2.le l) (Fin.castLE x.2.1.2.le m)
  have hA : A.det = ∏ a : Fin (x.2.1 : ℕ), T x.1 (Fin.castLE x.2.1.2.le a) (Fin.castLE x.2.1.2.le a) :=
    Matrix.det_of_lowerTriangular A fun l m hlm => hT _ _ _ ((Fin.castLE_lt_castLE_iff _).2 hlm)
  simp only [plkFn, plk, what₂, Pi.smul_apply, smul_eq_mul, ← hA, ← Matrix.det_mul]
  congr 1
  ext l l'
  simp only [Matrix.of_apply, Matrix.mul_apply, Pi.mul_apply, A]
  refine sum_castLE x.2.1.2.le _ fun m hm => ?_
  rw [hT _ _ _ (Fin.lt_iff_val_lt_val.2 (by simpa using lt_of_lt_of_le l.2 hm)), zero_mul]

end Tri

section Eqn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem isEqn_detDiv (C : FlagCpt Z e) (y : C.Y.X) (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → C.Y.Fnˣ)
    (hu : ∀ a, (C.gr τ a).IsEqn y (u a)) (i : ℕ) (hi : i ≤ Dw.mult τ) :
    (detDiv C τ i).IsEqn y (∏ a : Fin i, u (Fin.castLE hi a)) := by
  rw [prod_castLE hi, detDiv]
  have key : ∀ s : Finset (Fin (Dw.mult τ)), (∑ a ∈ s, if (a : ℕ) < i then C.gr τ a else 0).IsEqn y
      (∏ a ∈ s, if (a : ℕ) < i then u a else 1) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      refine IsEqn.add ?_ ih
      split_ifs
      · exact hu a
      · exact isEqn_zero y
  exact key _

theorem unitAt_chart (C : FlagCpt Z e) (y : C.Y.X) (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → C.Y.Fnˣ)
    (hu : ∀ a, (C.gr τ a).IsEqn y (u a)) (i : ℕ) (hi : i ≤ Dw.mult τ) (j : (toLB (-detDiv C τ i)).ι)
    (hj : y ∈ (toLB (-detDiv C τ i)).U j) :
    UnitAt y ((∏ a : Fin i, (u (Fin.castLE hi a) : C.Y.Fn)) * j.1.2) := by
  have h2 := (isEqn_detDiv C y τ u hu i hi).neg.iff_unitAt.1 (j.2.2 y hj)
  rw [Units.val_inv_eq_inv_val, div_inv_eq_mul, Units.coe_prod, mul_comm] at h2
  exact h2

end Eqn

section Plk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem map_plkFn {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') (M : Mat Dw.mult K) (x : Step Dw)
    (q : Fin (plkM x + 1)) : φ (plkFn M x q) = plkFn (M.map φ) x q :=
  congrFun (map_plk φ (what₂ (M x.1) x.2.1) id) q

theorem plkFn_ne_zero {K : Type} [Field K] (M : Mat Dw.mult K) (hM : ∀ τ, IsUnit (M τ).det) (x : Step Dw) :
    plkFn M x ≠ 0 := by
  have h0 := (Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (hM x.1))).comp _
    (Fin.castLE_injective x.2.1.2.le)
  have h1 := h0.map' (LinearEquiv.funCongrLeft K K (finCongr (Nat.sub_add_cancel (Fin.pos x.2.1)))).toLinearMap
    (LinearEquiv.ker _)
  exact ((PlkSpan.main K _ _ (what₂ (M x.1) x.2.1) (what₂ (M x.1) x.2.1)).1).2 h1

end Plk

section Main

theorem secPull_pullOn_f {X Y Z : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W)
    (θ : ∀ i, Γ(X, W ⊓ L.U i)) (hθ : θ ∈ secOn L W) (g : Z ⟶ Y) (k : PUnit → PUnit → L.ι)
    (e : ((L.pull φ).pull g).U k ≤ (g ≫ φ) ⁻¹ᵁ (W ⊓ L.U (k ⟨⟩ ⟨⟩))) :
    (secPull (KeyNear.pullOn φ hW θ hθ) g).f k = ((g ≫ φ).appLE _ _ e).hom (θ (k ⟨⟩ ⟨⟩)) := by
  show resG Z _ ((g.app _).hom ((φ.appLE _ _ _).hom (θ (k ⟨⟩ ⟨⟩)))) = _
  rw [Scheme.Hom.app_eq_appLE, resG_appLE]
  exact appLE_appLE g φ _ _ _

theorem top_le_pull_pull_U {X Y Z : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (g : Z ⟶ Y) (i : L.ι)
    (h : ∀ p, φ (g p) ∈ L.U i) : ⊤ ≤ ((L.pull φ).pull g).U (fun _ _ => i) := by
  refine le_trans ?_ (pull_U (L.pull φ) g (fun _ _ => i)).ge
  refine le_trans ?_ (g.preimage_mono (pull_U L φ (fun _ => i)).ge)
  exact fun p _ => h p

theorem le_preimage_inf {X Z : Scheme.{0}} (U : X.Opens) (g : Z ⟶ U.toScheme) (V : X.Opens) (W : Z.Opens)
    (h : ∀ p, U.ι (g p) ∈ V) : W ≤ (g ≫ U.ι) ⁻¹ᵁ (U ⊓ V) := fun p _ => ⟨(g p).2, h p⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem value_gen (C : FlagCpt Z e) (U : C.Y.X.Opens) (B : Mat Dw.mult C.Y.Fn) (x : Step Dw)
    (hreg : ∀ q, ∀ z ∈ U, (-detDiv C x.1 (x.2.1 : ℕ)).RegularAt z (plkFn B x q))
    (ht : ⨆ q, nonzeroLocus (plkSec C U B x q) = ⊤) {R K : Type} [CommRing R] [Field K]
    (f : U.toScheme ⟶ Sp R) (a : Sp K ⟶ U.toScheme) (c : R →+* K) (hac : a ≫ f = spMap c) (y : C.Y.X)
    (ψ : C.Y.X.presheaf.stalk y →+* K) (P : Mat Dw.mult (C.Y.X.presheaf.stalk y)) (T : Mat Dw.mult C.Y.Fn)
    (hay : a ≫ U.ι = spMap ψ ≫ stalkPt C.Y y) (hP : ∀ τ, IsUnit (P τ).det)
    (hB : B = T * P.map (algebraMap (C.Y.X.presheaf.stalk y) C.Y.Fn)) (hT : ∀ τ i l, i < l → T τ i l = 0)
    (hTd : ∀ τ i, ∃ u : C.Y.Fnˣ, T τ i i = u ∧ (C.gr τ i).IsEqn y u) :
    ∃ hv, a ≫ toProj f (plkSec C U B x) ht = pt c (plkFn (P.map ψ) x) hv := by
  have hw0 : plkFn (P.map ψ) x ≠ 0 := plkFn_ne_zero _ (fun τ => by
    have := (hP τ).map ψ
    rwa [RingHom.map_det] at this) x
  have hw := span_range_eq_top_iff_ne_zero.2 hw0
  refine ⟨hw, ?_⟩
  obtain ⟨i, hi0⟩ := Function.ne_iff.1 hw0
  choose u hu hue using hTd
  have hay' : a ≫ U.ι = spMap ψ ≫ C.Y.X.fromSpecStalk y := hay
  obtain ⟨i₀, hi₀⟩ := exists_chart (isLB_toLB (-detDiv C x.1 (x.2.1 : ℕ))) y
  obtain ⟨v, -, hva⟩ := unitAt_chart C y x.1 (u x.1) (hue x.1) x.2.1 x.2.1.2.le i₀ hi₀
  have hpt : ∀ p, U.ι (a p) ∈ (toLB (-detDiv C x.1 (x.2.1 : ℕ))).U i₀ := fun p => by
    have h1 := top_le_preimage_stalk y ψ hi₀ (show p ∈ (⊤ : (Sp K).Opens) from trivial)
    show (a ≫ U.ι) p ∈ _
    rw [hay']
    exact h1
  rw [← toProj_secPull ht a, hac]
  refine (eq_toProj_of_locally _ (pt_str c _ hw) fun z => ?_).symm
  let k : PUnit → PUnit → (toLB (-detDiv C x.1 (x.2.1 : ℕ))).ι := fun _ _ => i₀
  have hWtop : ⊤ ≤ ((((toLB (-detDiv C x.1 (x.2.1 : ℕ))).pull U.ι).pull a).U k) := top_le_pull_pull_U _ U.ι a i₀ hpt
  have hi : ((((toLB (-detDiv C x.1 (x.2.1 : ℕ))).pull U.ι).pull a).U k) ≤
      pt c (plkFn (P.map ψ) x) hw ⁻¹ᵁ chart R (plkM x) i := fun p _ => by
    rw [pt_preimage_chart]
    exact mem_spOpen.2 fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_iff_ne_zero.2 hi0))
  refine ⟨_, hWtop trivial, k, le_rfl, i, hi, fnOn _ (ψ v) * fnOn _ (plkFn (P.map ψ) x i), fun j => ?_⟩
  have e := le_preimage_inf U a _ ((((toLB (-detDiv C x.1 (x.2.1 : ℕ))).pull U.ι).pull a).U k) hpt
  have hg : genericPoint C.Y.X ∈ U ⊓ (toLB (-detDiv C x.1 (x.2.1 : ℕ))).U i₀ :=
    gen_mem (e (hWtop (show IsLocalRing.closedPoint K ∈ (⊤ : (Sp K).Opens) from trivial)))
  have hs : algebraMap _ C.Y.Fn (v * plkFn P x j) = fnOf _ hg (locFn _ U (plkFn B x j) i₀) := by
    rw [fnOf_locFn (hreg j) i₀ hg, map_mul, hva, map_plkFn, hB, plkFn_mul_tri _ _ hT]
    simp only [Pi.smul_apply, smul_eq_mul, hu]
    ring
  rw [resG_self]
  change (secPull (secOfRat _ U (plkFn B x j)) a).f k = _
  rw [secOfRat_eq (hreg j)]
  refine (secPull_pullOn_f U.ι _ _ _ a k e).trans ?_
  rw [appLE_of_eq hay' _ _ e (hay' ▸ e), appLE_stalk y ψ _ _ (v * plkFn P x j) hg hs, map_mul, map_mul, map_plkFn ψ,
    ← pullRatio_pt_mul c _ hw i j hi]
  ring

end Main

theorem value : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), (∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1)) (y : (Φ.C k).Y.X), y ∈ ((Φ.C k).π ⁻¹ᵁ V) → (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).RegularAt y (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q)) → ∀ (ht : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ⨆ q, nonzeroLocus (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x q) = ⊤) (K : Type) [Field K] (a : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme) (c : Γ(gen s.T.Z, V) →+* K), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c → ∀ (y : (Φ.C k).Y.X) (ψ : (Φ.C k).Y.X.presheaf.stalk y →+* K) (P : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι = spMap ψ ≫ stalkPt (Φ.C k).Y y → (∀ τ, IsUnit (P τ).det) → B = T * P.map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) → (∀ τ i l, i < l → T τ i l = 0) → (∀ τ i, ∃ u : (Φ.C k).Y.Fnˣ, T τ i i = u ∧ ((Φ.C k).gr τ i).IsEqn y u) → ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ∃ hv, a ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x) = GlobalTheory.ProjSpace.pt c (GlobalTheory.FlagAmple.PlkLoc.plkFn (P.map ψ) x) hv := by
  intro D A N j S κ s Φ k V hV B hreg ht K _ a c hac y ψ P T hay hP hB hT hTd x
  exact value_gen (Φ.C k) _ B x (fun q z hz => hreg x q z hz) (ht x) _ a c hac y ψ P T hay hP hB hT hTd

end GlobalTheory.FlagAmple.PlkVal
