import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AutomorphicArithmetic.DivisorFrames.AbelianSchemeMapsValuation
import Development.AutomorphicArithmetic.DivisorFrames.LineModelIntegralLattice
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

namespace UpperTheory.MAgree
open GlobalTheory.ShFam.Pad.Pull

private theorem top_le_preimage_genericPointMap {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : genericPoint X ∈ U) :
    ⊤ ≤ gpt X ⁻¹ᵁ U := fun w _ => by
  have : gpt X w ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open (x := gpt X w) this U.isOpen hU

private theorem top_le_preimage_genericPointMap_comp {X Z : Scheme.{0}} [IsIntegral X] (ι : X ⟶ Z) {U : Z.Opens} (hU : genericPoint X ∈ ι ⁻¹ᵁ U) :
    ⊤ ≤ (gpt X ≫ ι) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact top_le_preimage_genericPointMap hU

private theorem valueAt_genericPoint {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : genericPoint X ∈ U) (a : Γ(X, U)) :
    valF (gpt X) U a = fnOf U hU a := by
  have h := top_le_preimage_genericPointMap hU
  have e : (X.fromSpecStalk (genericPoint X)).appLE U ⊤ h =
      X.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk _)).presheaf.map_id _)).trans
      (Category.comp_id _))
  rw [valF, dif_pos h]
  have e' : (X.fromSpecStalk (genericPoint X)).appLE U ⊤ h ≫ (Scheme.ΓSpecIso _).hom = X.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => g.hom a) e'

private theorem cls_pullLB {X X' : Scheme.{0}} (f : X' ⟶ X) (L : FinLB X) :
    (pullLB f L).cls = CechPic.pull f L.cls :=
  (CechPic.cls_eq_iff _ (LB.isLB_pull L.isLB f)).2 (LBIso.chartPull (h := f) (A := L.lb) (B := L.lb)
    ⟨fun i => i, fun _ => le_rfl, fun y i j hi hj => by
      refine Eq.trans (congrArg _ (Units.ext ?_)) ((gm_pull (𝟙 X') f y (L.U i ⊓ L.U j) ⟨hi, hj⟩ (L.g i j)).trans (by
        rw [Category.id_comp]))
      exact congrArg (fun q => q.hom (L.g i j).val) (Scheme.Hom.appLE_eq_app f)⟩
    ⟨fun J => J PUnit.unit, fun _ _ h => mem_pull.1 h, fun y J J' h h' =>
      (gm_pull_g L.lb f (𝟙 _) y J J' h h').trans (by rw [Category.id_comp])⟩ ((CechPic.cls_eq_iff L.isLB L.isLB).1 rfl))

private theorem exists_div {X Z : Scheme.{0}} [IsIntegral X] (ι : X ⟶ Z) (L : FinLB Z) (s : Fin L.n → X.functionField)
    (h0 : ∀ i, ⊤ ≤ (gpt X ≫ ι) ⁻¹ᵁ L.U i → s i ≠ 0)
    (ht : ∀ i i', ⊤ ≤ (gpt X ≫ ι) ⁻¹ᵁ (L.U i ⊓ L.U i') → s i = valF (gpt X ≫ ι) _ (L.g i i').val * s i') :
    ∃ D : CartierDiv X, toPic D = pull ι L.cls ∧ ∀ (i : Fin L.n) (x : X) (g : X.functionFieldˣ), ι x ∈ L.U i →
      D.IsEqn x g → UnitAt x ((g : X.functionField) / s i) := by
  classical
  let r : (pullLB ι L).lb.ι → X.functionFieldˣ := fun i => if h : s i ≠ 0 then Units.mk0 _ h else 1
  have hr : ∀ i, genericPoint X ∈ ι ⁻¹ᵁ L.U i → (r i : X.functionField) = s i := fun i hi => by
    simp only [r]
    rw [dif_pos (h0 i (top_le_preimage_genericPointMap_comp ι hi))]
    rfl
  have hR : IsRatSec (pullLB ι L).lb r := fun i j h => by
    rw [hr i h.1, hr j h.2, ← valueAt_genericPoint h, ht i j (top_le_preimage_genericPointMap_comp ι (U := L.U i ⊓ L.U j) h)]
    exact congrArg (· * _) (valF_appLE (x := gpt X) (U := ι ⁻¹ᵁ L.U i ⊓ ι ⁻¹ᵁ L.U j) ι _ le_rfl (top_le_preimage_genericPointMap h) _).symm
  have P := presents_divOfRatSec (pullLB ι L).isLB hR
  refine ⟨_, P.toPic_eq.trans (cls_pullLB ι L), fun i x g hx hg => ?_⟩
  rw [← hr i (gen_mem (U := ι ⁻¹ᵁ L.U i) hx)]
  exact (P.isEqn i x hx).iff_unitAt.1 hg

private theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) h)

private theorem gpt_eq {X : Scheme.{0}} [IsIntegral X] (y : X) :
    spMap (algebraMap (X.presheaf.stalk y) X.functionField) ≫ X.fromSpecStalk y = gpt X :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

private theorem exists_stalk {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (R : ValuationSubring K)
    (θ : X.functionField →+* K) (b : Sp R ⟶ X) (hb : spMap R.subtype ≫ b = spMap θ ≫ gpt X) :
    ∃ ψ : X.presheaf.stalk (b (closedPoint R)) →+* R, b = spMap ψ ≫ X.fromSpecStalk _ ∧
      R.subtype.comp ψ = θ.comp (algebraMap _ X.functionField) := by
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) b
  refine ⟨(Scheme.stalkClosedPointTo (R := CommRingCat.of R) b).hom, e.symm, spMap_inj ?_⟩
  rw [← cancel_mono (X.fromSpecStalk (b (closedPoint R))), ← ModelRelProbe.spMap_comp, ← ModelRelProbe.spMap_comp,
    Category.assoc, Category.assoc, gpt_eq, ← hb]
  exact congrArg (_ ≫ ·) e

private theorem val_unit {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (R : ValuationSubring K)
    (θ : X.functionField →+* K) (b : Sp R ⟶ X) (hb : spMap R.subtype ≫ b = spMap θ ≫ gpt X) {f : X.functionField}
    (hf : UnitAt (b (closedPoint R)) f) : R.valuation (θ f) = 1 := by
  obtain ⟨ψ, -, e⟩ := exists_stalk R θ b hb
  obtain ⟨u, hu, rfl⟩ := hf
  have : θ (algebraMap _ X.functionField u) = ((ψ u : R) : K) := (congrArg (fun g => g u) e).symm
  rw [this]
  exact (R.valuation_eq_one_iff _).1 (hu.map ψ)

section Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}

private def DT (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ}
    (u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) (d : Fin m → R) : Prop :=
  ∀ i, ∃ cf : Fin m → R, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧ IsCombAtG t x u cf (u' i)

variable {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {m : ℕ}
  {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} {d d' : Fin m → k}

private theorem DT.tri (h : DT t x u u' d) : Tri t x u u' := fun i => have ⟨cf, _, h1, h2⟩ := h i; ⟨cf, h1, h2⟩

private theorem DT.of_tri (h : Tri t x u u') : ∃ d, DT t x u u' d := by
  choose A h1 h2 using h
  exact ⟨fun i => A i i, fun i => ⟨A i, rfl, h1 i, h2 i⟩⟩

private theorem DT.ne (hu : Ind t x u) (hu' : Ind t x u') (h : DT t x u u' d) (i : Fin m) : d i ≠ 0 := by
  obtain ⟨cf, h0, -, h2⟩ := h i
  exact h0 ▸ (h.tri.diag hu hu' h2).1

private theorem DT.trans (hu : Ind t x u) (hu' : Ind t x u') (h : DT t x u u' d) (h' : DT t x u' u'' d') :
    DT t x u u'' fun i => d' i * d i := fun i => by
  obtain ⟨a, a0, a1, a2⟩ := h' i
  obtain ⟨b, b0, -, b2⟩ := h i
  obtain ⟨c, e, c1, e1, e2, e3⟩ := h.tri.comp hu.1 hu'.1 a1 a2
  exact ⟨e, by rw [e2, hu.2 _ _ _ c1 b2, a0, b0], e1, e3⟩

private theorem DT.symm (hu : Ind t x u) (hu' : Ind t x u') (h : DT t x u u' d) :
    DT t x u' u fun i => (d i)⁻¹ := fun i => by
  obtain ⟨h1, h2⟩ := h.tri.symm hu hu'
  obtain ⟨a, a1, a2⟩ := h1 i
  obtain ⟨b, b0, -, b2⟩ := h i
  exact ⟨a, (eq_inv_of_mul_eq_one_right (h2 i b a b2 a2)).trans (congrArg (·⁻¹) b0), a1, a2⟩

private theorem DT.push {X' : Scheme.{0}} {t' : SAB H X'} {g : X' ⟶ X} (mu : SABMap t' t g) {x' : Sp k ⟶ X'}
    (hx : x' ≫ g = x) {v v' : Fin m → (Sp (DualNumber k) ⟶ t'.G.left)} (hv : ∀ i, IsTanAtG t' x' (v i))
    (hv' : ∀ i, IsTanAtG t' x' (v' i)) :
    DT t x (fun i => v i ≫ mu.φ) (fun i => v' i ≫ mu.φ) d ↔ DT t' x' v v' d :=
  forall_congr' fun i => exists_congr fun cf => and_congr_right' (and_congr_right' (comb_push mu hx hv (hv' i) cf))

private theorem DT.map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {d : Fin m → R} (h : DT t x u u' d) :
    DT t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ u i) (fun i => spMap (dualMap φ) ≫ u' i) fun i => φ (d i) :=
  fun i => by
    obtain ⟨a, a0, a1, a2⟩ := h i
    exact ⟨fun j => φ (a j), congrArg φ a0, fun j hj => (congrArg φ (a1 j hj)).trans (map_zero φ), GlobalTheory.LatDRFree.comb_map t φ a2⟩

private theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C)
    {Z : Scheme.{0}} (u : Sp (DualNumber A) ⟶ Z) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) ≫ u = spMap (dualMap (χ.comp ρ)) ≫ u := by
  rw [← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]

private theorem dual_id {A : Type} [CommRing A] {Z : Scheme.{0}} (u : Sp (DualNumber A) ⟶ Z) :
    spMap (dualMap (RingHom.id A)) ≫ u = u := by
  have h1 : spMap (dualMap (RingHom.id A)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

private theorem ind_congr {x' : Sp k ⟶ X} (e : x = x') (h : Ind t x u) : Ind t x' u := e ▸ h

private theorem frame_congr {Dw : Datum H} {l : Level H} {c : Coeff l} {R : Type} [CommRing R] {f : c.F →+* R}
    {x x' : Sp R ⟶ X} {u : Vecs Dw t R} (e : x = x') (h : LocM.IsFrame t f x u) : LocM.IsFrame t f x' u := e ▸ h

private theorem val_fin {K : Type} [Field K] (R : ValuationSubring K) {g₁ g₂ t₀ c r s : K} (h₀ : t₀ ≠ 0) (hc : c ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (h₁ : R.valuation (g₁ / (t₀ * c / r)) = 1) (h₂ : R.valuation (g₂ / s) = 1)
    (h₃ : R.valuation (r * (c⁻¹ * (t₀⁻¹ * s))) = 1) : R.valuation g₁ = R.valuation g₂ := by
  have e : g₁ * (r * (c⁻¹ * (t₀⁻¹ * s))) * (g₂ / s) = g₂ * (g₁ / (t₀ * c / r)) := by field_simp
  have := congrArg R.valuation e
  rwa [map_mul, map_mul, map_mul _ g₂, h₁, h₂, h₃, mul_one, mul_one, mul_one] at this

end Tri

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

private theorem eig_frame {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ T.X} (f : EigFrame T φ x) :
    LocM.IsFrame (Dw := Dw) T.t φ x f.v := ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩

private noncomputable def eigBC {R S : Type} [CommRing R] [CommRing S] {φ : c.F →+* R} {x : Sp R ⟶ T.X} (f : EigFrame T φ x)
    (θ : R →+* S) : EigFrame T (θ.comp φ) (spMap θ ≫ x) :=
  have h := GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ θ _ _ (eig_frame f)
  ⟨Vecs.bc (Dw := Dw) θ f.v, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩

private theorem tri_bc {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ T.X} {x' : Sp R' ⟶ T.X} {f : EigFrame T φ x} {ψ : R →+* R'} {g : EigFrame T φ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : f.Tri ψ g t) (θ : R' →+* S) :
    f.Tri (θ.comp ψ) (eigBC g θ) fun τ i => Units.map θ.toMonoidHom (t τ i) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [h1, ← Category.assoc, ModelRelProbe.spMap_comp], by rw [h2]; rfl, fun τ => ?_⟩
  have := DT.map θ (t := T.t) (d := fun i => (t τ i : R')) (h3 τ)
  simp only [dual_comp] at this
  exact this

variable {F : Type} [Field F] {e : F ≃+* c.F}

private theorem carries_bc (C : FlagCpt T e) {K : Type} [Field K] (θ : C.Y.X.functionField →+* K) :
    C.Carries (spMap θ ≫ gpt C.Y.X) (eigBC C.f0 θ) := by
  obtain ⟨φ, f, t, h, -⟩ := C.gr_spec (genericPoint C.Y.X)
  refine ⟨_, _, φ, f, t, _, ?_, h, tri_bc h θ⟩
  rw [← ModelRelProbe.spMap_comp, Category.assoc, stalkPt, gpt_eq]

end Eig

end UpperTheory.MAgree

open UpperTheory.MAgree GlobalTheory.ShFam.Pad.Pull in
theorem UpperTheory.level_flag_prime :
    GlobalTheory.Published.SemiAbelianHomExtension → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F}, p.Prime → (p : ℂ) ∈ W.nonunits → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (L : Lev Z T) (C : FlagCpt T e) (X : Scheme.{0}) [IsIntegral X] (ι : X ⟶ Z.X) (sX : X ⟶ Sp Z.i.c.F), ι ≫ Z.s = sX ≫ spMap (Z.i.c.V W).subtype → Algebra.EssFiniteType ℤ X.functionField → ∀ θ : C.Y.X.functionField →+* X.functionField, Match L C (gpt X ≫ ι) (spMap θ ≫ gpt C.Y.X) → ∀ (x : Letter Dw) (M : LineModel Z false (.inl (x.1, (x.2 : ℕ))) x), ∃ D : CartierDiv X, toPic D = pull ι M.L.cls ∧ DvrAgree θ D (C.gr x.1 x.2) := by
  intro hS E _ _ _ H Dw Xo p W Y i₀ O _ β Z T F _ e hp hW hty L C X _ ι sX hι hK θ hM x M
  obtain ⟨-, -, ⟨fK, hf1, hf2⟩, -⟩ := UpperTheory.level_flag_compact_point L C _ _ hM
  obtain ⟨y, v, φg, g, hw, hq, hv, ⟨a₀, φ, hφ, hFv, hSF⟩, hC, hg⟩ := hM
  obtain ⟨-, hcar⟩ := UpperTheory.flag_carries_eigenframe C _ (spMap θ ≫ gpt C.Y.X)
  obtain ⟨t0, -, -, ht0⟩ := ((hcar _ _ g hC).2.2 _ _ _).1 (carries_bc C θ)
  have hstr : θ.comp (constF e C.Y) = fK.comp (incl Z) :=
    spMap_inj ((hcar _ _ _ (carries_bc C θ)).2.1.symm.trans (hf2.trans (ModelRelProbe.spMap_comp _ _)))
  obtain ⟨c1, hc1⟩ := DT.of_tri (tri_of_sameFlag hty hSF x.1)
  have Ifr := frame_ind (chart_frame Z hφ) x.1
  have Iv := frame_ind hFv x.1
  have c0 := hc1.ne Ifr Iv x.2
  have Ig : Pull.Ind T.t (spMap θ ≫ genericPt C.Y ≫ C.π ≫ genι T) (g.v x.1) :=
    ind_congr (Category.assoc _ _ _) (frame_ind (eig_frame g) x.1)
  have I0 := frame_ind (eig_frame (eigBC C.f0 θ)) x.1
  have D0 : DT T.t (spMap θ ≫ genericPt C.Y ≫ C.π ≫ genι T) (g.v x.1) ((eigBC C.f0 θ).v x.1)
      fun i => (t0 x.1 i : X.functionField) := by
    have := ht0 x.1
    simp only [dual_id] at this
    exact this
  have ha₀ := le_of_fromSpec (Z.U a₀).2 hφ
  obtain ⟨D, hD, hE⟩ := exists_div ι M.L
    (fun i => (t0 x.1 x.2 : X.functionField) * c1 x.2 / valF (gpt X ≫ ι) _ (M.r a₀ i).val)
    (fun i hi => div_ne_zero (mul_ne_zero (Units.ne_zero _) c0) (val_ne M hφ hi)) (fun i i' h => by
      have e1 := M.trans _ (gpt X ≫ ι) a₀ i i' fun q hq => ⟨ha₀ hq, h hq⟩
      have n := val_ne M hφ (i := i') fun q hq => (h hq).2
      rw [e1] at n ⊢
      have := left_ne_zero_of_mul n
      have := right_ne_zero_of_mul n
      field_simp)
  refine ⟨D, hD, fun R hR a b ha hb g₁ g₂ h₁ h₂ => ?_⟩
  obtain ⟨φf, f, t, hft, heq⟩ := C.gr_spec (b (closedPoint R))
  obtain ⟨ψ, hψ, eψ⟩ := exists_stalk R θ b hb
  obtain ⟨i, hi⟩ := exists_chart M.L.isLB (ι (a (closedPoint R)))
  have u₁ := val_unit R (RingHom.id _) a (ha.trans (by
    rw [show spMap (RingHom.id X.functionField) = 𝟙 _ from Spec.map_id _, Category.id_comp])) (hE i _ g₁ hi h₁)
  have u₂ := val_unit R θ b hb ((heq x.1 x.2).iff_unitAt.1 h₂)
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Z.i.c.F →+* R, spMap φ₁ = a ≫ sX :=
    ⟨(Spec.preimage (a ≫ sX)).hom, Spec.map_preimage _⟩
  have e₁ : R.subtype.comp φ₁ = fK := by
    have := mono_spMap_subtype (Z.i.c.V W)
    refine spMap_inj ?_
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← hf1, ← ModelRelProbe.spMap_comp, hφ₁, ← ha]
    simp only [Category.assoc, hι]
  obtain ⟨hx0, hc0, hT⟩ := tri_bc hft θ
  have e₂ : R.subtype.comp (ψ.comp φf) = fK.comp (incl Z) := by
    rw [← RingHom.comp_assoc, eψ, ← hc0, hstr]
  obtain ⟨μ, hμ⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ T.m L.ν
  have hyx : y ≫ L.r ≫ T.j = spMap θ ≫ genericPt C.Y ≫ C.π ≫ genι T := by
    have := congrArg (· ≫ genι T) hq
    simp only [Category.assoc] at this
    exact this.symm
  have F₂ : LocM.IsFrame T.t (ψ.comp φf) (b ≫ C.π ≫ genι T) (eigBC f ψ).v :=
    frame_congr ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.π ≫ genι T) hψ.symm)) (eig_frame (eigBC f ψ))
  have hwa : spMap R.subtype ≫ a ≫ ι = gpt X ≫ ι := by rw [← Category.assoc, ha]
  obtain ⟨f₁, v', F₁, hv'⟩ := UpperTheory.abelian_scheme_maps_valuation hS (Y Z.i).m μ _ R hR y ((a ≫ ι) ≫ Z.π) (b ≫ C.π ≫ genι T)
    (hw.symm.trans (by rw [← hwa, Category.assoc]))
    (hyx.trans (by rw [← Category.assoc _ b, hb, Category.assoc]; rfl)) φ₁ (ψ.comp φf)
    (fun τ s => R.subtype_injective ((congrArg (fun z => z (embK Z.i.c τ s)) e₁).trans
      (congrArg (fun z => z (embK i₀.c τ s)) e₂).symm)) _ F₂
  have I₂ := ind_congr hx0.symm (frame_ind (eig_frame (eigBC f (θ.comp (algebraMap _ C.Y.X.functionField)))) x.1)
  have D₁ := DT.trans I₂ I0 (hT x.1) (D0.symm Ig I0)
  have a₁ : (eigBC f (θ.comp (algebraMap _ C.Y.X.functionField))).v x.1 = fun i => v' x.1 i ≫ μ.φ := funext fun i => by
    rw [(hv' x.1 i).2.2, ← eψ]
    exact (dual_comp _ _ _).symm
  have a₂ : g.v x.1 = fun i => v x.1 i ≫ μ.φ := funext fun i => by rw [hg, hμ]
  rw [a₁, a₂] at D₁
  have D₂ := (DT.push (Y Z.i).m hw.symm (fun i => (hv' x.1 i).1) (hv x.1)).2
    ((DT.push μ hyx (fun i => (hv' x.1 i).1) (hv x.1)).1 D₁)
  have a₃ : (fun i => v' x.1 i ≫ (Y Z.i).m.φ) = f₁.bc R.subtype x.1 := funext fun i => (hv' x.1 i).2.1
  have hpt : (gpt X ≫ ι) ≫ Z.π = spMap R.subtype ≫ (a ≫ ι) ≫ Z.π := by rw [← hwa, Category.assoc]
  have I₁ := frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ R.subtype _ _ F₁) x.1
  rw [← hpt] at I₁
  rw [a₃] at D₂
  have D₃ := DT.trans I₁ Iv D₂ (hc1.symm Ifr Iv)
  rw [hpt] at D₃
  have key := UpperTheory.line_model_integral_lattice hp hW Z x M _ R hK (a ≫ ι) φ₁ (by rw [hφ₁, Category.assoc, hι, Category.assoc]) f₁ F₁ a₀ φ
    (hφ.trans hwa.symm) _ D₃ i hi
  rw [hwa] at key
  have hi' : ⊤ ≤ (gpt X ≫ ι) ⁻¹ᵁ M.L.U i := top_le_preimage_genericPointMap_comp ι (gen_mem (U := ι ⁻¹ᵁ M.L.U i) hi)
  rw [map_div₀ θ] at u₂
  exact val_fin R (t0 x.1 x.2).ne_zero c0 (val_ne M hφ hi') ((map_ne_zero θ).2 (t x.1 x.2).ne_zero) u₁ u₂ key
