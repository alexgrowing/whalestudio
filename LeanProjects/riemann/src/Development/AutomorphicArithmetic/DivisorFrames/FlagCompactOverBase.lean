import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ChartFrameDivisor
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

namespace UpperTheory.TriangularSubMaps

private def posE (dual : Bool) (r : ℕ) : Equiv.Perm (Fin r) := ⟨pos dual, pos dual, pos_pos dual, pos_pos dual⟩

private theorem tri_mul {K : Type} [CommRing K] {r : ℕ} {S T : Matrix (Fin r) (Fin r) K} (hS : IsTri S) (hT : IsTri T) :
    IsTri (S * T) := fun _ _ h =>
  BlockTriangular.mul (b := id) (M := S) (N := T) (fun a i h => hS a i h) (fun a i h => hT a i h) h

private theorem tri_inv {K : Type} [CommRing K] {r : ℕ} {S : Matrix (Fin r) (Fin r) K} (hS : IsTri S)
    (hu : IsUnit S.det) : IsTri S⁻¹ := fun _ _ h => by
  have := invertibleOfIsUnitDet S hu
  exact blockTriangular_inv_of_blockTriangular (b := id) (M := S) (fun a i h => hS a i h) h

private theorem tri_map {K K' : Type} [CommRing K] [CommRing K'] {r : ℕ} {S : Matrix (Fin r) (Fin r) K} (hS : IsTri S)
    (ψ : K →+* K') : IsTri (S.map ψ) := fun a i h => by rw [map_apply, hS a i h, map_zero]

private theorem sub_mul {K : Type} [CommRing K] {r : ℕ} (dual : Bool) (S T : Matrix (Fin r) (Fin r) K) :
    S.submatrix id (pos dual) * T.submatrix (pos dual) id = S * T :=
  submatrix_mul_equiv S T id (posE dual r) id

private theorem sub_sub {K : Type} {r : ℕ} (dual : Bool) (T : Matrix (Fin r) (Fin r) K) :
    (T.submatrix (pos dual) id).submatrix (pos dual) id = T := by
  ext a i
  simp [pos_pos]

private theorem tri_sub {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {Q : Matrix (Fin r) (Fin r) K} (hu : IsUnit Q.det)
    (h : IsTri ((lieMat dual Q).submatrix (pos dual) id)) : IsTri (Q.submatrix id (pos dual)) := by
  cases dual
  · exact h
  · have h1 : Q.submatrix id (pos true) * (Q⁻¹).submatrix (pos true) id = 1 := by
      rw [sub_mul, mul_nonsing_inv _ hu]
    rw [← inv_eq_left_inv h1]
    refine tri_inv (fun a i hi => ?_) (isUnit_det_of_left_inverse h1)
    have := h i.rev a.rev (Fin.rev_lt_rev.2 hi)
    simpa [lieMat, pos] using this

private theorem mat_key {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {L Q R : Matrix (Fin r) (Fin r) K}
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (h : IsTri (Q.submatrix id (pos dual))) :
    IsTri (Q * R) ↔ ∃ T, IsTri T ∧ L * R = L.submatrix id (pos dual) * T := by
  constructor
  · intro hS
    refine ⟨R.submatrix (pos dual) id, ?_, (sub_mul dual L R).symm⟩
    have h1 : Q.submatrix id (pos dual) * (Q⁻¹).submatrix (pos dual) id = 1 := by
      rw [sub_mul, mul_nonsing_inv _ hQ]
    have hu := isUnit_det_of_right_inverse h1
    have := tri_mul (tri_inv h hu) hS
    rwa [← sub_mul dual Q R, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul] at this
  · rintro ⟨T, hT, e⟩
    rw [← sub_sub dual T, sub_mul, ((isUnit_iff_isUnit_det _).2 hL).mul_right_inj] at e
    rw [e, ← sub_mul dual, sub_sub]
    exact tri_mul h hT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

private theorem tri_symm {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f g : EigFrame Z φ x} {τ : E →+* ℂ}
    (h : IsTri (f.co g τ)) : IsTri (g.co f τ) := by
  rw [← inv_eq_right_inv ((f.co_mul g f τ).trans (f.co_self τ))]
  exact tri_inv h (f.isUnit_det_co g τ)

private theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {φ'' : c.F →+* R''} {x'' : Sp R'' ⟶ Z.X}
    {f : EigFrame Z φ x} {ψ : R →+* R'} {χ : R' →+* R''} {f' : EigFrame Z φ' x'}
    {f'' : EigFrame Z φ'' x''} (h : f.IsMap ψ f') (h' : f'.IsMap χ f'') : f.IsMap (χ.comp ψ) f'' := fun τ i => by
  rw [h' τ i, h τ i, GlobalTheory.GradedPieces.dual_comp]

private theorem carries_iff {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    (p : Sp K ⟶ C.Y.X) {φ : c.F →+* C.Y.X.presheaf.stalk (below p)} {s : StalkFrame C.π (below p) φ}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ} (hs : s.Tri (toFn (below p)) C.f0 t)
    {χ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (hχ : χ = (Scheme.stalkClosedPointTo p).hom.comp φ)
    (hx : x₀ = spMap (Scheme.stalkClosedPointTo p).hom ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z)
    {sp : EigFrame Z χ x₀} (hsp : s.IsMap (Scheme.stalkClosedPointTo p).hom sp) (k : EigFrame Z χ x₀) :
    C.Carries p k ↔ ∀ τ, IsTri (sp.co k τ) := by
  have hp0 : spMap (Scheme.stalkClosedPointTo p).hom ≫ stalkPt C.Y (below p) = p :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p
  constructor
  · rintro ⟨y, ψ, φ₁, f, t₁, t', hp, a, b⟩ τ
    have hsp' : below p ⤳ y := by
      have : below p ∈ Set.range (C.Y.X.fromSpecStalk y) := by rw [hp]; exact ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    let ρ : C.Y.X.presheaf.stalk y →+* C.Y.X.presheaf.stalk (below p) := (C.Y.X.presheaf.stalkSpecializes hsp').hom
    have h1 : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (below p) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp'
    have h2 : (Scheme.stalkClosedPointTo p).hom.comp ρ = ψ :=
      EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 (by
        refine Eq.trans ?_ (hp0.trans hp)
        rw [← h1, ← Category.assoc, ← Spec.map_comp]; rfl))
    have h3 : (toFn (below p)).comp ρ = toFn y :=
      congrArg CommRingCat.Hom.hom (C.Y.X.presheaf.stalkSpecializes_comp _ hsp')
    have hφ : φ = ρ.comp φ₁ := RingHom.ext fun z => toFn_injective (below p) (by
      have e1 := RingHom.congr_fun hs.2.1 z
      have e2 := RingHom.congr_fun a.2.1 z
      have e3 := RingHom.congr_fun h3 (φ₁ z)
      exact e1.symm.trans (e2.trans e3.symm))
    obtain ⟨f', hf⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (below p) ≫ C.π ≫ genι Z) hφ (by rw [← h1, Category.assoc])
    obtain ⟨fg, hfg⟩ := exists_isMap_toFn (e := e) f' hs.2.1
    obtain ⟨sg, hsg⟩ := exists_isMap_toFn (e := e) s hs.2.1
    obtain ⟨fp, hfp⟩ := f'.exists_isMap _ hχ hx
    have a1 : IsTri (fg.co C.f0 τ) := (a.co τ (by have := isMap_comp hf hfg; rwa [h3] at this)).1
    have a2 : IsTri (sg.co C.f0 τ) := (hs.co τ hsg).1
    have a3 : IsTri (fp.co k τ) := (b.co τ (by have := isMap_comp hf hfp; rwa [h2] at this)).1
    have a4 := tri_mul a2 (tri_symm a1)
    rw [EigFrame.co_mul, hsg.co τ hfg hs.1] at a4
    have a5 : IsTri (s.co f' τ) := fun u i h => toFn_injective _ ((a4 u i h).trans (map_zero _).symm)
    rw [← sp.co_mul fp, hsp.co τ hfp hx]
    exact tri_mul (tri_map a5 _) a3
  · intro h
    have hu : ∀ τ i, IsUnit (sp.co k τ i i) := fun τ i => by
      have := sp.isUnit_det_co k τ
      rw [Matrix.det_of_upperTriangular (fun a i hi => h τ a i hi)] at this
      exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => sp.co k τ i i) (Finset.mem_univ i)) this
    refine ⟨below p, _, φ, s, t, fun τ i => (hu τ i).unit, hp0.symm, hs, hx, hχ, fun τ i =>
      ⟨fun a => sp.co k τ a i, rfl, fun k hk => h τ _ _ hk, ?_⟩⟩
    rw [← funext (hsp τ)]
    exact sp.co_spec k τ i

end UpperTheory.TriangularSubMaps

theorem UpperTheory.flag_compact_over_base :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : Var F) (ρB : B.X ⟶ gen Z) (f : C.Y.X ⟶ B.X) (φ : B.Fn →+* C.Y.Fn), IsOver e ρB C.π f φ → ρB ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∀ (g : GenFrame e ρB) (g' : GenFrame e C.π), g.IsMap φ g' → ∀ (ι : Type) (emb : ι → (E →+* ℂ)), Function.Surjective emb → ∀ (dual : ι → Bool) (XB : Scheme.{0}) (jB : B.X ⟶ XB) (X : Scheme.{0}) (j : C.Y.X ⟶ X) (π : X ⟶ XB), j ≫ π = f ≫ jB → ∀ (M : ι → XB.Modules) (hM : ∀ a, IsVB (M a) (Dw.mult (emb a))) (A : ∀ a, Chart (M a) (Dw.mult (emb a)) → Matrix (Fin (Dw.mult (emb a))) (Fin (Dw.mult (emb a))) B.Fn) (A' : ∀ a, Chart ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a)) → Matrix (Fin (Dw.mult (emb a))) (Fin (Dw.mult (emb a))) C.Y.Fn) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a))), (∀ a, IsLie g (emb a) jB (dual a) (A a)) → (∀ a, IsLie C.f0 (emb a) j (dual a) (A' a)) → (∀ a, IsPullCo jB π (hM a) (dual a) φ g' C.f0 (A a) (A' a)) → (∀ a, IsFlag (genericPt C.Y ≫ j) (dual a) (A' a) (fl a)) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X) (b : ∀ a, Chart (M a) (Dw.mult (emb a))) (ch : ∀ a, Chart ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a))), (∀ a, ⊤ ≤ (p ≫ f ≫ jB) ⁻¹ᵁ (b a).U) → (∀ a, ⊤ ≤ (p ≫ j) ⁻¹ᵁ (ch a).U ∧ IsAdapted (fl a) (ch a)) → ∀ (χ : c.F →+* K) (x₀ : Sp K ⟶ Z.X) (gb : ι → EigFrame Z χ x₀) (k : EigFrame Z χ x₀), (∀ a, ValAt g (emb a) (p ≫ f) (lieMat (dual a) (A a (b a))) (gb a)) → (C.Carries p k ↔ ∀ a, ∃ T, IsTri T ∧ (gb a).co k (emb a) = (lieMat (dual a) (trAt (p ≫ j) ((b a).pull (hM a) π) (ch a))).submatrix id (pos (dual a)) * T) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C B ρB f φ hO _ g g' hg ι emb hemb dual XB jB X j π hj M hM A A' fl hA hA' hP
    hF K _ p b ch hb hch χ x₀ gb k hV
  obtain ⟨φs, s, t, hs, -⟩ := C.gr_spec (below p)
  have hp0 : spMap (Scheme.stalkClosedPointTo p).hom ≫ stalkPt C.Y (below p) = p :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p
  have hc : (Scheme.stalkClosedPointTo (p ≫ f)).hom =
      (Scheme.stalkClosedPointTo p).hom.comp (f.stalkMap (below p)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; rfl
  have key : ∀ a, ∃ k₁ : StalkFrame C.π (below p) φs, χ = (Scheme.stalkClosedPointTo p).hom.comp φs ∧
      k₁.IsMap (Scheme.stalkClosedPointTo p).hom (gb a) ∧
      Fits C.f0 (emb a) (below p) φs k₁ (lieMat (dual a) (A' a ((b a).pull (hM a) π))) := fun a => by
    obtain ⟨-, φ₀, k₀, h1, h2, h3⟩ := hV a
    have hU : jB (f (below p)) ∈ (b a).U := hb a (x := IsLocalRing.closedPoint K) trivial
    obtain ⟨k₁, h4, h5⟩ := Fits.pull (y := below p) hO hg C.f0 h1
    obtain rfl : φs = (f.stalkMap (below p)).hom.comp φ₀ := RingHom.ext fun z => toFn_injective _
      ((RingHom.congr_fun hs.2.1 z).symm.trans (RingHom.congr_fun h5.1 z))
    refine ⟨k₁, by rw [h2, hc]; rfl, fun τ i => ?_, ?_⟩
    · rw [h3 τ i, h4 τ i, GlobalTheory.GradedPieces.dual_comp, hc]; rfl
    · rwa [hP a _ (gen_le jB hU), lieMat_mul, lieMat_lieMat _ (C.f0.isUnit_det_co g' _),
        lieMat_map _ _ ((hA a).1.1 _ (gen_le jB hU))]
  obtain ⟨a₀, -⟩ := hemb (Classical.arbitrary _)
  have hχ := (key a₀).choose_spec.1
  have hx : x₀ = spMap (Scheme.stalkClosedPointTo p).hom ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z := by
    rw [(hV a₀).1, ← Category.assoc (spMap _), hp0, ← hO.1]
    simp only [Category.assoc]
  obtain ⟨sp, hsp⟩ := s.exists_isMap _ hχ hx
  rw [UpperTheory.TriangularSubMaps.carries_iff C p hs hχ hx hsp k, hemb.forall]
  refine forall_congr' fun a => ?_
  obtain ⟨k₁, -, h1, h2⟩ := key a
  have hU : j (below p) ∈ ((b a).pull (hM a) π).U := by
    change π (j (below p)) ∈ (b a).U
    rw [← Scheme.Hom.comp_apply, hj]
    exact hb a (x := IsLocalRing.closedPoint K) trivial
  have hU' : j (below p) ∈ (ch a).U := (hch a).1 (x := IsLocalRing.closedPoint K) trivial
  obtain ⟨k', h3, h4⟩ := h2.change (hA' a).1 hU hU'
  obtain ⟨kp, hkp⟩ := k'.exists_isMap _ hχ hx
  have h5 := (UpperTheory.chart_frame_divisor E H Dw l Xo c O β Z F e C (emb a) X j _ (dual a) (A' a) (fl a) (hA' a) (hF a) (ch a)
    (hch a).2 (below p) hU' φs s k' t hs h4).1
  have h6 : IsTri ((sp.co kp (emb a)).submatrix id (pos (dual a))) := by
    rw [hsp.co _ hkp hx]
    exact UpperTheory.TriangularSubMaps.tri_map (UpperTheory.TriangularSubMaps.tri_sub _ (s.isUnit_det_co k' _) h5)
      (Scheme.stalkClosedPointTo p).hom
  have h7 : (gb a).co kp (emb a) = lieMat (dual a) (trAt (p ≫ j) ((b a).pull (hM a) π) (ch a)) := by
    rw [h1.co _ hkp hx, h3, ← lieMat_map _ _ (isUnit_det_trAt _ _ (stalk_le j hU) (stalk_le j hU')),
      ← trAt_spMap _ _ _ (stalk_le j hU) (stalk_le j hU'), ← Category.assoc, hp0]
  rw [← sp.co_mul kp, ← (gb a).co_mul kp, ← h7]
  exact UpperTheory.TriangularSubMaps.mat_key _ ((gb a).isUnit_det_co kp _) (sp.isUnit_det_co kp _) h6
