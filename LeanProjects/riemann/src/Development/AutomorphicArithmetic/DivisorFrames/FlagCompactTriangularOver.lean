import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
import Development.AutomorphicArithmetic.DivisorFrames.FlagBundleChartPoints
import Development.AutomorphicArithmetic.DivisorFrames.FlagCompactOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelMapSurjectiveBirational
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem UpperTheory.exists_triangular_of_lie_submatrix {K : Type} [Field K] {r : ℕ} (d : Bool) {P Q T : Matrix (Fin r) (Fin r) K}
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (hT : IsTri T)
    (h : (lieMat d P).submatrix id (pos d) = (lieMat d Q).submatrix id (pos d) * T) : ∃ T', IsTri T' ∧ P = Q * T' := by
  cases d
  · exact ⟨T, hT, h⟩
  · have h₁ : lieMat true P = lieMat true Q * T.submatrix Fin.revPerm Fin.revPerm := by
      ext a i
      have := congrFun (congrFun h a) i.rev
      simp only [submatrix_apply, pos, cond_true, id, Fin.rev_rev, mul_apply] at this
      rw [this, mul_apply, ← Equiv.sum_comp Fin.revPerm]
      simp
    have hu : IsUnit T.det := by
      have := isUnit_det_lieMat true hP
      rw [h₁, det_mul, det_submatrix_equiv_self] at this
      exact isUnit_of_mul_isUnit_right this
    refine ⟨lieMat true (T.submatrix Fin.revPerm Fin.revPerm), fun a i hi => ?_, ?_⟩
    · have := invertibleOfIsUnitDet T hu
      have hi' : T⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular fun _ _ h => hT _ _ h
      simp only [lieMat, cond_true, transpose_apply, inv_submatrix_equiv, submatrix_apply]
      exact hi' (Fin.rev_lt_rev.2 hi)
    · rw [← lieMat_lieMat true hP, h₁, lieMat_mul, lieMat_lieMat true hQ]

private theorem UpperTheory.det_submatrix_pos_unit {K : Type} [Field K] {r : ℕ} (d : Bool) {P : Matrix (Fin r) (Fin r) K}
    (hP : IsUnit P.det) : IsUnit (P.submatrix id (pos d)).det := by
  cases d
  · exact hP
  · have := det_permute' (Fin.revPerm : Equiv.Perm (Fin r)) P
    have h₂ : P.submatrix id (pos true) = P.submatrix id (Fin.revPerm : Equiv.Perm (Fin r)) := rfl
    rw [h₂, this]
    exact ((Equiv.Perm.sign _).isUnit.map (Int.castRingHom K)).mul hP

private theorem UpperTheory.preimage_open_point_top {X : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ X) {U : X.Opens} (h : below x ∈ U) :
    ⊤ ≤ x ⁻¹ᵁ U := fun q _ => by
  rw [show q = IsLocalRing.closedPoint K from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  exact h

private theorem UpperTheory.stalk_structure_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {Y : Var F}
    {ρ : Y.X ⟶ gen Z} (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (y : Y.X)
    (φ₀ : c.F →+* Y.X.presheaf.stalk y) (h₀ : constF e Y = (toFn y).comp φ₀) :
    stalkPt Y y ≫ ρ ≫ genStr Z = spMap φ₀ := by
  let φ : c.F →+* Y.X.presheaf.stalk y := (Spec.preimage ((stalkPt Y y ≫ ρ) ≫ genStr Z)).hom
  have hφ : (stalkPt Y y ≫ ρ) ≫ genStr Z = spMap φ := (Spec.map_preimage _).symm
  have h : constF e Y = (toFn y).comp φ := EigLoc.spMap_inj (by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    have h3 : spMap ((toFn y).comp φ) = spMap (toFn y) ≫ spMap φ := by rw [← Spec.map_comp]; rfl
    have h4 : spMap (constF e Y) = spMap (algebraMap F Y.Fn) ≫ spMap e.symm.toRingHom := by rw [← Spec.map_comp]; rfl
    rw [h3, h4, ← hφ, ← h1, ← hρ, ← spMap_toFn y]
    simp only [Category.assoc, h2, Category.comp_id])
  obtain rfl : φ₀ = φ := RingHom.ext fun a => toFn_injective y ((RingHom.congr_fun h₀ a).symm.trans (RingHom.congr_fun h a))
  rw [← hφ, Category.assoc]

theorem UpperTheory.flag_compact_triangular_over :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : Var F) (ρB : B.X ⟶ gen Z) (f : C.Y.X ⟶ B.X) (φ : B.Fn →+* C.Y.Fn), IsOver e ρB C.π f φ → ρB ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∀ (g : GenFrame e ρB) (g' : GenFrame e C.π), g.IsMap φ g' → ∀ (ι : Type) (emb : ι → (E →+* ℂ)), Function.Bijective emb → ∀ (dual : ι → Bool) (N : GlobalTheory.TrueGeo.Model B) (X : Scheme.{0}) (j : C.Y.X ⟶ X) (π : X ⟶ N.X), j ≫ π = f ≫ N.j → ∀ (M : ι → N.X.Modules) (hM : ∀ a, IsVB (M a) (Dw.mult (emb a))) (A : ∀ a, Chart (M a) (Dw.mult (emb a)) → Matrix (Fin (Dw.mult (emb a))) (Fin (Dw.mult (emb a))) B.Fn) (A' : ∀ a, Chart ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a)) → Matrix (Fin (Dw.mult (emb a))) (Fin (Dw.mult (emb a))) C.Y.Fn) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a))), (∀ a, IsLie g (emb a) N.j (dual a) (A a)) → (∀ a, IsLie C.f0 (emb a) j (dual a) (A' a)) → (∀ a, IsPullCo N.j π (hM a) (dual a) φ g' C.f0 (A a) (A' a)) → (∀ a, IsFlag (genericPt C.Y ≫ j) (dual a) (A' a) (fl a)) → IsFlagBundle π M (fun a => Dw.mult (emb a)) fl → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ B.X), x ≫ ρB ≫ genStr Z = spMap χ → ∀ k : EigFrame Z χ (x ≫ ρB ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p k) → ∀ (K : Type) [Field K] [IsAlgClosed K] (q : Sp K ⟶ X) (ψ : F →+* K), q ≫ π ≫ N.p = spMap ψ ≫ spMap (algebraMap (𝓞 F) F) → ∃! p : Sp K ⟶ C.Y.X, p ≫ j = q := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C B ρB f φ hov hρ g g' hg ι emb hemb dual N X j π hj M hM A A' fl hA hA' hP hF
    hFB hlift K _ _ q ψ hq
  haveI := GlobalTheory.ModelBirational.isPreimmersion_j N
  let x : Sp K ⟶ B.X := N.pb.lift (q ≫ π) (spMap ψ) (by rw [Category.assoc, hq])
  have hx : x ≫ N.j = q ≫ π := N.pb.lift_fst _ _ _
  clear_value x
  let χ : c.F →+* K := (Spec.preimage (x ≫ ρB ≫ genStr Z)).hom
  have hχ : x ≫ ρB ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  clear_value χ
  have hs : spMap (Scheme.stalkClosedPointTo x).hom ≫ stalkPt B (below x) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have key (a : ι) : ∃ (b : Chart (M a) (Dw.mult (emb a))) (gb : EigFrame Z χ (x ≫ ρB ≫ genι Z)),
      ⊤ ≤ (x ≫ N.j) ⁻¹ᵁ b.U ∧ ValAt g (emb a) x (lieMat (dual a) (A a b)) gb := by
    obtain ⟨U, s, hU, hs'⟩ := hM a (N.j (below x))
    let b : Chart (M a) (Dw.mult (emb a)) := ⟨U, s, hs'⟩
    obtain ⟨φ₀, k₀, hk₀⟩ := (hA a).2 b (below x) hU
    have hc : χ = (Scheme.stalkClosedPointTo x).hom.comp φ₀ := EigLoc.spMap_inj (by
      have h3 : spMap ((Scheme.stalkClosedPointTo x).hom.comp φ₀) =
        spMap (Scheme.stalkClosedPointTo x).hom ≫ spMap φ₀ := by rw [← Spec.map_comp]; rfl
      rw [h3, ← UpperTheory.stalk_structure_frame hρ _ φ₀ hk₀.1, ← Category.assoc, hs, hχ])
    obtain ⟨gb, hgb⟩ := k₀.exists_isMap (Scheme.stalkClosedPointTo x).hom (x' := x ≫ ρB ≫ genι Z) hc
      (by rw [← Category.assoc (spMap _), hs])
    exact ⟨b, gb, UpperTheory.preimage_open_point_top _ hU, rfl, φ₀, k₀, hk₀, hc, hgb⟩
  choose b gb hb hgb using key
  have adp (q' : Sp K ⟶ X) (a : ι) : ∃ ch : Chart ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a)),
      ⊤ ≤ q' ⁻¹ᵁ ch.U ∧ IsAdapted (fl a) ch := by
    obtain ⟨ch, h₁, h₂⟩ := (UpperTheory.exists_adapted_flag_charts _ _ _ (fl a)).1 (below q')
    exact ⟨ch, UpperTheory.preimage_open_point_top _ h₁, h₂⟩
  choose ch hch using adp
  have hu (q' : Sp K ⟶ X) (h : q' ≫ π = x ≫ N.j) (a : ι) :
      IsUnit (trAt q' ((b a).pull (hM a) π) (ch q' a)).det :=
    isUnit_det_trAt _ _ (by have := hb a; rw [← h] at this; exact this) (hch q' a).1
  obtain ⟨k, hk⟩ : ∃ k : EigFrame Z χ (x ≫ ρB ≫ genι Z), ∀ a, (gb a).co k (emb a) =
      (lieMat (dual a) (trAt q ((b a).pull (hM a) π) (ch q a))).submatrix id (pos (dual a)) := by
    have ex (τ : E →+* ℂ) : ∃ (u : EigFrame Z χ (x ≫ ρB ≫ genι Z)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K),
        IsUnit T.det ∧ ∀ k : EigFrame Z χ (x ≫ ρB ≫ genι Z), u.co k τ = T → ∀ a, emb a = τ → (gb a).co k (emb a) =
          (lieMat (dual a) (trAt q ((b a).pull (hM a) π) (ch q a))).submatrix id (pos (dual a)) := by
      obtain ⟨a, rfl⟩ := hemb.2 τ
      refine ⟨gb a, _, UpperTheory.det_submatrix_pos_unit (dual a) (isUnit_det_lieMat (dual a) (hu q hx.symm a)), fun k h a' ha => ?_⟩
      obtain rfl := hemb.1 ha
      exact h
    choose u T h₁ h₂ using ex
    obtain ⟨k, hk⟩ := exists_co_eq u T h₁
    exact ⟨k, fun a => h₂ _ k (hk _) a rfl⟩
  have car (p : Sp K ⟶ C.Y.X) (hp : p ≫ f = x) :=
    UpperTheory.flag_compact_over_base E H Dw l Xo c O β Z F e C B ρB f φ hov hρ g g' hg ι emb hemb.2 dual N.X N.j X j π hj M hM A A' fl hA hA'
      hP hF K p b (ch (p ≫ j)) (fun a => by rw [← Category.assoc, hp]; exact hb a) (hch (p ≫ j)) χ _ gb k
      (fun a => by rw [hp]; exact hgb a)
  obtain ⟨p, ⟨hp, hc⟩, hun⟩ := hlift K χ x hχ k
  have hpj : (p ≫ j) ≫ π = x ≫ N.j := by rw [Category.assoc, hj, ← Category.assoc, hp]
  refine ⟨p, ?_, fun p' hp' => ?_⟩
  · refine UpperTheory.flag_bundle_chart_points N.X X π ι M _ hM fl hFB K (p ≫ j) q (hpj.trans hx) b (ch (p ≫ j)) (ch q)
      (fun a => by rw [hpj]; exact hb a) (hch _) (hch _) fun a => ?_
    obtain ⟨T, hT, h⟩ := (car p hp).1 hc a
    exact UpperTheory.exists_triangular_of_lie_submatrix (dual a) (hu q hx.symm a) (hu _ hpj a) hT ((hk a).symm.trans h)
  · have hp'' : p' ≫ f = x := (cancel_mono N.j).1 (by rw [Category.assoc, ← hj, ← Category.assoc, hp', hx])
    refine hun p' ⟨hp'', (car p' hp'').2 fun a => ⟨1, fun a i h => one_apply_ne h.ne', ?_⟩⟩
    rw [hp', hk a, Matrix.mul_one]
