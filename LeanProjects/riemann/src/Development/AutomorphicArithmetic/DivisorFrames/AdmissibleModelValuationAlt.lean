import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleModelValuation
import Development.AutomorphicArithmetic.DivisorFrames.ExistsSphericallyCompleteIsometric
import Development.AutomorphicArithmetic.DivisorFrames.TangentModelsCompat
import Development.AutomorphicArithmetic.DivisorFrames.LnStepIsometricBaseChange
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem valF_map {F F' : Type} [Field F] [Field F'] {X : Scheme.{0}} (χ : F →+* F') {w : Sp F ⟶ X}
    {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (r : Γ(X, U)) : valF (spMap χ ≫ w) U r = χ (valF w U r) := by
  have h' : ⊤ ≤ (spMap χ ≫ w) ⁻¹ᵁ U := fun q _ => h (Set.mem_univ (spMap χ q))
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (spMap χ) w U ⊤ ⊤ h le_rfl]
  exact congrArg (fun g => g.hom ((w.appLE U ⊤ h).hom r)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))

private theorem bc_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (ρ : A →+* B) (χ : B →+* C) (u : Vecs Dw t A) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    u.bc (χ.comp ρ) σ j = spMap (dualMap χ) ≫ u.bc ρ σ j := by
  rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]

theorem UpperTheory.admissible_model_valuation_alt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (O : Type) [CommRing O] (β : O →+* i₀.c.F) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β) (b₀ : O →+* i₀.c.V W), p.Prime → (p : ℂ) ∈ W.nonunits → (i₀.c.V W).subtype.comp b₀ = β → Dominates T (Y i₀) b₀ → ∀ (k : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Pad.Letter Dw), letterOf Dw st = some x → ∀ (M : LineModel Z k st x) (a : Fin Z.m) (i : Fin M.L.n) (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ), LocM.IsTrans i₀ Z.i τ mu → ∀ [Fact p.Prime] (K : Type) [Field K] (V : ValuationSubring K) (io : K →+* ℂ_[p]), (∀ s, ‖io s‖ ≤ 1 ↔ s ∈ V) → ∀ (zO : Sp ↥V ⟶ Z.X) (φ : Γ(Z.X, (Z.U a).1) →+* K) (y : Sp K ⟶ (Xo i₀.l).XF i₀.c) (f : i₀.c.F →+* K) (u G : Vecs Dw T.t K) (cf : Fin (Dw.mult x.1) → K), spMap φ ≫ Z.chart a = spMap V.subtype ≫ zO → ⊤ ≤ zO ⁻¹ᵁ M.L.U i → y ≫ (Y i₀).j = (spMap V.subtype ≫ zO) ≫ Z.π ≫ τ → y ≫ pullback.snd _ _ = spMap f → LocM.IsFrame T.t f (y ≫ T.j) u → LocM.IsFrame T.t f (y ≫ T.j) G → (∀ σ m, Transp T (Y i₀) y (u σ m) ((Z.fr a).bc φ σ m ≫ mu.φ)) → (∀ σ, Pull.Tri T.t (y ≫ T.j) (G σ) (u σ)) → IsCombAtG T.t (y ≫ T.j) (G x.1) cf (u x.1 x.2) → lnStep T.t (spMap io ≫ y ≫ T.j) (Vecs.bc io G) p k st = -Real.log ‖io (cf x.2)‖ - Real.log ‖io (valF (spMap V.subtype ≫ zO) _ (M.r a i).val)‖ := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ β T b₀ hp hW hb hD k st x hx M a i τ mu hT _ K _ V io hio zO φ y f u G cf
    hφ hi hy hf hu hG htr htri hc
  obtain ⟨C, j, hj⟩ := UpperTheory.exists_spherically_complete_isometric p
  let χ : K →+* ↥C.S := j.toRingHom.comp io
  let χO : ↥V →+* ↥(Formalism.MainNotions.DIV.Cons.intO ↥C.S) :=
    (χ.comp V.subtype).codRestrict (Formalism.MainNotions.DIV.Cons.intO ↥C.S) fun s =>
      show ‖j (io s)‖ ≤ 1 from (hj _).trans_le ((hio s).2 s.2)
  have e : spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ spMap χO ≫ zO = spMap χ ≫ spMap V.subtype ≫ zO := by
    rw [← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
    rfl
  have hw : ⊤ ≤ (spMap V.subtype ≫ zO) ⁻¹ᵁ ((Z.U a).1 ⊓ M.L.U i) := fun q hq =>
    ⟨Pull.le_of_fromSpec (Z.U a).2 hφ hq, hi (Set.mem_univ (spMap V.subtype q))⟩
  have key := UpperTheory.admissible_model_valuation E H Dw Xo p W Y i₀ Z O β T b₀ hp hW hb hD k st x hx M a i τ mu hT C (spMap χO ≫ zO)
    (χ.comp φ) (spMap χ ≫ y) (χ.comp f) (Vecs.bc χ u) (Vecs.bc χ G) (fun m => χ (cf m))
    (by rw [e, ← ModelRelProbe.spMap_comp, Category.assoc, hφ])
    (fun q _ => hi (Set.mem_univ (spMap χO q)))
    (by rw [e, Category.assoc, hy]; simp only [Category.assoc])
    (by rw [Category.assoc, hf, ModelRelProbe.spMap_comp])
    (by rw [Category.assoc]; exact GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ χ _ _ hu)
    (by rw [Category.assoc]; exact GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ χ _ _ hG)
    (fun σ m => by
      rw [bc_comp φ χ, Category.assoc]
      exact (UpperTheory.tangent_models_compat E H Dw _ _ _ _ _ _ _ _ _ _ _ _ _ (htr σ m)).2 _ χ)
    (fun σ m => by
      obtain ⟨c, c1, c2⟩ := htri σ m
      refine ⟨fun n => χ (c n), fun n hn => (congrArg χ (c1 n hn)).trans (map_zero χ), ?_⟩
      rw [Category.assoc]
      exact GlobalTheory.LatDRFree.comb_map _ χ c2)
    (by rw [Category.assoc]; exact GlobalTheory.LatDRFree.comb_map _ χ hc)
  rw [e, valF_map χ hw] at key
  have e1 : Vecs.bc χ G = Vecs.bc j.toRingHom (Vecs.bc io G) := funext fun σ => funext fun m => bc_comp io _ G σ m
  have e2 : (spMap χ ≫ y) ≫ T.j = spMap j.toRingHom ≫ spMap io ≫ y ≫ T.j := by
    rw [Category.assoc, ← Category.assoc (spMap j.toRingHom), ModelRelProbe.spMap_comp]
  rw [e1, e2, UpperTheory.lnStep_isometric_base_change E H Dw _ _ _ _ j hj] at key
  rw [key, ← hj (io (cf x.2)), ← hj (io _)]
  rfl
