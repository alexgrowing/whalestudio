import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLUBRangeOfMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.DeKeyTrue GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.CoordLift

theorem unit_prod_cancel {K ι : Type} [CommRing K] [Fintype ι] (t : ι → Kˣ) (n : ι → ℤ) (a : K) :
    ((∏ z, t z ^ n z : Kˣ) : K) * a * ((∏ z, t z ^ (-n z) : Kˣ) : K) = a := by
  rw [mul_right_comm, ← Units.val_mul, ← Finset.prod_mul_distrib]
  simp

theorem invol_prod {ι : Type} [Fintype ι] (ψ : ℂ →+* ℂ) (hψ : ∀ z, ψ (ψ z) = z) (t : ι → ℂˣ) (n : ι → ℤ) (a : ℂ) :
    ψ (((∏ z, (Units.map ψ.toMonoidHom (t z)) ^ n z : ℂˣ) : ℂ) * ψ a) =
      a * ((∏ z, t z ^ (-(-n z)) : ℂˣ) : ℂ) := by
  simp [map_prod, map_zpow₀, hψ, mul_comm]

theorem isCoord_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e) {σ : F →+* ℂ} {σ' : c.F →+* ℂ} (ψ : ℂ →+* ℂ) (p : C.Y.pts σ) (g : C.FrameAt p) (y : FrPt Xo c (CAt σ')) (ex : Ix Dw → ℤ) (h : Rul Xo c), ψ.comp ψ = RingHom.id ℂ → σ' = ψ.comp (GlobalTheory.ShFam.embOf e σ) → C.Carries p.1 g → (C.down p).1 = spMap ψ ≫ (cxPt Z y).1 → (cxFrame Z y).IsMap ψ g → ex none = 0 → h ∈ GlobalTheory.AllWt.secZ Xo c ex → IsCoord C p.1 g (fun z => -ex (some z)) (C.val h) (ψ (Formalism.L2.PjFree.toC (evR Xo c h y))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C σ σ' ψ p g y ex h hψ hσ' hC hdown hmap hex hsec
  obtain ⟨y₁, ψ₁, φ₁, f₁, t, t', h1, h2, h3⟩ := hC
  obtain ⟨⟨φ, f, a1, a2⟩, -⟩ := FlagCpt.adapted_of_tri h1 h2 h3
  letI : Algebra c.F (C.Y.X.presheaf.stalk (base p)) := φ.toAlgebra
  letI : Algebra c.F C.Y.Fn := (constF e C.Y).toAlgebra
  haveI := Z.jQ_open
  let ι : C.Y.X.presheaf.stalk (base p) →+* C.Y.Fn := algebraMap _ C.Y.X.functionField
  have hι : Function.Injective ι := IsFractionRing.injective (C.Y.X.presheaf.stalk (base p)) C.Y.X.functionField
  let χ : C.Y.X.presheaf.stalk (base p) →+* CAt σ' := ψ.comp (evStalk p)
  haveI : IsLocalHom χ := ⟨fun r hr => (evStalk_ne_zero_iff r).1 (fun h0 => (show IsUnit (ψ (evStalk p r) : ℂ) from hr).ne_zero (by
    show ψ (evStalk p r) = 0
    rw [h0, map_zero]))⟩
  let x : Sp (C.Y.X.presheaf.stalk (base p)) ⟶ gen Z := stalkPt C.Y (base p) ≫ C.π
  have hψψ : spMap ψ ≫ spMap ψ = 𝟙 _ := by rw [OpenReg.spMap_comp, hψ]; exact Spec.map_id _
  have hy : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap χ ≫ x := by
    have e1 : (C.down p).1 = spMap (evStalk p) ≫ x := by
      show p.1 ≫ C.π = _
      rw [← C.spMap_evStalk p, Category.assoc]
    have e2 : (cxPt Z y).1 = spMap ψ ≫ (C.down p).1 := by rw [hdown, ← Category.assoc, hψψ, Category.id_comp]
    show (cxPt Z y).1 = _
    rw [e2, e1, ← Category.assoc, OpenReg.spMap_comp]
    rfl
  haveI : IsLocalRing (CAt σ') := inferInstanceAs (IsLocalRing ℂ)
  have hr : Set.range x ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 : q ⤳ spMap χ (IsLocalRing.closedPoint (CAt σ')) := by
      have : spMap χ (IsLocalRing.closedPoint (CAt σ')) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint χ
      rw [this]
      exact IsLocalRing.specializes_closedPoint q
    refine (h1.map x.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
      ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint (CAt σ')), ?_⟩
    exact congrArg (fun m : Sp (CAt σ') ⟶ gen Z => m (IsLocalRing.closedPoint (CAt σ'))) hy
  let xF := IsOpenImmersion.lift Z.jQ x hr
  have hxF : xF ≫ Z.jQ = x := IsOpenImmersion.lift_fac _ _ _
  have hpt : GlobalTheory.AllWt.ptF y = spMap χ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, hy]
  have hgen : genericPt C.Y = spMap ι ≫ stalkPt C.Y (base p) :=
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (base p))).symm
  have hpt0 : GlobalTheory.AllWt.ptF C.y0 = spMap ι ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, C.y0_x, hgen, Category.assoc]
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (C.Y.X.presheaf.stalk (base p))) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ι ≫ spMap φ₂.hom = spMap (algebraMap c.F C.Y.Fn) := by
      have h0 : GlobalTheory.AllWt.ptF C.y0 ≫ pullback.snd _ _ = spMap (algebraMap c.F C.Y.Fn) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [OpenReg.spMap_comp] at h1
    have h2 : ι.comp φ₂.hom = algebraMap c.F C.Y.Fn := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₂.hom = φ := RingHom.ext fun r =>
      hι ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun a1.2.1 r))
    rw [← h]
    show Spec.map φ₂ = Spec.map (CommRingCat.ofHom φ)
    exact congrArg Spec.map (CommRingCat.hom_ext h3)
  obtain ⟨a, ha⟩ := ChartValue.exists_evR_eq_of_tri (Z := Z) xF hs (x := stalkPt C.Y (base p) ≫ C.π ≫ genι Z)
    (by rw [← Category.assoc, hxF]; rfl) f hex hsec
  let ι' : C.Y.X.presheaf.stalk (base p) →ₐ[c.F] C.Y.Fn :=
    { ι with commutes' := fun r => (RingHom.congr_fun a1.2.1 r).symm }
  have hv1 := ha C.Y.Fn ι' C.f0.v t C.y0 (fun τ i => by
      obtain ⟨cf, c1, c2, c3⟩ := a1.2.2 τ i
      exact ⟨cf, c1, c2, (congrArg (fun X => IsCombAtG Z.t X (fun k => spMap (dualMap ι) ≫ f.v τ k) cf (C.f0.v τ i))
        a1.1).mp c3⟩) hpt0 C.flagComponentFramedPoint_frame
  let ψC : ℂ →+* CAt σ' := ψ
  have hχc : ∀ r, χ (algebraMap c.F _ r) = algebraMap c.F (CAt σ') r := fun r => by
    show ψ (evStalk p (φ r)) = σ' r
    rw [hσ']
    exact congrArg ψ (RingHom.congr_fun a2.2.1 r).symm
  let χ' : C.Y.X.presheaf.stalk (base p) →ₐ[c.F] CAt σ' := { χ with commutes' := hχc }
  let t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (CAt σ')ˣ := fun τ i => Units.map ψC.toMonoidHom (t' τ i)
  have hv2 := ha (CAt σ') χ' (cxFrame Z y).v t'' y (fun τ i => by
      obtain ⟨cf, c1, c2, c3⟩ := a2.2.2 τ i
      refine ⟨fun k => ψC (cf k), by simp [c1, t''], fun k hk => by simp [c2 k hk], ?_⟩
      have hx' : spMap ψC ≫ (C.down p).1 ≫ genι Z = spMap χ'.toRingHom ≫ stalkPt C.Y (base p) ≫ C.π ≫ genι Z := by
        rw [a2.1, ← Category.assoc, OpenReg.spMap_comp]
        rfl
      have c4 := GlobalTheory.GradedPieces.comb_map ψC hx' c3
      simp only [GlobalTheory.GradedPieces.dual_comp] at c4
      have hid : spMap (dualMap (RingHom.id ℂ)) = 𝟙 _ := by
        rw [← Spec.map_id]
        congr 1
        ext r <;> simp [dualMap]
      have hv : (cxFrame Z y).v τ i = spMap (dualMap ψ) ≫ g.v τ i := by
        rw [hmap τ i, GlobalTheory.GradedPieces.dual_comp, hψ, hid, Category.id_comp]
      rw [hv]
      exact c4) hpt (fun τ i => by
      obtain ⟨w, hw1, hw2, hw3⟩ := EigFrame.ofFrPt_v (S := CAt σ') Z y (Category.assoc _ _ _).symm τ i
      exact ⟨w, hw1.1, hw2, hw3⟩)
  refine ⟨base p, evStalk p, φ, f, t, t', a, (C.spMap_evStalk p).symm, a1, a2, ?_, ?_⟩
  · show ι a = evR Xo c h C.y0 * _
    rw [hv1]
    exact (unit_prod_cancel (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => t z.1 z.2) (fun z => ex (some z)) (ι a)).symm
  · have hψ' : ∀ z, ψ (ψ z) = z := fun z => RingHom.congr_fun hψ z
    rw [hv2]
    exact invol_prod ψ hψ' (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => t' z.1 z.2) (fun z => ex (some z)) (evStalk p a)

end GlobalTheory.ShFam.CoordLift
