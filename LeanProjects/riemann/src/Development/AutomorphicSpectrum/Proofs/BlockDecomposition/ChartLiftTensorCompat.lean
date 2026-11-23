import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section
namespace GlobalTheory.CompanionTheory.DisoHm
section Cmp
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_base {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU W T) (a : O) (r : R)
    (hr : κ a = Ideal.Quotient.mk I r) : ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i r) := by
  have e := evalAt_base q κ (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q κ (T.B ⧸ T.J) from T.y).2 h a
  refine e.trans ?_
  rw [hr]
  exact T.w r

theorem quot_eq_id {W : X.Opens} {d : ℕ} (c : Chart γ p q κ W d) (hW : IsAffineOpen W)
    (θ : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J)
    (h1 : ∀ r, θ (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r))
    (h2 : ∀ f, θ (ev c.D c.inV f) = ev c.D c.inV f) : θ = RingHom.id _ := by
  have key : ∀ θ' : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J,
      (∀ r, θ' (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r)) →
      (∀ f, θ' (ev c.D c.inV f) = ev c.D c.inV f) →
      (ptFun X q κ).map (CommRingCat.ofHom θ') c.D.y = c.D.y := by
    intro θ' a b
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have w := c.D.w r
      change θ' ((show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)) =
        (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)
      have w' : (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c.D.i r) := w
      rw [w']
      exact a r
    · change Spec.map (CommRingCat.ofHom θ') ≫ pt c.D = pt c.D
      have e : Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec = pt c.D :=
        GlobalTheory.CompanionTheory.ChartAlg.eq_specMap hW (pt c.D) c.inV
      have e2 : θ'.comp (ev c.D c.inV) = ev c.D c.inV := RingHom.ext b
      calc Spec.map (CommRingCat.ofHom θ') ≫ pt c.D
          = Spec.map (CommRingCat.ofHom θ') ≫ Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec := by rw [e]
        _ = Spec.map (CommRingCat.ofHom (θ'.comp (ev c.D c.inV))) ≫ hW.fromSpec := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = pt c.D := by rw [e2, e]
  obtain ⟨g₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
  exact (hu _ (key θ h1 h2)).trans (hu _ (key _ (fun _ => rfl) (fun _ => rfl))).symm

end Cmp

theorem cmp_bij : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  intro l _ O _ X q h W d c m cL hcL cO
  letI := (strV q W).toAlgebra
  intro e he het hev hT σ hσ
  let E : Γ(X, W) ≃+* cO.D.B := (Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv.trans e
  have hE : ∀ f, E f = e (1 ⊗ₜ f) := fun f => rfl
  have hEs : ∀ a, E (strV q W a) = cO.D.i a := fun a => by
    rw [hE, ← he]
    congr 1
    change (1 : O) ⊗ₜ[O] (algebraMap O Γ(X, W) a) = a ⊗ₜ 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEt : ∀ i, E (c.t i) = cO.t i := het
  have hevE : ∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (E f) := hev
  let ψ : MvPolynomial (Fin d) O →+* cO.D.B := MvPolynomial.eval₂Hom cO.D.i cO.t
  have hψ : ψ.Etale := cO.etale
  let g : cO.D.B →+* cL.D.B ⧸ cL.D.J := (ev cL.D cL.inV).comp (E.symm : cO.D.B →+* Γ(X, W))
  let f₁ : MvPolynomial (Fin d) O →+* cL.D.B :=
    MvPolynomial.eval₂Hom (cL.D.i.comp (Ideal.Quotient.mk _)) cL.t
  have hg1 : ∀ f, g (E f) = ev cL.D cL.inV f := fun f => by
    change ev cL.D cL.inV (E.symm (E f)) = _
    rw [RingEquiv.symm_apply_apply]
  have hc : g.comp ψ = (Ideal.Quotient.mk cL.D.J).comp f₁ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have e1 : ψ (MvPolynomial.C a) = E (strV q W a) := by
        rw [hEs]; simp [ψ]
      have e2 : f₁ (MvPolynomial.C a) = cL.D.i (Ideal.Quotient.mk _ a) := by simp [f₁]
      change g (ψ (MvPolynomial.C a)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.C a))
      rw [e1, e2, hg1]
      exact ev_base cL.D cL.inV a _ rfl
    · have e1 : ψ (MvPolynomial.X i) = E (c.t i) := by
        rw [hEt]; simp [ψ]
      have e2 : f₁ (MvPolynomial.X i) = cL.t i := by simp [f₁]
      change g (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.X i))
      rw [e1, e2, hg1]
      exact hcL i
  obtain ⟨H, ⟨hH1, hH2⟩, -⟩ := GlobalTheory.T.etale_lifting_of_nil_ideal cL.D.J (GlobalTheory.CompanionTheory.ChartMaps.nil_J cL.D) _ _ ψ hψ f₁ g hc
  have hHi : ∀ a, H (cO.D.i a) = cL.D.i (Ideal.Quotient.mk _ a) := fun a => by
    have := RingHom.congr_fun hH1 (MvPolynomial.C a)
    simpa [ψ, f₁] using this
  have hHt : ∀ i, H (cO.t i) = cL.t i := fun i => by
    have := RingHom.congr_fun hH1 (MvPolynomial.X i)
    simpa [ψ, f₁] using this
  have hHe : ∀ f, Ideal.Quotient.mk cL.D.J (H (E f)) = ev cL.D cL.inV f := fun f => by
    rw [← hg1, ← hH2]
    rfl
  have hk : ∀ a ∈ lm (l := l) cO.D m, H a = 0 := by
    have hle : lm (l := l) cO.D m ≤ RingHom.ker H := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change H ((l : cO.D.B) ^ m) = 0
      have e1 : (l : cO.D.B) ^ m = cO.D.i ((l : O) ^ m) := by
        rw [map_pow, map_natCast]
      rw [e1, hHi, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    exact fun a ha => hle ha
  let Hb : GB (l := l) cO.D m →+* cL.D.B := Ideal.Quotient.lift _ H hk
  have hHb : ∀ x, Hb (Ideal.Quotient.mk _ x) = H x := fun x => Ideal.Quotient.lift_mk _ H hk
  let mkG : cO.D.B →+* (GObj h cO.D m hT).B := Ideal.Quotient.mk (lm (l := l) cO.D m)
  have hV := inU_G h cO.D m hT cO.inV
  have hs : σ.φ.comp H = mkG := by
    have uniq := GlobalTheory.T.etale_lifting_of_nil_ideal (GObj h cO.D m hT).J (GlobalTheory.CompanionTheory.ChartMaps.nil_J (GObj h cO.D m hT)) _ _ ψ hψ
      (mkG.comp ψ) ((Ideal.Quotient.mk (GObj h cO.D m hT).J).comp mkG) rfl
    refine uniq.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · have e1 : ψ (MvPolynomial.C a) = cO.D.i a := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.C a))) = mkG (ψ (MvPolynomial.C a))
        rw [e1, hHi, σ.comm]
        rfl
      · have e1 : ψ (MvPolynomial.X i) = cO.t i := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.X i))) = mkG (ψ (MvPolynomial.X i))
        rw [e1, hHt, hσ]
        rfl
    · refine RingHom.ext fun x => ?_
      obtain ⟨f, rfl⟩ := E.surjective x
      have a1 := ev_G h cO.D m hT cO.inV hV f
      have a2 := ev_hom σ cL.inV hV f
      rw [hevE] at a1
      rw [← hHe] at a2
      exact a2.symm.trans a1
  have hs' : ∀ x, σ.φ (H x) = mkG x := fun x => RingHom.congr_fun hs x
  let ρ : cL.D.B →+* cL.D.B := Hb.comp σ.φ
  have hρH : ∀ x, ρ (H x) = H x := fun x => by
    change Hb (σ.φ (H x)) = H x
    rw [hs']
    exact hHb x
  have hρi : ∀ r, ρ (cL.D.i r) = cL.D.i r := fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← hHi, hρH]
  have hρt : ∀ i, ρ (cL.t i) = cL.t i := fun i => by
    rw [← hHt, hρH]
  have hle : cL.D.J ≤ cL.D.J.comap ρ := by
    intro x hx
    have : cL.D.J ≤ cL.D.J.comap ρ := by
      conv_lhs => rw [cL.J_eq]
      refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap, hρi, cL.J_eq]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  have hθ : Ideal.quotientMap cL.D.J ρ hle = RingHom.id _ := by
    refine quot_eq_id cL c.affine _ (fun r => ?_) (fun f => ?_)
    · rw [Ideal.quotientMap_mk, hρi]
    · rw [← hHe, Ideal.quotientMap_mk, hρH]
  have hid : ρ = RingHom.id _ := by
    refine (GlobalTheory.CompanionTheory.ChartMaps.exists_unique_lift cL cL.D (RingHom.id _) (fun _ => rfl) cL.t (fun _ => rfl)).unique
      ⟨hρi, hρt, RingHom.ext fun x => ?_⟩ ⟨fun _ => rfl, fun _ => rfl, rfl⟩
    have := RingHom.congr_fun hθ (Ideal.Quotient.mk _ x)
    rw [Ideal.quotientMap_mk] at this
    exact this
  refine Function.bijective_iff_has_inverse.2 ⟨Hb, fun x => RingHom.congr_fun hid x, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) cO.D m from y)
  change σ.φ (Hb (Ideal.Quotient.mk _ x)) = _
  rw [hHb, hs']
  rfl

end GlobalTheory.CompanionTheory.DisoHm
