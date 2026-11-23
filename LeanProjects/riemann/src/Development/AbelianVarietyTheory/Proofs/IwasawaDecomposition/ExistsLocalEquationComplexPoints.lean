import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HolFrames

section Hol

open GlobalTheory.Points

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {T : Scheme.{0}}

theorem holTan_of_affine {U : T.Opens} (hU : IsAffineOpen U) (hB : IsOpen B) {z : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hz : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ U)
    (h₁ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).fst) B)
    (h₂ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).snd) B) : HolTan B z := by
  intro W f v hv
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (le_preimage_iff _ _).1 hv.2⟩
    ((le_preimage_iff _ _).1 (hz v hv.1))
  have key : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ T.basicOpen h ↔ (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 := fun b hb =>
    (le_preimage_basicOpen_iff _ (hz b hb) h).trans (TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero)
  have hv0 := (key v hv.1).1 ((le_preimage_iff _ _).2 hh)
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((T.presheaf.map (homOfLE hhW).op).hom f)
  have d₁ := fun a => (h₁ a).differentiableAt (hB.mem_nhds hv.1)
  have d₂ := fun a => (h₂ a).differentiableAt (hB.mem_nhds hv.1)
  have nz : ∀ b ∈ B, (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 →
      (valR (A := DualNumber ℂ) (z b) U (h ^ n)).fst ≠ 0 := fun b hb h0 => by
    rw [valR_pow _ _ (hz b hb), TrivSqZeroExt.fst_pow]
    exact pow_ne_zero n h0
  have di := (d₁ (h ^ n)).inv (nz v hv.1 hv0)
  have hq := ((d₂ a).sub (((d₁ a).mul di).mul (d₂ (h ^ n)))).mul di
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hB.mem_nhds hv.1, (d₁ h).continuousAt.eventually_ne hv0] with w hw hw0
  have hw1 := (key w hw).2 hw0
  have ha' : (T.presheaf.map (homOfLE hhW).op).hom f * (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom h ^ n =
    (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom a := ha
  have e := congrArg (valR (z w) (T.basicOpen h)) ha'
  rw [← map_pow, valR_mul _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1] at e
  have e₁ := congrArg TrivSqZeroExt.fst e
  have e₂ := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul] at e₁
  rw [DualNumber.snd_mul] at e₂
  have := nz w hw hw0
  simp only [Pi.inv_apply, Pi.sub_apply, Pi.mul_apply]
  rw [← e₁, ← e₂]
  field_simp
  ring

theorem holTan_dualMap {A : Type} [CommRing A] (hB : IsOpen B) (v : Sp (DualNumber A) ⟶ T) (ψ : ∀ b ∈ B, A →+* ℂ)
    (hψ : ∀ a, ∃ g : V → ℂ, DifferentiableOn ℂ g B ∧ ∀ b hb, ψ b hb a = g b) {w : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hw : ∀ b hb, w b = spMap (dualMap (ψ b hb)) ≫ v) : HolTan B w := by
  classical
  by_cases hne : B.Nonempty
  swap
  · intro U f b hb
    exact (hne ⟨b, hb.1⟩).elim
  obtain ⟨b₀, hb₀⟩ := hne
  let ψ' : V → (A →+* ℂ) := fun b => if hb : b ∈ B then ψ b hb else ψ b₀ hb₀
  have e : ∀ b hb, ψ' b = ψ b hb := fun b hb => dif_pos hb
  have hd : ∀ a, DifferentiableOn ℂ (fun b => ψ' b a) B := fun a =>
    have ⟨g, hg, hg'⟩ := hψ a
    hg.congr fun b hb => by rw [e b hb, hg']
  have hv : ∀ b (a : DualNumber A), valR (spMap (dualMap (ψ' b))) ⊤
      ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a) = dualMap (ψ' b) a := fun b a =>
    valR_specMap (CommRingCat.ofHom (dualMap (ψ' b))) a
  have hs : ∀ s : Γ(Sp (DualNumber A), ⊤), ∃ a, (Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a = s := fun s =>
    ⟨(Scheme.ΓSpecIso (.of (DualNumber A))).hom.hom s, by simp⟩
  have h0 : HolTan B fun b => spMap (dualMap (ψ' b)) :=
    holTan_of_affine (isAffineOpen_top _) hB (fun b _ => le_preimage_top _)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.fst)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.snd)
  intro U f
  refine ((h0 (v ⁻¹ᵁ U) ((v.app U).hom f)).mono fun b hb => ⟨hb.1, ?_⟩).congr fun b hb => ?_
  · have := hb.2
    rw [hw b hb.1, ← e b hb.1] at this
    exact this
  · rw [hw b hb.1, ← e b hb.1, valR_comp]

theorem valR_eq_germ {C : Type} [CommRing C] [IsLocalRing C] (p : Sp C ⟶ T) (U : T.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    valMap p U h = T.presheaf.germ U _ ((le_preimage_iff p U).1 h) ≫ Scheme.stalkClosedPointTo (R := .of C) p := by
  rw [Scheme.germ_stalkClosedPointTo]
  rfl

end Hol

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem letterOf_inl (τ : E →+* ℂ) (k : ℕ) (x : Pad.Letter Dw) :
    letterOf Dw (.inl (τ, k)) = some x ↔ τ = x.1 ∧ k = x.2 := by
  obtain ⟨ρ, i⟩ := x
  simp only [letterOf]
  split_ifs with h
  · constructor
    · intro e
      obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      exact ⟨rfl, congrArg Fin.val (eq_of_heq e')⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  · refine ⟨fun e => by simp at e, ?_⟩
    rintro ⟨rfl, rfl⟩
    exact (h i.2).elim

open Classical in

theorem expo_detSym (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (x : Pad.Letter Dw) :
    expo Dw (detSym Dw a R τ) x = (if τ = x.1 then 1 else 0) - if conjEmb τ = x.1 then 1 else 0 := by
  have hp : Dw.mult τ = Dw.p := if_pos hτ
  have hq : Dw.mult (conjEmb τ) = Dw.q := GlobalTheory.Harm.mult_conjEmb_of_mem Dw hτ
  have hs : ∀ (s : Finset ℕ) (w : ℕ → Sym E →₀ ℤ), expo Dw (∑ i ∈ s, w i) x = ∑ i ∈ s, expo Dw (w i) x := fun s w => by
    unfold expo
    exact (Finsupp.sum_finsetSum_index (by simp) (fun _ _ _ => by split_ifs <;> simp)).symm
  have h1 : ∀ (b : Sym E) (n : ℤ), expo Dw (Finsupp.single b n) x = if letterOf Dw b.2.2 = some x then n else 0 :=
    fun b n => by unfold expo; rw [Finsupp.sum_single_index (by simp)]; congr
  rw [detSym, hs, Finset.sum_range_add, sub_eq_add_neg]
  congr 1
  · rw [Finset.sum_congr rfl fun i hi => by rw [rootSym, if_pos (Finset.mem_range.1 hi), h1]]
    simp only [letterOf_inl]
    split_ifs with h
    · rw [Finset.sum_eq_single (x.2 : ℕ) (fun i _ hi => if_neg fun e => hi e.2)
        (fun hn => (hn (Finset.mem_range.2 (by rw [← hp, h]; exact x.2.2))).elim), if_pos ⟨h, rfl⟩]
    · exact Finset.sum_eq_zero fun i _ => if_neg fun e => h e.1
  · rw [Finset.sum_congr rfl fun i hi => by rw [rootSym, if_neg (by omega), h1]]
    simp only [letterOf_inl]
    split_ifs with h
    · have hx : (x.2 : ℕ) < Dw.q := by rw [← hq, h]; exact x.2.2
      rw [Finset.sum_eq_single (Dw.q - 1 - x.2) (fun i hi hi' => if_neg fun e => hi' (by
          have := e.2; have := Finset.mem_range.1 hi; omega))
        (fun hn => (hn (Finset.mem_range.2 (by omega))).elim), if_pos ⟨h, by omega⟩]
    · exact (Finset.sum_eq_zero fun i _ => if_neg fun e => h e.1).trans neg_zero.symm

theorem prod_expo_detSym (a : ℕ → Bool) (R : Option ℝ) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {G : Type} [CommGroup G]
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G) :
    ∏ z : Pad.Letter Dw, t z.1 z.2 ^ expo Dw (detSym Dw a R τ) z = (∏ i, t τ i) / ∏ j, t (conjEmb τ) j := by
  classical
  have k : ∀ ρ : E →+* ℂ, ∏ z : Pad.Letter Dw, t z.1 z.2 ^ (if ρ = z.1 then 1 else 0 : ℤ) = ∏ i, t ρ i := fun ρ => by
    rw [Fintype.prod_sigma, Finset.prod_eq_single ρ (fun b _ hb => by simp [hb.symm]) (by simp)]
    simp
  rw [← k τ, ← k (conjEmb τ), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [expo_detSym Dw a R hτ, zpow_sub, div_eq_mul_inv]

end Expo

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix_det {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
    {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (h₁ : f₁.Tri ψ g t₁) (h₂ : f₂.Tri ψ g t₂) (τ : E →+* ℂ) :
    ∃ M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, (∀ i, IsCombAtG Z.t x (f₁.v τ) (M i) (f₂.v τ i)) ∧
      ((∏ i, t₁ τ i : kˣ) : k) = (∏ i, t₂ τ i : kˣ) * ψ M.det := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨Matrix.of M, hM, ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  have hT : Matrix.of T₁ = Matrix.of T₂ * ψ.mapMatrix (Matrix.of M) := Matrix.ext fun i k' => by
    have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
      (fun a ha => hind a (by simpa only [d₁] using ha))
      (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← d₁, d₂, sub_eq_zero]
        funext q
        simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
          Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
        exact Finset.sum_comm)
    exact sub_eq_zero.1 (congrFun this k')
  have hd := congrArg Matrix.det hT
  rw [Matrix.det_mul, ← RingHom.map_det, Matrix.det_of_isLowerTriangular (Matrix.of T₁) (fun i k hk => b₁ i k hk),
    Matrix.det_of_isLowerTriangular (Matrix.of T₂) (fun i k hk => b₂ i k hk)] at hd
  simp only [Matrix.of_apply, a₁, a₂] at hd
  rw [Units.coe_prod, Units.coe_prod]
  exact hd

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ψ : A →+* B) {φ' : c.F →+* B} {x' : Sp B ⟶ Z.X} (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  subst hφ hx
  exact GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A B φ x fr ψ

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_transition {A A' R K k : Type} [CommRing A] [CommRing A'] [CommRing R] [IsLocalRing R] [Field K] [Field k]
    {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x) {φ' : c.F →+* A'} {x' : Sp A' ⟶ Z.X} (fr' : EigFrame Z φ' x')
    (ρ : A →+* R) (ρ' : A' →+* R) (hx : spMap ρ ≫ x = spMap ρ' ≫ x') {κ : R →+* K} (hκ : Function.Injective κ)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h : fr.Tri (κ.comp ρ) f₀ t) (h' : fr'.Tri (κ.comp ρ') f₀ t') (χ : R →+* k) (τ : E →+* ℂ) :
    ∃ M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, IsUnit M.det ∧
      ((∏ i, t' τ i : Kˣ) : K) = (∏ i, t τ i : Kˣ) * κ M.det ∧
      ∀ i, IsCombAtG Z.t (spMap (χ.comp ρ) ≫ x) (fun j => spMap (dualMap (χ.comp ρ')) ≫ fr'.v τ j)
        (χ.mapMatrix M i) (spMap (dualMap (χ.comp ρ)) ≫ fr.v τ i) := by
  obtain ⟨g, hg⟩ := exists_bc fr ρ rfl rfl
  obtain ⟨g', hg'⟩ := exists_bc fr' ρ' (φ' := ρ.comp φ)
    (RingHom.ext fun a => hκ ((RingHom.congr_fun h.2.1 a).symm.trans (RingHom.congr_fun h'.2.1 a))) hx
  have T : g.Tri κ f₀ t := ⟨by rw [h.1, spMap_comp₂, Category.assoc], h.2.1, fun τ i => by
    simpa only [hg, GlobalTheory.GradedPieces.dual_comp] using h.2.2 τ i⟩
  have T' : g'.Tri κ f₀ t' := ⟨T.1, T.2.1, fun τ i => by
    simpa only [hg', GlobalTheory.GradedPieces.dual_comp] using h'.2.2 τ i⟩
  obtain ⟨M, hM, hd⟩ := exists_matrix_det g' g κ f₀ T' T τ
  obtain ⟨N, -, hd'⟩ := exists_matrix_det g g' κ f₀ T T' τ
  refine ⟨M, IsUnit.of_mul_eq_one N.det (hκ ?_), hd, fun i => ?_⟩
  · rw [hd, _root_.mul_assoc] at hd'
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (Units.ne_zero _) ((_root_.mul_one _).trans hd')).symm
  · have := GlobalTheory.GradedPieces.comb_map χ (x' := spMap (χ.comp ρ) ≫ x) (by rw [spMap_comp₂, Category.assoc]) (hM i)
    simp only [hg, hg', GlobalTheory.GradedPieces.dual_comp] at this
    exact this

end Frames

open GlobalTheory.Points GlobalTheory.ShFam.EigLoc in

theorem exists_holFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∃ (W : C.Y.X → C.Y.X.Opens) (δ : C.Y.X → C.Y.Fnˣ) (a : C.Y.X → CxPts C.Y.str (σ.comp e.toRingHom) → CxFr Z σ), (∀ y, y ∈ W y) ∧ (∀ y, ∀ y' ∈ W y, (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))).IsEqn y' (δ y)) ∧ (∀ y, ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y), (a y p).1.1 = p.1 ≫ C.π) ∧ (∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts C.Y.str (σ.comp e.toRingHom)), IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B (CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y)) → HolFam B (fun b => a y (x b))) ∧ ∀ y y' (U : C.Y.X.Opens) (hU : genericPoint C.Y.X ∈ U) (r : Γ(C.Y.X, U)), fnOf U hU r = (δ y : C.Y.Fn) / (δ y' : C.Y.Fn) → ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y ⊓ W y' ⊓ U), ∃ M N, Chg (a y' p) (a y p) τ M ∧ Chg (a y' p) (a y p) (conjEmb τ) N ∧ M.det ≠ 0 ∧ M.det * CxPts.ev C.Y.str (σ.comp e.toRingHom) U r p = N.det := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ _ e C τ hτ
  choose U hU hy φ fr t _ hφ hT ht using fun y => GlobalTheory.T.exists_affine_eigenframe_flag E H Dw l Xo c O β Z F e C y ⊤ trivial
  have hov : ∀ p : CxPts C.Y.str (σ.comp e.toRingHom), (p.1 ≫ C.π) ≫ genStr Z = spMap σ := fun p => by
    have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      rw [← spMap_comp₂, RingEquiv.toRingHom_comp_symm_toRingHom]
      exact Spec.map_id _
    have h2 : ((p.1 ≫ C.π) ≫ genStr Z) ≫ spMap e.toRingHom = spMap σ ≫ spMap e.toRingHom := by
      rw [Category.assoc, Category.assoc, C.π_str, p.2, spMap_comp₂]
    rw [← Category.comp_id (_ ≫ genStr Z), ← h1, ← Category.assoc, h2, Category.assoc, h1, Category.comp_id]
  have hp : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)) (h : p ∈ CxPts.ptsIn _ _ (U y)),
      spMap (CxPts.evHom h) ≫ (show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)) (h : p ∈ CxPts.ptsIn _ _ (U y)), (p.1 ≫ C.π) ≫ genι Z =
      spMap (CxPts.evHom h) ≫ ((show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) ≫ C.π) ≫ genι Z := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)), ∃ g : EigFrame Z σ ((p.1 ≫ C.π) ≫ genι Z),
      ∀ h : p ∈ CxPts.ptsIn _ _ (U y), ∀ ρ i, g.v ρ i = spMap (dualMap (CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (CxPts.evHom h) (φ' := σ) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H Dw l Xo c O β Z ℂ σ _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, fun y => ∏ z : Pad.Letter Dw, t y z.1 z.2 ^ expo Dw (detSym Dw (fun _ => false) none τ) z,
    fun y p => ⟨⟨p.1 ≫ C.π, hov p⟩, g y p⟩, hy, fun y y' hy' => ?_, fun _ _ _ => rfl,
    fun y V _ _ _ B x hB hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (C.π ⁻¹ᵁ W) ((C.π.app W).hom f), fun ρ i => ?_⟩,
    fun y y' W hW r hr p hpm => ?_⟩
  · have hE : ∀ s : Finset (Pad.Letter Dw), (∑ z ∈ s, expo Dw (detSym Dw (fun _ => false) none τ) z • C.gr z.1 z.2).IsEqn y'
        (∏ z ∈ s, t y z.1 z.2 ^ expo Dw (detSym Dw (fun _ => false) none τ) z) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using CartierDiv.isEqn_zero y'
      | insert z s hz ih =>
        rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht y y' hy' _ _).zsmul _).add ih
    exact hE Finset.univ
  · refine holTan_dualMap hB ((fr y).v ρ i) (fun b hb => CxPts.evHom (hm hb)) (fun a => ⟨_,
      (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (CxPts.ev_eq (hm hb) a).symm⟩) fun b hb => hg y _ (hm hb) ρ i
  · obtain ⟨h₁₂, h₃⟩ := CxPts.mem_ptsIn_inf.1 hpm
    obtain ⟨h₁, h₂⟩ := CxPts.mem_ptsIn_inf.1 h₁₂
    let z : C.Y.X := p.1 (IsLocalRing.closedPoint ℂ)
    let R : Type := C.Y.X.presheaf.stalk z
    let χ : R →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
    let gm : ∀ {W : C.Y.X.Opens}, p ∈ CxPts.ptsIn _ _ W → (Γ(C.Y.X, W) →+* R) := fun {W} h =>
      (C.Y.X.presheaf.germ W z (CxPts.mem_ptsIn.1 h)).hom
    have hχ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W), χ.comp (gm h) = CxPts.evHom h := fun {W} h =>
      (congrArg CommRingCat.Hom.hom (valR_eq_germ p.1 W h)).symm
    have hκ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W) (h' : genericPoint C.Y.X ∈ W),
        (algebraMap R C.Y.X.functionField).comp (gm h) = fnOf W h' := fun {W} h h' =>
      RingHom.ext fun a => algebraMap_germ _ a
    have hs : ∀ y (h : p ∈ CxPts.ptsIn _ _ (U y)),
        spMap (gm h) ≫ (show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) = C.Y.X.fromSpecStalk z := fun y h =>
      (hU y).fromSpecStalk_eq_fromSpecStalk (CxPts.mem_ptsIn.1 h)
    have inj := IsFractionRing.injective R C.Y.X.functionField
    have tr := exists_transition (fr y) (fr y') (gm h₁) (gm h₂) (by
      simp only [← Category.assoc]
      rw [hs y h₁, hs y' h₂]) inj (hκ h₁ _ ▸ hT y) (hκ h₂ _ ▸ hT y') χ
    simp only [hχ] at tr
    have chg : ∀ ρ (M : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ), (∀ i, IsCombAtG Z.t
        (spMap (CxPts.evHom h₁) ≫ ((show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) ≫ C.π) ≫ genι Z)
        (fun j => spMap (dualMap (CxPts.evHom h₂)) ≫ (fr y').v ρ j) (M i)
        (spMap (dualMap (CxPts.evHom h₁)) ≫ (fr y).v ρ i)) →
        Chg (Z := Z) (σ := σ) ⟨⟨p.1 ≫ C.π, hov p⟩, g y' p⟩ ⟨⟨p.1 ≫ C.π, hov p⟩, g y p⟩ ρ M := fun ρ M hM =>
      ⟨rfl, fun i => by
        have := hM i
        rw [← hx y p h₁, ← hg y p h₁, ← funext (hg y' p h₂ ρ)] at this
        exact this⟩
    obtain ⟨M, uM, dM, cM⟩ := tr τ
    obtain ⟨N, -, dN, cN⟩ := tr (conjEmb τ)
    refine ⟨_, _, chg _ _ cM, chg _ _ cN, ?_, ?_⟩
    · rw [← RingHom.map_det]
      exact (uM.map χ).ne_zero
    · rw [← RingHom.map_det, ← RingHom.map_det, CxPts.ev_eq h₃, ← hχ, RingHom.comp_apply, ← map_mul]
      refine congrArg χ (inj ?_)
      have hM0 := (uM.map (algebraMap R C.Y.X.functionField)).ne_zero
      rw [map_mul, ← RingHom.comp_apply _ (gm h₃), hκ h₃ hW, hr]
      simp only [prod_expo_detSym Dw _ _ hτ, Units.val_div_eq_div_val]
      rw [dM, dN]
      have := (∏ i, t y τ i).ne_zero
      have := (∏ i, t y (conjEmb τ) i).ne_zero
      field_simp

end GlobalTheory.ShFam.HolFrames
