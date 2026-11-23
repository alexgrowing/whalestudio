import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem isTan_of_comb {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {cf : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x u cf w) : IsTanAtG t x w := by
  have h' := (GlobalTheory.LieMet.isComb_iff (fun l => GlobalTheory.LieMet.tanOf (hu l)) cf _).2 rfl
  have e := ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h).symm.trans
    ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h')
  rw [e]
  exact GlobalTheory.LieMet.isTan_tv _

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in

private theorem eq_zero_of_mulVec {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (τ : E →+* ℂ) {g : ℕ} {B : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hB : ∀ k, IsTanAtG Z.t x (B k))
    (a : Matrix (Fin g) (Fin (Dw.mult τ)) R) (ha : ∀ i, IsCombAtG Z.t x B (fun k => a k i) (f.v τ i))
    {v : Fin (Dw.mult τ) → R} (hv : a *ᵥ v = 0) : v = 0 := by
  have h1 : ∀ i, f.vec τ i = ∑ k, a k i • GlobalTheory.LieMet.tanOf (hB k) := fun i =>
    (GlobalTheory.LieMet.isComb_iff (fun k => GlobalTheory.LieMet.tanOf (hB k)) _ (f.vec τ i)).1 (ha i)
  refine funext (Fintype.linearIndependent_iff.1 (f.linearIndependent_vec τ) v ?_)
  have h2 : ∑ i, v i • f.vec τ i = ∑ k, (a *ᵥ v) k • GlobalTheory.LieMet.tanOf (hB k) := by
    simp only [h1, Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul, mul_comm]
    exact Finset.sum_comm
  rw [h2, hv]
  simp

private theorem isUnit_det_of_factor {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) (τ : E →+* ℂ) {g : ℕ} {B : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)}
    (hB : ∀ k, IsTanAtG Z.t x (B k)) (S : Matrix (Fin g) (Fin (Dw.mult τ)) R)
    (Q : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R)
    (ha : ∀ i, IsCombAtG Z.t x B (fun k => (S * Q) k i) (f.v τ i)) : IsUnit Q.det := by
  by_contra hQ
  have h0 : (Q.map (IsLocalRing.residue R)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, IsLocalRing.residue_eq_zero_iff]
    exact hQ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨f', hf'⟩ := f.exists_isMap (IsLocalRing.residue R) rfl rfl
  refine hv0 (eq_zero_of_mulVec f' τ (fun k => GlobalTheory.LieMet.isTan_map (IsLocalRing.residue R) rfl (hB k))
    ((S * Q).map (IsLocalRing.residue R)) (fun i => ?_) ?_)
  · rw [hf' τ i]
    exact GlobalTheory.GradedPieces.comb_map _ rfl (ha i)
  · rw [Matrix.map_mul, ← mulVec_mulVec, hv, mulVec_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.frame_generic_chart_norm :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (X : Scheme.{0}) (j : Y.X ⟶ X) (ρ' : X ⟶ Z.X), j ≫ ρ' = ρ ≫ genι Z → ∀ (V : X.Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), SplitOn g₀ τ j ρ' V P → FrOn g₀ τ j V P := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ hρ g₀ τ X j ρ' hj V P hS y hy
  obtain ⟨hV, hξ, g, b, S, S', hb, hSS, -, hw⟩ := hS
  obtain ⟨φ, f₁, P₁, h₁⟩ := exists_fits hρ g₀ τ y
  obtain ⟨k, hk⟩ := exists_isMap_toFn (e := e) f₁ h₁.1
  have hP₁ : g₀.co k τ = P₁ := (fits_iff h₁.1 hk).1 h₁
  obtain ⟨α, hα0⟩ : ∃ α : Γ(X, V) →+* Y.X.presheaf.stalk y,
      α = evalPt (stalkPt Y y ≫ j) V (stalk_le j hy) := ⟨_, rfl⟩
  obtain ⟨ev, hev0⟩ : ∃ ev : Γ(X, V) →+* Y.Fn, ev = evalPt (genericPt Y ≫ j) V hξ := ⟨_, rfl⟩
  rw [← hev0] at hw
  have hα : spMap α ≫ hV.fromSpec ≫ ρ' = stalkPt Y y ≫ ρ ≫ genι Z := by
    rw [← hj, ← Category.assoc, ← Category.assoc, hα0]
    exact congrArg (· ≫ ρ') (eq_spec_fromSpec hV _ _).symm
  have hev : spMap ev ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ ρ ≫ genι Z := by
    rw [← hj, ← Category.assoc, ← Category.assoc, hev0]
    exact congrArg (· ≫ ρ') (eq_spec_fromSpec hV _ _).symm
  have hg : spMap (toFn y) ≫ stalkPt Y y ≫ j = genericPt Y ≫ j := by rw [← Category.assoc, spMap_toFn]
  have hx : spMap (toFn y) ≫ stalkPt Y y ≫ ρ ≫ genι Z = genericPt Y ≫ ρ ≫ genι Z := by
    rw [← Category.assoc, spMap_toFn]
  have hc : (toFn y).comp α = ev := RingHom.ext fun s => by
    have h' : ⊤ ≤ (spMap (toFn y) ≫ stalkPt Y y ≫ j) ⁻¹ᵁ V := hg.symm ▸ hξ
    have := evalPt_spMap_comp (toFn y) (stalkPt Y y ≫ j) V (stalk_le j hy) h' s
    rw [hα0, hev0, RingHom.comp_apply, ← this]
    congr 1
    simp only [hg]
  have hBα : ∀ i, IsTanAtG Z.t (stalkPt Y y ≫ ρ ≫ genι Z) (spMap (dualMap α) ≫ b i) := fun i =>
    GlobalTheory.LieMet.isTan_map α hα (hb.1 i)
  have hBev : ∀ i, IsTanAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (spMap (dualMap ev) ≫ b i) := fun i =>
    GlobalTheory.LieMet.isTan_map ev hev (hb.1 i)
  have h2 := hb.2 _ α
  have h3 := hb.2 _ ev
  rw [hα] at h2
  rw [hev] at h3
  choose a₀ ha₀ using fun i => (h2 (f₁.v τ i) (f₁.tan τ i)).exists
  obtain ⟨a, ha⟩ : ∃ a : Matrix (Fin g) (Fin (Dw.mult τ)) (Y.X.presheaf.stalk y), ∀ i,
      IsCombAtG Z.t (stalkPt Y y ≫ ρ ≫ genι Z) (fun i => spMap (dualMap α) ≫ b i) (fun r => a r i) (f₁.v τ i) :=
    ⟨Matrix.of fun r i => a₀ i r, ha₀⟩
  have ha' : ∀ i, IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (fun i => spMap (dualMap ev) ≫ b i)
      (fun r => a.map (toFn y) r i) (k.v τ i) := fun i => by
    have := GlobalTheory.GradedPieces.comb_map (toFn y) hx (ha i)
    simp only [GlobalTheory.GradedPieces.dual_comp, hc] at this
    rw [hk τ i]
    exact this
  have hSC : S.map ev = a.map (toFn y) * (k.co g₀ τ * P) := by
    ext r i
    obtain ⟨w, hw₁, hw₂⟩ := hw i
    have e₁ := tanLinG _ (k.tan τ) _ _ _ w (k.co_spec g₀ τ) hw₁
    have e₂ := tanLinG _ hBev _ _ _ w ha' e₁
    have e₃ := congrFun ((h3 w (isTan_of_comb hBev hw₂)).unique hw₂ e₂) r
    rw [mulVec_mulVec] at e₃
    rw [← Matrix.mul_assoc]
    exact e₃
  have hα' : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) Γ(X, V)), (M.map α).map (toFn y) = M.map ev := fun M => by
    rw [← hc]; rfl
  have hQ : (S'.map α * a).map (toFn y) * (k.co g₀ τ * P) = 1 := by
    rw [Matrix.map_mul, hα', Matrix.mul_assoc, ← hSC, ← Matrix.map_mul, hSS,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hfac : S.map α * (S'.map α * a) = a := Matrix.map_injective (toFn_injective y) (by
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, hα', hSC, Matrix.mul_assoc, mul_eq_one_comm.1 hQ, Matrix.mul_one])
  have hu : IsUnit (S'.map α * a).det := isUnit_det_of_factor f₁ τ hBα (S.map α) _ (by rw [hfac]; exact ha)
  obtain ⟨f', -, hf'⟩ := h₁.exists_mul (isUnit_nonsing_inv_det _ hu)
  refine ⟨φ, f', ?_⟩
  have hinv : ((S'.map α * a)⁻¹).map (toFn y) = k.co g₀ τ * P := by
    rw [← Matrix.mul_one (Matrix.map _ _), ← hQ, ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ hu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rwa [hinv, ← hP₁, ← Matrix.mul_assoc, EigFrame.co_mul, EigFrame.co_self, Matrix.one_mul] at hf'
