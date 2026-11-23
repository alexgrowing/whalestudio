import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem split_tr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X₀ : Scheme.{0}} (t : SAB H X₀) {A A' R K : Type} [CommRing A] [CommRing A'] [CommRing R] [CommRing K]
    {x₀ : Sp A ⟶ X₀} {x₀' : Sp A' ⟶ X₀} {g g' m : ℕ} {b : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}
    {b' : Fin g' → (Sp (DualNumber A') ⟶ t.G.left)} (hb : IsTanBasis t x₀ b) (hb' : IsTanBasis t x₀' b')
    (α : A →+* R) (α' : A' →+* R) (ψ : R →+* K) (hα : spMap α ≫ x₀ = spMap α' ≫ x₀')
    {x : Sp K ⟶ X₀} (hx : spMap (ψ.comp α) ≫ x₀ = x) {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)}
    (hu : ∀ a, IsTanAtG t x (u a)) {P P' : Matrix (Fin m) (Fin m) K} (hP : IsUnit P.det)
    {S : Matrix (Fin g) (Fin m) A} {S' : Matrix (Fin m) (Fin g) A} (hS : S' * S = 1) {S₂ : Matrix (Fin g') (Fin m) A'}
    (h₁ : ∀ i, ∃ w, IsCombAtG t x u (fun a => P a i) w ∧
      IsCombAtG t x (fun k => spMap (dualMap (ψ.comp α)) ≫ b k) (fun k => (ψ.comp α) (S k i)) w)
    (h₂ : ∀ i, ∃ w, IsCombAtG t x u (fun a => P' a i) w ∧
      IsCombAtG t x (fun k => spMap (dualMap (ψ.comp α')) ≫ b' k) (fun k => (ψ.comp α') (S₂ k i)) w) :
    ∃ T : Matrix (Fin m) (Fin m) R, P' = P * T.map ψ := by
  subst hx
  have hbt : ∀ k, IsTanAtG t (spMap (ψ.comp α) ≫ x₀) (spMap (dualMap (ψ.comp α)) ≫ b k) :=
    fun k => GlobalTheory.LieMet.isTan_map _ rfl (hb.1 k)
  choose U hU using fun a => (hb.2 K (ψ.comp α) (u a) (hu a)).exists
  choose C hC using fun k => (hb.2 R α _ (GlobalTheory.LieMet.isTan_map α' hα.symm (hb'.1 k))).exists
  have hC' : ∀ k, IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun l => spMap (dualMap (ψ.comp α)) ≫ b l)
      (fun l => ψ (C k l)) (spMap (dualMap (ψ.comp α')) ≫ b' k) := fun k => by
    have := Chart.coord_map α ψ (hC k)
    rwa [Chart.dual_comp] at this
  have e₁ : (S.map α).map ψ = (Matrix.of U)ᵀ * P := by
    ext k i
    obtain ⟨w, hw, hw'⟩ := h₁ i
    have := congrFun ((hb.2 K (ψ.comp α) w (Chart.comb_tan hu hw)).unique hw' (Chart.comb_comb hbt hU hw)) k
    simpa [Matrix.mul_apply, mul_comm] using this
  have e₂ : ((Matrix.of C)ᵀ * S₂.map α').map ψ = (Matrix.of U)ᵀ * P' := by
    ext k i
    obtain ⟨w, hw, hw'⟩ := h₂ i
    have := congrFun ((hb.2 K (ψ.comp α) w (Chart.comb_tan hu hw)).unique (Chart.comb_comb hbt hC' hw')
      (Chart.comb_comb hbt hU hw)) k
    simpa [Matrix.mul_apply, mul_comm] using this
  have e₃ : (S'.map α).map ψ * (Matrix.of U)ᵀ * P = 1 := by
    rw [Matrix.mul_assoc, ← e₁, ← Matrix.map_mul, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨S'.map α * ((Matrix.of C)ᵀ * S₂.map α'), ?_⟩
  rw [Matrix.map_mul, e₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc P, mul_eq_one_comm.1 e₃, Matrix.one_mul]

private theorem le_stalk {X : Scheme.{0}} {y : X} {V : X.Opens} (hV : y ∈ V) : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ V := by
  intro s _
  have : X.fromSpecStalk y s ∈ Set.range (X.fromSpecStalk y) := ⟨s, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact this.mem_open V.isOpen hV

private theorem evalPt_stalk {X : Scheme.{0}} {y : X} {V : X.Opens} (hV : y ∈ V) (h : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ V)
    (a : Γ(X, V)) : evalPt (R := X.presheaf.stalk y) (X.fromSpecStalk y) V h a = X.presheaf.germ V y hV a := by
  have : (X.fromSpecStalk y).appLE _ ⊤ h ≫ (Scheme.ΓSpecIso (X.presheaf.stalk y)).hom =
      X.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (X.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (X.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

private theorem glue {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (κ : X.functionField →+* K) {U : X.Opens}
    (hU : genericPoint X ∈ U) {m : ℕ} (T₀ : Matrix (Fin m) (Fin m) K)
    (h : ∀ x ∈ U, ∃ T : Matrix (Fin m) (Fin m) (X.presheaf.stalk x),
      T₀ = T.map (κ.comp (algebraMap _ X.functionField))) :
    ∃ T : Matrix (Fin m) (Fin m) Γ(X, U), T₀ = T.map (κ.comp (fnOf U hU)) := by
  obtain ⟨T₁, h₁⟩ : ∃ T₁ : Matrix (Fin m) (Fin m) X.functionField, T₀ = T₁.map κ :=
    have ⟨T₁, h₁⟩ := h _ hU
    ⟨_, h₁.trans (Matrix.map_map).symm⟩
  have key (a b : Fin m) : ∃ s : Γ(X, U), fnOf U hU s = T₁ a b :=
    exists_fnOf_eq hU fun x hx => by
      obtain ⟨T, hT⟩ := h x hx
      exact ⟨T a b, κ.injective (congrFun (congrFun (hT.symm.trans h₁) a) b)⟩
  choose s hs using key
  refine ⟨Matrix.of s, h₁.trans ?_⟩
  ext a b
  exact congrArg κ (hs a b).symm

theorem UpperTheory.frame_generic_chart :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (X : Scheme.{0}) [IsIntegral X] (j : Y.X ⟶ X) (ρ' : X ⟶ Z.X), j (genericPoint Y.X) = genericPoint X → j ≫ ρ' = ρ ≫ genι Z → ∀ (V V' : X.Opens) (P P' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), SplitOn g₀ τ j ρ' V P → SplitOn g₀ τ j ρ' V' P' → ∀ h : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ (V ⊓ V'), ∃ T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X, V ⊓ V'), IsUnit T.det ∧ P' = P * T.map (evalPt _ _ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ _ g₀ τ X _ j ρ' hj hρ
  have hκ : ∀ p : X, j (genericPoint Y.X) = p →
      ∃ κ : X.presheaf.stalk p →+* Y.Fn, genericPt Y ≫ j = spMap κ ≫ X.fromSpecStalk p := by
    rintro _ rfl
    exact ⟨(j.stalkMap _).hom, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : X.functionField →+* Y.Fn, genericPt Y ≫ j = spMap κ ≫ X.fromSpecStalk (genericPoint X) :=
    hκ _ hj
  have hev : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (h : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ U),
      evalPt _ U h = κ.comp (fnOf U hU) := by
    rw [hκ]
    intro U hU h
    refine RingHom.ext fun a => ?_
    exact (evalPt_spMap_comp κ _ U (le_stalk hU) h a).trans (congrArg κ (evalPt_stalk hU _ a))
  have hloc : ∀ (V V' : X.Opens) (P P' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn),
      SplitOn g₀ τ j ρ' V P → SplitOn g₀ τ j ρ' V' P' → ∀ x : X, x ∈ V → x ∈ V' →
      ∃ T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X.presheaf.stalk x),
        P⁻¹ * P' = T.map (κ.comp (algebraMap _ X.functionField)) := by
    rintro V V' P P' ⟨hV, hξ, g, b, S, S', hb, hS, hP, h₁⟩ ⟨hV', hξ', g', b', S₂, -, hb', -, -, h₂⟩ x hx hx'
    have hc : ∀ (U : X.Opens) (hU : x ∈ U) (h : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ U), evalPt _ U h =
        (κ.comp (algebraMap _ X.functionField)).comp (evalPt (R := X.presheaf.stalk x) _ U (le_stalk hU)) :=
      fun U hU h => (hev U (gen_mem hU) h).trans (RingHom.ext fun a =>
        congrArg κ ((algebraMap_germ hU a).symm.trans (congrArg _ (evalPt_stalk hU _ a).symm)))
    have hx₀ : spMap (evalPt _ V hξ) ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ ρ ≫ genι Z := by
      rw [← hρ, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ ρ') (eq_spec_fromSpec hV _ hξ).symm
    rw [hc V hx] at h₁ hx₀
    rw [hc V' hx'] at h₂
    obtain ⟨T, hT⟩ := split_tr Z.t hb hb' _ _ _ (by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ ρ') ((eq_spec_fromSpec hV _ (le_stalk hx)).symm.trans
        (eq_spec_fromSpec hV' _ (le_stalk hx')))) hx₀ (g₀.tan τ) hP hS h₁ h₂
    exact ⟨T, by rw [hT, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]⟩
  intro V V' P P' hP hP' h
  have hU : genericPoint X ∈ V ⊓ V' := by
    have h' := h
    rw [hκ] at h'
    have h₁ : X.fromSpecStalk _ (spMap κ (IsLocalRing.closedPoint Y.Fn)) ∈ V ⊓ V' := h' (Set.mem_univ _)
    exact gen_mem h₁
  obtain ⟨T, hT⟩ := glue κ hU _ fun x hx => hloc V V' P P' hP hP' x hx.1 hx.2
  obtain ⟨T', hT'⟩ := glue κ hU _ fun x hx => hloc V' V P' P hP' hP x hx.2 hx.1
  obtain ⟨-, -, -, -, -, -, -, -, hu, -⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, -, hu', -⟩ := hP'
  refine ⟨T, Matrix.isUnit_det_of_right_inverse (B := T') ?_, ?_⟩
  · refine Matrix.map_injective (f := κ.comp (fnOf _ hU)) (κ.injective.comp (fnOf_injective _ hU)) ?_
    beta_reduce
    rw [Matrix.map_mul, ← hT, ← hT', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]
  · rw [hev _ hU h, ← hT, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
