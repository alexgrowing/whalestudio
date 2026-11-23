import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.StalkMatrixLeftInverse
import Development.AutomorphicArithmetic.DivisorFrames.ExistsDivisorFrameGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_leftInv {R : Type} [CommRing R] [IsLocalRing R] {m g : ℕ} (a : Fin m → Fin g → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R) fun l i => IsLocalRing.residue R (a l i)) :
    ∃ a' : Matrix (Fin m) (Fin g) R, a' * (Matrix.of fun k l => a l k) = 1 := by
  obtain ⟨s, hs⟩ := GlobalTheory.LineNorm.Chart.exists_minor_ne_zero _ h le_rfl
  rw [← GlobalTheory.LineNorm.Chart.map_minor, IsLocalRing.residue_ne_zero_iff_isUnit] at hs
  let A : Matrix (Fin g) (Fin m) R := Matrix.of fun k l => a l k
  have hu : IsUnit (A.submatrix s id).det := by
    rw [← Matrix.det_transpose]; exact hs
  refine ⟨(A.submatrix s id)⁻¹ * (1 : Matrix (Fin g) (Fin g) R).submatrix s id, ?_⟩
  have e1 : (1 : Matrix (Fin g) (Fin g) R).submatrix s id * A = A.submatrix s id := by
    conv_rhs => rw [← Matrix.one_mul A]
    rfl
  rw [Matrix.mul_assoc]
  exact (congrArg _ e1).trans (Matrix.nonsing_inv_mul _ hu)

private theorem ev_from {R : Type} [CommRing R] {M X : Scheme.{0}} {V : M.Opens} (hV : IsAffineOpen V)
    (x : Sp R ⟶ M) (h : ⊤ ≤ x ⁻¹ᵁ V) (r : M ⟶ X) : spMap (evalPt x V h) ≫ hV.fromSpec ≫ r = x ≫ r :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) (eq_spec_fromSpec hV x h).symm)

section SlopeTestRemainingChoices

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem isTanBasis_map {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X}
    {g : ℕ} {b : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x b) (β : R →+* S) :
    IsTanBasis t (spMap β ≫ x) fun i => spMap (dualMap β) ≫ b i := by
  refine ⟨fun i => GlobalTheory.LieMet.isTan_map _ rfl (h.1 i), fun T _ φ w hw => ?_⟩
  rw [← Category.assoc, spMap_comp'] at hw ⊢
  simp only [GlobalTheory.LineNorm.Chart.dual_comp]
  exact h.2 T _ w hw

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : Var F}
  {ρ : Y.X ⟶ gen Z}

omit [NumberField F] in
private theorem pull_split (g₀ : GenFrame e ρ) (τ : E →+* ℂ) {X M N : Scheme.{0}} (j : Y.X ⟶ X) (p : X ⟶ M)
    (q : X ⟶ N) (ρ' : M ⟶ Z.X) (hρ : (j ≫ p) ≫ ρ' = ρ ≫ genι Z) {V : M.Opens} (hV : IsAffineOpen V) {W : N.Opens}
    {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ p ⁻¹ᵁ V) (hUW : U ≤ q ⁻¹ᵁ W)
    (hξ : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ U) (hξV : ⊤ ≤ (genericPt Y ≫ j ≫ p) ⁻¹ᵁ V)
    (hξW : ⊤ ≤ (genericPt Y ≫ j ≫ q) ⁻¹ᵁ W) {g : ℕ} {b : Fin g → (Sp (DualNumber Γ(M, V)) ⟶ Z.t.G.left)}
    (hb : IsTanBasis Z.t (R := Γ(M, V)) (hV.fromSpec ≫ ρ') b) (A₀ : Matrix (Fin g) (Fin (Dw.mult τ)) Y.Fn)
    (hA : ∀ i, IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (fun k => spMap (dualMap (evalPt _ V hξV)) ≫ b k)
      (fun k => A₀ k i) (g₀.v τ i))
    (S : Matrix (Fin g) (Fin (Dw.mult τ)) Γ(N, W)) (S' : Matrix (Fin (Dw.mult τ)) (Fin g) Γ(N, W))
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) (hS : S' * S = 1) (hT : IsUnit T.det)
    (hAS : A₀ = S.map (evalPt _ W hξW) * T) : SplitOn g₀ τ j (p ≫ ρ') U T⁻¹ := by
  let γ : Γ(M, V) →+* Γ(X, U) := (p.appLE V U hUV).hom
  let δ : Γ(N, W) →+* Γ(X, U) := (q.appLE W U hUW).hom
  have hγ : spMap γ ≫ hV.fromSpec = hU.fromSpec ≫ p := IsAffineOpen.SpecMap_appLE_fromSpec p hV hU hUV
  have h1 : (evalPt _ U hξ).comp γ = evalPt _ V hξV := RingHom.ext fun s =>
    evalPt_appLE (genericPt Y ≫ j) p hUV hξ hξV s
  have h2 : ∀ s, evalPt _ U hξ (δ s) = evalPt _ W hξW s := fun s =>
    evalPt_appLE (genericPt Y ≫ j) q hUW hξ hξW s
  have hx : spMap (evalPt _ V hξV) ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ ρ ≫ genι Z := by
    rw [ev_from, Category.assoc, hρ]
  refine ⟨hU, hξ, g, fun i => spMap (dualMap γ) ≫ b i, S.map δ, S'.map δ, ?_, ?_, isUnit_nonsing_inv_det T hT,
    fun i => ⟨_, (GlobalTheory.LineNorm.Chart.comb_iff (g₀.tan τ) _ _).2 rfl, ?_⟩⟩
  · have := isTanBasis_map hb γ
    rwa [← Category.assoc, hγ, Category.assoc] at this
  · rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := GlobalTheory.LineNorm.Chart.comb_comb (fun k => GlobalTheory.LieMet.isTan_map _ hx (hb.1 k)) hA
      ((GlobalTheory.LineNorm.Chart.comb_iff (g₀.tan τ) (fun a => T⁻¹ a i) _).2 rfl)
    simp only [GlobalTheory.LineNorm.Chart.dual_comp, h1, Matrix.map_apply, h2]
    convert this using 1
    funext k
    have h3 : A₀ * T⁻¹ = S.map (evalPt _ W hξW) := by rw [hAS, Matrix.mul_assoc, mul_nonsing_inv _ hT, Matrix.mul_one]
    have h4 := congrFun (congrFun h3 k) i
    rw [Matrix.map_apply, mul_apply] at h4
    rw [← h4]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [NumberField F] in
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
private theorem local_coord (g₀ : GenFrame e ρ) (τ : E →+* ℂ) {M : Scheme.{0}} (j : Y.X ⟶ M)
    (ρ' : M ⟶ Z.X) (hρ : j ≫ ρ' = ρ ≫ genι Z) {V : M.Opens} (hV : IsAffineOpen V)
    (hξV : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ V) {g : ℕ} {b : Fin g → (Sp (DualNumber Γ(M, V)) ⟶ Z.t.G.left)}
    (hb : IsTanBasis Z.t (R := Γ(M, V)) (hV.fromSpec ≫ ρ') b) :
    ∃ A₀ : Matrix (Fin g) (Fin (Dw.mult τ)) Y.Fn,
      (∀ i, IsCombAtG Z.t (genericPt Y ≫ ρ ≫ genι Z) (fun k => spMap (dualMap (evalPt _ V hξV)) ≫ b k)
        (fun k => A₀ k i) (g₀.v τ i)) ∧
      ∀ (y : Y.X) (_ : j y ∈ V) φ f P, Fits g₀ τ y φ f P →
        ∃ (a : Matrix (Fin g) (Fin (Dw.mult τ)) (Y.X.presheaf.stalk y))
          (a' : Matrix (Fin (Dw.mult τ)) (Fin g) (Y.X.presheaf.stalk y)), a' * a = 1 ∧ A₀ * P = a.map (toFn y) := by
  have hx : spMap (evalPt _ V hξV) ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ ρ ≫ genι Z := by
    rw [ev_from, Category.assoc, hρ]
  have hA := fun i => (hb.2 _ (evalPt _ V hξV) (g₀.v τ i) (by rw [hx]; exact g₀.tan τ i)).exists
  choose A hA using hA
  refine ⟨Matrix.of fun k i => A i k, fun i => by have := hA i; rwa [hx] at this, fun y hy φ f P hf => ?_⟩
  have hs := stalk_le j hy
  let α : Γ(M, V) →+* Y.X.presheaf.stalk y := evalPt _ V hs
  have hα : spMap α ≫ hV.fromSpec ≫ ρ' = stalkPt Y y ≫ ρ ≫ genι Z := by
    rw [ev_from, Category.assoc, hρ]
  have hαι : (toFn y).comp α = evalPt _ V hξV := GlobalTheory.LineNorm.Chart.ringHom_ext hV (by
    refine Eq.trans ?_ (eq_spec_fromSpec hV _ hξV)
    rw [← spMap_comp', Category.assoc, ← spMap_toFn y, Category.assoc]
    exact congrArg _ (eq_spec_fromSpec hV _ hs).symm)
  have ha := fun i => (hb.2 _ α (f.v τ i) (by rw [hα]; exact f.tan τ i)).exists
  choose a ha using ha
  obtain ⟨f', hf'⟩ := f.exists_isMap (IsLocalRing.residue _) rfl rfl
  have hli := GlobalTheory.LineNorm.Chart.coord_linInd hb α (IsLocalRing.residue _) ha (by
    rw [hα, ← funext (hf' τ)]
    intro cf cf' w h h'
    have h1 := (GlobalTheory.LineNorm.Chart.comb_iff (f'.tan τ) _ _).1 h
    have h2 := (GlobalTheory.LineNorm.Chart.comb_iff (f'.tan τ) _ _).1 h'
    exact funext ((Fintype.linearIndependent_iffₛ.1 (f'.linearIndependent_vec τ)) _ _
      (GlobalTheory.LieMet.tan_ext (h1.symm.trans h2))))
  obtain ⟨a', ha'⟩ := exists_leftInv a hli
  refine ⟨_, a', ha', ?_⟩
  ext k i
  have h1 := GlobalTheory.LineNorm.Chart.coord_map α (toFn y) (ha i)
  rw [hαι] at h1
  have he := fun k => GlobalTheory.LieMet.isTan_map (evalPt _ V hξV) rfl (hb.1 k)
  have h2 := GlobalTheory.LineNorm.Chart.comb_comb he hA (by rw [hx]; exact hf.2 i)
  have h3 := congrFun ((hb.2 _ _ _ (GlobalTheory.LineNorm.Chart.comb_tan he h1)).unique h1 h2) k
  rw [Matrix.map_apply, Matrix.of_apply, h3, mul_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, Matrix.of_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_true_model_over :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ), ∃ (N : GlobalTheory.TrueGeo.Model Y) (ρ' : N.X ⟶ Z.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X ∧ N.j ≫ ρ' = ρ ≫ genι Z ∧ ∀ (τ : E →+* ℂ) (z : N.X), ∃ V P, z ∈ V ∧ SplitOn g₀ τ N.j ρ' V P := by
  intro E _ _ _ H Dw l Xo c Z F _ _ e Y ρ hρ g₀
  classical
  obtain ⟨-, -, M, ρ', -, hM⟩ := GlobalTheory.T.exists_normal_model_over_projective F Y (𝓞 c.F) (RingOfIntegers.mapRingEquiv e)
    Z.X Z.s (ρ ≫ genι Z) Z.proj (by
      rw [← hρ]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hgen : ∀ (N : GlobalTheory.TrueGeo.Model Y) (U : N.X.Opens) (z : N.X), z ∈ U → ⊤ ≤ (genericPt Y ≫ N.j) ⁻¹ᵁ U :=
    fun N U z hz => by
      have := N.ar.isIntegral
      exact gen_le N.j ((SmallSec.j_gen_specializes N).mem_open U.isOpen (gen_mem hz))
  have key : ∀ (τ : E →+* ℂ) (z : M.X), ∃ (N : GlobalTheory.TrueGeo.Model Y) (π : N.X ⟶ M.X) (V' : M.X.Opens),
      N.j ≫ π = M.j ∧ z ∈ V' ∧ ∀ (P : GlobalTheory.TrueGeo.Model Y) (q : P.X ⟶ N.X), P.j ≫ q = N.j → ∀ x : P.X,
        (q ≫ π) x ∈ V' → ∃ V T, x ∈ V ∧ SplitOn g₀ τ P.j ((q ≫ π) ≫ ρ') V T := by
    intro τ z
    obtain ⟨⟨V, hV⟩, g, b, hz, hb⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H Z.X Z.t M.X ρ' z
    replace hV : IsAffineOpen V := hV
    obtain ⟨Δ, t, ht, hfit⟩ := UpperTheory.exists_divisor_frame_generic E H Dw l Xo c _ _ Z F e Y ρ hρ g₀ τ
    obtain ⟨A₀, hA, hloc⟩ := local_coord g₀ τ M.j ρ' hM hV (hgen M V z hz) hb
    obtain ⟨N, π, V', h1, h2, h3, h4⟩ := UpperTheory.stalk_matrix_left_inverse F Y M Δ t ht V z hz g _ A₀ fun y hy => by
      obtain ⟨φ, f, P, hf, hP⟩ := hfit y
      obtain ⟨a, a', ha, haP⟩ := hloc y hy φ f P hf
      refine ⟨a, a', P⁻¹, ha, ?_, ?_⟩
      · rw [← haP, Matrix.mul_assoc, mul_nonsing_inv _ hf.isUnit_det, Matrix.mul_one]
      · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact (eq_inv_of_mul_eq_one_left hP).symm
    refine ⟨N, π, V', h1, h2, fun P q hq x hx => ?_⟩
    obtain ⟨W, hW, S, S', T, hxW, hS, hT, hAS⟩ := h4 (q x) hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ := P.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((q ≫ π) ⁻¹ᵁ V ⊓ q ⁻¹ᵁ W : P.X.Opens) from ⟨h3 hx, hxW⟩) ((q ≫ π) ⁻¹ᵁ V ⊓ q ⁻¹ᵁ W : P.X.Opens).isOpen
    have e1 : P.j ≫ q ≫ π = M.j := by rw [← Category.assoc, hq, h1]
    refine ⟨U, T⁻¹, hxU, pull_split g₀ τ P.j (q ≫ π) q ρ' (by rw [e1, hM]) hV hU (fun a ha => (hle ha).1)
      (fun a ha => (hle ha).2) (hgen P U x hxU) (by rw [e1]; exact hgen M V z hz) (by rw [hq]; exact hW) hb A₀
      ?_ S S' T hS hT ?_⟩
    · simpa only [e1] using hA
    · simpa only [hq] using hAS
  choose N π V' h1 h2 h3 using key
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.p
  choose S hS using fun τ => CompactSpace.elim_nhds_subcover (fun z => (V' τ z : Set M.X))
    fun z => (V' τ z).isOpen.mem_nhds (h2 τ z)
  obtain ⟨P, σ, hP, hσ, hdom⟩ := GlobalTheory.LineNorm.Glue.exists_normal_dominating_finset M
    (fun a : (_ : E →+* ℂ) × M.X => N a.1 a.2) (Finset.univ.sigma S)
  refine ⟨P, σ ≫ ρ', hP, by rw [← Category.assoc, hσ, hM], fun τ x => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 ((hS τ).ge (Set.mem_univ (σ x)))
  obtain ⟨q, hq⟩ := hdom ⟨τ, a⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ _, ha⟩)
  obtain rfl : σ = q ≫ π τ a := GlobalTheory.LineNorm.Glue.hom_unique hσ (by rw [← Category.assoc, hq, h1])
  exact h3 τ a P q hq x hxa
