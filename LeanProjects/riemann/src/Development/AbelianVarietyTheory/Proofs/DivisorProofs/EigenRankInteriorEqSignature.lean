import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionOnModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjInt

open GlobalTheory.ShFam.Pad GlobalTheory.ArLieBase GlobalTheory.BalProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_act {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comb_act_mat {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x0 (u i)) (a : 𝓞 E)
    {B : Matrix (Fin m) (Fin m) S} (hB : ∀ i, IsCombAtG t x0 u (B i) (u i ≫ (t.act.act a).left))
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsCombAtG t x0 u cf w) :
    IsCombAtG t x0 u (cf ᵥ* B) (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  have hu' := fun i => tan_act t a (hu i)
  have h2 : IsCombAtG t x0 (fun i => u i ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left) := by
    have h1 := (isCombAtG_iff t x0 (fun j => ovT (hu j)) cf w).1 hw
    refine (isCombAtG_iff t x0 (fun j => ovT (hu' j)) cf _).2 ?_
    rw [← h1, ← Over.comp_left, combT_post]
    congr 2
  have h3 := tanLinG u hu _ Bᵀ cf _ (fun i => hB i) h2
  rwa [Matrix.mulVec_transpose] at h3

theorem affineOpenChart_comp_structure_eq_spMap {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    chart U ≫ s = spMap (fnHom s U.1) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of K))) U.2
    (le_top : U.1 ≤ s ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [chart, ← e, ← Spec.map_comp]
  rfl

theorem exists_eig_subspace_gen {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Z : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) (K : Type) [Field K]
    (ψ : R →+* K) (φ : c.F →+* K) (hφ : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β)) :
    ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧
      ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
        IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
          (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap β := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩

theorem mem_eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) (c : Fin n → k) :
    c ∈ eigSp B χ ↔ ∀ a, c ᵥ* B a = χ a • c := Iff.rfl

theorem eigRank_field {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) (K : Type) [Field K]
    (ψ : Γ(Y.X, U.1) →+* K) (τ : E →+* ℂ) :
    eigRank ψ A (embR c.F c.conj (fnHom Y.s U.1) τ) = Dw.mult τ := by
  let φ : c.F →+* K := ψ.comp (fnHom Y.s U.1)
  have he := GlobalTheory.LineNorm.isTanBasis_of_basis E H Y.X Y.t Γ(Y.X, U.1) (chart U) n v hv hb
  have hφ : spMap ψ ≫ chart U ≫ Y.s = spMap (φ.comp (RingHom.id c.F)) := by
    rw [affineOpenChart_comp_structure_eq_spMap, Guard.sp_comp]
  obtain ⟨V, hVr, hV⟩ := exists_eig_subspace_gen Y (chart U) τ v he K ψ φ hφ
  have hvK : ∀ i, IsTanAtG Y.t (spMap ψ ≫ chart U) (spMap (dualMap ψ) ≫ v i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Y.t ψ (hv i)
  have hbK := he.2 K ψ
  have hAK : ∀ a i, IsCombAtG Y.t (spMap ψ ≫ chart U) (fun j => spMap (dualMap ψ) ≫ v j) ((A a).map ψ i)
      ((spMap (dualMap ψ) ≫ v i) ≫ (Y.t.act.act a).left) := fun a i => by
    rw [Category.assoc]
    exact GlobalTheory.LatDRFree.comb_map Y.t ψ (hA a i)
  have key : eigSp (fun a => (A a).map ψ) (fun a => ψ (embR c.F c.conj (fnHom Y.s U.1) τ a)) = V := by
    ext cf
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hvK cf
    rw [← hV cf w hw]
    have hs : ∀ a : 𝓞 E, ψ (embR c.F c.conj (fnHom Y.s U.1) τ a) • cf = fun k => φ (embK c τ a) * cf k :=
      fun a => rfl
    rw [mem_eigSp]
    constructor
    · intro h
      refine ⟨Guard.comb_tan hvK hw, fun a => ?_⟩
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      rw [h a, hs a] at h1
      exact Guard.comb_unique hvK h1 (Guard.comb_smul hvK hw (φ (embK c τ a)))
    · rintro ⟨-, h⟩ a
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      have h2 := Guard.comb_smul hvK hw (φ (embK c τ a))
      rw [← h a] at h2
      rw [hs a]
      exact (hbK _ (Guard.comb_tan hvK h1)).unique h1 h2
  unfold eigRank
  rw [key, hVr]

end GlobalTheory.BalProjInt

theorem GlobalTheory.BalProjInt.eigRank_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ U n v A hv hb hA 𝔭 _ τ
  exact GlobalTheory.BalProjInt.eigRank_field Y U n v A hv hb hA _ _ τ
