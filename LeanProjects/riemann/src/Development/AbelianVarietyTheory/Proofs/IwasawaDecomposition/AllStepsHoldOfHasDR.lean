import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChangeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC GlobalTheory.LocM.MapComp GlobalTheory.LocM.CommonMod

namespace GlobalTheory.LocM.StepOfFrame

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_dual {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] [Nontrivial R] {y : Sp R ⟶ X} {V : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ V) {n n' d : ℕ} {m : Fin n' → Γ(GlobalTheory.LieVB.omega t.G, V)} (hm : VB.IsFrame m)
    {v : Fin n → TanM y t.G} (hv : Full v) (e : Fin d ↪ Fin n) :
    ∃ a : GL (Fin n') R, ∀ (j : Fin n') (i : Fin d), (i : ℕ) ≠ j →
      ∑ l, a j l * tanEv t (isTan_tv (v (e i))) h (m l) = 0 := by
  classical
  let M : Matrix (Fin n') (Fin n) R := Matrix.of fun l i => tanEv t (isTan_tv (v i)) h (m l)
  have key : ∀ (c : Fin n → R) (l : Fin n'), tanEv t (isTan_tv (∑ i, c i • v i)) h (m l) = M.mulVec c l := fun c l => by
    rw [GlobalTheory.T.tanEv_linear_combination E H X t R y V h n _ (fun i => isTan_tv (v i)) c _ _ ((LieMet.isComb_iff v c _).2 rfl)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hb : Function.Bijective M.mulVecLin := by
    refine ⟨fun c c' hc => ?_, fun b => ?_⟩
    · have := (GlobalTheory.T.existsUnique_tangent_of_values E H X t R y V h n' m hm (M.mulVec c)).unique ⟨_, key c⟩
        ⟨_, fun l => (key c' l).trans (congrFun hc l).symm⟩
      exact (hv _).unique rfl (tan_ext this)
    · obtain ⟨w, ⟨hw, hw'⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_of_values E H X t R y V h n' m hm b
      obtain ⟨c, hc, -⟩ := hv (tanOf hw)
      refine ⟨c, funext fun l => ((key c l).symm.trans ?_).trans (hw' l)⟩
      simp only [← hc]
      rfl
  obtain rfl : n = n' := by simpa using (LinearEquiv.ofBijective _ hb).finrank_eq
  obtain ⟨u, hu⟩ : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hb.2
  have hd : d ≤ n := by simpa using Fintype.card_le_of_embedding e
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair _ _ (Fin.castLE_injective hd) e.injective
  refine ⟨⟨(u⁻¹).1.submatrix ρ id, M.submatrix id ρ, ?_, ?_⟩, fun j i hij => ?_⟩
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← hu, Units.inv_mul, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, ← hu, Units.mul_inv, Matrix.submatrix_id_id]
  · have e₁ : ((u⁻¹).1 * M) (ρ j) (e i) = 0 := by
      rw [← hu, Units.inv_mul, Matrix.one_apply_ne]
      rw [← hρ i]
      exact fun q => hij (congrArg Fin.val (ρ.injective q)).symm
    exact e₁

theorem full_map {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {R : Type} [CommRing R] {y : Sp R ⟶ X} {y' : Sp R ⟶ X'}
    (L : TanM y t.G ≃ₗ[R] TanM y' t'.G) {n : ℕ} {v : Fin n → TanM y t.G} (hv : Full v) : Full fun i => L (v i) := fun w => by
  obtain ⟨w, rfl⟩ := L.surjective w
  refine (existsUnique_congr fun a => ?_).1 (hv w)
  rw [← L.injective.eq_iff, map_sum]
  simp only [map_smul]

theorem exists_full {X X' X₁ : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₁ : SAB H X₁} {τ : X' ⟶ X} {π : X₁ ⟶ X}
    (mu : SABMap t' t τ) (nu : SABMap t₁ t π) {R₀ R : Type} [CommRing R₀] [CommRing R] (ρ : R₀ →+* R) {y₀ : Sp R₀ ⟶ X'}
    {y : Sp R ⟶ X₁} (q : (spMap ρ ≫ y₀) ≫ τ = y ≫ π) {n : ℕ} {v : Fin n → (Sp (DualNumber R₀) ⟶ t'.G.left)}
    (hvt : ∀ i, IsTanAtG t' y₀ (v i)) (hvb : ∀ u, IsTanAtG t' y₀ u → ∃! cf, IsCombAtG t' y₀ v cf u) :
    ∃ v₁ : Fin n → TanM y t₁.G, Full v₁ ∧
      ∀ i, (tv (v₁ i)).left ≫ nu.φ = (spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) ≫ mu.φ := by
  have hv₀ : Full fun i => tanOf (hvt i) := fun u =>
    (existsUnique_congr fun a => LieMet.isComb_iff (fun i => tanOf (hvt i)) a u).1 (hvb _ (isTan_tv u))
  exact ⟨_, full_map ((pushE mu _ q).trans (pushE nu y rfl).symm) (full_bc ρ hv₀), fun i =>
    congrArg (fun z => (tv z).left) ((pushE nu y rfl).apply_symm_apply _)⟩

theorem sum_map_mul_eq_zero {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n : ℕ} (a b : Fin n → R) (c : k)
    (h : ∑ l, a l * b l = 0) : ∑ l, φ (a l) * (c * φ (b l)) = 0 := by
  have := congrArg (fun s => c * φ s) h
  simp only [map_sum, map_mul, map_zero, mul_zero, Finset.mul_sum] at this
  exact (Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _).trans this

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem exists_isTrans {Z' Z : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) (x : Z'.X) :
    ∃ (τ : (Y Z'.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z'.i).t (Y Z.i).t τ), LocM.IsTrans Z.i Z'.i τ mu := by
  haveI : Nonempty Z'.X := ⟨x⟩
  obtain ⟨z, hz⟩ := Z'.dense.nonempty
  obtain ⟨τ, mu, -, ht, -⟩ := hf.2 (Z'.X.residueField z) (Z'.X.fromSpecResidueField z) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply z a).symm ▸ hz)
  exact ⟨τ, mu, ht⟩

theorem isIso_incl_top (Z : Mdl Y i₀) : IsIso (Lat.top Z).N.incl :=
  Twist.isIso_of_bijective _ fun V => ⟨(Lat.top Z).N.incl_app_injective V, fun s =>
    ⟨(Lat.top Z).N.mkSec s (by rw [Lat.isTop_top V]; trivial), (Lat.top Z).N.incl_app_mkSec _ _⟩⟩

theorem holds_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), HasDR Z' → (∃ f, IsMap Z' Z f) → ∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z' := by
  intro E _ _ _ H Dw Xo p W _ _ Y i₀ Z Z' hZ ⟨f, hf⟩ t ht
  obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
  have hrt : r ∈ Z'.ty σ := by rw [hZ.1, Finset.mem_range]; omega
  refine ⟨hrt, f, hf, fun x => ?_⟩
  obtain ⟨τ, mu, htr⟩ := exists_isTrans hf x
  have hπ := comp_π_eq hf htr
  obtain ⟨U₀, hU₀, w, hx₀, hw, hfl⟩ := hZ.2 x
  obtain ⟨n, v, e, hve, hvt, hvb⟩ := hw σ
  obtain ⟨V, n', m, hxV, hm⟩ := (Lat.top Z).free (f x)
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U₀ ⊓ f ⁻¹ᵁ V) ⟨hx₀, hxV⟩
  have h₀ : U ≤ U₀ := fun z hz => (hle hz).1
  have h₁ : U ≤ f ⁻¹ᵁ V := fun z hz => (hle hz).2
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  let ρ : Γ(Z'.X, U₀) →+* Γ(Z'.X, U) := (Z'.X.presheaf.map (homOfLE h₀).op).hom
  have hρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec := hU₀.map_fromSpec hU (homOfLE h₀).op
  have hy : ⊤ ≤ (hU.fromSpec ≫ f) ⁻¹ᵁ V := fun z _ => by
    have := h₁ (hU.range_fromSpec.le ⟨z, rfl⟩)
    rwa [Scheme.Hom.comp_preimage]
  have q₁ : (spMap ρ ≫ hU₀.fromSpec ≫ Z'.π) ≫ τ = (hU.fromSpec ≫ f) ≫ Z.π := by
    rw [← Category.assoc (spMap ρ), hρ, Category.assoc, Category.assoc, hπ]
  obtain ⟨v₁, hv₁, hL⟩ := exists_full (R := Γ(Z'.X, U)) mu Z.tMap ρ q₁ hvt hvb
  have := isIso_incl_top Z
  obtain ⟨a, ha⟩ := exists_dual (R := Γ(Z'.X, U)) Z.t hy (hm.map_iso (Lat.top Z).N.incl) hv₁ e
  refine ⟨U, hU, V, n', m, a, hxU, h₁, hm, ?_⟩
  rintro k _ φ z hz h ⟨τ', mu', u, i, htr', hu, hi, hzu⟩ j hj
  obtain ⟨rfl, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' hf.1.2.1 htr htr'
  have ept : spMap (φ.comp ρ) ≫ hU₀.fromSpec = spMap φ ≫ hU.fromSpec := by
    rw [← sp_comp, Category.assoc, hρ]
  have hw' := hfl k (φ.comp ρ) (by rw [ept]; exact range_subset_opn Z' hu)
  rw [ept] at hw'
  obtain ⟨c, -, fu, sf⟩ := flagAt_two Z' hw' hu
  obtain ⟨cf, hcf, hcomb⟩ := sf σ r hrt i hi
  obtain ⟨b, ψ, hb, -⟩ := hu
  obtain ⟨y, hy', -⟩ := exists_lift_chart Z' hb
  rw [← hmu k y _ _ _ (by rw [hy']; exact (fu.1 σ i).1.1)] at hzu
  let z' : Fin (Dw.mult σ) → (Sp (DualNumber k) ⟶ Z.t.G.left) := fun i' =>
    spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (v₁ (e i'))).left
  have hz' : ∀ i', IsTanAtG Z.t (spMap φ ≫ hU.fromSpec ≫ f) (z' i') := fun i' => isTan_map φ rfl (isTan_tv _)
  have hc₁ := comb_push mu hcomb
  have q₂ : ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) ≫ τ = (spMap φ ≫ hU.fromSpec ≫ f) ≫ Z.π := by
    simp only [Category.assoc, hπ]
  have q₃ : (fun i' => w.bc (φ.comp ρ) σ i' ≫ mu.φ) = fun i' => z' i' ≫ Z.tMap.φ := funext fun i' => by
    rw [← Vecs.bc_bc, Category.assoc, hL, hve]
    exact Category.assoc _ _ _
  rw [q₂, q₃, ← hzu] at hc₁
  have hz₁ : IsTanAtG Z.t (spMap φ ≫ hU.fromSpec ≫ f) z := by rw [← Category.assoc]; exact hz
  have h' : ⊤ ≤ (spMap φ ≫ hU.fromSpec ≫ f) ⁻¹ᵁ V := by rw [← Category.assoc]; exact h
  have hc₂ := (comb_push_iff Z.tMap hz' cf hz₁).1 hc₁
  have ev : ∀ s, tanEv Z.t hz h s = ∑ i', cf i' * φ (tanEv Z.t (isTan_tv (v₁ (e i'))) hy s) :=
    fun s => by
      refine Eq.trans ?_ ((GlobalTheory.T.tanEv_linear_combination E H _ Z.t k _ V h' _ z' hz' cf z hz₁ hc₂ s).trans
        (Finset.sum_congr rfl fun i' _ => congrArg (cf i' * ·) (GlobalTheory.T.tanEv_base_change E H _ Z.t _ _ V hy _ _ k φ _ h' s)))
      congr 1
  show ∑ l, φ (a j l) * tanEv Z.t hz h ((Lat.top Z).N.incl.app V (m l)) = 0
  simp only [ev, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i' _ => ?_
  by_cases hi' : r ≤ (i' : ℕ)
  · simp [hcf i' hi']
  · exact sum_map_mul_eq_zero (R := Γ(Z'.X, U)) φ _ _ _ (ha j i' (by have : r ≤ (j : ℕ) := hj; omega))

end GlobalTheory.LocM.StepOfFrame
