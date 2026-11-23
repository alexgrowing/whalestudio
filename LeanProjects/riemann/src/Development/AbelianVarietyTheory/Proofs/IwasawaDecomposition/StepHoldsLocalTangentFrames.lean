import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open scoped MonObj
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE isTan_map)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.StepBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V)
  {n : ℕ} {m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)} {b : Fin n → (Sp (DualNumber S) ⟶ t.G.left)}
  (hb : ∀ j, IsTanAtG t x (b j)) {A B : Matrix (Fin n) (Fin n) S} (hB : ∀ l j, tanEv t (hb j) h (m l) = B l j)

include hB in

theorem tanEv_eq_mulVec {cf : Fin n → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w)
    (hc : IsCombAtG t x b cf w) : (fun l => tanEv t hw h (m l)) = B.mulVec cf := by
  funext l
  rw [GlobalTheory.LocM.tanEv_comb E H X t S x V h n b hb cf w hw hc]
  exact Finset.sum_congr rfl fun j _ => by rw [hB, _root_.mul_comm]

include hB in

theorem coeff_eq (hAB : A * B = 1) {cf : Fin n → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w)
    (hc : IsCombAtG t x b cf w) : cf = A.mulVec fun l => tanEv t hw h (m l) := by
  rw [tanEv_eq_mulVec h hb hB hw hc, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

include hB in

theorem isComb_dual (hm : VB.IsFrame m) (hBA : B * A = 1) {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w) :
    IsCombAtG t x b (A.mulVec fun l => tanEv t hw h (m l)) w := by
  have hc := (LieMet.isComb_iff (fun j => tanOf (hb j)) (A.mulVec fun l => tanEv t hw h (m l)) _).2 rfl
  have e := tanEv_eq_mulVec h hb hB (isTan_tv _) hc
  rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at e
  have e' := (GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x V h n m hm fun l => tanEv t hw h (m l)).unique
    ⟨isTan_tv _, congrFun e⟩ ⟨hw, fun _ => rfl⟩
  rw [e'] at hc
  exact hc

end Dual

section Transport

variable {X X₁ X₂ : Scheme.{0}} {t : SAB H X} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
  (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂) {S : Type} [CommRing S] {x₁ : Sp S ⟶ X₁} {x₂ : Sp S ⟶ X₂}
  (hx : x₁ ≫ f₁ = x₂ ≫ f₂)

include hx in

theorem exists_corr {w : Sp (DualNumber S) ⟶ t₂.G.left} (hw : IsTanAtG t₂ x₂ w) :
    ∃ v, IsTanAtG t₁ x₁ v ∧ v ≫ m₁.φ = w ≫ m₂.φ :=
  ⟨_, isTan_tv ((pushE m₁ x₁ hx).symm (pushE m₂ x₂ rfl (tanOf hw))), by
    rw [← left_pushE m₁ x₁ hx, LinearEquiv.apply_symm_apply]
    rfl⟩

include hx in

theorem isComb_corr {n : ℕ} {b₁ : Fin n → (Sp (DualNumber S) ⟶ t₁.G.left)} {b₂ : Fin n → (Sp (DualNumber S) ⟶ t₂.G.left)}
    (h₁ : ∀ j, IsTanAtG t₁ x₁ (b₁ j)) (h₂ : ∀ j, IsTanAtG t₂ x₂ (b₂ j)) (hb : ∀ j, b₁ j ≫ m₁.φ = b₂ j ≫ m₂.φ)
    {w₁ : Sp (DualNumber S) ⟶ t₁.G.left} {w₂ : Sp (DualNumber S) ⟶ t₂.G.left} (k₁ : IsTanAtG t₁ x₁ w₁)
    (k₂ : IsTanAtG t₂ x₂ w₂) (hw : w₁ ≫ m₁.φ = w₂ ≫ m₂.φ) {cf : Fin n → S} (hc : IsCombAtG t₁ x₁ b₁ cf w₁) :
    IsCombAtG t₂ x₂ b₂ cf w₂ := by
  have e := (LieMet.isComb_iff (fun j => tanOf (h₁ j)) cf (tanOf k₁)).1 hc
  refine (LieMet.isComb_iff (fun j => tanOf (h₂ j)) cf (tanOf k₂)).2 ((pushE m₂ x₂ rfl).injective ?_)
  have e₁ : pushE m₂ x₂ rfl (tanOf k₂) = pushE m₁ x₁ hx (tanOf k₁) := tan_ext hw.symm
  have e₂ (j) : pushE m₂ x₂ rfl (tanOf (h₂ j)) = pushE m₁ x₁ hx (tanOf (h₁ j)) := tan_ext (hb j).symm
  rw [e₁, e, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, e₂]

include hx in

theorem exists_dual_basis {V : X₁.Opens} (h : ⊤ ≤ x₁ ⁻¹ᵁ V) {n : ℕ} {m : Fin n → Γ(GlobalTheory.LieVB.omega t₁.G, V)}
    (hm : VB.IsFrame m) (a : GL (Fin n) S) :
    ∃ v : Fin n → (Sp (DualNumber S) ⟶ t₂.G.left), (∀ j, IsTanAtG t₂ x₂ (v j)) ∧
      (∀ u, IsTanAtG t₂ x₂ u → ∃! cf, IsCombAtG t₂ x₂ v cf u) ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k) (y₁ : Sp k ⟶ X₁) (y₂ : Sp k ⟶ X₂), spMap φ ≫ x₁ = y₁ → spMap φ ≫ x₂ = y₂ →
        ∀ u, IsTanAtG t₂ y₂ u → ∃ (w : Sp (DualNumber k) ⟶ t₁.G.left) (hw : IsTanAtG t₁ y₁ w) (h' : ⊤ ≤ y₁ ⁻¹ᵁ V),
          w ≫ m₁.φ = u ≫ m₂.φ ∧ IsCombAtG t₂ y₂ (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j)
            (fun j => ∑ l, φ (a j l) * tanEv t₁ hw h' (m l)) u := by
  choose b hb hbe using fun j : Fin n =>
    (GlobalTheory.TanFibre.existsUnique_tanEv E H X₁ t₁ S x₁ V h n m hm fun l => (a⁻¹).1 l j).exists
  choose v hv hve using fun j => exists_corr m₂ m₁ hx.symm (hb j)
  refine ⟨v, hv, fun u hu => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := exists_corr m₁ m₂ hx hu
    exact ⟨_, isComb_corr m₁ m₂ hx hb hv (fun j => (hve j).symm) hw hu e
      (isComb_dual h hb (A := a.1) (fun l j => hbe j l) hm a.inv_mul hw), fun cf hc =>
      coeff_eq h hb (fun l j => hbe j l) a.mul_inv hw (isComb_corr m₂ m₁ hx.symm hv hb hve hu hw e.symm hc)⟩
  · rintro k _ φ _ _ rfl rfl u hu
    have hx' : (spMap φ ≫ x₁) ≫ f₁ = (spMap φ ≫ x₂) ≫ f₂ := by rw [Category.assoc, Category.assoc, hx]
    have h' : ⊤ ≤ (spMap φ ≫ x₁) ⁻¹ᵁ V := (spMap φ).preimage_mono h
    obtain ⟨w, hw, e⟩ := exists_corr m₁ m₂ hx' hu
    have hb' (j) := isTan_map φ rfl (hb j)
    have hv' (j) := isTan_map φ rfl (hv j)
    have hc := isComb_dual h' hb' (A := a.1.map φ) (B := (a⁻¹).1.map φ) (fun l j => by
      rw [GlobalTheory.LocM.tanEv_baseChange E H X₁ t₁ S x₁ V h (b j) (hb j) k φ, hbe]
      rfl) hm (by rw [← Matrix.map_mul, a.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]) hw
    exact ⟨w, hw, h', e, isComb_corr m₁ m₂ hx' hb' hv' (fun j => by rw [Category.assoc, Category.assoc, hve]) hw hu e hc⟩

end Transport

section Models

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem isFrame_incl {Z : Mdl Y i₀} {V : Z.X.Opens} {n : ℕ} {m : Fin n → Γ((Lat.top Z).N.toMod, V)} (hm : VB.IsFrame m) :
    VB.IsFrame fun l => (Lat.top Z).N.incl.app V (m l) :=
  have : IsIso (Lat.top Z).N.incl := Twist.isIso_of_bijective _ fun V =>
    ⟨(Lat.top Z).N.incl_app_injective V, fun s => ⟨⟨s, (Lat.isTop_top V).ge trivial⟩, rfl⟩⟩
  hm.map_iso (Lat.top Z).N.incl

theorem exists_isTrans {Z Z' : Mdl Y i₀} {g : Z'.X ⟶ Z.X} (hg : IsMap Z' Z g) (x : Z'.X) :
    ∃ (τ : (Y Z'.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z'.i).t (Y Z.i).t τ), LocM.IsTrans Z.i Z'.i τ mu ∧
      g ≫ Z.π = Z'.π ≫ τ := by
  have : Nonempty Z'.X := ⟨x⟩
  obtain ⟨z, hz⟩ := Z'.dense.nonempty
  obtain ⟨τ, mu, -, htr, -⟩ := hg.2 (Z'.X.residueField z) (Z'.X.fromSpecResidueField z) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply z a).symm ▸ hz)
  exact ⟨τ, mu, htr, CommonMod.comp_π_eq hg htr⟩

end Models

theorem exists_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z Z' : Mdl Y i₀) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ), Step.Holds ⟨Z, Lat.top Z, σ, r, hr⟩ Z' → ∀ x : Z'.X, ∃ (U : Z'.X.Opens) (hU : IsAffineOpen U) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Z'.X, U)) ⟶ (Y Z'.i).t.G.left)), x ∈ U ∧ (∀ j, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) (v j)) ∧ (∀ u, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) u → ∃! cf, IsCombAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) v cf u) ∧ ∀ (k : Type) [Field k] (φ : Γ(Z'.X, U) →+* k) (u : Vecs Dw (Y Z'.i).t k), Z'.FlagAt (spMap φ ≫ hU.fromSpec) u → ∀ i : Fin (Dw.mult σ), (i : ℕ) < r → ∃ cf : Fin n → k, (∀ j : Fin n, r ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z'.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j) cf (u σ i) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z Z' σ r hr hH x
  obtain ⟨-, g, hg, hS⟩ := hH
  dsimp only at g hg hS
  obtain ⟨U, hU, V, n, m, a, hxU, hUV, hm, hcl⟩ := hS x
  refine (exists_isTrans hg x).elim fun τ h₀ => h₀.elim fun mu h₁ => ?_
  have htr := h₁.1
  have hπ := h₁.2
  have h : ⊤ ≤ (hU.fromSpec ≫ g) ⁻¹ᵁ V := hU.fromSpec_preimage_self.ge.trans (hU.fromSpec.preimage_mono hUV)
  have hx : (hU.fromSpec ≫ g) ≫ Z.π = (hU.fromSpec ≫ Z'.π) ≫ τ :=
    (Category.assoc _ _ _).trans ((congrArg (hU.fromSpec ≫ ·) hπ).trans (Category.assoc _ _ _).symm)
  have hm' := isFrame_incl hm
  have hd := exists_dual_basis Z.tMap mu hx h hm' a
  refine hd.elim fun v hv => ⟨U, hU, n, v, hxU, hv.1, hv.2.1, fun k _ φ u hu i hi => ?_⟩
  have hu' : IsTanAtG (Y Z'.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) (u σ i) := by
    exact hu.elim fun _ h₂ => h₂.elim fun _ hf => (hf.2.1.1 σ i).1
  have hw := hv.2.2 k φ ((spMap φ ≫ hU.fromSpec) ≫ g) _ (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _ hu'
  exact hw.elim fun w h₂ => h₂.elim fun hw h₃ => h₃.elim fun h' e =>
    ⟨_, hcl k φ w hw h' ⟨τ, mu, u, i, htr, hu, hi, e.1⟩, e.2⟩

end GlobalTheory.LocM.StepBasis
