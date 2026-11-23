import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan ev_appLE ev_spMap_tau tau tau_le le_preimage_comp le_preimage_map le_preimage_mono)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.LocM.MapComp GlobalTheory.LocM.CommonMod GlobalTheory.LocM.StepMono

namespace GlobalTheory.GrCl.RowCombination

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_comb {Z₁ Z B : Mdl Y i₀} {g : Z.X ⟶ B.X} (hg : IsMap Z B g) {X' : Scheme.{0}} {f : X' ⟶ Z.X}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y Z.i) (f ≫ Z.π) ty'} {h : Z₁.X ⟶ X'} (hm : MapsTo Z₁ A' h)
    (hf : IsMap Z₁ Z (h ≫ f)) {σ : E →+* ℂ} {r : ℕ} (hr : r ∈ Z₁.ty σ) {K : Type} [Field K] {w : Sp K ⟶ Z₁.X}
    {v : Sp (DualNumber K) ⟶ B.t.G.left} (hs : InStep Z₁ B σ r w v) :
    ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ)
      (u : TVecs Dw (Y Z.i).t (((w ≫ h) ≫ f) ≫ Z.π)) (cf : Fin (Dw.mult σ) → K),
      LocM.IsTrans B.i Z.i τ mu ∧ Set.range ((w ≫ h) ≫ f) ⊆ Z.opn ∧ A'.FlagAt (w ≫ h) (up u) ∧
        (∀ j : Fin (Dw.mult σ), r ≤ (j : ℕ) → cf j = 0) ∧
        v ≫ B.tMap.φ = (tv (∑ j, cf j • u σ j)).left ≫ mu.φ := by
  obtain ⟨τ₁, mu₁, u₁, i, t₁, fu₁, hi, hv⟩ := hs
  have hw := range_subset_opn Z₁ fu₁
  obtain ⟨τ, mu, u, t, e, fu, fu'⟩ := hm K w hw
  have hz : Set.range ((w ≫ h) ≫ f) ⊆ Z.opn := by
    rintro _ ⟨x, rfl⟩
    have := map_mem_opn hf (hw ⟨x, rfl⟩)
    simpa only [Scheme.Hom.comp_apply] using this
  obtain ⟨τ₀, mu₀, -, t₀, -⟩ := hg.2 K _ hz
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have t' := isTrans_comp hg.1.1 hf.1.1 t₀ t mu' hmu'
  obtain ⟨-, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ _ _ mu₁ mu' (hg.1.2.1.trans hf.1.2.1) t₁ t'
  obtain ⟨c, gu, gu₁, hsf⟩ := flagAt_two Z₁ fu fu₁
  obtain ⟨cf, hcf, hc⟩ := hsf σ r hr i hi
  have e' : (w ≫ Z₁.π) ≫ τ = ((w ≫ h) ≫ f) ≫ Z.π := by
    rw [Category.assoc, ← e]; simp only [Category.assoc]
  have hc' := comb_push mu hc
  rw [e'] at hc'
  obtain ⟨U, hU⟩ := exists_up (Dw := Dw) (u := fun σ j => u σ j ≫ mu.φ)
    fun σ j => isTan_push mu _ e' (gu.1 σ j).1
  have hcomb : tanOf (isTan_push mu _ e' (gu₁.1 σ i).1) = ∑ j, cf j • U σ j := by
    refine (isComb_iff (U σ) cf _).1 ?_
    have : (fun j => (tv (U σ j)).left) = fun j => u σ j ≫ mu.φ := congrFun hU σ
    rw [this]
    exact hc'
  obtain ⟨a, φ, ha, -⟩ := fu₁
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z₁ ha
  refine ⟨τ₀, mu₀, U, cf, t₀, hz, hU ▸ fu', hcf, hv.trans ?_⟩
  rw [← hcomb, left_tanOf, hmu K y _ _ _ (by rw [hy]; exact (gu₁.1 σ i).1.1), hmu', Category.assoc]

theorem row_comb {K N : Type} [Field K] [AddCommGroup N] [Module K N] {m n r : ℕ} (hr : r ≤ m) (L : N →ₗ[K] (Fin n → K))
    (a : Fin n → K) (u : Fin m → N) (cf : Fin m → K) (hcf : ∀ j : Fin m, r ≤ (j : ℕ) → cf j = 0)
    (ha : ∀ l : Fin r, ∑ i, a i * L (u (Fin.castLE hr l)) i = 0) : ∑ i, a i * L (∑ j, cf j • u j) i = 0 := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ (j : ℕ)
  · simp [hcf j hj]
  · have := ha ⟨j, by omega⟩
    simp only [mul_left_comm _ (cf j), ← Finset.mul_sum]
    exact mul_eq_zero_of_right _ this

theorem holds_of_planar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ t Z g D hg hL A X' f q ty' A' _ hG hP Z₁ h hm hf hk
  refine ⟨hk, (h ≫ f) ≫ g, isMap_comp hf hg, fun x => ?_⟩
  obtain ⟨U, -, α, a, hx, hUα, H₁⟩ := hP (h x)
  obtain ⟨V, m, hαV, hfr, H₂⟩ := hL α
  obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ := Z₁.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((h ⁻¹ᵁ U : Z₁.X.Opens) : Set Z₁.X) from hx) (h ⁻¹ᵁ U).2
  have e : U' ≤ h ⁻¹ᵁ U := hle
  refine ⟨U', hU', V, _, m, Matrix.GeneralLinearGroup.map (h.appLE U U' e).hom a, hx',
    fun y hy => hαV (hUα (e hy)), hfr, fun K _ φ v hv hh hs j hj => ?_⟩
  have h₀ : ⊤ ≤ (spMap φ ≫ tau hU') ⁻¹ᵁ U' := le_preimage_comp _ (tau_le hU' le_rfl)
  have eφ := ev_spMap_tau hU' φ h₀
  change IsTanAtG t.B.t ((spMap φ ≫ tau hU') ≫ _) v at hv
  change InStep Z₁ t.B t.σ t.k (spMap φ ≫ tau hU') v at hs
  change ⊤ ≤ ((spMap φ ≫ tau hU') ≫ _) ⁻¹ᵁ V at hh
  change ∑ l, φ ((h.appLE U U' e).hom (a j l)) * tanEv t.B.t hv hh _ = 0
  generalize spMap φ ≫ tau hU' = w at h₀ eφ hv hs hh
  subst eφ
  have h₁ : ⊤ ≤ (w ≫ h) ⁻¹ᵁ U := le_preimage_map h e h₀
  have h₂ : ⊤ ≤ ((w ≫ h) ≫ f) ⁻¹ᵁ D.C.B α := le_preimage_map f hUα h₁
  obtain ⟨τ, mu, u, cf, tr, hz, fu, hcf, hvv⟩ := exists_comb hg hm hf hk hs
  have eq : w ≫ (h ≫ f) ≫ g = ((w ≫ h) ≫ f) ≫ g := by simp only [Category.assoc]
  obtain ⟨hv', hh', he⟩ := tanEv_congr t.B.t eq hv hh
  have key := row_comb t.le (D.crd α K _ h₂) (fun i => ev (w ≫ h) U h₁ (a j i)) (u t.σ) cf hcf
    fun l => H₁ K _ h₁ h₂ _ (((hG K _ u).1 fu).2 α h₂) l j hj
  refine (Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ev_appLE w h e h₀ h₁ _) ?_).trans key
  exact (he _).trans (H₂ τ mu tr K _ h₂ hz _ v hv' hh' hvv l).symm

end GlobalTheory.GrCl.RowCombination
