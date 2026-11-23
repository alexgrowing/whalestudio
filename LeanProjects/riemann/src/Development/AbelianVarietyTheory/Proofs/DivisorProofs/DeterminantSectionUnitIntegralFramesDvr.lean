import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenBasisSameVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.DvrUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] {β' : O' →+* c.F}
  {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ext (Z : Model Xo c β) (U : Set (Xo.XF c)) (j : c.F →+* R) (x : Sp K ⟶ Xo.XF c)
    (h1 : x ≫ toF Xo c = spMap ((algebraMap R K).comp j)) (hU : Set.range x ⊆ U) :
    ∃ χ : Sp R ⟶ gen Z, χ ≫ genStr Z = spMap j ∧ x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ ∧
      Set.range χ ⊆ compactOf Z U := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h2, h3⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap j) (x ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp]
    exact h1)
  refine ⟨χ, h3, h2.symm, ?_⟩
  rintro _ ⟨p, rfl⟩
  let g0 : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hg : χ (spMap (algebraMap R K) g0) ∈ Z.jQ '' U := by
    rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]
    exact ⟨_, hU ⟨g0, rfl⟩, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap R K) g0} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap R K) (⊥ : Ideal K) ≤ (p : PrimeSpectrum R).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hg)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem exists_ident (Z : Model Xo c β) {χ : Sp R ⟶ gen Z} {x : Sp K ⟶ Xo.XF c}
    (hχ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)) {t : SAB H (Sp R)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap R K))) (mF : SABMap tK Z.oF.t x),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) x
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) x Z.m mF
  have hj : x ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap R K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap R K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem exists_lift_vec {Z : Model Xo c β} {Y : Model Xo c β'} {χ : Sp R ⟶ gen Z} {χ' : Sp R ⟶ gen Y}
    {x : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)} {t t' : SAB H (Sp R)}
    {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Y.t (χ' ≫ genι Y)} {ψ : SABMap t t' (𝟙 (Sp R))}
    {a : SABMap tK t (spMap (algebraMap R K))} {a' : SABMap tK t' (spMap (algebraMap R K))}
    {mF : SABMap tK Z.oF.t x} {mF' : SABMap tK Y.oF.t x}
    (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Y.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Y.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _)
    (w' : epsAt x ⟶ Y.oF.t.G)
    (hw3 : w'.left ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : epsAt x ⟶ Z.oF.t.G, w.left ≫ Z.m0.toSABMap.φ = w'.left ≫ Y.m0.toSABMap.φ ∧
      w.left ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
  rw [Category.comp_id] at hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Sp (DualNumber K) ⟶ Y.oF.t.G.left, w₀ = w'.left := ⟨_, rfl⟩
  have hw1 : w₀ ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := hw₀ ▸ Over.w w'
  have hw3' : w₀ ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ := hw₀ ▸ hw3
  obtain ⟨u, e1, hu1⟩ : ∃ u : Sp (DualNumber K) ⟶ tK.G.left, u ≫ mF'.φ = w₀ ∧
      u ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) :=
    ⟨mF'.cart.1.lift _ _ hw1, mF'.cart.1.lift_fst _ _ _, mF'.cart.1.lift_snd _ _ _⟩
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap R K) =
      spMap (Chart.dualMapR (algebraMap R K)) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp]
    congr 1
    ext z <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : u ≫ a.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3']
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  have k1 : (u ≫ mF.φ) ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := by
    rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  have k2 : (u ≫ mF.φ) ≫ Z.m0.toSABMap.φ = w₀ ≫ Y.m0.toSABMap.φ := by
    rw [Category.assoc, hF0, ← e1, Category.assoc, hF0']
  have k3 : (u ≫ mF.φ) ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
    rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]
  subst hw₀
  exact ⟨Over.homMk (u ≫ mF.φ) k1, k2, k3⟩

theorem exists_move (Y : Model Xo c β') (Z : Model Xo c β) {xR : Sp R ⟶ gen Y} {xZ : Sp R ⟶ gen Z}
    {x : Sp K ⟶ Xo.XF c} (hY : x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR) (hZ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ xZ)
    (χ : 𝓞 E →+* R) {n : ℕ} (vR : Fin n → (epsAt (xR ≫ genι Y) ⟶ Y.t.G))
    (hvR : IsEigBasisAt Y.t.act (xR ≫ genι Y) χ vR) {v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} (hs : SameVecs Y x v vb)
    (hb : ∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) :
    ∃ vZ : Fin n → (epsAt (xZ ≫ genι Z) ⟶ Z.t.G), IsEigBasisAt Z.t.act (xZ ≫ genι Z) χ vZ ∧
      ∀ vK : Fin n → (epsAt ((x ≫ Z.jQ) ≫ genι Z) ⟶ Z.t.G),
        (∀ i, (vK i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vZ i).left) → SameVecs Z x v vK := by
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (x ≫ toX Xo c) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xZ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xR ≫ genι Y) Y.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_ident Z hZ mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_ident Y hY mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map R K t t' tK a a'
  obtain ⟨e, he, hbe⟩ := BdryUnit.exists_eigEquiv m.cart m.act (𝟙 _) (xZ ≫ genι Z) (Category.id_comp _).symm
  obtain ⟨e', he', hbe'⟩ := BdryUnit.exists_eigEquiv m'.cart m'.act (𝟙 _) (xR ≫ genι Y) (Category.id_comp _).symm
  obtain ⟨f, hf, hbf⟩ := BdryUnit.exists_eigEquiv ψ.cart ψ.act (𝟙 _) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : Fin n → _, vR = fun i => e' (f (v₀ i)) :=
    ⟨fun i => f.symm (e'.symm (vR i)), funext fun i => by simp⟩
  refine ⟨fun i => e (v₀ i), (hbe χ n v₀).1 ((hbf χ n v₀).2 ((hbe' χ n fun i => f (v₀ i)).2 hvR)), fun vK hK i => ?_⟩
  obtain ⟨w', h1, h2⟩ := hs i
  have h3 := h2.trans (hb i)
  rw [he', hf] at h3
  obtain ⟨w, h4, h5⟩ := exists_lift_vec hψ hF0 hFm hF0' hFm' (Over.w (v₀ i)) w' h3
  refine ⟨w, h4.trans h1, h5.trans ?_⟩
  rw [hK i, he]

theorem unit_in_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hsec hnz hres R K _ _ _ _ _ _ j xR x V vR wR v w vb wb
    hR hU hx hv hw ev ew
  obtain ⟨xZ, h1, h2, h3⟩ := exists_ext Z U j x hU.1 hU.2.1
  obtain ⟨vZ, hvZ, sv⟩ := exists_move Y Z hx h2 _ vR hR.2.2.1 hv ev
  obtain ⟨wZ, hwZ, sw⟩ := exists_move Y Z hx h2 _ wR hR.2.2.2 hw ew
  have hZ : FrY Z (compactOf Z U) τ j xZ vZ wZ := ⟨h1, h3, hvZ, hwZ⟩
  obtain ⟨vK, wK, hK, a, b⟩ := exists_pull (algebraMap R K) hZ h2
  obtain ⟨u, hu⟩ := hnz R j xZ vZ wZ hZ
  refine ⟨u, ?_⟩
  rw [← hres K _ x v w vK wK hU hK (sv vK a) (sw wK b), hu]
  exact hsec.1 R K (algebraMap R K) (Chart.dualMapR (algebraMap R K)) j _ xZ _ vZ wZ vK wK
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) hZ hK h2 a b

end GlobalTheory.DetLine.DvrUnit
