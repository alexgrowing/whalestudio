import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpDerEigenIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.LieEigenspaceFinrank

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem isLieEigen_iff (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (w : Fin g → ℂ) :
    IsLieEigen act y τ' (expDer he w) ↔ w ∈ eigSp φ τ := by
  rw [mem_eigSp]
  constructor
  · intro h c
    rw [hτ]
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).1 (h.2 c)
  · intro h
    refine ⟨expDer_base he w, fun c => ?_⟩
    exact (expDer_eigen_iff he (φ c) (act.act c) (hM c) (τ' c) w).2 (by rw [← hτ]; exact h c)

theorem comb_iff (he : IsExp y e) {n : ℕ} (w : Fin n → Fin g → ℂ) (c : Fin n → ℂ) (z : Fin g → ℂ) :
    (∃ u : Fin n → (epsPt y ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (expDer he (w i)).left) ∧
      expDer he z = (List.ofFn u).prod) ↔ z = ∑ i, c i • w i := by
  constructor
  · rintro ⟨u, hu, hz⟩
    have hu' : u = fun i => expDer he (c i • w i) := by
      funext i
      exact Over.OverMorphism.ext (by rw [hu i, expDer_smul he])
    rw [hu', expDer_prod he (fun i => c i • w i)] at hz
    exact expDer_injective he hz
  · intro hz
    refine ⟨fun i => expDer he (c i • w i), fun i => expDer_smul he _ _, ?_⟩
    rw [expDer_prod he (fun i => c i • w i), hz]

theorem finrank_eigSp (he : IsExp y e) {F : Type} [Field F] [NumberField F]
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (act : OAct (𝓞 F) G)
    (hM : ∀ c z, e (φ c *ᵥ z) = e z ≫ act.act c) (τ : F →+* ℂ) (τ' : 𝓞 F →+* ℂ)
    (hτ : ∀ c : 𝓞 F, τ (c : F) = τ' c) (n : ℕ) (h : LieMult act y τ' n) :
    Module.finrank ℂ (eigSp φ τ) = n := by
  obtain ⟨v, hv, hb⟩ := h
  choose w hw using fun i => expDer_surj he (v i) (hv i).1
  obtain rfl : v = fun i => expDer he (w i) := funext fun i => (hw i).symm
  have hwm : ∀ i, w i ∈ eigSp φ τ := fun i => (isLieEigen_iff he φ act hM τ τ' hτ _).1 (hv i)
  have key : ∀ z ∈ eigSp φ τ, ∃! c : Fin n → ℂ, z = ∑ i, c i • w i := by
    intro z hz
    have := hb _ ((isLieEigen_iff he φ act hM τ τ' hτ z).2 hz)
    simpa only [comb_iff he w] using this
  let L : (Fin n → ℂ) →ₗ[ℂ] eigSp φ τ := Fintype.linearCombination ℂ (fun i => (⟨w i, hwm i⟩ : eigSp φ τ))
  have hL : ∀ c, (L c : Fin g → ℂ) = ∑ i, c i • w i := by
    intro c
    simp [L, Fintype.linearCombination_apply]
  have hbij : Function.Bijective L := by
    rw [Function.bijective_iff_existsUnique]
    intro z
    obtain ⟨c, hc, hu⟩ := key z.1 z.2
    refine ⟨c, Subtype.ext (by rw [hL]; exact hc.symm), fun c' hc' => hu c' ?_⟩
    exact (congrArg Subtype.val hc').symm.trans (hL c')
  rw [← (LinearEquiv.ofBijective L hbij).finrank_eq]
  simp

theorem lie_type_of_unif (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ))
    (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ))
    (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ (o.fam h hL).A))
    (hU : UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 (Sp ℂ)) e) (τ : Fin D.a → D.F →+* ℂ)
    (hτ : ∀ (i : Fin D.a) (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) :
    (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧
      ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u →
        u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  have he : IsExp (G := o.A) (𝟙 (Sp ℂ)) e := hU.2.2.1
  have hM : ∀ (a : D.O) z, e (ρ a *ᵥ z) = e z ≫ o.act.act a := hU.2.2.2.2.1
  have hx : 𝟙 (Sp ℂ) ≫ spMap σ = spMap σ := Category.id_comp _
  have hM' : ∀ (c : 𝓞 D.F) z, e ((ρ.comp (algebraMap (𝓞 D.F) D.O)) c *ᵥ z) = e z ≫ (o.act.toF D).act c :=
    fun c z => hM _ z
  refine ⟨fun i => ?_, fun u hu => ?_⟩
  · exact finrank_eigSp (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _
      (o.lieRank ℂ (𝟙 _) σ hx i)
  · obtain ⟨v, hv, hprod⟩ := o.lie ℂ σ (𝟙 _) hx (expDer (G := o.A) he u)
      ⟨expDer_base he u, (expDer_eigen_iff (G := o.A) he _ _ (hM _) (σ b.ρ) u).2 hu⟩
    choose w hw using fun i => expDer_surj (G := o.A) he (v i) (hv i 0).1
    obtain rfl : v = fun i => expDer (G := o.A) he (w i) := funext fun i => (hw i).symm
    have hu' : u = ∑ i, w i := expDer_injective he (hprod.trans (expDer_prod he w))
    rw [hu']
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact (isLieEigen_iff (G := o.A) he _ (o.act.toF D) hM' (τ i) (σ.comp (b.t i)) (hτ i) _).1
      ⟨(hv i 0).1, fun c => (hv i c).2⟩

end GlobalTheory.LieEigenspaceFinrank
