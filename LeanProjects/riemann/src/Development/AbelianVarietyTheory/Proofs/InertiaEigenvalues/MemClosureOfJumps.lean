import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadicStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.HodgeTateCochar

theorem poly_vanish : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL K'' : FinExt l) (m : ℕ) (r₁ : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    LL.1 ≤ K''.1 → K.1 ≤ K''.1 → ∀ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      (r₁ g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) *
        (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) =
      (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) *
        Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]))) →
    ∀ f : MvPolynomial (Fin m × Fin m) ℂ_[l],
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K'' →
      MvPolynomial.eval (fun ij => ((((r₁ g : Matrix (Fin m) (Fin m) ↥LL.1) ij.1 ij.2 : ↥LL.1) : Om l) : ℂ_[l])) f = 0) →
    ∀ t : ℂ_[l], t ≠ 0 →
      MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) *
        ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) : Matrix (Fin m) (Fin m) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT K LL K'' m r₁ hLL hK Pm k heig f hf t ht
  letI act : MulSemiringAction ↥(GK K'') ℂ_[l] :=
    { smul := fun g x => Per.σC (g : GQ l) x
      one_smul := fun x => GlobalTheory.RingBasics.σC_one x
      mul_smul := fun g h x => GlobalTheory.RingBasics.σC_mul (g : GQ l) (h : GQ l) x
      smul_zero := fun g => map_zero (Per.σC (g : GQ l))
      smul_add := fun g x y => map_add (Per.σC (g : GQ l)) x y
      smul_one := fun g => map_one (Per.σC (g : GQ l))
      smul_mul := fun g x y => map_mul (Per.σC (g : GQ l)) x y }
  let χ : ↥(GK K'') →* ℂ_[l]ˣ :=
    ((Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom).comp (P.χQ.comp (GK K'').subtype))⁻¹
  have hχ : ∀ (g : ↥(GK K'')) (n : ℤ), ((χ g ^ n : ℂ_[l]ˣ) : ℂ_[l]) =
      ((((P.χQ (g : GQ l)) ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
    intro g n
    have e : χ g ^ n = Units.map (algebraMap ℚ_[l] ℂ_[l]).toMonoidHom (P.χQ (g : GQ l) ^ (-n)) := by
      rw [map_zpow]
      simp [χ, zpow_neg, inv_zpow']
    rw [e]
    rfl
  let φ : ↥LL.1 →+* ℂ_[l] := (UniformSpace.Completion.coeRingHom).comp (algebraMap ↥LL.1 (Om l))
  let ρ : ↥(GK K'') →* Matrix.GeneralLinearGroup (Fin m) ℂ_[l] :=
    (mapRep φ r₁).comp (Subgroup.inclusion (GK_le hK))
  have hρ : ∀ (γ : ↥(GK K'')) i j, (ρ γ : Matrix (Fin m) (Fin m) ℂ_[l]) i j =
      ((((r₁ (Subgroup.inclusion (GK_le hK) γ) : Matrix (Fin m) (Fin m) ↥LL.1) i j : ↥LL.1) : Om l) : ℂ_[l]) :=
    fun _ _ _ => rfl
  have key := GlobalTheory.T.vanish_at_hodgeTate_cocharacter (C := ℂ_[l]) (Γ := ↥(GK K'')) (n := Fin m) χ ?_ ρ ?_ Pm k ?_ f ?_ (Units.mk0 t ht)
  · simpa [Units.val_zpow_eq_zpow_val] using key
  · intro n hn x H
    refine GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (-n) (neg_ne_zero.mpr hn) x fun g => ?_
    exact (H g).trans (by rw [hχ])
  · intro g γ i j
    change Per.σC (g : GQ l) _ = _
    rw [hρ, GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (hLL (r₁ _ i j).2)
  · intro g
    have h1 := heig (Subgroup.inclusion (GK_le hK) g) g.2
    change (ρ g : Matrix (Fin m) (Fin m) ℂ_[l]) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = _
    simp only [hχ]
    exact h1
  · intro γ
    exact hf _ γ.2

theorem mem_closure_of_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin a) (Om l)) (τ : E →+* Om l) (J : Multiset ℤ), GlobalTheory.Pst.IsJumpsAt P Bw r τ J → Multiset.card J = a → ∃ (Pm : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) (k : Fin a → ℤ), Multiset.map k Finset.univ.val = J ∧ ∀ (K' : FinExt l), Bw.Kw.1 ≤ K'.1 → ∀ f : MvPolynomial (Fin a × Fin a) ℂ_[l], (∀ g : ↥Gw, ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' → MvPolynomial.eval (fun ij => (((r g : Matrix (Fin a) (Fin a) (Om l)) ij.1 ij.2 : Om l) : ℂ_[l])) f = 0) → ∀ t : ℂ_[l], t ≠ 0 → MvPolynomial.eval (fun ij => ((Pm : Matrix (Fin a) (Fin a) ℂ_[l]) * Matrix.diagonal (fun i => t ^ k i) * ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin a) ℂ_[l]) : Matrix (Fin a) (Fin a) ℂ_[l])) ij.1 ij.2) f = 0 := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r τ J hJ hcard
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', -, hcnt⟩ := hJ
  haveI := Bw.Kw.2
  haveI := LL'.2

  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) := fun x => τo.liftNormal_commutes (Om l) x

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    have := hg ⟨x, hx⟩
    simp only at this
    change g x ∈ LL'.1
    rw [this]; exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₀ : ↥(GK Bw.Kw) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r'.comp Bw.e.symm.toMonoidHom
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin a) ↥LL'.1 := r₀.comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = g * h * g⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin a → ↥LL'.1) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * a := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change g (g⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' a r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  refine ⟨Pm, k, ?_, ?_⟩
  · refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this
  intro K' hK' f hf t ht
  haveI := K'.2
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : FinExt l, K₂.1 = K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨K'.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap K'.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K₂.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₂
  haveI := K₂.2
  let K'' : FinExt l := ⟨K₂.1 ⊔ K₀.1, inferInstance⟩
  refine poly_vanish l P AI hT K₁ LL' K'' a r₁ (le_trans le_sup_right le_sup_right)
    (le_trans le_sup_left le_sup_right) Pm k (fun h hh => heig h (GK_le le_sup_right hh)) f ?_ t ht
  intro h hh
  have h2 : (h : GQ l) ∈ GK K₂ := GK_le le_sup_left hh
  have h3 : ((cj h : ↥(GK Bw.Kw)) : GQ l) ∈ GK K' := GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK' h2
  have h4 := hf (Bw.e.symm (cj h)) (by simpa using h3)
  rw [← hmod] at h4
  exact h4

end GlobalTheory.HodgeTateCochar
