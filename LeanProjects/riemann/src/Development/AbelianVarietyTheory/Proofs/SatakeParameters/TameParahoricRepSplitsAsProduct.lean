import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVectStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenformStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirstStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProductStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_eq_on_units {ψ θ : kˣ →* ℂˣ} (hθ : IsSmoothChar θ)
    (h : ∀ u : kˣ, valuation k (u : k) = 1 → ψ u = θ u) : IsSmoothChar ψ := by
  have h1 : IsUnram (ψ * θ⁻¹) := fun u hu => by simp [h u hu]
  have h2 : ψ = (ψ * θ⁻¹) * θ := by ext u; simp
  rw [h2]
  exact (isSmoothChar_of_isUnram h1).mul hθ

theorem exists_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {n : ℕ} (π : Irr k n) {v : π.V} {θ : Fin n → kˣ →* ℂˣ}
    (hθ : ∀ i, IsSmoothChar (θ i)) (hv : v ≠ 0) (h : IsIwVec θ π.π v) :
    ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u) ∧
      (∀ i, InSupport π.π (ψ i)) ∧ IsSubquotient π.π (prinSeries ψ) := by
  have hl : HasFiniteLength (jacB π.π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr))
  obtain ⟨ψ, l, hl0, hψ, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π.π) (Submodule.Quotient.mk v) θ
    (isSmooth_jacB π.smooth) hl hθ (GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero hD k n π v θ hv h) fun t ht => by
      rw [UnramFixed.jacB_apply, jacBU_mk, h.2 t ht]
      have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
        UnramFixed.deltaHalf_torusO k ht
      rw [this]
      simp
  exact ⟨ψ, hu, GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform k n _ π.π ψ l hl0 hψ,
    SatakeExists.isSubquotient_of_eigenform π.smooth π.irr _ l hl0 hψ⟩

theorem hasFiniteLength_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) : HasFiniteLength (prinSeries ψ) := by
  have hs : IsSmoothChar (torusChar ψ) := by
    unfold torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  refine (hBZ k).2.2.1 _ _ _ (points (Fin n)) _ _ ?_ ?_
  · refine isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i => ?_)
    exact continuous_glDet.comp (continuous_apply i)
  · exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).symm.surjective).2
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))

theorem exists_model (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (A : Representation ℂ (GL (Fin n) k) V),
      Nonempty (A.Equiv (prinSeries ψ)) ∧ IsSmooth A ∧ HasFiniteLength A :=
  ⟨_, _, _, prinSeries ψ, ⟨.refl _⟩, isSmooth_parInd _ _, hasFiniteLength_prinSeries hBZ hψ⟩

theorem isCuspSupport_of_prinSeries {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) :
    IsCuspSupport σ.π (fun _ : Fin n => 1) fun a => (Irr.ofDet 1 (ψ a) (hψ a)).π :=
  ⟨σ.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hψ a)⟩, _,
    h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)⟩

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) {μ : kˣ →* ℂˣ}
    (hμ : InSupport σ.π μ) : ∃ i, μ = ψ i := by
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ _ _ μ (isSmooth_parInd _ _)
    (h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)) hμ
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k _ _ _ _ _ _ μ
    (fun a => (Irr.ofDet 1 (ψ a) (hψ a)).smooth) (fun a => isIrreducible_ofChar _) h1
  exact ⟨a, (Model.inSupport_one_iff _ _).1 ha⟩

def twistIrr {n : ℕ} (σ : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := σ.V
  π := twist σ.π (detChar (Fin n) χ)
  smooth := isSmooth_twist σ.smooth hχ.detChar
  irr := by
    have φ : Subrepresentation (twist σ.π (detChar (Fin n) χ)) ≃o Subrepresentation σ.π :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have := S.toSubmodule.smul_mem (((detChar (Fin n) χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
          S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact φ.isSimpleOrder_iff.2 σ.irr

theorem tameSplit : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  intro hBZ hG hU hD k _ _ _ _ r t χ π v hχ htame hram hv hpar
  let θ : Fin (r + t) → kˣ →* ℂˣ := Fin.append (fun _ : Fin r => 1) fun _ : Fin t => χ
  have hθ : ∀ i, IsSmoothChar (θ i) := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [θ] using isSmoothChar_one
    | right i => simpa [θ] using hχ
  obtain ⟨ψ, hψθ, -, hsub⟩ := exists_prinSeries hBZ hD π hθ hv (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ π.π v htame hpar)
  have hψ : ∀ i, IsSmoothChar (ψ i) := fun i => isSmoothChar_of_eq_on_units (hθ i) (hψθ i)
  let ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i)
  let ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i)
  have hψ₁ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₁ i u = 1 := fun i u hu => by
    simpa [θ] using hψθ (Fin.castAdd t i) u hu
  have hψ₂ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₂ i u = χ u := fun i u hu => by
    simpa [θ] using hψθ (Fin.natAdd r i) u hu
  have happ : Fin.append ψ₁ ψ₂ = ψ := Fin.append_castAdd_natAdd
  rw [← happ] at hsub
  obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ : ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π (prinSeries ψ₁) ∧
      IsSubquotient σ₂.π (prinSeries ψ₂) ∧ IsSubquotient π.π (prod₂ σ₁.π σ₂.π) := by
    obtain ⟨V, _, _, A, ⟨φA⟩, sA, lA⟩ := exists_model hBZ (ψ := ψ₁) fun i => hψ _
    obtain ⟨W, _, _, B, ⟨φB⟩, sB, lB⟩ := exists_model hBZ (ψ := ψ₂) fun i => hψ _
    obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ := GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents k r t _ _ _ π.π A B π.irr sA sB lA lB
      (hsub.trans (GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ k r t ψ₁ ψ₂ V W A B ⟨φA⟩ ⟨φB⟩))
    exact ⟨σ₁, σ₂, h₁.trans (.of_injective φA.toIntertwiningMap φA.injective),
      h₂.trans (.of_injective φB.toIntertwiningMap φB.injective), hπ⟩
  have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
    refine hU k r t r t σ₁ σ₂ _ _ _ _ (isCuspSupport_of_prinSeries σ₁ (fun i => hψ _) h₁)
      (isCuspSupport_of_prinSeries σ₂ (fun i => hψ _) h₂) ?_
    rintro a b h α ⟨φ⟩
    refine hram fun u hu => ?_
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar (Fin 1) u
    have hg : Matrix.GeneralLinearGroup.det g = u := ProdSupport.det_scalar_one rfl u
    obtain ⟨c, hc⟩ : ∃ c : ℂ, φ (1 : ℂ) = c := ⟨_, rfl⟩
    have h0 : c ≠ 0 := fun h => one_ne_zero (α := ℂ) (φ.injective ((hc.trans h).trans (map_zero φ).symm))
    have h1 : φ (detRep (Fin 1) (ψ₁ a) g (1 : ℂ)) = (detChar (Fin 1) (unrChar k α) g : ℂ) •
        detRep (Fin 1) (ψ₂ b) g c := hc ▸ φ.toIntertwiningMap.isIntertwining _ _ g (1 : ℂ)
    simp only [detRep, ofChar_apply, detChar_apply, hg, hψ₁ a u hu, hψ₂ b u hu, isUnram_unrChar k α u hu,
      Units.val_one, one_mul, one_smul] at h1
    exact Units.ext ((mul_eq_right₀ h0).1 (h1.symm.trans hc))
  obtain ⟨φ⟩ := hπ.nonempty_equiv π.irr hirr
  let f := φ.symm v
  have hf0 : f ≠ 0 := fun h => hv (φ.symm.injective (h.trans (map_zero φ.symm).symm))
  have hf : IsParahoricVec χ (prod₂ σ₁.π σ₂.π) f := fun h hh hl u hu => by
    have := φ.symm.toIntertwiningMap.isIntertwining _ _ h v
    rw [hpar h hh hl u hu, map_smul] at this
    exact this.symm
  obtain ⟨w, hw⟩ := GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero k r t χ _ _ σ₁.π σ₂.π f hf0 hf
  obtain ⟨s, y, hy0, hy⟩ := GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first k r t θ _ _ σ₁.π σ₂.π f w (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ _ f htame hf) hw
  obtain ⟨μ, hμ, hμs, -⟩ := exists_prinSeries hBZ hD σ₁ (fun i => hθ _) hy0 hy
  have hwP : GlobalTheory.Parabolic.permGL k w ∈ parab k (two (stdSum (rfl : r + t = r + t))) := by
    have key : ∀ (i : Fin r) (j : Fin t), Fin.castAdd t i ≠ w (Fin.natAdd r j) := fun i j hij => by
      obtain ⟨i, rfl⟩ := s.surjective i
      obtain ⟨a, ha⟩ := exists_eq_of_inSupport hG σ₁ (fun i => hψ _) h₁ (hμs i)
      refine hram fun u hu => ?_
      have h1 := hμ i u hu
      rw [ha, hij, Equiv.symm_apply_apply] at h1
      simpa [θ] using h1.symm.trans (hψ₁ a u hu)
    refine (mem_parab_two k).2 fun j i => (GlobalTheory.Parabolic.permGL_apply w _ _).trans (if_neg fun hji => ?_)
    have hF : ∀ b, ∃ c, w (Fin.natAdd r b) = Fin.natAdd r c := fun b => by
      generalize hx : w (Fin.natAdd r b) = x
      induction x using Fin.addCases with
      | left a => exact absurd hx.symm (key a b)
      | right c => exact ⟨c, rfl⟩
    choose c hc using hF
    have hinj : Function.Injective c := fun b b' h =>
      Fin.natAdd_injective _ _ (w.injective (by rw [hc, hc, h]))
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj j
    have h2 : w (Fin.natAdd r b) = w (Fin.castAdd t i) := by rw [hc, hb]; exact hji
    have h3 := congrArg Fin.val (w.injective h2)
    have := i.2
    simp at h3
    omega
  have hf1 : f.1.1 1 ≠ 0 := fun h => hw (by
    have := f.1.2 ⟨_, hwP⟩ 1
    rw [mul_one, h, map_zero] at this
    exact this)
  obtain ⟨s₁, s₂⟩ := GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct k r t χ _ _ σ₁.π σ₂.π f hf hf1
  refine ⟨σ₁, twistIrr σ₂ χ⁻¹ hχ.inv, s₁, s₂, ?_⟩
  have e : twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ) = σ₂.π := by
    ext g x
    simp [smul_smul]
  show Nonempty (π.π.Equiv (prod₂ σ₁.π (twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
  rw [e]
  exact ⟨φ.symm⟩

end GlobalTheory.TameIwahori
