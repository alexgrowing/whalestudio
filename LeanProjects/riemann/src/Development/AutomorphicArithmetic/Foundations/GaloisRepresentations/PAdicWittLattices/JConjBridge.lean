import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual
universe u v

theorem UpperTheory.Gal.G3.jConjBridge :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.ConjBridge := by
  intro E Ω _ _ _ _ _ l _ Gw O iR iA iT Bw τ LL' τ' hτ
  haveI := Bw.Kw.2
  haveI := LL'.2
  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) :=
    fun x => τo.liftNormal_commutes (Om l) x
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hcont : Continuous (fun x : Om l => g x) := (GlobalTheory.Cyc.Model.isom_gal g).continuous
  let c : ↥(GK Bw.Kw) ≃* ↥(GK K₁) :=
    { toFun := fun h => ⟨g * (h : GQ l) * g⁻¹, GlobalTheory.Pst.BridgeInd.mem_GK_conj hK h.2⟩
      invFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  have c_cont : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have c_symm_cont : Continuous c.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let Bw' : LocBridge l E Ω Gw O :=
    { Kw := K₁
      j := (g : Om l →+* Om l).comp Bw.j
      j_E := fun x => (hK _).1 (Bw.j_E x)
      j_dense := by
        intro y hy
        have h1 : g⁻¹ y ∈ Bw.Kw.1 := (hK _).2 (by simpa using hy)
        have h2 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem _ (Bw.j_dense h1))
        have h3 : g (g⁻¹ y) = y := g.apply_symm_apply y
        simp only [h3] at h2
        refine closure_mono ?_ h2
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      e := Bw.e.trans c
      e_cont := c_cont.comp Bw.e_cont
      e_symm_cont := Bw.e_symm_cont.comp c_symm_cont
      e_comm := fun h x => by
        have h1 : g⁻¹ (g (Bw.j x)) = Bw.j x := g.symm_apply_apply _
        have h2 := Bw.e_comm h x
        change g (((Bw.e h : ↥(GK Bw.Kw)) : GQ l) (g⁻¹ (g (Bw.j x)))) = g (Bw.j ((h : Ω ≃ₐ[E] Ω) x))
        rw [h1, h2]
      LL := Bw.LL
      LL_split := fun σ x => by
        have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
        let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
          ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
        have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (g.apply_symm_apply _)
        rw [← he]
        exact Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩
      eO := Bw.eO
      eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont
      eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨g, O, iR, iA, iT, Bw', ⟨fun x => rfl, fun h => rfl⟩, ?_⟩
  refine RingHom.ext fun x => ?_
  exact (hg ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩).trans (hτ x).symm
