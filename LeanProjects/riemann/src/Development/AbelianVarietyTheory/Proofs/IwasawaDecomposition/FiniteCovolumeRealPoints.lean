import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.CovolTransport

section General

theorem isometry_iff {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (J g : Matrix (Fin M) (Fin M) A) :
    (∀ u w : Fin M → A, ∑ a, ∑ b, (g *ᵥ u) a * J b a * s ((g *ᵥ w) b) = ∑ a, ∑ b, u a * J b a * s (w b)) ↔
      Formalism.UG.cT s g * J * g = J := by
  have h1 : ∀ (K : Matrix (Fin M) (Fin M) A) (u w : Fin M → A),
      ∑ a, ∑ b, u a * K b a * s (w b) = (s ∘ w) ⬝ᵥ (K *ᵥ u) := by
    intro K u w
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∀ u w : Fin M → A, (s ∘ (g *ᵥ w)) ⬝ᵥ (J *ᵥ (g *ᵥ u)) =
      (s ∘ w) ⬝ᵥ ((Formalism.UG.cT s g * J * g) *ᵥ u) := by
    intro u w
    have e : s ∘ (g *ᵥ w) = g.map s *ᵥ (s ∘ w) := by
      funext a; exact RingHom.map_mulVec s g w a
    rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    rfl
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single b 1) (Pi.single a 1)
    have e : s ∘ (Pi.single a 1 : Fin M → A) = Pi.single a 1 := by
      funext k
      by_cases hk : k = a <;> simp [Pi.single_apply, hk]
    rw [e] at this
    simpa using this
  · intro h u w
    rw [h]

variable {S : Type} [CommRing S] {I : Type} {M : ℕ} {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) :
    (Formalism.UG.cT s X).map t = Formalism.UG.cT (starRingEnd ℂ) (X.map t) := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (H : Subgroup (I → GL (Fin M) ℂ))
    (hH : ∀ g, g ∈ H ↔ ∀ i, g i ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map (θ i))) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* H, ∀ h i, (((f h : I → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
      ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  let fw : Formalism.UG.UJ s J → H := fun h => ⟨fun i => Formalism.UG.bc (θ i) h.1, (hH _).2 fun i => by
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    exact h2⟩
  have hfw : ∀ h i, ((fw h).1 i).1 = h.1.1.map (θ i) := fun _ _ => rfl
  let L : H → Matrix (Fin M) (Fin M) S :=
    fun g => Matrix.of fun a b => e.symm fun i => (g.1 i).1 a b
  have hL : ∀ g i, (L g).map (θ i) = (g.1 i).1 := fun g i => by
    ext a b
    simp [L, ← he]
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL]
    rfl
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, hone]
    rfl
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact (hH _).1 g.2 i
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : H => (g.1 i).1 :=
      Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact this.matrix_elem a b
  let bw : H → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => rfl⟩
  · exact Subtype.ext (Units.ext (ext_map he fun i => hL (fw h) i))
  · exact Subtype.ext (funext fun i => Units.ext (hL g i))
  · exact Subtype.ext (funext fun i => map_mul (Formalism.UG.bc (θ i)) h.1 h'.1)
  · refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (hθ i)
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (hθ i)
  · exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _

end General

theorem isCMFam_val {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    IsCMFam (fun τ : Ψ => τ.1) := by
  constructor
  · intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ j.2) ((hΨ _).1 i.2)
  · intro w
    by_cases h : w.embedding ∈ Ψ
    · exact ⟨⟨_, h⟩, w.mk_embedding⟩
    · have h' : ComplexEmbedding.conjugate w.embedding ∈ Ψ := by
        by_contra hn
        exact h ((hΨ _).2 hn)
      exact ⟨⟨_, h'⟩, (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩

theorem finite_covolume_real_points : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  intro hyp F E _ _ _ _ _ σ hcm M J hJ L hL hsp ν hν
  haveI := hcm.1
  haveI := hcm.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [ReciprocityTheory.ChartRestriction.G.FD.emb_cc, hcm.2.2.2]
    rfl
  obtain ⟨Ψ, hΨ, hcov⟩ := hyp E M Jᵀ L (fun a b => by rw [hcc]; exact hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) hL hsp
  choose θ hθ using fun τ : Ψ => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hcm τ.1).exists
  obtain ⟨e, he, hc, hc', hs⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ Ψ _ θ hcm (isCMFam_val Ψ hΨ) hθ
  have hincl : ∀ (X : Matrix (Fin M) (Fin M) E) (τ : Ψ),
      (X.map (inclR (F := F) (Ainf F))).map (θ τ) = X.map τ.1 := fun X τ => by
    ext a b
    exact (hθ τ).1 (X a b)
  let H : Subgroup (Ψ → GL (Fin M) ℂ) :=
    Subgroup.pi Set.univ fun τ => Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1)
  obtain ⟨f, hf⟩ : ∃ f : HA (Ainf F) σ J ≃ₜ* H, ∀ h i,
      (((f h : Ψ → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
        (HA.mat (Ainf F) σ J h : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) :=
    exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs]) (JR (Ainf F) J) H
      fun g => by
        simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const, JR, hincl]
  borelize ↥H
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Ainf F) σ J) :=
    f.toHomeomorph.isInducing.topologicalGroup f
  haveI : (ν.map f).IsHaarMeasure := f.isHaarMeasure_map ν
  obtain ⟨Ω, hΩm, hΩf, hΩ⟩ := hcov H (fun g => by
    simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const]
    exact forall_congr' fun τ => (isometry_iff (starRingEnd ℂ) (J.map τ.1) (g τ).1).symm) (ν.map f)
  have hfm : Measurable f := f.continuous.measurable
  refine ⟨f ⁻¹' Ω, hfm hΩm, by rwa [Measure.map_apply hfm hΩm] at hΩf, fun g => ?_⟩
  obtain ⟨γ, hγ, w, hw, hgw⟩ := hΩ (f g)
  refine ⟨γ, (isometry_iff (σ : E →+* E) J γ.1).1 fun u v => ?_, hγ.2, f.symm w, by simpa using hw, ?_⟩
  · have := hγ.1 u v
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, hcc, Matrix.transpose_apply] at this
    exact this
  · refine Units.ext (ext_map he fun τ => ?_)
    rw [Units.val_mul, Matrix.map_mul, ← hf, ← hf, f.apply_symm_apply, hgw, ← hincl]
    rfl

end GlobalTheory.Mem.CovolTransport
