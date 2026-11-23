import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Glue

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R']
    (φ : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) k =
      φ ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def coH {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem continuous_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun y : R ⊗[F] E => (Algebra.TensorProduct.basis R b).repr y k :=
  (continuous_apply k).comp (coH R b).continuous

theorem continuous_map {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Continuous fun y : R ⊗[F] E => Algebra.TensorProduct.map φ (AlgHom.id F E) y := by
  rw [← (coH R' b).comp_continuous_iff]
  refine continuous_pi fun k => ?_
  have : (fun y : R ⊗[F] E => ((coH R' b) ∘ fun y : R ⊗[F] E =>
      Algebra.TensorProduct.map φ (AlgHom.id F E) y) y k) =
      fun y => φ ((Algebra.TensorProduct.basis R b).repr y k) := by
    funext y
    exact repr_map φ b y k
  rw [this]
  exact hφ.comp (continuous_repr R b k)

end Coord

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def pV (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)

theorem continuous_pV (v : HeightOneSpectrum (𝓞 F)) : Continuous (pV (F := F) v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_inf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      fstA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) :=
  repr_map (fstA F) b (X a i) k

theorem crd_v (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) := by
  have h1 := repr_map (evalV F v) b (projFin X a i) k
  have h2 := repr_map (sndA F) b (X a i) k
  refine h1.trans ?_
  exact congrArg (evalV F v) h2

include b in

theorem tuple_ext (X Y : Fin n → Fin M → AF F ⊗[F] E) (hinf : projInf X = projInf Y)
    (hv : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  refine (Algebra.TensorProduct.basis (AF F) b).ext_elem fun k => ?_
  refine Prod.ext ?_ ?_
  · have := crd_inf b X a i k
    rw [hinf, crd_inf b Y a i k] at this
    exact this.symm
  · refine Subtype.ext (funext fun v => ?_)
    have := crd_v b v X a i k
    rw [hv v, crd_v b v Y a i k] at this
    exact this.symm

theorem eventually_lat (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
  have h : ∀ (a : Fin n) (i : Fin M) (k : Fin d), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k ∈
        v.adicCompletionIntegers F := by
    intro a i k
    have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) ∈
          v.adicCompletionIntegers F :=
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    exact h0.mono fun v hv => by rwa [crd_v]
  have h' := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 (h a i)
  exact h'

theorem exists_glue (Xinf : Fin n → Fin M → Ainf F ⊗[F] E)
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E)
    (h : ∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) :
    ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v := by
  let cf : Fin n → Fin M → Fin d → Af F := fun a i k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Xv v a i) k, h.mono fun v hv => hv a i k⟩
  let c : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Xinf a i) k) (cf a i k)
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i => (coH (AF F) b).symm (c a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = c a i k := fun a i k =>
    congrFun ((coH (AF F) b).apply_symm_apply (c a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    rw [crd_inf, hX]
    rfl
  · funext a i
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    rw [crd_v, hX]
    rfl

theorem isCompact_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in Filter.cofinite, D v ⊆ (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v ⊆ (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[Filter.principal S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[Filter.principal S] → ∀ v, R v) '' K = Set.pi Set.univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (Set.mem_univ v), rfl⟩
        rw [Filter.eventually_principal]
        intro v hv
        exact hv (hg v (Set.mem_univ v))
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [Filter.eventually_principal]
      intro v hv
      exact hv (hx v)
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

theorem isCompact_glue (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hinf : IsCompact Cinf) (hv : ∀ v, IsCompact (Cv v))
    (hlat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) :
    IsCompact {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  haveI : T2Space (Ainf F ⊗[F] E) := (coH (Ainf F) b).isEmbedding.t2Space
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v ⊗[F] E) := fun v =>
    (coH (Fv F v) b).isEmbedding.t2Space

  let DI : Fin n → Fin M → Fin d → Set (Ainf F) := fun a i k =>
    (fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k) '' Cinf
  have hDI : ∀ a i k, IsCompact (DI a i k) := fun a i k =>
    hinf.image ((continuous_repr (Ainf F) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  let DV : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun a i k v =>
    (fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Y a i) k) '' Cv v
  have hDV : ∀ a i k v, IsCompact (DV a i k v) := fun a i k v =>
    (hv v).image ((continuous_repr (Fv F v) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  have hB : ∀ a i k, IsCompact {x : Af F | ∀ v, x v ∈ DV a i k v} := fun a i k =>
    isCompact_box (hDV a i k) (hlat.mono fun v hsub => by
      rintro _ ⟨Y, hY, rfl⟩
      exact hsub hY a i k)

  let Q : Fin n → Fin M → Fin d → Set (AF F) := fun a i k =>
    (DI a i k) ×ˢ {x : Af F | ∀ v, x v ∈ DV a i k v}
  have hQ : ∀ a i k, IsCompact (Q a i k) := fun a i k => (hDI a i k).prod (hB a i k)
  let L : Set (Fin n → Fin M → Fin d → AF F) :=
    Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k => Q a i k
  have hL : IsCompact L :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun i => isCompact_univ_pi fun k => hQ a i k
  let g : (Fin n → Fin M → Fin d → AF F) → Fin n → Fin M → AF F ⊗[F] E :=
    fun c a i => (coH (AF F) b).symm (c a i)
  have hg : Continuous g := continuous_pi fun a => continuous_pi fun i =>
    (coH (AF F) b).symm.continuous.comp ((continuous_apply i).comp (continuous_apply a))
  have hcl : IsClosed {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
    have c1 : Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
      continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (fstA F) continuous_fstA b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have c2 : ∀ v : HeightOneSpectrum (𝓞 F), Continuous
        (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
      have e : (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) =
          fun X a i => Algebra.TensorProduct.map (pV v) (AlgHom.id F E) (X a i) := by
        funext X a i
        refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
        rw [crd_v]
        exact (repr_map (pV v) b (X a i) k).symm
      rw [e]
      exact continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (pV v) (continuous_pV v) b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have e : {X : Fin n → Fin M → AF F ⊗[F] E |
        projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} =
        projInf ⁻¹' Cinf ∩ ⋂ v, (fun X => projV v (projFin X)) ⁻¹' Cv v := by
      ext X
      simp
    rw [e]
    exact (hinf.isClosed.preimage c1).inter
      (isClosed_iInter fun v => (hv v).isClosed.preimage (c2 v))
  refine (hL.image hg).of_isClosed_subset hcl ?_
  rintro X ⟨h1, h2⟩
  refine ⟨fun a i k => (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k, ?_, ?_⟩
  · intro a _ i _ k _
    refine ⟨⟨projInf X, h1, crd_inf b X a i k⟩, fun v => ⟨_, h2 v, crd_v b v X a i k⟩⟩
  · funext a i
    exact (coH (AF F) b).symm_apply_apply (X a i)

end Adelic

theorem glue_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨tuple_ext b, eventually_lat b, exists_glue b, isCompact_glue b⟩

end GlobalTheory.CompanionTheory.SW.Glue
