import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicQuotientMeasure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

open MeasureTheory NumberField GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
open scoped ENNReal NNReal Pointwise Classical

namespace GlobalTheory.AutQuotCompare

section First

variable {H : Type} [Group H] (Γ : Subgroup H)

abbrev ClassSpace : Type := Quotient (QuotientGroup.rightRel Γ)

abbrev classOf (g : H) : ClassSpace Γ := Quotient.mk _ g

variable [MeasurableSpace H] (P P' : Measure H × Set H → Prop)

def chosenPair : Measure H × Set H := if h : ∃ p, P p then h.choose else Classical.epsilon P'

def chosenQuot : Measure (ClassSpace Γ) :=
  ((chosenPair P P').1.restrict (chosenPair P P').2).map (classOf Γ)

def chosenProb : Measure (ClassSpace Γ) :=
  if chosenQuot Γ P P' Set.univ ≠ 0 ∧ chosenQuot Γ P P' Set.univ ≠ ⊤ then
    (chosenQuot Γ P P' Set.univ)⁻¹ • chosenQuot Γ P P' else Measure.dirac (classOf Γ 1)

theorem measurable_classOf : Measurable (classOf Γ) := fun _ hs => hs

end First

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Haar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

variable {G}

end Adelic

section Transport

variable {H H' : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']
  {Γ : Subgroup H} {Γ' : Subgroup H'} (e : H ≃ₜ* H') (he : ∀ g, e g ∈ Γ' ↔ g ∈ Γ)

include he in
theorem classOf_eq_iff (a b : H) : classOf Γ a = classOf Γ b ↔ cls Γ' (e a) = cls Γ' (e b) := by
  refine (cls_eq_iff Γ a b).trans (Iff.trans ?_ (cls_eq_iff Γ' _ _).symm)
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨e γ, (he γ).2 hγ, map_mul e _ _⟩
  · rintro ⟨γ, hγ, h⟩
    refine ⟨e.symm γ, (he _).1 (by simpa using hγ), e.injective ?_⟩
    rw [map_mul, h]; simp

def quotEquiv : ClassSpace Γ ≃ LQuot Γ' :=
  Quotient.congr e.toEquiv fun a b =>
    Quotient.eq.symm.trans ((classOf_eq_iff e he a b).trans Quotient.eq)

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H']

def quotMeasurableEquiv : ClassSpace Γ ≃ᵐ LQuot Γ' where
  toEquiv := quotEquiv e he
  measurable_toFun := fun _ hs => ((measurable_cls Γ').comp e.continuous.measurable) hs
  measurable_invFun := fun _ hs => ((measurable_classOf Γ).comp e.symm.continuous.measurable) hs

end Transport

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  {Γ : Subgroup H}

def IsHaarPair (Γ : Subgroup H) (p : Measure H × Set H) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain Γ p.2 p.1

example (K : Subgroup (UFin G)) :
    (∀ g, ContinuousMulEquiv.refl (UAd G) g ∈ ratPts G ↔ g ∈ ratPts G) ∧
      ∀ p : Measure (UAd G) × Set (UAd G), IsVolDatum G K p.1 p.2 → IsHaarPair (ratPts G) p :=
  ⟨fun _ => Iff.rfl, fun _ h => ⟨h.1.2.2.1, h.2⟩⟩

end Main

section Split

open scoped Matrix

theorem mem_UJ_iff {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) :
    g ∈ Formalism.UG.UJ s J ↔ g ∈ unitaryOf s Jᵀ := by
  change ((g : Matrix (Fin n) (Fin n) R).map s)ᵀ * J * (g : Matrix (Fin n) (Fin n) R) = J ↔
    (g : Matrix (Fin n) (Fin n) R)ᵀ * Jᵀ * (g : Matrix (Fin n) (Fin n) R).map s = Jᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

variable {R S ι : Type} [CommRing R] [CommRing S] (Φ : R ≃+* (ι → ℂ) × S) {n : ℕ}

def compAt (w : ι) : R →+* ℂ := (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp Φ.toRingHom)

def compLast : R →+* S := (RingHom.snd _ _).comp Φ.toRingHom

def glue (A : ι → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) S) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => Φ.symm (fun w => A w i j, B i j)

theorem glue_at (A : ι → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) S) (w : ι) :
    (glue Φ A B).map (compAt Φ w) = A w := by
  ext i j; simp [glue, compAt]

theorem glue_last (A : ι → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) S) :
    (glue Φ A B).map (compLast Φ) = B := by
  ext i j; simp [glue, compLast]

theorem comp_ext {M N : Matrix (Fin n) (Fin n) R} (h : ∀ w, M.map (compAt Φ w) = N.map (compAt Φ w))
    (h' : M.map (compLast Φ) = N.map (compLast Φ)) : M = N := by
  ext i j
  exact Φ.injective (Prod.ext (funext fun w => congrFun (congrFun (h w) i) j) (congrFun (congrFun h' i) j))

def glueGL (a : ι → GL (Fin n) ℂ) (b : GL (Fin n) S) : GL (Fin n) R where
  val := glue Φ (fun w => (a w).val) b.val
  inv := glue Φ (fun w => (a w).inv) b.inv
  val_inv := comp_ext Φ (fun w => by rw [Matrix.map_mul, glue_at, glue_at, (a w).val_inv]; simp)
    (by rw [Matrix.map_mul, glue_last, glue_last, b.val_inv]; simp)
  inv_val := comp_ext Φ (fun w => by rw [Matrix.map_mul, glue_at, glue_at, (a w).inv_val]; simp)
    (by rw [Matrix.map_mul, glue_last, glue_last, b.inv_val]; simp)

theorem continuous_map {R R' : Type} [CommRing R] [CommRing R'] [TopologicalSpace R] [TopologicalSpace R']
    {φ : R →+* R'} (h : Continuous φ) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map h, Units.continuous_coe_inv.matrix_map h⟩

variable [TopologicalSpace R] [TopologicalSpace S] (hc : Continuous Φ) (hc' : Continuous Φ.symm)
  {s : R →+* R} {s' : S →+* S} (hs : ∀ w z, compAt Φ w (s z) = starRingEnd ℂ (compAt Φ w z))
  (hs' : ∀ z, compLast Φ (s z) = s' (compLast Φ z)) {J : Matrix (Fin n) (Fin n) R}
  {A : ι → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) S}
  (hA : ∀ w, Jᵀ.map (compAt Φ w) = A w) (hB : Jᵀ.map (compLast Φ) = B)

def splitEquiv : Formalism.UG.UJ s J ≃ₜ* (∀ w, unitaryOf (starRingEnd ℂ) (A w)) × unitaryOf s' B where
  toFun g :=
    (fun w => ⟨Matrix.GeneralLinearGroup.map (compAt Φ w) g.1,
      hA w ▸ (unitaryMap s _ _ (hs w) Jᵀ ⟨g.1, (mem_UJ_iff s J _).1 g.2⟩).2⟩,
    ⟨Matrix.GeneralLinearGroup.map (compLast Φ) g.1,
      hB ▸ (unitaryMap s _ _ hs' Jᵀ ⟨g.1, (mem_UJ_iff s J _).1 g.2⟩).2⟩)
  invFun y := ⟨glueGL Φ (fun w => (y.1 w).1) y.2.1, (mem_UJ_iff s J _).2 (by
    refine comp_ext Φ (fun w => ?_) ?_
    · have e : ∀ M : Matrix (Fin n) (Fin n) R,
          (M.map s).map (compAt Φ w) = (M.map (compAt Φ w)).map (starRingEnd ℂ) := fun M => by
        ext i j; exact hs w _
      rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, hA]
      change ((glue Φ _ _).map _)ᵀ * _ * ((glue Φ _ _).map _).map _ = _
      rw [glue_at]
      exact (y.1 w).2
    · have e : ∀ M : Matrix (Fin n) (Fin n) R,
          (M.map s).map (compLast Φ) = (M.map (compLast Φ)).map s' := fun M => by
        ext i j; exact hs' _
      rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, hB]
      change ((glue Φ _ _).map _)ᵀ * _ * ((glue Φ _ _).map _).map _ = _
      rw [glue_last]
      exact y.2.2)⟩
  left_inv g := Subtype.ext (Units.ext (comp_ext Φ (fun w => glue_at Φ _ _ w) (glue_last Φ _ _)))
  right_inv y := Prod.ext (funext fun w => Subtype.ext (Units.ext (glue_at Φ _ _ w)))
    (Subtype.ext (Units.ext (glue_last Φ _ _)))
  map_mul' g h := Prod.ext (funext fun w => Subtype.ext (map_mul _ g.1 h.1)) (Subtype.ext (map_mul _ g.1 h.1))
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun w => Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact (continuous_map ((continuous_apply w).comp (continuous_fst.comp hc))).comp continuous_subtype_val
    · exact (continuous_map (continuous_snd.comp hc)).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk (continuous_pi fun w => ?_) ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp
          ((continuous_apply w).comp continuous_fst))).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk (continuous_pi fun w => ?_) ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp
          ((continuous_apply w).comp continuous_fst))).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j

end Split

section Adeles

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem sigmaCompact_inf (F : Type) [Field F] [NumberField F] [Algebra F E] : SigmaCompactSpace (Ainf F ⊗[F] E) := by
  have : ∀ v : InfinitePlace F, SigmaCompactSpace v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace (Ainf F) := inferInstanceAs (SigmaCompactSpace (∀ v : InfinitePlace F, v.Completion))
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (Ainf F) (Ainf F ⊗[F] E)
  refine ⟨?_⟩
  rw [← hf.range_eq]
  exact isSigmaCompact_range (IsModuleTopology.continuous_of_linearMap f)

theorem exists_inf_equiv : ∃ Θ : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E ≃+* (InfinitePlace E → ℂ),
    Continuous Θ ∧ Continuous Θ.symm ∧ (∀ x w, Θ (1 ⊗ₜ x) w = w.embedding x) ∧
      ∀ z w, Θ (GlobalTheory.AdLat.sg _ (IsCMField.complexConj E) z) w = starRingEnd ℂ (Θ z w) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) inferInstance
    (IsCMField.complexEmbedding_complexConj E)
  choose θ hθ using h1
  obtain ⟨h3, h4, h5⟩ := h2 θ hθ
  have hinj : Function.Injective (fun w : InfinitePlace E => w.embedding) := fun v w h => by
    rw [← v.mk_embedding, ← w.mk_embedding]; exact congrArg _ h
  have hmem : ∀ τ : E →+* ℂ, τ ∈ Set.range (fun w : InfinitePlace E => w.embedding) ↔
      (InfinitePlace.mk τ).embedding = τ := fun τ =>
    ⟨fun ⟨w, hw⟩ => by rw [← hw]; simp only [InfinitePlace.mk_embedding], fun h => ⟨_, h⟩⟩
  have hb := h5 (Set.range fun w : InfinitePlace E => w.embedding) fun τ => by
    have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
    rw [hmem, hmem, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]; simp [hne.symm]
    · rw [h]; simp [hne]
  let f : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* (InfinitePlace E → ℂ) :=
    Pi.ringHom fun w => θ w.embedding
  have hf : Function.Bijective f :=
    (Equiv.arrowCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl ℂ)).bijective.comp hb
  have hfc : Continuous f := continuous_pi fun w => h3 _
  have := sigmaCompact_inf E (maximalRealSubfield E)
  have : IsModuleTopology (Ainf (maximalRealSubfield E))
    (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    IsModuleTopology.isTopologicalRing (Ainf (maximalRealSubfield E)) _
  have ho : IsOpenMap f := f.toAddMonoidHom.isOpenMap_of_sigmaCompact hf.2 hfc
  refine ⟨RingEquiv.ofBijective f hf, hfc, ?_, fun x w => (hθ _).1 x, fun z w => h4 _ z⟩
  exact ((RingEquiv.ofBijective f hf).toEquiv.toHomeomorphOfContinuousOpen hfc ho).symm.continuous

end Adeles

section Groups

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Groups

section Record

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} [IsCMField D.host.E] (V : HSp D)

omit [IsCMField D.host.E]

def PairFirst (p : Measure (GA D V) × Set (GA D V)) : Prop := IsVolPair D V p.1 p.2

def PairSecond (p : Measure (GA D V) × Set (GA D V)) : Prop :=
  ∃ P Q : D.what₂.Tau → ℕ, IsVolMeasG D V P Q p.1 ∧ IsFundamentalDomain (GQ V) p.2 p.1

end Record

end GlobalTheory.AutQuotCompare
