import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.exBridge :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) →
        ∃ Bw' : LocBridge l K Ω (Dec (F := K) A) O, Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw hK
  haveI : IsGalois K Ω := {}
  haveI : IsGalois F Ω := {}
  haveI : T2Space (G F Ω) := krullTopology_t2
  let r : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have hr : Continuous r := continuous_restrictScalarsHom F K Ω
  have hinj : Function.Injective r := fun a b h => AlgEquiv.ext fun x => congrArg (fun g : G F Ω => g x) h
  have hind : Topology.IsInducing r := (hr.isClosedEmbedding hinj).isInducing
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ r σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hfix : ∀ (g : ↥(Dec (F := F) A)) (x : K), (g : G F Ω) (algebraMap K Ω x) = algebraMap K Ω x := fun g x => by
    apply Bw.j.injective
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e g).2 _ (hK x)
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    (r.comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun g => ?_⟩
    let σ : G K Ω := AlgEquiv.ofRingEquiv (f := (g : G F Ω).toRingEquiv) (hfix g)
    have hσ : r σ = g := AlgEquiv.ext fun _ => rfl
    exact ⟨⟨σ, (hmem σ).2 (hσ ▸ g.2)⟩, Subtype.ext hσ⟩
  let φ : ↥(Dec (F := K) A) ≃* ↥(Dec (F := F) A) := MulEquiv.ofBijective f hf
  have hφ : Continuous φ := (hr.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := by
    rw [(hind.comp Topology.IsInducing.subtypeVal).continuous_iff]
    exact continuous_subtype_val.congr fun g => (congrArg Subtype.val (φ.apply_symm_apply g)).symm
  refine ⟨{ Kw := Bw.Kw, j := Bw.j, j_E := hK, j_dense := ?_, e := φ.trans Bw.e
            e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
            e_comm := fun g x => Bw.e_comm (φ g) x
            LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
            eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }, rfl, rfl, rfl⟩
  refine Bw.j_dense.trans (closure_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨algebraMap F K x, by simp only [← IsScalarTower.algebraMap_apply]⟩
