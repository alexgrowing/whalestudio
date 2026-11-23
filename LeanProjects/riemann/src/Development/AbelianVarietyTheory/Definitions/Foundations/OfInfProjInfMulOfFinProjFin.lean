import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapU mapH extH diagH)
open GlobalTheory.AutFunCompare (HA_ext mapH_extH_self mapH_extH_zero continuous_mapH continuous_extH evW sgW sgW_mul)

section Inst

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

instance borelSpace_HA : BorelSpace (HA R σ J) := ⟨rfl⟩

instance isTopologicalGroup_HA [IsTopologicalRing R] [FiniteDimensional F E] : IsTopologicalGroup (HA R σ J) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  inferInstanceAs (IsTopologicalGroup (HR R σ J))

def matHom : HA R σ J →* GL (Fin n) (R ⊗[F] E) := (HR R σ J).subtype

omit [TopologicalSpace R] in
theorem matHom_apply (g : HA R σ J) : matHom R σ J g = HA.mat R σ J g := rfl

omit [TopologicalSpace R] in
theorem matHom_injective : Function.Injective (matHom R σ J) := Subtype.val_injective

theorem isEmbedding_matHom : Topology.IsEmbedding (matHom R σ J) := Topology.IsEmbedding.subtypeVal

end Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

abbrev GAd : Type := HA (AF F) σ J

abbrev GFin : Type := HA (Af F) σ J

abbrev GInf : Type := HA (Ainf F) σ J

abbrev GLoc (v : HeightOneSpectrum (𝓞 F)) : Type := HA (Fv F v) σ J

abbrev GArch (w : InfinitePlace F) : Type := HA w.Completion σ J

abbrev GRat : Type := UJ (σ : E →+* E) J

section LCSC

open GlobalTheory.AdelicUnitaryTop

theorem lcsc_GFin : LocallyCompactSpace (GFin σ J) ∧ SecondCountableTopology (GFin σ J) ∧ T2Space (GFin σ J) :=
  haveI := locallyCompact_finiteAdele F
  haveI := secondCountable_finiteAdele F
  haveI := t2Space_finiteAdeleRing_of_numberField F
  lcsc_HA (Af F) σ n J

theorem lcsc_GInf : LocallyCompactSpace (GInf σ J) ∧ SecondCountableTopology (GInf σ J) ∧ T2Space (GInf σ J) :=
  haveI := secondCountable_infiniteAdele F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  lcsc_HA (Ainf F) σ n J

theorem lcsc_GLoc (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (GLoc σ J v) ∧ SecondCountableTopology (GLoc σ J v) ∧ T2Space (GLoc σ J v) :=
  haveI := properSpace_adicCompletion F v
  lcsc_HA (Fv F v) σ n J

theorem lcsc_GArch (w : InfinitePlace F) :
    LocallyCompactSpace (GArch σ J w) ∧ SecondCountableTopology (GArch σ J w) ∧ T2Space (GArch σ J w) :=
  haveI : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  lcsc_HA w.Completion σ n J

instance : LocallyCompactSpace (GAd σ J) := (lcsc_adelicUnitary F E σ n J).1
instance : SecondCountableTopology (GAd σ J) := (lcsc_adelicUnitary F E σ n J).2.1
instance : T2Space (GAd σ J) := (lcsc_adelicUnitary F E σ n J).2.2
instance : LocallyCompactSpace (GFin σ J) := (lcsc_GFin σ J).1
instance : SecondCountableTopology (GFin σ J) := (lcsc_GFin σ J).2.1
instance : T2Space (GFin σ J) := (lcsc_GFin σ J).2.2
instance : LocallyCompactSpace (GInf σ J) := (lcsc_GInf σ J).1
instance : SecondCountableTopology (GInf σ J) := (lcsc_GInf σ J).2.1
instance : T2Space (GInf σ J) := (lcsc_GInf σ J).2.2
instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (GLoc σ J v) := (lcsc_GLoc σ J v).1
instance (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (GLoc σ J v) := (lcsc_GLoc σ J v).2.1
instance (v : HeightOneSpectrum (𝓞 F)) : T2Space (GLoc σ J v) := (lcsc_GLoc σ J v).2.2
instance (w : InfinitePlace F) : LocallyCompactSpace (GArch σ J w) := (lcsc_GArch σ J w).1
instance (w : InfinitePlace F) : SecondCountableTopology (GArch σ J w) := (lcsc_GArch σ J w).2.1
instance (w : InfinitePlace F) : T2Space (GArch σ J w) := (lcsc_GArch σ J w).2.2

end LCSC

omit [NumberField F] [NumberField E] in
theorem mapH_mapH {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (g : HA R σ J) :
    mapH σ J ψ (mapH σ J φ g) = mapH σ J (ψ.comp φ) g :=
  HA_ext σ J fun r s => by
    simp only [GlobalTheory.AutFunCompare.mat_mapH]
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

theorem af_ext {a b : Af F}
    (h : ∀ u, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u b) : a = b := Subtype.ext (funext h)

open Classical in
theorem evalV_singleV (v u : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleV F v y) = (Pi.single v y : ∀ t : HeightOneSpectrum (𝓞 F), Fv F t) u := rfl

open Classical in

def singleFin (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' a b := Subtype.ext (Pi.single_add v a b)
  map_smul' c a := af_ext fun u => by
    simp only [map_smul, evalV_singleV, Pi.single_smul, Pi.smul_apply, RingHom.id_apply]

theorem singleFin_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    singleFin v (a * b) = singleFin v a * singleFin v b := by
  classical
  exact Subtype.ext (Pi.single_mul v a b)

theorem evalV_singleFin_self (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin v a) = a := by
  classical
  exact Pi.single_eq_same v a

theorem evalV_singleFin_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (a : Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v a) = 0 := by
  classical
  exact Pi.single_eq_of_ne h a

theorem continuous_singleFin (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleFin v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : Fv F v → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

def projFin : GAd σ J →* GFin σ J := mapH σ J (sndA F)

def projInf : GAd σ J →* GInf σ J := mapH σ J (fstA F)

def projFinLoc (v : HeightOneSpectrum (𝓞 F)) : GFin σ J →* GLoc σ J v := mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

def projInfArch (w : InfinitePlace F) : GInf σ J →* GArch σ J w := mapH σ J (evW w)

def proj (v : HeightOneSpectrum (𝓞 F)) : GAd σ J →* GLoc σ J v := mapH σ J (evFin F v)

def projArch (w : InfinitePlace F) : GAd σ J →* GArch σ J w := mapH σ J (evInf F w)

def ofFin : GFin σ J →* GAd σ J :=
  extH (R' := AF F) σ J (LinearMap.inr F (Ainf F) (Af F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)

def ofInf : GInf σ J →* GAd σ J :=
  extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)

def embLocFin (v : HeightOneSpectrum (𝓞 F)) : GLoc σ J v →* GFin σ J := extH σ J (singleFin v) (singleFin_mul v)

def embArchInf (w : InfinitePlace F) : GArch σ J w →* GInf σ J := extH σ J (sgW w) (sgW_mul w)

def emb (v : HeightOneSpectrum (𝓞 F)) : GLoc σ J v →* GAd σ J := (ofFin σ J).comp (embLocFin σ J v)

def embArch (w : InfinitePlace F) : GArch σ J w →* GAd σ J := (ofInf σ J).comp (embArchInf σ J w)

def ratEmb : GRat σ J →* GAd σ J := diagH σ J (AF F)

def ratLoc (v : HeightOneSpectrum (𝓞 F)) : GRat σ J →* GLoc σ J v := diagH σ J (Fv F v)

def ratArch (w : InfinitePlace F) : GRat σ J →* GArch σ J w := diagH σ J w.Completion

section Lemmas

omit [NumberField E]

theorem matHom_proj (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) :
    matHom _ σ J (proj σ J v g) = bc (compFin F E v) (matHom _ σ J g) := rfl

theorem matHom_projArch (w : InfinitePlace F) (g : GAd σ J) :
    matHom _ σ J (projArch σ J w g) = bc (compInf F E w) (matHom _ σ J g) := rfl

@[simp] theorem projFinLoc_projFin (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) :
    projFinLoc σ J v (projFin σ J g) = proj σ J v g := mapH_mapH σ J _ _ g

@[simp] theorem projInfArch_projInf (w : InfinitePlace F) (g : GAd σ J) :
    projInfArch σ J w (projInf σ J g) = projArch σ J w g := mapH_mapH σ J _ _ g

@[simp] theorem projFin_ofFin (y : GFin σ J) : projFin σ J (ofFin σ J y) = y :=
  mapH_extH_self _ _ _ _ _ (fun _ => rfl) y
@[simp] theorem projInf_ofFin (y : GFin σ J) : projInf σ J (ofFin σ J y) = 1 :=
  mapH_extH_zero _ _ _ _ _ (fun _ => rfl) y
@[simp] theorem projInf_ofInf (y : GInf σ J) : projInf σ J (ofInf σ J y) = y :=
  mapH_extH_self _ _ _ _ _ (fun _ => rfl) y
@[simp] theorem projFin_ofInf (y : GInf σ J) : projFin σ J (ofInf σ J y) = 1 :=
  mapH_extH_zero _ _ _ _ _ (fun _ => rfl) y

@[simp] theorem projFinLoc_embLocFin_self (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    projFinLoc σ J v (embLocFin σ J v x) = x := mapH_extH_self _ _ _ _ _ (evalV_singleFin_self v) x
theorem projFinLoc_embLocFin_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : GLoc σ J v) :
    projFinLoc σ J u (embLocFin σ J v x) = 1 := mapH_extH_zero _ _ _ _ _ (evalV_singleFin_ne h) x
@[simp] theorem projInfArch_embArchInf_self (w : InfinitePlace F) (x : GArch σ J w) :
    projInfArch σ J w (embArchInf σ J w x) = x := by
  classical
  exact mapH_extH_self _ _ _ _ _ (fun a => Pi.single_eq_same w a) x
theorem projInfArch_embArchInf_ne {w u : InfinitePlace F} (h : u ≠ w) (x : GArch σ J w) :
    projInfArch σ J u (embArchInf σ J w x) = 1 := by
  classical
  exact mapH_extH_zero _ _ _ _ _ (fun a => Pi.single_eq_of_ne h a) x

@[simp] theorem proj_ofFin (v : HeightOneSpectrum (𝓞 F)) (y : GFin σ J) :
    proj σ J v (ofFin σ J y) = projFinLoc σ J v y := by rw [← projFinLoc_projFin, projFin_ofFin]
@[simp] theorem proj_ofInf (v : HeightOneSpectrum (𝓞 F)) (y : GInf σ J) : proj σ J v (ofInf σ J y) = 1 := by
  rw [← projFinLoc_projFin, projFin_ofInf, map_one]
@[simp] theorem projArch_ofInf (w : InfinitePlace F) (y : GInf σ J) :
    projArch σ J w (ofInf σ J y) = projInfArch σ J w y := by rw [← projInfArch_projInf, projInf_ofInf]
@[simp] theorem projArch_ofFin (w : InfinitePlace F) (y : GFin σ J) : projArch σ J w (ofFin σ J y) = 1 := by
  rw [← projInfArch_projInf, projInf_ofFin, map_one]

@[simp] theorem proj_emb_self (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) : proj σ J v (emb σ J v x) = x := by
  simp [emb]
theorem proj_emb_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : GLoc σ J v) : proj σ J u (emb σ J v x) = 1 := by
  simp [emb, projFinLoc_embLocFin_ne σ J h]
@[simp] theorem projArch_emb (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    projArch σ J w (emb σ J v x) = 1 := by simp [emb]
@[simp] theorem projInf_emb (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) : projInf σ J (emb σ J v x) = 1 := by
  simp [emb]
@[simp] theorem projArch_embArch_self (w : InfinitePlace F) (x : GArch σ J w) :
    projArch σ J w (embArch σ J w x) = x := by simp [embArch]
theorem projArch_embArch_ne {w u : InfinitePlace F} (h : u ≠ w) (x : GArch σ J w) :
    projArch σ J u (embArch σ J w x) = 1 := by simp [embArch, projInfArch_embArchInf_ne σ J h]
@[simp] theorem proj_embArch (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (x : GArch σ J w) :
    proj σ J v (embArch σ J w x) = 1 := by simp [embArch]
@[simp] theorem projFin_embArch (w : InfinitePlace F) (x : GArch σ J w) : projFin σ J (embArch σ J w x) = 1 := by
  simp [embArch]

theorem emb_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (emb σ J v) :=
  Function.LeftInverse.injective (proj_emb_self σ J v)

@[simp] theorem proj_ratEmb (v : HeightOneSpectrum (𝓞 F)) (γ : GRat σ J) :
    proj σ J v (ratEmb σ J γ) = ratLoc σ J v γ :=
  HA_ext σ J fun r s => by
    change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
      (1 : Fv F v) ⊗ₜ[F] (γ.1.1 r s)
    simp

@[simp] theorem projArch_ratEmb (w : InfinitePlace F) (γ : GRat σ J) :
    projArch σ J w (ratEmb σ J γ) = ratArch σ J w γ :=
  HA_ext σ J fun r s => by
    change Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
      (1 : w.Completion) ⊗ₜ[F] (γ.1.1 r s)
    simp

theorem ext_inf_fin {g h : GAd σ J} (h1 : projInf σ J g = projInf σ J h) (h2 : projFin σ J g = projFin σ J h) :
    g = h := by
  rw [← mul_inv_eq_one]
  have a : projInf σ J (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have b : projFin σ J (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  exact Subtype.ext (Units.ext (GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) _
    (congrArg (fun x => (HA.mat _ _ _ x).1) a) (congrArg (fun x => (HA.mat _ _ _ x).1) b)))

theorem GFin_ext {g h : GFin σ J} (e : ∀ v, projFinLoc σ J v g = projFinLoc σ J v h) : g = h :=
  HA_ext σ J fun r s => GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
    congrArg (fun x => (HA.mat _ _ _ x).1 r s) (e v)

theorem GInf_ext {g h : GInf σ J} (e : ∀ w, projInfArch σ J w g = projInfArch σ J w h) : g = h :=
  HA_ext σ J fun r s => GlobalTheory.AutFunCompare.infTens_ext fun w => congrArg (fun x => (HA.mat _ _ _ x).1 r s) (e w)

theorem GAd_ext {g h : GAd σ J} (h1 : ∀ w, projArch σ J w g = projArch σ J w h)
    (h2 : ∀ v, proj σ J v g = proj σ J v h) : g = h :=
  ext_inf_fin σ J (GInf_ext σ J fun w => by simp [h1 w]) (GFin_ext σ J fun v => by simp [h2 v])

theorem ofInf_projInf_mul_ofFin_projFin (g : GAd σ J) :
    ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) = g := ext_inf_fin σ J (by simp) (by simp)

theorem commute_ofInf_ofFin (x : GInf σ J) (y : GFin σ J) : Commute (ofInf σ J x) (ofFin σ J y) :=
  ext_inf_fin σ J (by simp) (by simp)

theorem commute_emb {v : HeightOneSpectrum (𝓞 F)} (x : GLoc σ J v) {g : GAd σ J} (hg : proj σ J v g = 1) :
    Commute (emb σ J v x) g :=
  GAd_ext σ J (fun w => by simp) fun u => by
    by_cases h : u = v
    · subst h; simp [hg]
    · simp [proj_emb_ne σ J h]

theorem commute_embArch {w : InfinitePlace F} (x : GArch σ J w) {g : GAd σ J} (hg : projArch σ J w g = 1) :
    Commute (embArch σ J w x) g :=
  GAd_ext σ J (fun u => by
    by_cases h : u = w
    · subst h; simp [hg]
    · simp [projArch_embArch_ne σ J h]) fun v => by simp

theorem ratEmb_injective : Function.Injective (ratEmb σ J) := fun a b h =>
  haveI : Nontrivial (AF F) := ⟨⟨0, 1, fun e => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact zero_ne_one ((map_zero (evInf F w)).symm.trans ((congrArg (evInf F w) e).trans (map_one _)))⟩⟩
  Subtype.ext (Units.ext (Matrix.ext fun r s => (inclR (F := F) (E := E) (AF F)).injective
    (congrArg (fun x => (HA.mat _ _ _ x).1 r s) h)))

end Lemmas

section Cont

theorem continuous_projFin : Continuous (projFin σ J) := continuous_mapH _ _ _ continuous_snd
theorem continuous_projInf : Continuous (projInf σ J) := continuous_mapH _ _ _ continuous_fst
theorem continuous_projFinLoc (v : HeightOneSpectrum (𝓞 F)) : Continuous (projFinLoc σ J v) :=
  continuous_mapH _ _ _ (RestrictedProduct.continuous_eval v)
theorem continuous_projInfArch (w : InfinitePlace F) : Continuous (projInfArch σ J w) :=
  continuous_mapH _ _ _ (continuous_apply w)
theorem continuous_proj (v : HeightOneSpectrum (𝓞 F)) : Continuous (proj σ J v) :=
  continuous_mapH _ _ _ ((RestrictedProduct.continuous_eval v).comp continuous_snd)
theorem continuous_projArch (w : InfinitePlace F) : Continuous (projArch σ J w) :=
  continuous_mapH _ _ _ ((continuous_apply w).comp continuous_fst)
theorem continuous_ofFin : Continuous (ofFin σ J) := continuous_extH _ _ _ _ (continuous_const.prodMk continuous_id)
theorem continuous_ofInf : Continuous (ofInf σ J) := continuous_extH _ _ _ _ (continuous_id.prodMk continuous_const)
theorem continuous_embLocFin (v : HeightOneSpectrum (𝓞 F)) : Continuous (embLocFin σ J v) :=
  continuous_extH _ _ _ _ (continuous_singleFin v)
theorem continuous_embArchInf (w : InfinitePlace F) : Continuous (embArchInf σ J w) := by
  classical
  exact continuous_extH _ _ _ _ (continuous_single w)
theorem continuous_emb (v : HeightOneSpectrum (𝓞 F)) : Continuous (emb σ J v) :=
  (continuous_ofFin σ J).comp (continuous_embLocFin σ J v)
theorem continuous_embArch (w : InfinitePlace F) : Continuous (embArch σ J w) :=
  (continuous_ofInf σ J).comp (continuous_embArchInf σ J w)

theorem isClosedEmbedding_emb (v : HeightOneSpectrum (𝓞 F)) : Topology.IsClosedEmbedding (emb σ J v) :=
  Function.LeftInverse.isClosedEmbedding (proj_emb_self σ J v) (continuous_proj σ J v) (continuous_emb σ J v)

def infFinEquiv : GAd σ J ≃ₜ* GInf σ J × GFin σ J where
  toFun g := (projInf σ J g, projFin σ J g)
  invFun p := ofInf σ J p.1 * ofFin σ J p.2
  left_inv := ofInf_projInf_mul_ofFin_projFin σ J
  right_inv p := by simp
  map_mul' g h := by simp
  continuous_toFun := (continuous_projInf σ J).prodMk (continuous_projFin σ J)
  continuous_invFun :=
    ((continuous_ofInf σ J).comp continuous_fst).mul ((continuous_ofFin σ J).comp continuous_snd)

end Cont

section Subgroups

omit [NumberField E]

def ratPts : Subgroup (GAd σ J) := HFinIn (AF F) σ J

def finPts : Subgroup (GAd σ J) :=
  ((bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom).comp (matHom (AF F) σ J)).ker

def infPts : Subgroup (GAd σ J) :=
  ((bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom).comp (matHom (AF F) σ J)).ker

def awayPts (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GAd σ J) := ⨅ v ∈ S, (proj σ J v).ker

def finAwayPts (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GAd σ J) := finPts σ J ⊓ awayPts σ J S

def atPts (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GAd σ J) :=
  finPts σ J ⊓ ⨅ v, ⨅ (_ : v ∉ S), (proj σ J v).ker

variable {σ J}

theorem mem_finPts {g : GAd σ J} : g ∈ finPts σ J ↔ projInf σ J g = 1 :=
  ⟨fun h => Subtype.ext h, fun h => congrArg (matHom _ σ J) h⟩

theorem mem_infPts {g : GAd σ J} : g ∈ infPts σ J ↔ projFin σ J g = 1 :=
  ⟨fun h => Subtype.ext h, fun h => congrArg (matHom _ σ J) h⟩

theorem mem_finPts_iff_forall {g : GAd σ J} : g ∈ finPts σ J ↔ ∀ w, projArch σ J w g = 1 :=
  mem_finPts.trans ⟨fun h w => by rw [← projInfArch_projInf, h, map_one],
    fun h => GInf_ext σ J fun w => by simp [h w]⟩

theorem mem_infPts_iff_forall {g : GAd σ J} : g ∈ infPts σ J ↔ ∀ v, proj σ J v g = 1 :=
  mem_infPts.trans ⟨fun h v => by rw [← projFinLoc_projFin, h, map_one],
    fun h => GFin_ext σ J fun v => by simp [h v]⟩

theorem mem_awayPts {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} :
    g ∈ awayPts σ J S ↔ ∀ v ∈ S, proj σ J v g = 1 := by simp [awayPts, Subgroup.mem_iInf]

theorem mem_finAwayPts {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} :
    g ∈ finAwayPts σ J S ↔ g ∈ finPts σ J ∧ ∀ v ∈ S, proj σ J v g = 1 := by
  rw [finAwayPts, Subgroup.mem_inf, mem_awayPts]

theorem mem_atPts {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} :
    g ∈ atPts σ J S ↔ g ∈ finPts σ J ∧ ∀ v ∉ S, proj σ J v g = 1 := by simp [atPts, Subgroup.mem_iInf]

variable (σ J)

theorem range_ratEmb : (ratEmb σ J).range = ratPts σ J := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, γ.2, rfl⟩
  · rintro ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩

theorem range_ofFin : (ofFin σ J).range = finPts σ J := by
  ext g
  rw [mem_finPts]
  exact ⟨by rintro ⟨y, rfl⟩; simp, fun h => ⟨projFin σ J g, ext_inf_fin σ J (by simp [h]) (by simp)⟩⟩

theorem range_ofInf : (ofInf σ J).range = infPts σ J := by
  ext g
  rw [mem_infPts]
  exact ⟨by rintro ⟨y, rfl⟩; simp, fun h => ⟨projInf σ J g, ext_inf_fin σ J (by simp) (by simp [h])⟩⟩

@[simp] theorem awayPts_empty : awayPts σ J ∅ = ⊤ := by simp [awayPts]

def projAt (S : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* ∀ v : S, GLoc σ J v :=
  Pi.monoidHom fun v => proj σ J v

@[simp] theorem projAt_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (v : S) :
    projAt σ J S g v = proj σ J v g := rfl

def embAt (S : Finset (HeightOneSpectrum (𝓞 F))) : (∀ v : S, GLoc σ J v) →* GAd σ J :=
  MonoidHom.noncommPiCoprod (fun v : S => emb σ J v) fun _ _ h x y =>
    commute_emb σ J x (proj_emb_ne σ J (fun e => h (Subtype.ext e)) y)

theorem embAt_mulSingle (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidableEq S] (v : S) (y : GLoc σ J v) :
    embAt σ J S (Pi.mulSingle v y) = emb σ J v y :=
  MonoidHom.noncommPiCoprod_mulSingle (fun v : S => emb σ J v) v y

@[simp] theorem projAt_embAt (S : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ v : S, GLoc σ J v) :
    projAt σ J S (embAt σ J S x) = x := by
  classical
  have : (projAt σ J S).comp (embAt σ J S) = MonoidHom.id _ := MonoidHom.pi_ext fun v y => by
    funext u
    rw [MonoidHom.comp_apply, embAt_mulSingle, projAt_apply, MonoidHom.id_apply]
    by_cases h : u = v
    · subst h; simp
    · rw [proj_emb_ne σ J fun e => h (Subtype.ext e), Pi.mulSingle_eq_of_ne h]
  exact DFunLike.congr_fun this x

@[simp] theorem proj_embAt (S : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ v : S, GLoc σ J v) (v : S) :
    proj σ J v (embAt σ J S x) = x v := congrFun (projAt_embAt σ J S x) v

theorem embAt_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ v : S, GLoc σ J v) : embAt σ J S x ∈ atPts σ J S := by
  refine Subgroup.noncommProd_mem _ (f := fun v : S => emb σ J v (x v))
    (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => mem_atPts.2 ⟨mem_finPts.2 (by simp), fun u hu => ?_⟩
  exact proj_emb_ne σ J (fun e : u = v.1 => hu (e ▸ v.2)) _

theorem range_embAt (S : Finset (HeightOneSpectrum (𝓞 F))) : (embAt σ J S).range = atPts σ J S := by
  refine le_antisymm (by rintro _ ⟨x, rfl⟩; exact embAt_mem σ J S x) fun g hg => ⟨projAt σ J S g, ?_⟩
  have h := mem_atPts.1 (embAt_mem σ J S (projAt σ J S g))
  have h' := mem_atPts.1 hg
  refine GAd_ext σ J (fun w => ?_) fun v => ?_
  · rw [mem_finPts_iff_forall.1 h.1 w, mem_finPts_iff_forall.1 h'.1 w]
  · by_cases hv : v ∈ S
    · exact proj_embAt σ J S _ ⟨v, hv⟩
    · rw [h.2 v hv, h'.2 v hv]

theorem range_emb (v : HeightOneSpectrum (𝓞 F)) : (emb σ J v).range = atPts σ J {v} := by
  ext g
  rw [mem_atPts]
  refine ⟨?_, fun h => ⟨proj σ J v g, GAd_ext σ J (fun w => ?_) fun u => ?_⟩⟩
  · rintro ⟨x, rfl⟩
    exact ⟨mem_finPts.2 (by simp), fun u hu => proj_emb_ne σ J (by simpa using hu) x⟩
  · rw [projArch_emb, mem_finPts_iff_forall.1 h.1 w]
  · by_cases hu : u = v
    · subst hu; simp
    · rw [proj_emb_ne σ J hu, h.2 u (by simpa using hu)]

theorem commute_atPts_awayPts {S : Finset (HeightOneSpectrum (𝓞 F))} {x y : GAd σ J} (hx : x ∈ atPts σ J S)
    (hy : y ∈ awayPts σ J S) : Commute x y :=
  GAd_ext σ J (fun w => by simp [mem_finPts_iff_forall.1 (mem_atPts.1 hx).1 w]) fun v => by
    by_cases hv : v ∈ S
    · simp [mem_awayPts.1 hy v hv]
    · simp [(mem_atPts.1 hx).2 v hv]

def partAway (S : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) : awayPts σ J S :=
  ⟨(embAt σ J S (projAt σ J S g))⁻¹ * g, mem_awayPts.2 fun v hv => by
    rw [map_mul, map_inv, proj_embAt σ J S _ ⟨v, hv⟩, projAt_apply, inv_mul_cancel]⟩

theorem embAt_mul_partAway (S : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) :
    embAt σ J S (projAt σ J S g) * partAway σ J S g = g := mul_inv_cancel_left _ _

def atAwayEquiv (S : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J ≃* (∀ v : S, GLoc σ J v) × awayPts σ J S :=
  MulEquiv.symm (MulEquiv.ofBijective
    (MonoidHom.noncommCoprod (embAt σ J S) (awayPts σ J S).subtype fun x y =>
      commute_atPts_awayPts σ J (embAt_mem σ J S x) y.2)
    ⟨(injective_iff_map_eq_one _).2 fun p hp => by
      have hp' : embAt σ J S p.1 * p.2.1 = 1 := hp
      have h1 : p.1 = 1 := funext fun v => by
        have := congrArg (proj σ J v) hp'
        rwa [map_mul, proj_embAt, mem_awayPts.1 p.2.2 v v.2, mul_one, map_one] at this
      rw [h1, map_one, one_mul] at hp'
      exact Prod.ext h1 (Subtype.ext hp'),
    fun g => ⟨(projAt σ J S g, partAway σ J S g), embAt_mul_partAway σ J S g⟩⟩)

theorem atAwayEquiv_symm_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (p : (∀ v : S, GLoc σ J v) × awayPts σ J S) :
    (atAwayEquiv σ J S).symm p = embAt σ J S p.1 * p.2 := rfl

theorem atAwayEquiv_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) :
    atAwayEquiv σ J S g = (projAt σ J S g, partAway σ J S g) :=
  (atAwayEquiv σ J S).symm.injective (by
    rw [MulEquiv.symm_apply_apply]; exact (embAt_mul_partAway σ J S g).symm)

def embArchPi : (∀ w, GArch σ J w) →* GInf σ J :=
  MonoidHom.noncommPiCoprod (fun w => embArchInf σ J w) fun u w h x y => GInf_ext σ J fun t => by
    by_cases ht : t = u
    · subst ht; simp [projInfArch_embArchInf_ne σ J h]
    · simp [projInfArch_embArchInf_ne σ J ht]

theorem embArchPi_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (y : GArch σ J w) :
    embArchPi σ J (Pi.mulSingle w y) = embArchInf σ J w y :=
  MonoidHom.noncommPiCoprod_mulSingle (fun w => embArchInf σ J w) w y

@[simp] theorem projInfArch_embArchPi (x : ∀ w, GArch σ J w) (w : InfinitePlace F) :
    projInfArch σ J w (embArchPi σ J x) = x w := by
  classical
  have : (projInfArch σ J w).comp (embArchPi σ J) = Pi.evalMonoidHom _ w := MonoidHom.pi_ext fun u y => by
    rw [MonoidHom.comp_apply, embArchPi_mulSingle, Pi.evalMonoidHom_apply]
    by_cases h : w = u
    · subst h; simp
    · rw [projInfArch_embArchInf_ne σ J h, Pi.mulSingle_eq_of_ne h]
  exact DFunLike.congr_fun this x

def infEquivPi : GInf σ J ≃* ∀ w, GArch σ J w where
  toFun g w := projInfArch σ J w g
  invFun := embArchPi σ J
  left_inv g := GInf_ext σ J fun w => by simp
  right_inv x := funext fun w => by simp
  map_mul' g h := funext fun w => by simp

end Subgroups

section ContProd

theorem continuous_noncommProd {ι X M : Type} [TopologicalSpace X] [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    (f : ι → X → M) (hf : ∀ i, Continuous (f i)) (comm : ∀ x, Pairwise fun i j => Commute (f i x) (f j x))
    (s : Finset ι) : Continuous fun x => s.noncommProd (fun i => f i x) fun _ _ _ _ h => comm x h := by
  classical
  induction s using Finset.induction_on with
  | empty => exact continuous_const
  | insert i s hi ih =>
    exact ((hf i).mul ih).congr fun x => (Finset.noncommProd_insert_of_notMem s i (fun i => f i x) _ hi).symm

theorem continuous_projAt (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (projAt σ J S) :=
  continuous_pi fun v => continuous_proj σ J v

theorem continuous_embAt (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (embAt σ J S) :=
  continuous_noncommProd (fun (v : S) (x : ∀ v : S, GLoc σ J v) => emb σ J v (x v))
    (fun v => (continuous_emb σ J v).comp (continuous_apply v))
    (fun _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) Finset.univ

theorem continuous_partAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (partAway σ J S) :=
  (((continuous_embAt σ J S).comp (continuous_projAt σ J S)).inv.mul continuous_id).subtype_mk _

def atAwayContEquiv (S : Finset (HeightOneSpectrum (𝓞 F))) :
    GAd σ J ≃ₜ* (∀ v : S, GLoc σ J v) × awayPts σ J S :=
  { atAwayEquiv σ J S with
    continuous_toFun := ((continuous_projAt σ J S).prodMk (continuous_partAway σ J S)).congr fun g =>
      (atAwayEquiv_apply σ J S g).symm
    continuous_invFun := ((continuous_embAt σ J S).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd) }

theorem continuous_embArchPi : Continuous (embArchPi σ J) :=
  continuous_noncommProd (fun w (x : ∀ w, GArch σ J w) => embArchInf σ J w (x w))
    (fun w => (continuous_embArchInf σ J w).comp (continuous_apply w))
    (fun _ u w h => GInf_ext σ J fun t => by
      by_cases ht : t = u
      · subst ht; simp [projInfArch_embArchInf_ne σ J h]
      · simp [projInfArch_embArchInf_ne σ J ht]) Finset.univ

def infContEquivPi : GInf σ J ≃ₜ* ∀ w, GArch σ J w :=
  { infEquivPi σ J with
    continuous_toFun := continuous_pi fun w => continuous_projInfArch σ J w
    continuous_invFun := continuous_embArchPi σ J }

theorem isClosed_finPts : IsClosed (finPts σ J : Set (GAd σ J)) := by
  have : (finPts σ J : Set (GAd σ J)) = projInf σ J ⁻¹' {1} := Set.ext fun _ => mem_finPts
  rw [this]; exact isClosed_singleton.preimage (continuous_projInf σ J)

theorem isClosed_infPts : IsClosed (infPts σ J : Set (GAd σ J)) := by
  have : (infPts σ J : Set (GAd σ J)) = projFin σ J ⁻¹' {1} := Set.ext fun _ => mem_infPts
  rw [this]; exact isClosed_singleton.preimage (continuous_projFin σ J)

theorem isClosed_awayPts (S : Finset (HeightOneSpectrum (𝓞 F))) : IsClosed (awayPts σ J S : Set (GAd σ J)) := by
  have : (awayPts σ J S : Set (GAd σ J)) = ⋂ v ∈ S, proj σ J v ⁻¹' {1} := Set.ext fun _ => by simp [mem_awayPts]
  rw [this]; exact isClosed_biInter fun v _ => isClosed_singleton.preimage (continuous_proj σ J v)

end ContProd

section Arch

variable {σ} {w : InfinitePlace F}

theorem infEmb_sigR (h : IsCMExt F E σ) (τ : EmbOver E w) (y : w.Completion ⊗[F] E) :
    starRingEnd ℂ (infEmb τ y) = infEmb τ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    have := h.1
    have h2 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a
    have h3 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, infEmb_tmul, infEmb_tmul, map_mul, h.2.2.2 τ.1 e, ← h2, Complex.conj_ofReal]
    rfl

theorem infEmb_bijective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Bijective (infEmb τ) := by
  have := h.1
  have := h.2.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  let e : w.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hr
  have he : ∀ a, InfinitePlace.Completion.extensionEmbedding w a = ((e a : ℝ) : ℂ) :=
    fun a => (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr a).symm
  obtain ⟨x, hx⟩ : ∃ x : E, (τ.1 x).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2
        (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (hcon x))))
  have hsurj : Function.Surjective (infEmb τ) := by
    intro z
    refine ⟨e.symm (z.re - z.im / (τ.1 x).im * (τ.1 x).re) ⊗ₜ[F] 1 + e.symm (z.im / (τ.1 x).im) ⊗ₜ[F] x, ?_⟩
    rw [map_add, infEmb_tmul, infEmb_tmul, he, he, e.apply_symm_apply, e.apply_symm_apply, map_one]
    apply Complex.ext
    · simp only [mul_one, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [mul_one, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  have hC : Module.finrank w.Completion ℂ = 2 := by
    rw [← Complex.finrank_real_complex]
    exact Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl ℂ) (by ext a; exact (he a).symm)
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by rw [hC]; norm_num)
  let L : w.Completion ⊗[F] E →ₗ[w.Completion] ℂ :=
    { toFun := infEmb τ
      map_add' := map_add _
      map_smul' := by
        intro c y
        have : c • y = (c ⊗ₜ[F] (1 : E)) * y := by
          rw [Algebra.smul_def]; rfl
        rw [this, map_mul, infEmb_tmul, map_one, mul_one]; rfl }
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange, h.2.2.1, hC])).2 hsurj
  exact ⟨hinj, hsurj⟩

def archMap (h : IsCMExt F E σ) (τ : EmbOver E w) : GArch σ J w →* UJ (starRingEnd ℂ) (J.map τ.1) :=
  mapU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (starRingEnd ℂ) (infEmb τ) (infEmb_sigR h τ) (JR _ J) (J.map τ.1)
    (by ext r s; simp [JR, inclR])

def archEquiv (h : IsCMExt F E σ) (τ : EmbOver E w) : GArch σ J w ≃* UJ (starRingEnd ℂ) (J.map τ.1) :=
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  { archMap J h τ with
    invFun := mapU (starRingEnd ℂ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) e.symm.toRingHom
      (fun z => e.injective <| ((infEmb_sigR h τ (e.symm z)).symm.trans
        (congrArg _ (e.apply_symm_apply z))).trans (e.apply_symm_apply _).symm)
      (J.map τ.1) (JR _ J) (by
        ext r s
        apply e.injective
        change e (e.symm _) = infEmb τ ((1 : w.Completion) ⊗ₜ[F] J r s)
        rw [RingEquiv.apply_symm_apply]
        simp)
    left_inv := fun g => HA_ext σ J fun r s => e.symm_apply_apply _
    right_inv := fun g => Subtype.ext (Units.ext (Matrix.ext fun r s => e.apply_symm_apply _)) }

theorem archEquiv_val (h : IsCMExt F E σ) (τ : EmbOver E w) (g : GArch σ J w) :
    (archEquiv J h τ g).1.1 = (matHom _ σ J g).1.map (infEmb τ) := rfl

def infProj (τ : EmbOver E w) : Ainf F ⊗[F] E →+* ℂ :=
  (infEmb τ).comp (Algebra.TensorProduct.map (evW w) (AlgHom.id F E)).toRingHom

omit [NumberField E] in
theorem isInfEmb_infProj (τ : EmbOver E w) : Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (infProj τ) := by
  refine ⟨fun x => ?_, ?_⟩
  · change infEmb τ ((1 : w.Completion) ⊗ₜ[F] x) = _
    simp
  · have : (fun a : Ainf F => infProj τ (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      change infEmb τ (a w ⊗ₜ[F] (1 : E)) = _
      simp
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _)

theorem infMat_infProj (h : IsCMExt F E σ) (τ : EmbOver E w) (g : GAd σ J) :
    Formalism.MainNotions.StandardLattice.infMat σ J (infProj τ) g = (archEquiv J h τ (projArch σ J w g)).1.1 := by
  rw [← projInfArch_projInf]; rfl

end Arch

end GlobalTheory.AdelicU

end
