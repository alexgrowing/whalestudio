import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {m n : ℕ}

theorem JR_blkMat (J : Matrix (Fin m) (Fin m) E) (J' : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (blkMat finSumFinEquiv J J') = blkMat finSumFinEquiv (JR R J) (JR R J') := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR
  exact blkMat_map _ _ (map_zero _) _ _

theorem JR_dblGram (J : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (dblGram finSumFinEquiv J) = dblGram finSumFinEquiv (JR R J) := by
  unfold dblGram Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR
  rw [blkMat_map _ _ (map_zero _)]
  congr 1
  ext i j
  simp

def sumH {J : Matrix (Fin m) (Fin m) E} {J' : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (m + n)) (Fin (m + n)) E}
    (h : Q = blkMat finSumFinEquiv J J') : HA R σ J × HA R σ J' →* HA R σ Q :=
  sumU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) finSumFinEquiv (J := JR R J) (J' := JR R J') (Q := JR R Q) (h ▸ JR_blkMat R J J')

variable {J : Matrix (Fin n) (Fin n) E} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)

variable {Q} in

def ioH (h : Q = dblGram finSumFinEquiv J) : HA R σ J × HA R σ J →* HA R σ Q :=
  ioU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) finSumFinEquiv (J := JR R J) (Q := JR R Q) (h ▸ JR_dblGram R J)

abbrev siegelH : Subgroup (HA R σ Q) := siegelOf finSumFinEquiv (matHom R σ Q)

abbrev aH : siegelH R σ Q →* (R ⊗[F] E)ˣ := aOf finSumFinEquiv (matHom R σ Q)

abbrev unipH : Subgroup (HA R σ Q) := unipOf finSumFinEquiv (matHom R σ Q)

abbrev leviH : Subgroup (HA R σ Q) := leviSubOf finSumFinEquiv (matHom R σ Q)

def detH (J : Matrix (Fin m) (Fin m) E) : HA R σ J →* (R ⊗[F] E)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom R σ J)

variable {R σ Q} (h : Q = dblGram finSumFinEquiv J)

theorem val_detH {J : Matrix (Fin m) (Fin m) E} (g : HA R σ J) : (detH R σ J g).1 = (matHom R σ J g).1.det := rfl

theorem matHom_ioH (g g' : HA R σ J) :
    matHom R σ Q (ioH R σ h (g, g')) = blkGL finSumFinEquiv (matHom R σ J g, matHom R σ J g') := rfl

theorem ioH_one : ioH R σ h (1, 1) = 1 := by
  exact map_one (ioH R σ h)

theorem ioH_injective : Function.Injective (ioH R σ h) := by
  rintro ⟨g, g'⟩ ⟨k, k'⟩ hx
  have e1 := congrArg (matHom R σ Q) hx
  rw [matHom_ioH, matHom_ioH] at e1
  have e2 := blkGL_injective _ e1
  simp only [Prod.mk.injEq] at e2
  exact Prod.ext (matHom_injective R σ J e2.1) (matHom_injective R σ J e2.2)

theorem continuous_ioH [TopologicalSpace R] : Continuous (ioH R σ h) := by
  rw [(isEmbedding_matHom R σ Q).continuous_iff]
  have e1 : (matHom R σ Q) ∘ (ioH R σ h) =
      (blkGL finSumFinEquiv) ∘ (Prod.map (matHom R σ J) (matHom R σ J)) :=
    funext fun x => matHom_ioH h x.1 x.2
  rw [e1]
  exact (continuous_blkGL _).comp
    ((isEmbedding_matHom R σ J).continuous.prodMap (isEmbedding_matHom R σ J).continuous)

theorem ioH_mem_siegelH {g g' : HA R σ J} : ioH R σ h (g, g') ∈ siegelH R σ Q ↔ g = g' := by
  rw [mem_siegelOf, matHom_ioH, val_blkGL, keepsDiag_blkMat]
  constructor
  · intro e1
    exact (matHom_injective R σ J (Units.ext e1)).symm
  · rintro rfl
    rfl

def ioDiag : HA R σ J →* siegelH R σ Q :=
  ((ioH R σ h).comp ((MonoidHom.id _).prod (MonoidHom.id _))).codRestrict _ fun _ => (ioH_mem_siegelH h).2 rfl

theorem coe_ioDiag (g : HA R σ J) : (ioDiag h g : HA R σ Q) = ioH R σ h (g, g) := rfl

theorem aH_ioDiag (g : HA R σ J) : aH R σ Q (ioDiag h g) = detH R σ J g := by
  ext
  rw [val_aOf, coe_ioDiag, matHom_ioH, val_blkGL, leviMat_blkMat, val_detH]

theorem isUnit_det_JR (hJ : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have e1 : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [e1]
  exact (isUnit_iff_ne_zero.2 hJ).map _

include h in

theorem sigR_det_quot_mul_aH (hJ : J.det ≠ 0) (p : siegelH R σ Q) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (quotMat finSumFinEquiv (matHom R σ Q p).1).det * (aH R σ Q p).1 = 1 := by
  have hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (matHom R σ Q (p : HA R σ Q)).1 *
      dblGram finSumFinEquiv (JR R J) * (matHom R σ Q (p : HA R σ Q)).1 = dblGram finSumFinEquiv (JR R J) := by
    rw [← JR_dblGram, ← h]
    exact Subtype.prop (p : HA R σ Q)
  have e1 := det_quot_mul_det_levi finSumFinEquiv (isUnit_det_JR (R := R) hJ) hM (mem_siegelOf.1 p.2)
  rw [val_aOf]
  exact e1

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjUnit_detH {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : HA R σ J) :
    conjUnit σ (detH R σ J g) = (detH R σ J g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext
  simp only [Units.val_mul, Units.val_one]
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (matHom R σ J g).1.det * (matHom R σ J g).1.det = 1
  have hg : ((matHom R σ J g).1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)).transpose * JR R J * (matHom R σ J g).1 =
      JR R J := Subtype.prop g
  have hd : ((matHom R σ J g).1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)).det =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (matHom R σ J g).1.det := (RingHom.map_det _ _).symm
  have e1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd] at e1
  apply (isUnit_det_JR (R := R) hJ).mul_left_cancel
  linear_combination e1

variable {R' : Type} [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')

theorem mapH_ioH (g g' : HA R σ J) : mapH σ Q φ (ioH R σ h (g, g')) = ioH R' σ h (mapH σ J φ g, mapH σ J φ g') := by
  apply matHom_injective
  have key : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) E} (x : HA R σ K),
      matHom R' σ K (mapH σ K φ x) = bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (matHom R σ K x) :=
    fun _ => rfl
  simp only [key, matHom_ioH, bc_blkGL]

theorem mapH_mem_siegelH {g : HA R σ Q} (hg : g ∈ siegelH R σ Q) : mapH σ Q φ g ∈ siegelH R' σ Q := by
  rw [mem_siegelOf] at hg ⊢
  exact KeepsDiag.map (e := finSumFinEquiv) hg (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom

theorem aH_mapH (p : siegelH R σ Q) : aH R' σ Q ⟨mapH σ Q φ p, mapH_mem_siegelH φ p.2⟩ =
    Units.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom.toMonoidHom (aH R σ Q p) := by
  ext
  rw [Units.coe_map, val_aOf, val_aOf]
  exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom _)).trans
    (RingHom.map_det _ _).symm

variable (σ Q) in

abbrev siegelRat : Subgroup (UJ (σ : E →+* E) Q) := siegelOf finSumFinEquiv (UJ (σ : E →+* E) Q).subtype

theorem diagH_mem_siegelH [Nontrivial R] {γ : UJ (σ : E →+* E) Q} :
    diagH σ Q R γ ∈ siegelH R σ Q ↔ γ ∈ siegelRat σ Q := by
  have hinj : Function.Injective (inclR (F := F) R : E → R ⊗[F] E) := by
    have : Nontrivial (R ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (S := F) (FaithfulSMul.algebraMap_injective F E)).nontrivial
    exact RingHom.injective _
  rw [mem_siegelOf, mem_siegelOf, keepsDiag_iff, keepsDiag_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change inclR (F := F) R _ + inclR (F := F) R _ = inclR (F := F) R _ + inclR (F := F) R _ ↔ _
  rw [← map_add, ← map_add, hinj.eq_iff]

theorem aH_diagH {γ : UJ (σ : E →+* E) Q} (hγ : γ ∈ siegelRat σ Q) (hγ' : diagH σ Q R γ ∈ siegelH R σ Q) :
    aH R σ Q ⟨_, hγ'⟩ = Units.map (inclR (F := F) R).toMonoidHom (aOf finSumFinEquiv (UJ (σ : E →+* E) Q).subtype ⟨γ, hγ⟩) := by
  ext
  rw [Units.coe_map, val_aOf, val_aOf]
  exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (inclR (F := F) R) _)).trans (RingHom.map_det _ _).symm

theorem ioH_diagH (γ γ' : UJ (σ : E →+* E) J) :
    ioH R σ h (diagH σ J R γ, diagH σ J R γ') = diagH σ Q R (ioU (σ : E →+* E) finSumFinEquiv h (γ, γ')) := by
  apply matHom_injective
  have key : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) E} (x : UJ (σ : E →+* E) K),
      matHom R σ K (diagH σ K R x) = bc (inclR (F := F) R) x.1 := fun _ => rfl
  rw [matHom_ioH, key, key, key, coe_ioU, bc_blkGL]

end Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

section LocalGlobal

variable (h : Q = dblGram finSumFinEquiv J)

section

omit [NumberField E]

theorem proj_ioH (v : HeightOneSpectrum (𝓞 F)) (g g' : GAd σ J) :
    proj σ Q v (ioH _ σ h (g, g')) = ioH _ σ h (proj σ J v g, proj σ J v g') := by
  exact mapH_ioH h (evFin F v) g g'

theorem projArch_ioH (w : InfinitePlace F) (g g' : GAd σ J) :
    projArch σ Q w (ioH _ σ h (g, g')) = ioH _ σ h (projArch σ J w g, projArch σ J w g') := by
  exact mapH_ioH h (evInf F w) g g'

theorem emb_ioH (v : HeightOneSpectrum (𝓞 F)) (g g' : GLoc σ J v) :
    emb σ Q v (ioH _ σ h (g, g')) = ioH _ σ h (emb σ J v g, emb σ J v g') := by
  refine GAd_ext σ Q (fun w => ?_) (fun u => ?_)
  · simp only [projArch_ioH, projArch_emb, ioH_one]
  · by_cases e : u = v
    · subst e
      simp only [proj_ioH, proj_emb_self]
    · simp only [proj_ioH, proj_emb_ne σ Q e, proj_emb_ne σ J e, ioH_one]

theorem ioH_mem_ratPts {g g' : GAd σ J} (hg : g ∈ AdelicU.ratPts σ J) (hg' : g' ∈ AdelicU.ratPts σ J) :
    ioH _ σ h (g, g') ∈ AdelicU.ratPts σ Q := by
  rw [← range_ratEmb σ J] at hg hg'
  rw [← range_ratEmb σ Q]
  obtain ⟨γ, rfl⟩ := hg
  obtain ⟨γ', rfl⟩ := hg'
  exact ⟨ioU (σ : E →+* E) finSumFinEquiv h (γ, γ'), (ioH_diagH h γ γ').symm⟩

def projP (v : HeightOneSpectrum (𝓞 F)) : siegelH (AF F) σ Q →* siegelH (Fv F v) σ Q :=
  ((proj σ Q v).comp (Subgroup.subtype _)).codRestrict _ fun p => mapH_mem_siegelH _ p.2

def projArchP (w : InfinitePlace F) : siegelH (AF F) σ Q →* siegelH w.Completion σ Q :=
  ((projArch σ Q w).comp (Subgroup.subtype _)).codRestrict _ fun p => mapH_mem_siegelH _ p.2

@[simp] theorem coe_projP (v : HeightOneSpectrum (𝓞 F)) (p : siegelH (AF F) σ Q) :
    (projP v p : GLoc σ Q v) = proj σ Q v p := rfl

@[simp] theorem coe_projArchP (w : InfinitePlace F) (p : siegelH (AF F) σ Q) :
    (projArchP w p : GArch σ Q w) = projArch σ Q w p := rfl

theorem aH_projP (v : HeightOneSpectrum (𝓞 F)) (p : siegelH (AF F) σ Q) :
    aH _ σ Q (projP v p) = unitFin F E v (aH _ σ Q p) := by
  exact aH_mapH (evFin F v) p

theorem aH_projArchP (w : InfinitePlace F) (p : siegelH (AF F) σ Q) :
    aH _ σ Q (projArchP w p) = unitInf F E w (aH _ σ Q p) := by
  exact aH_mapH (evInf F w) p

end

theorem mem_siegelH_adelic {g : GAd σ Q} : g ∈ siegelH (AF F) σ Q ↔
    (∀ w, projArch σ Q w g ∈ siegelH _ σ Q) ∧ ∀ v, proj σ Q v g ∈ siegelH _ σ Q := by
  constructor
  · intro hg
    exact ⟨fun w => mapH_mem_siegelH _ hg, fun v => mapH_mem_siegelH _ hg⟩
  · rintro ⟨h1, h2⟩
    rw [mem_siegelOf, keepsDiag_iff]
    intro i j
    apply adele_ext
    · intro w
      have e1 := (keepsDiag_iff _).1 (mem_siegelOf.1 (h1 w)) i j
      rw [matHom_projArch] at e1
      rw [map_add, map_add]
      exact e1
    · intro v
      have e1 := (keepsDiag_iff _).1 (mem_siegelOf.1 (h2 v)) i j
      rw [matHom_proj] at e1
      rw [map_add, map_add]
      exact e1

def embP (v : HeightOneSpectrum (𝓞 F)) : siegelH (Fv F v) σ Q →* siegelH (AF F) σ Q :=
  ((emb σ Q v).comp (Subgroup.subtype _)).codRestrict _ fun p => mem_siegelH_adelic.2
    ⟨fun w => by simp, fun u => by
      by_cases e : u = v
      · subst e; simp
      · simp [proj_emb_ne σ Q e]⟩

def embArchP (w : InfinitePlace F) : siegelH w.Completion σ Q →* siegelH (AF F) σ Q :=
  ((embArch σ Q w).comp (Subgroup.subtype _)).codRestrict _ fun p => mem_siegelH_adelic.2
    ⟨fun u => by
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ Q e], fun u => by simp⟩

@[simp] theorem coe_embP (v : HeightOneSpectrum (𝓞 F)) (p : siegelH (Fv F v) σ Q) :
    (embP v p : GAd σ Q) = emb σ Q v p := rfl

@[simp] theorem coe_embArchP (w : InfinitePlace F) (p : siegelH w.Completion σ Q) :
    (embArchP w p : GAd σ Q) = embArch σ Q w p := rfl

theorem aH_embP (v : HeightOneSpectrum (𝓞 F)) (p : siegelH (Fv F v) σ Q) :
    aH _ σ Q (embP v p) = ideleAt F E v (aH _ σ Q p) := by
  apply idele_ext
  · intro w
    rw [unitInf_ideleAt, ← aH_projArchP]
    have e1 : projArchP w (embP v p) = 1 :=
      Subtype.ext (by rw [coe_projArchP, coe_embP]; exact projArch_emb σ Q w v _)
    rw [e1, map_one]
  · intro u
    rw [← aH_projP]
    by_cases e : u = v
    · subst e
      rw [unitFin_ideleAt_self]
      congr 1
      exact Subtype.ext (by rw [coe_projP, coe_embP, proj_emb_self])
    · rw [unitFin_ideleAt_ne e]
      have e1 : projP u (embP v p) = 1 :=
        Subtype.ext (by rw [coe_projP, coe_embP]; exact proj_emb_ne σ Q e _)
      rw [e1, map_one]

omit [NumberField E] in

theorem exists_aH_eq_of_mem_ratPts (p : siegelH (AF F) σ Q) (hp : (p : GAd σ Q) ∈ AdelicU.ratPts σ Q) :
    ∃ x : Eˣ, aH _ σ Q p = Units.map (inclR (F := F) (AF F)).toMonoidHom x := by
  have : Nontrivial (AF F) := (show Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from inferInstance)
  rw [← range_ratEmb σ Q] at hp
  obtain ⟨γ, hγ⟩ := hp
  have hγ' : diagH σ Q (AF F) γ ∈ siegelH (AF F) σ Q := by
    have e1 : diagH σ Q (AF F) γ = (p : GAd σ Q) := hγ
    rw [e1]
    exact p.2
  have hs : γ ∈ siegelRat σ Q := diagH_mem_siegelH.1 hγ'
  refine ⟨aOf finSumFinEquiv (UJ (σ : E →+* E) Q).subtype ⟨γ, hs⟩, ?_⟩
  rw [← aH_diagH hs hγ']
  congr 1
  exact Subtype.ext hγ.symm

end LocalGlobal

section Level

instance isLattice_sumLat (L : Submodule (𝓞 E) (Fin m → E)) (L' : Submodule (𝓞 E) (Fin n → E))
    [h : Submodule.IsLattice E L] [h' : Submodule.IsLattice E L'] :
    Submodule.IsLattice E (sumLat finSumFinEquiv L L') := by
  let φ : ((Fin m → E) × (Fin n → E)) ≃ₗ[E] (Fin (m + n) → E) :=
    (LinearEquiv.sumArrowLequivProdArrow _ _ E E).symm.trans (LinearEquiv.funCongrLeft E E finSumFinEquiv.symm)
  have hφ : ∀ x, φ x = pairVec finSumFinEquiv x.1 x.2 := fun x => rfl
  have e : sumLat finSumFinEquiv L L' = (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 E)) := by
    ext w
    refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact (pairVec_mem_sumLat _).2 hx
  refine ⟨e ▸ (h.fg.prod h'.fg).map _, ?_⟩
  rw [e, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, Submodule.prod_coe,
    Submodule.span_prod_eq E (zero_mem L) (zero_mem L'), h.span_eq_top, h'.span_eq_top, Submodule.prod_top,
    Submodule.map_top, LinearEquiv.range]

omit [NumberField E] in

theorem latLoc_sumLat (L : Submodule (𝓞 E) (Fin m → E)) (L' : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    latLoc F (sumLat finSumFinEquiv L L') v = sumLat finSumFinEquiv (latLoc F L v) (latLoc F L' v) := by
  ext w
  constructor
  · intro hw
    change w ∈ AddSubgroup.closure _ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      rw [mem_sumLat] at hx ⊢
      exact ⟨AddSubgroup.subset_closure ⟨a, ha, _, hx.1, rfl⟩, AddSubgroup.subset_closure ⟨a, ha, _, hx.2, rfl⟩⟩
    | zero => exact zero_mem _
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | neg _ _ h1 => exact neg_mem h1
  · intro hw
    rw [mem_sumLat] at hw
    let ℓ : (Fin m → Fv F v ⊗[F] E) →+ (Fin (m + n) → Fv F v ⊗[F] E) :=
      AddMonoidHom.mk' (fun y => pairVec finSumFinEquiv y 0) (fun y y' => by
        funext k
        simp only [pairVec, Function.comp_apply, Pi.add_apply]
        cases finSumFinEquiv.symm k <;> simp)
    let ℓ' : (Fin n → Fv F v ⊗[F] E) →+ (Fin (m + n) → Fv F v ⊗[F] E) :=
      AddMonoidHom.mk' (fun y => pairVec finSumFinEquiv 0 y) (fun y y' => by
        funext k
        simp only [pairVec, Function.comp_apply, Pi.add_apply]
        cases finSumFinEquiv.symm k <;> simp)
    have hl : ℓ (fun i => w (finSumFinEquiv (.inl i))) ∈ latLoc F (sumLat finSumFinEquiv L L') v := by
      have h1 := AddSubgroup.mem_map_of_mem (K := AddSubgroup.closure
        {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}) ℓ hw.1
      rw [AddMonoidHom.map_closure] at h1
      refine AddSubgroup.closure_mono ?_ h1
      rintro _ ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      refine ⟨a, ha, pairVec finSumFinEquiv x 0, (pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩, ?_⟩
      funext k
      simp only [ℓ, AddMonoidHom.mk'_apply, pairVec, Function.comp_apply]
      cases finSumFinEquiv.symm k <;> simp
    have hr : ℓ' (fun i => w (finSumFinEquiv (.inr i))) ∈ latLoc F (sumLat finSumFinEquiv L L') v := by
      have h1 := AddSubgroup.mem_map_of_mem (K := AddSubgroup.closure
        {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ L', y = fun i => a ⊗ₜ[F] x i}) ℓ' hw.2
      rw [AddMonoidHom.map_closure] at h1
      refine AddSubgroup.closure_mono ?_ h1
      rintro _ ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      refine ⟨a, ha, pairVec finSumFinEquiv 0 x, (pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩, ?_⟩
      funext k
      simp only [ℓ', AddMonoidHom.mk'_apply, pairVec, Function.comp_apply]
      cases finSumFinEquiv.symm k <;> simp
    have e1 : w = ℓ (fun i => w (finSumFinEquiv (.inl i))) + ℓ' (fun i => w (finSumFinEquiv (.inr i))) := by
      conv_lhs => rw [← pairVec_eta finSumFinEquiv w]
      funext k
      simp only [ℓ, ℓ', AddMonoidHom.mk'_apply, Pi.add_apply, pairVec, Function.comp_apply]
      cases finSumFinEquiv.symm k <;> simp
    rw [e1]
    exact add_mem hl hr

variable (σ Q)

abbrev KFin (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GLoc σ Q v) :=
  stabLoc σ Q (sumLat finSumFinEquiv L L) v

abbrev KArch (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Subgroup (GArch σ Q w) :=
  stabArch σ Q w (blkGL finSumFinEquiv (b, b))

abbrev KAd (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) : Subgroup (GAd σ Q) :=
  levelAll σ Q (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a))

variable {σ Q} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}

section

omit [NumberField E]

theorem mem_KAd {g : GAd σ Q} : g ∈ KAd σ Q L a ↔
    (∀ v, proj σ Q v g ∈ KFin σ Q L v) ∧ ∀ w, projArch σ Q w g ∈ KArch σ Q w (bc (compInf F E w) a) := by
  rw [mem_levelAll]
  simp only [bc_blkGL, KFin, KArch]

theorem emb_mem_KAd {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v) :
    emb σ Q v k ∈ KAd σ Q L a := by
  rw [mem_KAd]
  refine ⟨fun u => ?_, fun w => ?_⟩
  · by_cases e : u = v
    · subst e
      rwa [proj_emb_self]
    · rw [proj_emb_ne σ Q e]
      exact one_mem _
  · rw [projArch_emb]
    exact one_mem _

variable (h : Q = dblGram finSumFinEquiv J)

theorem ioH_mem_KFin {v : HeightOneSpectrum (𝓞 F)} {g g' : GLoc σ J v} :
    ioH _ σ h (g, g') ∈ KFin σ Q L v ↔ g ∈ stabLoc σ J L v ∧ g' ∈ stabLoc σ J L v := by
  simp only [KFin, stabLoc, Subgroup.mem_comap, matHom_ioH, latLoc_sumLat]
  exact blkGL_mem_stabGL _

theorem ioH_mem_KArch {w : InfinitePlace F} {b : GL (Fin n) (w.Completion ⊗[F] E)} {g g' : GArch σ J w} :
    ioH _ σ h (g, g') ∈ KArch σ Q w b ↔ g ∈ stabArch σ J w b ∧ g' ∈ stabArch σ J w b := by
  rw [mem_stabArch, mem_stabArch, mem_stabArch, matHom_ioH, ← map_inv (blkGL finSumFinEquiv),
    ← map_mul (blkGL finSumFinEquiv), ← map_mul (blkGL finSumFinEquiv), ← blkMat_one finSumFinEquiv, blkGL_mem_UJ]
  try exact Iff.rfl

theorem ioH_mem_KAd {g g' : GAd σ J} :
    ioH _ σ h (g, g') ∈ KAd σ Q L a ↔ g ∈ levelAll σ J L a ∧ g' ∈ levelAll σ J L a := by
  rw [mem_KAd, mem_levelAll, mem_levelAll]
  simp only [proj_ioH, projArch_ioH, ioH_mem_KFin, ioH_mem_KArch]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun v => (h1 v).1, fun w => (h2 w).1⟩, ⟨fun v => (h1 v).2, fun w => (h2 w).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun v => ⟨h1 v, h3 v⟩, fun w => ⟨h2 w, h4 w⟩⟩

theorem isLatticeFrame_dbl (ha : IsLatticeFrame L a) :
    IsLatticeFrame (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro v y
  simp only [bc_blkGL, val_blkGL, latLoc_sumLat]
  rw [← pairVec_eta finSumFinEquiv y, blkMat_mulVec, pairVec_mem_sumLat, ← ha v, ← ha v]
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have e1 := hy (finSumFinEquiv (.inl i))
      rwa [pairVec_inl] at e1
    · have e1 := hy (finSumFinEquiv (.inr i))
      rwa [pairVec_inr] at e1
  · rintro ⟨h1, h2⟩ k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    rcases k with i | i
    · rw [pairVec_inl]
      exact h1 i
    · rw [pairVec_inr]
      exact h2 i

include h in

theorem isMajorantFrame_dbl (ha : IsMajorantFrame σ J a) : IsMajorantFrame σ Q (blkGL finSumFinEquiv (a, a)) := by
  intro w
  obtain ⟨ε, hε⟩ := ha w
  refine ⟨Sum.elim ε (fun i => !ε i) ∘ finSumFinEquiv.symm, ?_⟩
  rw [h, JR_dblGram, bc_blkGL, val_blkGL]
  dsimp only
  rw [dblGram, cT_blkMat, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, hε, Matrix.diagonal_neg, blkMat,
    Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext k
  simp only [Function.comp_apply]
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  simp only [Equiv.symm_apply_apply]
  rcases k with i | i <;> simp <;> split_ifs <;> simp_all

include h in

theorem isSelfDualAt_dbl {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) :
    IsSelfDualAt σ Q (sumLat finSumFinEquiv L L) v := by
  have hz : ∀ y : Fin n → Fv F v ⊗[F] E,
      Formalism.UG.hform (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (JR (Fv F v) J) 0 y = 0 := by
    intro y
    simp [Formalism.UG.hform]
  unfold IsSelfDualAt at hL ⊢
  ext w
  rw [← pairVec_eta finSumFinEquiv w]
  rw [latLoc_sumLat, pairVec_mem_sumLat, hL]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    rw [latLoc_sumLat, mem_sumLat] at hx
    rw [← pairVec_eta finSumFinEquiv x]
    have e1 : hLin σ J (Fv F v) _ _ ∈ intLoc F E v := h1 _ hx.1
    have e2 : hLin σ J (Fv F v) _ _ ∈ intLoc F E v := h2 _ hx.2
    change Formalism.UG.hform _ (JR _ Q) (pairVec _ _ _) (pairVec _ _ _) ∈ intLoc F E v
    rw [h, JR_dblGram, hform_dblGram]
    exact sub_mem e1 e2
  · intro hw
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have e1 := hw (pairVec finSumFinEquiv x 0)
        (by rw [latLoc_sumLat, pairVec_mem_sumLat]; exact ⟨hx, zero_mem _⟩)
      change Formalism.UG.hform _ (JR _ Q) _ _ ∈ intLoc F E v at e1
      rw [h, JR_dblGram, hform_dblGram, hz, sub_zero] at e1
      exact e1
    · have e1 := hw (pairVec finSumFinEquiv 0 x)
        (by rw [latLoc_sumLat, pairVec_mem_sumLat]; exact ⟨zero_mem _, hx⟩)
      change Formalism.UG.hform _ (JR _ Q) _ _ ∈ intLoc F E v at e1
      rw [h, JR_dblGram, hform_dblGram, hz, zero_sub] at e1
      exact neg_mem_iff.1 e1

end

theorem isCompact_levelAll (h : IsCMExt F E σ) (J : Matrix (Fin m) (Fin m) E) (L : Submodule (𝓞 E) (Fin m → E))
    [Submodule.IsLattice E L] (a : GL (Fin m) (AF F ⊗[F] E)) : IsCompact (levelAll σ J L a : Set (GAd σ J)) := by
  have hA : IsCompact (Set.pi Set.univ fun w =>
      (stabArch σ J w (bc (compInf F E w) a) : Set (GArch σ J w))) :=
    isCompact_univ_pi fun w => GlobalTheory.AdelicU.Frames.isCompact_stabArch h J w _
  have hK := hA.image ((continuous_ofInf σ J).comp (continuous_embArchPi σ J))
  have hS := hK.mul (isCompact_levelFin (σ := σ) (J := J) (L := L))
  convert hS using 1
  ext g
  constructor
  · intro hg
    rw [SetLike.mem_coe, mem_levelAll] at hg
    rw [Set.mem_mul]
    refine ⟨ofInf σ J (projInf σ J g), ⟨fun w => projInfArch σ J w (projInf σ J g), fun w _ => ?_, ?_⟩,
      ofFin σ J (projFin σ J g), ?_, ofInf_projInf_mul_ofFin_projFin σ J g⟩
    · dsimp only
      rw [projInfArch_projInf]
      exact hg.2 w
    · exact congrArg (ofInf σ J) (GInf_ext σ J fun w => projInfArch_embArchPi σ J _ w)
    · rw [SetLike.mem_coe, mem_levelFin]
      refine ⟨mem_finPts.2 (projInf_ofFin σ J _), fun v => ?_⟩
      rw [proj_ofFin, projFinLoc_projFin]
      exact hg.1 v
  · intro hg
    obtain ⟨x, ⟨k, hk, rfl⟩, y, hy, rfl⟩ := Set.mem_mul.1 hg
    rw [SetLike.mem_coe] at hy ⊢
    rw [mem_levelFin] at hy
    refine mul_mem (mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩) (mem_levelAll.2 ⟨hy.2, fun w => ?_⟩)
    · simp only [Function.comp_apply, proj_ofInf]
      exact one_mem _
    · simp only [Function.comp_apply, projArch_ofInf, projInfArch_embArchPi]
      exact hk w (Set.mem_univ w)
    · rw [mem_finPts_iff_forall.1 hy.1 w]
      exact one_mem _

end Level

end GlobalTheory.Doubling

end
