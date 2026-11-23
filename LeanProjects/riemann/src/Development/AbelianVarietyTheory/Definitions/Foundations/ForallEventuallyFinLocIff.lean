import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
import Development.AbelianVarietyTheory.Definitions.Foundations.ToContinuousLinearMapMemHomIn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
open NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Mem.Th
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open GlobalTheory.PRep (smoothPart smoothRep IsSmooth IsAdmissible fixed)
open GlobalTheory.Orb (dsRep TypeDataG)
open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult

section Vectors

variable {G X H : Type} [Group G] [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ρ : Representation ℂ G X) (K : Subgroup G) : Submodule ℂ X where
  carrier := {x | ∃ W : Submodule ℂ X, FiniteDimensional ℂ W ∧ ∀ k ∈ K, ρ k x ∈ W}
  zero_mem' := ⟨⊥, inferInstance, fun k _ => by simp⟩
  add_mem' := fun ⟨W, _, h⟩ ⟨W', _, h'⟩ =>
    ⟨W ⊔ W', inferInstance, fun k hk => by rw [map_add]; exact Submodule.add_mem_sup (h k hk) (h' k hk)⟩
  smul_mem' := fun c _ ⟨W, hW, h⟩ => ⟨W, hW, fun k hk => by rw [map_smul]; exact W.smul_mem c (h k hk)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isSmooth_smoothRep (ρ : Representation ℂ G X) : IsSmooth (smoothRep ρ) := fun v => by
  have : {g : G | smoothRep ρ g v = v} = {g : G | ρ g v = v} := Set.ext fun _ => Subtype.ext_iff
  exact this ▸ v.2

abbrev smRep (π : G →* (H →L[ℂ] H)) : Representation ℂ G (smoothPart (toRep π)) := smoothRep (toRep π)

end Vectors

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def GPl : Formalism.MainNotions.SchurIrreducible.Pl F → Type
  | .inl w => GArch σ J w
  | .inr v => GLoc σ J v

instance : ∀ v, Group (GPl σ J v)
  | .inl w => inferInstanceAs (Group (GArch σ J w))
  | .inr v => inferInstanceAs (Group (GLoc σ J v))

instance : ∀ v, TopologicalSpace (GPl σ J v)
  | .inl w => inferInstanceAs (TopologicalSpace (GArch σ J w))
  | .inr v => inferInstanceAs (TopologicalSpace (GLoc σ J v))

def projPl : ∀ v, GAd σ J →* GPl σ J v
  | .inl w => projArch σ J w
  | .inr v => proj σ J v

def embPl : ∀ v, GPl σ J v →* GAd σ J
  | .inl w => embArch σ J w
  | .inr v => emb σ J v

theorem continuous_embPl : ∀ v, Continuous (embPl σ J v)
  | .inl w => continuous_embArch σ J w
  | .inr v => continuous_emb σ J v

@[simp] theorem projPl_embPl_self : ∀ v x, projPl σ J v (embPl σ J v x) = x
  | .inl w, x => projArch_embArch_self σ J w x
  | .inr v, x => proj_emb_self σ J v x

theorem projPl_embPl_ne : ∀ {u v}, u ≠ v → ∀ x, projPl σ J u (embPl σ J v x) = 1
  | .inl _, .inl _, h, x => projArch_embArch_ne σ J (fun e => h (congrArg _ e)) x
  | .inl u, .inr v, _, x => projArch_emb σ J u v x
  | .inr u, .inl v, _, x => proj_embArch σ J u v x
  | .inr _, .inr _, h, x => proj_emb_ne σ J (fun e => h (congrArg _ e)) x

theorem forall_eventually_proj_iff (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    (a : ∀ v, GLoc σ J v → Prop) : (∀ g : GFin σ J, ∀ᶠ v in cofinite, a v (projFinLoc σ J v g)) ↔
      ∀ᶠ v in cofinite, ∀ k ∈ stabLoc σ J L v, a v k := by
  refine ⟨fun h => ?_, fun h g => (h.and (eventually_projFinLoc_mem_stabLoc σ J L g)).mono fun v hv => hv.1 _ hv.2⟩
  have : ∀ v, ∃ k ∈ stabLoc σ J L v, a v k → ∀ k' ∈ stabLoc σ J L v, a v k' := fun v => by
    by_cases e : ∀ k' ∈ stabLoc σ J L v, a v k'
    · exact ⟨1, one_mem _, fun _ => e⟩
    · push Not at e
      exact e.imp fun k hk => ⟨hk.1, fun h => absurd h hk.2⟩
  choose k hk hk' using this
  obtain ⟨g, hg, -⟩ := existsUnique_projFinLoc_eq σ J L k (.of_forall hk)
  exact (h g).mono fun v hv => hk' v (hg v ▸ hv)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def HasCompPl (v : Formalism.MainNotions.SchurIrreducible.Pl F) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (δ : GPl σ J v →* (X →L[ℂ] X)) (π : GAd σ J →* (H →L[ℂ] H)) : Prop := IsIsotypic δ (π.comp (embPl σ J v))

variable {Hs : Formalism.MainNotions.SchurIrreducible.Pl F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]

abbrev IsFactorisation (δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)) (ξ : ∀ v, Hs v) (π : GAd σ J →* (H →L[ℂ] H))
    (B : (∀ v, Hs v) → H) : Prop := IsRestrTensor (projPl σ J) δ ξ π B

variable {σ J} {δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)} {ξ : ∀ v, Hs v} {π : GAd σ J →* (H →L[ℂ] H)}
  {B : (∀ v, Hs v) → H}

theorem IsFactorisation.eventually_fixed (h : IsFactorisation σ J δ ξ π B) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] : ∀ᶠ v in cofinite, ∀ k ∈ stabLoc σ J L v, δ (.inr v) k (ξ (.inr v)) = ξ (.inr v) :=
  (forall_eventually_proj_iff σ J L fun v k => δ (.inr v) k (ξ (.inr v)) = ξ (.inr v)).1 fun g =>
    (Sum.inr_injective.tendsto_cofinite.eventually (h.fixed (ofFin σ J g))).mono fun v hv =>
      (congrArg (δ (.inr v) · _) (proj_ofFin σ J v g)).symm.trans hv

theorem IsFactorisation.apply_embPl [DecidableEq (Formalism.MainNotions.SchurIrreducible.Pl F)] (h : IsFactorisation σ J δ ξ π B) {y : ∀ v, Hs v}
    (hy : Restr ξ y) (v : Formalism.MainNotions.SchurIrreducible.Pl F) (g : GPl σ J v) :
    π (embPl σ J v g) (B y) = B (Function.update y v (δ v g (y v))) := by
  rw [h.apply_pure _ _ hy]
  congr 1
  funext u
  by_cases e : u = v
  · subst e; simp
  · simp [projPl_embPl_ne σ J e, e]

theorem IsFactorisation.hasCompPl (h : IsFactorisation σ J δ ξ π B) (v : Formalism.MainNotions.SchurIrreducible.Pl F) :
    HasCompPl σ J v (δ v) π := by
  classical
  refine eq_top_iff.2 (h.dense.ge.trans
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) isSubrep_isoPart.1))
  rintro _ ⟨y, hy, rfl⟩
  have hr := SmallThetaModules.restr_update hy v
  have h0 : B (Function.update y v 0) = 0 := h.ext fun z hz => by simp [h.inner_update hy hz]
  let T : Hs v →ₗ[ℂ] H :=
    { toFun := fun x => B (Function.update y v x)
      map_add' := fun a b => by simpa using h.pure_update hy v 1 a b
      map_smul' := fun c a => by simpa [h0] using h.pure_update hy v c a 0 }
  have hT : ∀ x, ‖T x‖ ≤ √‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ * ‖x‖ := fun x => by
    have e := h.inner_update hy (hr x) v x
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    refine le_of_sq_le_sq (le_of_eq ?_) (by positivity)
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]
    simpa [T] using e'
  have := apply_mem_isoPart (π := δ v) (ρ := π.comp (embPl σ J v)) (U := ⊤) (T := T.mkContinuous _ hT)
    (mem_homIn_top.2 fun g x => by
      simpa [T] using (h.apply_embPl (hr x) v g).symm) (y v)
  simpa [T] using this

end Places

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D)

section Groups

abbrev Gv (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Gw (w : InfinitePlace D.host.F) : Type := GArch D.sp.cm.sig V.gram w

abbrev Kv (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev embW (w : InfinitePlace D.host.F) : Gw V w →* GA D V := embArch D.sp.cm.sig V.gram w

def locFin (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GfC V :=
  (embV V v).codRestrict _ fun x => mem_finPts.2 (projInf_emb _ _ v x)

def finLoc (v : HeightOneSpectrum (𝓞 D.host.F)) : GfC V →* Gv V v := (proj D.sp.cm.sig V.gram v).comp (GfC V).subtype

def archInf (w : InfinitePlace D.host.F) : Gw V w →* GinfC V :=
  (embW V w).codRestrict _ fun x => mem_infPts.2 (projFin_embArch _ _ w x)

def infArch (w : InfinitePlace D.host.F) : GinfC V →* Gw V w := (projArch D.sp.cm.sig V.gram w).comp (GinfC V).subtype

def toFin : GA D V →* GfC V :=
  ((ofFin D.sp.cm.sig V.gram).comp (projFin _ _)).codRestrict _ fun _ => mem_finPts.2 (projInf_ofFin _ _ _)

def toInf : GA D V →* GinfC V :=
  ((ofInf D.sp.cm.sig V.gram).comp (projInf _ _)).codRestrict _ fun _ => mem_infPts.2 (projFin_ofInf _ _ _)

def KOff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) :=
  (levelOff D.sp.cm.sig V.gram (frameLat V) S).subgroupOf (GfC V)

variable {V}

theorem mem_KOff {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {g : GfC V} : g ∈ KOff V S ↔ (g : GA D V) ∈ KsphC V S := by
  rw [KsphC_eq]; rfl

@[simp] theorem coe_locFin (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) : (locFin V v x : GA D V) = embV V v x := rfl

@[simp] theorem coe_archInf (w : InfinitePlace D.host.F) (x : Gw V w) : (archInf V w x : GA D V) = embW V w x := rfl

theorem toInf_mul_toFin (g : GA D V) : (toInf V g : GA D V) * toFin V g = g := ofInf_projInf_mul_ofFin_projFin _ _ g

theorem commute_inf_fin (x : GinfC V) (y : GfC V) : Commute (x : GA D V) y :=
  ext_inf_fin _ _ (by simp [mem_finPts.1 y.2]) (by simp [mem_infPts.1 x.2])

@[simp] theorem toFin_coe (y : GfC V) : toFin V y = y := (finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y

@[simp] theorem toFin_coe_inf (x : GinfC V) : toFin V x = 1 :=
  Subtype.ext ((congrArg (ofFin _ _) (mem_infPts.1 x.2)).trans (map_one _))

@[simp] theorem toInf_coe_fin (y : GfC V) : toInf V y = 1 :=
  Subtype.ext ((congrArg (ofInf _ _) (mem_finPts.1 y.2)).trans (map_one _))

@[simp] theorem toInf_coe (x : GinfC V) : toInf V x = x :=
  Subtype.ext (by simpa using toInf_mul_toFin (x : GA D V))

variable (V)

theorem continuous_toFin : Continuous (toFin V) := ((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _

theorem continuous_toInf : Continuous (toInf V) := ((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _

end Groups

variable {H X W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [AddCommGroup W] [Module ℂ W] {S : D.what₂.Tau → SPar}

section Components

def HasLocComp (v : HeightOneSpectrum (𝓞 D.host.F)) (δ : Gv V v →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop :=
  IsIsotypic δ (π.comp (embV V v))

def HasArchComp (w : InfinitePlace D.host.F) (δ : Gw V w →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop :=
  IsIsotypic δ (π.comp (embW V w))

def HasFinComp (δ : GfC V →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop := IsIsotypic δ (π.comp (GfC V).subtype)

def HasInfComp (δ : GinfC V →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop :=
  IsIsotypic δ (π.comp (GinfC V).subtype)

def HasLocCompSm (v : HeightOneSpectrum (𝓞 D.host.F)) (σ : Representation ℂ (Gv V v) W)
    (π : GA D V →* (H →L[ℂ] H)) : Prop := IsIsotypicDense σ (π.comp (embV V v))

def HasFinCompSm (σ : Representation ℂ (GfC V) W) (π : GA D V →* (H →L[ℂ] H)) : Prop :=
  IsIsotypicDense σ (π.comp (GfC V).subtype)

def FinHasLocComp {Y : Type} [AddCommGroup Y] [Module ℂ Y] (v : HeightOneSpectrum (𝓞 D.host.F))
    (σv : Representation ℂ (Gv V v) Y) (σ : Representation ℂ (GfC V) W) : Prop := IsIsotypicAlg σv (σ.comp (locFin V v))

abbrev IsFinFactorisation {N : HeightOneSpectrum (𝓞 D.host.F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (σs : ∀ v, Representation ℂ (Gv V v) (N v)) (s : ∀ v, N v) (σ : Representation ℂ (GfC V) W) : Prop :=
  IsRestrTensorAlg (finLoc V) σs s σ

def IsFinInf {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (πf : GfC V →* (Y →L[ℂ] Y))
    (πi : GinfC V →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop := ∃ J, IsTensorMap (toFin V) (toInf V) πf πi π J

abbrev finInf {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (πf : GfC V →* (Y →L[ℂ] Y))
    (πi : GinfC V →* (X →L[ℂ] X)) : GA D V →* (HTensor Y X →L[ℂ] HTensor Y X) := hTensor (toFin V) (toInf V) πf πi

def IsInfTensor {Hs : InfinitePlace D.host.F → Type} [∀ w, NormedAddCommGroup (Hs w)] [∀ w, InnerProductSpace ℂ (Hs w)]
    (δs : ∀ w, Gw V w →* (Hs w →L[ℂ] Hs w)) (δ : GinfC V →* (X →L[ℂ] X)) : Prop :=
  ∃ B, IsRestrTensor (infArch V) δs 0 δ B

abbrev IsCopyFinInf (σ : Representation ℂ (GfC V) W) (δ : GinfC V →* (X →L[ℂ] X)) (ρ : GA D V →* (H →L[ℂ] H))
    (U : Submodule ℂ H) : Prop := IsTensorCopy (GfC V).subtype (GinfC V).subtype σ δ ρ U

variable {V}

theorem isIrrUnitary_dsRep (M : DSModel V S) (τ : D.what₂.Tau) : IsIrrUnitary (dsRep M τ) :=
  ⟨(M.ds τ).1, Orb.isUnitaryRep_dsRep M τ, Orb.isTopIrreducible_dsRep M τ⟩

def HasDSComp (M : DSModel V S) (π : GA D V →* (H →L[ℂ] H)) : Prop := ∀ τ, HasArchComp V (placeOf D τ) (dsRep M τ) π

def IsDSTensor (M : DSModel V S) (δ : GinfC V →* (X →L[ℂ] X)) : Prop :=
  ∃ B, IsRestrTensor (fun τ => infArch V (placeOf D τ)) (dsRep M) 0 δ B

open Classical in

def homDS (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Submodule ℂ (ContinuousMultilinearMap ℂ M.H H) := homPi (fun τ => embW V (placeOf D τ)) (dsRep M) ρ U

open Classical in

def homFinDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Submodule ℂ (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H) :=
  homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) ρ U

open Classical in

def IsCopyFinDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Prop := IsTensorCopyPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) ρ U

open Classical in

theorem mem_homDS {θ : InfF D} (hθ : IsInfFam θ) {M : DSModel V S} {ρ : GA D V →* (H →L[ℂ] H)} {U : Submodule ℂ H}
    {Φ : ContinuousMultilinearMap ℂ M.H H} : Φ ∈ homDS M ρ U ↔ (∀ y, Φ y ∈ U) ∧ ∀ τ,
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y) := by
  refine and_congr_right fun _ => forall_congr' fun τ => ⟨fun h g hg y => ?_, fun h x y => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl hg
    rw [atTau_archEquiv hθ V _ rfl]
    exact h x y
  · exact atTau_archEquiv hθ V (embOverOf D τ) rfl x ▸ h _ (archEquiv_mem_UH V (embOverOf D τ) rfl x) y

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] {πf : GfC V →* (Y →L[ℂ] Y)}
  {πi : GinfC V →* (X →L[ℂ] X)} {π ρ : GA D V →* (H →L[ℂ] H)} {U : Submodule ℂ H}

theorem IsFinInf.isUnitaryRep (h : IsFinInf V πf πi π) (hf : IsUnitaryRep πf) (hi : IsUnitaryRep πi) : IsUnitaryRep π :=
  let ⟨_, h⟩ := h
  h.isUnitaryRep (continuous_toFin V) (continuous_toInf V) hf hi

theorem IsFinInf.uEquiv [CompleteSpace H] (h : IsFinInf V πf πi π) : UEquiv (finInf V πf πi) π := h.choose_spec.uEquiv

def finPart (δ : GinfC V →* (X →L[ℂ] X)) (hU : IsSubrep ρ U) :
    Representation ℂ (GfC V) (homIn δ (ρ.comp (GinfC V).subtype) U) :=
  PRep.sub (postRep X (ρ.comp (GfC V).subtype)) _ fun g T hT => ⟨fun x => hU.2 g _ (hT.1 x), fun k x =>
    (congrArg (ρ g) (hT.2 k x)).trans (DFunLike.congr_fun (((commute_inf_fin k g).map ρ).eq.symm) (T x))⟩

abbrev finPartSm (δ : GinfC V →* (X →L[ℂ] X)) (hU : IsSubrep ρ U) :
    Representation ℂ (GfC V) (smoothPart (finPart δ hU)) := smoothRep (finPart δ hU)

def finPartDS (M : DSModel V S) (hU : IsSubrep ρ U) : Representation ℂ (GfC V) (homDS M ρ U) :=
  PRep.sub (postRepPi M.H (ρ.comp (GfC V).subtype)) _ fun g T hT => ⟨fun x => hU.2 g _ (hT.1 x), fun τ k x =>
    (congrArg (ρ g) (hT.2 τ k x)).trans
      (DFunLike.congr_fun (((commute_inf_fin (archInf V _ k) g).map ρ).eq.symm) (T x))⟩

abbrev finPartDSSm (M : DSModel V S) (hU : IsSubrep ρ U) : Representation ℂ (GfC V) (smoothPart (finPartDS M hU)) :=
  smoothRep (finPartDS M hU)

abbrev finRes (π : GA D V →* (H →L[ℂ] H)) : Representation ℂ (GfC V) H := toRep (π.comp (GfC V).subtype)

end Components

end GlobalTheory.AutMult

end
