import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFramesTransportLocalLatticeIsometryStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTransport

section General

variable {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

theorem conv_map (j : G ≃ₜ* G') (μ : Measure G) (f g : G → ℂ) :
    GlobalTheory.AutomorphicL2Unitary.conv (μ.map j) (f ∘ j.symm) (g ∘ j.symm) = GlobalTheory.AutomorphicL2Unitary.conv μ f g ∘ j.symm := by
  funext y
  rw [show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl]
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, Function.comp_apply]
  rw [integral_map_equiv]
  congr 1
  funext x
  change f (j.symm (j x)) * g (j.symm ((j x)⁻¹ * y)) = _
  rw [map_mul, map_inv, j.symm_apply_apply]

theorem typeIdem_map {Q Q' W : Type} [Group Q] [Group Q'] [AddCommGroup W] [Module ℂ W]
    (j : G ≃ₜ* G') (μ : Measure G) {K : Subgroup G} {K' : Subgroup G'} (hK : ∀ g, j g ∈ K' ↔ g ∈ K)
    (r : K →* Q) (r' : K' →* Q') (φ : Q' →* Q) (τ : Representation ℂ Q W)
    (hr : ∀ (k : K) (k' : K'), (k' : G') = j k → φ (r' k') = r k) :
    GlobalTheory.Orb.typeIdem (μ.map j) r' (τ.comp φ) = GlobalTheory.Orb.typeIdem μ r τ ∘ j.symm := by
  funext y
  have hv : (μ.map j).real K' = μ.real K := by
    rw [Measure.real, Measure.real, show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 2
    ext x
    exact hK x
  have hy : ∀ y, y ∈ K' ↔ j.symm y ∈ K := fun y => by
    rw [← hK, j.apply_symm_apply]
  simp only [GlobalTheory.Orb.typeIdem, Function.comp_apply]
  by_cases hg : j.symm y ∈ K
  · rw [dif_pos ((hy y).2 hg), dif_pos hg, hv]
    simp only [Representation.character, MonoidHom.comp_apply,
      hr ⟨j.symm y, hg⟩ ⟨y, (hy y).2 hg⟩ (j.apply_symm_apply y).symm]
  · rw [dif_neg (mt (hy y).1 hg), dif_neg hg]

theorem isIrreducible_comp_mulEquiv {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  let e : Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        have h := U.apply_mem_toSubmodule (φ.symm g) hv
        simpa using h⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

end General

def glCast {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] : GL (Fin n') k ≃* GL (Fin n) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (finCongr hr)).toMulEquiv

theorem glCast_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n') k) (a b : Fin n) :
    (glCast hr k g : Matrix (Fin n) (Fin n) k) a b = (g : Matrix (Fin n') (Fin n') k) (Fin.cast hr.symm a) (Fin.cast hr.symm b) :=
  rfl

theorem glCast_symm_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n) k) (a b : Fin n') :
    ((glCast hr k).symm g : Matrix (Fin n') (Fin n') k) a b = (g : Matrix (Fin n) (Fin n) k) (Fin.cast hr a) (Fin.cast hr b) :=
  rfl

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} {v : HeightOneSpectrum (𝓞 F)}
  (hr : n' = n) (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hK : ∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v)
  (s : SplitAt σ J L v) (s' : SplitAt σ J' L' v)
  (he : ∀ g (a b : Fin n'), (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr))
include he

include hK in

theorem mem_iwahori_iff (g : GLoc σ J v) : j g ∈ s'.iwahori ↔ g ∈ s.iwahori := by
  rw [s'.mem_iwahori, s.mem_iwahori, hK]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · have := h (a.cast hr.symm) (b.cast hr.symm) hab
    rwa [he, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_eq_self] at this
  · rw [he]
    exact h _ _ hab

theorem map_diag (t : Fin n → (Fv F v)ˣ) : j (s.diag t) = s'.diag fun i => t (i.cast hr) := by
  apply s'.equiv.injective
  ext a b
  rw [he]
  simp only [SplitAt.diag, ContinuousMulEquiv.apply_symm_apply, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply,
    Fin.cast_inj]

include hK in

theorem mem_iwahoriCoset_iff (t : Fin n → (Fv F v)ˣ) (g : GLoc σ J v) :
    j g ∈ s'.iwahoriCoset (fun i => t (i.cast hr)) ↔ g ∈ s.iwahoriCoset t := by
  simp only [SplitAt.iwahoriCoset, DoubleCoset.mem_doubleCoset, ← map_diag hr j s s' he]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨j.symm a, (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using ha), j.symm b,
      (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using hb), j.injective ?_⟩
    simp [e, map_mul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨j a, (mem_iwahori_iff hr j hK s s' he _).2 ha, j b, (mem_iwahori_iff hr j hK s s' he _).2 hb, by
      simp [map_mul]⟩

include hK in
theorem cosetFn_transfer (t : Fin n → (Fv F v)ˣ) :
    s'.cosetFn (fun i => t (i.cast hr)) = s.cosetFn t ∘ j.symm := by
  funext y
  obtain ⟨g, rfl⟩ := j.surjective y
  change (s'.iwahoriCoset _).indicator 1 (j g) = (s.iwahoriCoset t).indicator 1 (j.symm (j g))
  rw [j.symm_apply_apply]
  by_cases h : g ∈ s.iwahoriCoset t
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_iwahoriCoset_iff hr j hK s s' he t g).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (mem_iwahoriCoset_iff hr j hK s s' he t g).1 h)]

end Local

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Types

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (hr : n' = n)

def moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) : TypeData σ J' L' where
  S := T.S
  frame := fr
  W := T.W
  τ := fun v => (T.τ v).comp (glCast hr (ResF v.1)).toMonoidHom
  irred := fun v => isIrreducible_comp_mulEquiv _ _ (T.irred v)

theorem noFixed_moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) (h : NoFixed T) :
    NoFixed (moveTypes hr T fr) := by
  refine ⟨h.1, fun a ha0 han => ?_⟩
  obtain ⟨v, hv⟩ := h.2 a ha0 (by omega)
  refine ⟨v, fun y hy => hv y fun g hg => ?_⟩
  have := hy ((glCast hr (ResF v.1)).symm g) (fun i k hik => ?_)
  · change T.τ v (glCast hr _ ((glCast hr _).symm g)) y = y at this
    rwa [MulEquiv.apply_symm_apply] at this
  · rw [glCast_symm_apply, hg _ _ hik]
    simp [Matrix.one_apply, Fin.cast_inj]

end Types

set_option maxHeartbeats 1000000 in

theorem isTestFin_transport : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  intro D V V' hr j hj
  have h := fun v => GlobalTheory.T.splitFrames_transport_localLatticeIsometry D V V' hr v (j v) (hj v)
  refine ⟨fun v g => (h v).1 g, fun T U => ?_⟩
  choose fr hfr1 hfr2 using fun v => (h v).2
  refine ⟨moveTypes hr T (fun v => fr v (T.frame v)), ⟨U.u, fr U.u U.frame, U.ϖ, U.unif⟩,
    noFixed_moveTypes hr T _, fun μf ff hf => ?_⟩
  obtain ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩ := hf
  have hid : ∀ v : T.S, (moveTypes hr T fun v => fr v (T.frame v)).idem (fun v => (μf v).map (j v)) v =
      T.idem μf v ∘ (j v).symm := fun v =>
    typeIdem_map (j v) (μf v) ((h v).1 ·) (T.frame v).red (fr v (T.frame v)).red (glCast hr (ResF v.1)).toMonoidHom
      (T.τ v) fun k k' e => Units.ext (Matrix.ext fun a b => by
        show (glCast hr (ResF v.1) ((fr v (T.frame v)).red k')).1 a b = ((T.frame v).red k).1 a b
        rw [glCast_apply, hfr2 v (T.frame v) k k' e]
        simp)
  refine ⟨hu, fun v => ?_, ⟨fun i => t (i.cast hr), ?_, ?_⟩,
    fun v hv hv' => comp_mem_SB (h3 v hv hv') (j v).symm.toHomeomorph, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h1 v
    refine ⟨φ ∘ (j v).symm, comp_mem_SB hφ (j v).symm.toHomeomorph, ?_⟩
    have e1 := conv_map (j v) (μf v) (conv (μf v) (T.idem μf v) φ) (T.idem μf v)
    have e2 := conv_map (j v) (μf v) (T.idem μf v) φ
    have e3 := (congrArg (fun X => conv ((μf v).map (j v)) X (T.idem μf v ∘ (j v).symm)) e2).trans e1
    rewrite [hid v]
    exact (congrArg (· ∘ (j v).symm) e).trans e3.symm
  · obtain ⟨a, ha, rfl⟩ := ht
    exact ⟨fun i => a (i.cast hr), fun x y hxy => ha hxy, rfl⟩
  · show ff U.u ∘ (j U.u).symm = _
    rw [h2]
    exact (cosetFn_transfer hr (j U.u) ((h U.u).1 ·) U.frame _ (hfr1 U.u U.frame) t).symm
  · exact ((IsTestFin.isFinFamily ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩).transfer j (.of_forall fun v g => (h v).1 g)).2

end GlobalTheory.LatTransport
