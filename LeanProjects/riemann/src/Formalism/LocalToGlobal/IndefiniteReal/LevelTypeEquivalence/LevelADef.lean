import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasFr

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem finHom_eq_one_iff (h : GA D V) : finHom V h = 1 ↔ Lev.finE V h = 1 := by
  unfold Lev.finE
  rw [MonoidHom.comp_apply]
  refine ⟨fun h1 => by rw [h1, map_one], fun h1 => ?_⟩
  have hinj : Function.Injective (Formalism.IndefR.Lev.swapAE D) := by
    intro a b hab
    unfold Formalism.IndefR.Lev.swapAE at hab
    simpa using hab
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g => (Units.val g) i j) h1
  simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Units.val_one] at h2
  apply hinj
  refine Eq.trans h2 ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem brg_mem_GinfC (fr : UI.Frames D V) (x : (UI.instV fr).GA) : UI.brg fr x ∈ GinfC V ↔ x.2 = 1 := by
  unfold GinfC
  rw [MonoidHom.mem_ker, finHom_eq_one_iff, ← Units.val_eq_one]
  have hb := (UI.brg_isBridge fr x).2
  have hz : ∀ z, Formalism.IndefR.Lev.swapAE D (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)
      (AlgHom.id D.host.F D.host.E) z) = (Algebra.TensorProduct.lift ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af D.host.F →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)) (Algebra.TensorProduct.includeLeft : D.host.E →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) (fun _ _ => Commute.all _ _)) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).symm
    | tmul a e => simp [Formalism.IndefR.Lev.swapAE, Algebra.TensorProduct.tmul_mul_tmul]
    | add y w hy hw => erw [map_add, map_add, hy, hw, map_add]
  have key : Units.val (Lev.finE V (UI.brg fr x)) =
      Formalism.L2.SG.AdBridge.ofHAFin (UI.instV fr) (UI.brg fr x) := by
    ext i j
    exact hz _
  rw [key]
  constructor
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := hb.trans h1
    simpa [Units.val_eq_one] using h2
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := by simp [h1]
    exact hb.symm.trans h2

theorem ginf_compact (F : MF.FrA V) (hD : V.IsDefinite) : CompactSpace (UI.instV (MF.toFrames F)).Ginf := by
  have hc : ∀ v : InfinitePlace D.host.F, CompactSpace (Formalism.REAL.UJ ((MF.toFrames F).ε v)) := by
    intro v
    haveI : CompactSpace (UpqT (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).1
        (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).2) := by
      rcases hD (tauE D ((Formalism.L2.Host.tauPl D).symm v)) with h | h
      · rw [h]; infer_instance
      · rw [h]; infer_instance
    exact (MF.phiR F v).toHomeomorph.compactSpace
  exact @Pi.compactSpace _ _ (fun _ => inferInstance) hc

theorem isCompact_GinfC (hS : V.SigOK) (hD : V.IsDefinite) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  have e : (GinfC V : Set (GA D V)) = UI.brg (MF.toFrames F) '' (Set.univ ×ˢ {1}) := by
    ext h
    obtain ⟨x, rfl⟩ := (UI.brg (MF.toFrames F)).surjective h
    rw [SetLike.mem_coe, brg_mem_GinfC]
    constructor
    · intro hx
      exact ⟨x, ⟨trivial, hx⟩, rfl⟩
    · rintro ⟨x', ⟨-, hx'⟩, e'⟩
      have := (UI.brg (MF.toFrames F)).injective e'
      subst this
      exact hx'
  rw [e]
  exact (isCompact_univ.prod isCompact_singleton).image (UI.brg (MF.toFrames F)).continuous

theorem exists_open_compact (hS : V.SigOK) (hD : V.IsDefinite) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ IsCompact (U : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  let fr := MF.toFrames F
  let H : Subgroup (UI.instV fr).Gf :=
    { carrier := (UI.instV fr).Kset
      one_mem' := (Formalism.UG.stabGL (UI.instV fr).Lf).one_mem
      mul_mem' := fun ha hb => (Formalism.UG.stabGL (UI.instV fr).Lf).mul_mem ha hb
      inv_mem' := fun ha => (Formalism.UG.stabGL (UI.instV fr).Lf).inv_mem ha }
  have ho : IsOpen (H : Set (UI.instV fr).Gf) := by
    show IsOpen (UI.instV fr).Kset
    rw [stabilizer_eq_level_subgroup]
    exact (UI.instV fr).topf_open 1 le_rfl
  have hc : IsCompact (H : Set (UI.instV fr).Gf) := Formalism.L2.SG.Closed.AutKCompact_holds (UI.instV fr)
  refine ⟨(Subgroup.prod ⊤ H).map ((UI.brg fr : (UI.instV fr).GA →* GA D V)), ?_, ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_prod, Subgroup.coe_top]
    exact (UI.brg fr).toHomeomorph.isOpenMap _ (isOpen_univ.prod ho)
  · rw [Subgroup.coe_map, Subgroup.coe_prod, Subgroup.coe_top]
    exact (isCompact_univ.prod hc).image (UI.brg fr).continuous

end Formalism.IndefR.Eqv

end
