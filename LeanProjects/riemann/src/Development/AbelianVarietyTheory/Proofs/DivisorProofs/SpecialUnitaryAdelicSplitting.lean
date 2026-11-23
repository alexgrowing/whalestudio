import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

namespace GlobalTheory.TamUnf

def restrictProd {G A B : Type} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B] (e : G ≃ₜ* A × B) (S : Subgroup G) (SA : Subgroup A) (SB : Subgroup B)
    (h : ∀ g, g ∈ S ↔ (e g).1 ∈ SA ∧ (e g).2 ∈ SB) : S ≃ₜ* SA × SB where
  toFun g := (⟨(e g.1).1, ((h _).1 g.2).1⟩, ⟨(e g.1).2, ((h _).1 g.2).2⟩)
  invFun p := ⟨e.symm (p.1.1, p.2.1), (h _).2 (by rw [e.apply_symm_apply]; exact ⟨p.1.2, p.2.2⟩)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.1)
  right_inv p := Prod.ext (Subtype.ext (congrArg Prod.fst (e.apply_symm_apply _)))
    (Subtype.ext (congrArg Prod.snd (e.apply_symm_apply _)))
  map_mul' a b := Prod.ext (Subtype.ext (congrArg Prod.fst (map_mul e a.1 b.1)))
    (Subtype.ext (congrArg Prod.snd (map_mul e a.1 b.1)))
  continuous_toFun := Continuous.prodMk
    (Continuous.subtype_mk (continuous_fst.comp (e.continuous.comp continuous_subtype_val)) _)
    (Continuous.subtype_mk (continuous_snd.comp (e.continuous.comp continuous_subtype_val)) _)
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))) _

theorem exists_adelic_split_detOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E),
    ∃ e : SUAdelic σ J ≃ₜ*
        ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ J).subtype).ker : Subgroup (HA (Ainf F) σ J)) ×
          finSU σ J,
      ∀ h, ((HA.mat (Ainf F) σ J (e h).1.1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) =
          ((HA.mat (AF F) σ J h.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
            (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ∧
        ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J (e h).2.1 : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) =
          finMat σ J h.1 := by
  intro F E _ _ _ _ _ σ M J
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hinf : ∀ k : HA (Ainf F) σ J,
      k ∈ ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ J).subtype).ker : Subgroup (HA (Ainf F) σ J)) ↔
      ((HA.mat (Ainf F) σ J k : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).det = 1 :=
    fun k => by
      show Matrix.GeneralLinearGroup.det ((HR (Ainf F) σ J).subtype k) = 1 ↔ _
      rw [Units.ext_iff]
      rfl
  have key : ∀ g, g ∈ SUAdelic σ J ↔
      (e0 g).1 ∈ ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ J).subtype).ker : Subgroup (HA (Ainf F) σ J)) ∧
        (e0 g).2 ∈ finSU σ J := fun g => by
    rw [hinf, mem_finSU, (he0 g).1, (he0 g).2, GlobalTheory.Published.StrongApprox.mem_SUAdelic]
    have h1 := pInf.map_det (HA.mat (AF F) σ J g).1
    have h2 := pFin.map_det (HA.mat (AF F) σ J g).1
    constructor
    · intro hg
      have hg' : (HA.mat (AF F) σ J g).1.det = 1 := hg
      rw [hg', map_one] at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨a, b⟩
      show (HA.mat (AF F) σ J g).1.det = 1
      refine e.injective (Prod.ext ?_ ?_)
      · rw [(he _).1, (he _).1]
        exact (h1.trans a).trans (map_one pInf).symm
      · rw [(he _).2, (he _).2]
        exact (h2.trans b).trans (map_one pFin).symm
  exact ⟨restrictProd e0 _ _ _ key, fun h => ⟨(he0 h.1).2, (he0 h.1).1⟩⟩

end GlobalTheory.TamUnf
