import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GlueMove

open Formalism.L2.SG.Pf.Cnt

section Gen

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_gmap (n : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap n L ↔ n.symm x ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨n.symm x, hx, n.apply_symm_apply x⟩

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  rw [mem_gmap, mem_gmap, mem_gmap]
  rfl

theorem gmap_symm_gmap (n : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap n.symm (Formalism.HermitianLatticesTheory.gmap n L) = L := by
  ext x
  rw [mem_gmap, mem_gmap, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

theorem gmap_gmap_symm (n : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.gmap n.symm L) = L := by
  ext x
  rw [mem_gmap, mem_gmap, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

theorem gmap_injective (n : V ≃ₗ[K] V) : Function.Injective (Formalism.HermitianLatticesTheory.gmap (R := 𝓞 K) n) := by
  intro L L' hLL
  rw [← gmap_symm_gmap n L, hLL, gmap_symm_gmap]

theorem linearEquiv_map_smul_ringOfIntegers (n : V ≃ₗ[K] V) (s : 𝓞 K) (x : V) : n (s • x) = s • n x := by
  rw [← algebraMap_smul K s x, map_smul, algebraMap_smul]

theorem gmap_span (n : V ≃ₗ[K] V) (S : Set V) :
    Formalism.HermitianLatticesTheory.gmap n (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K) (n '' S) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_span]
  rfl

theorem gmap_sup (n : V ≃ₗ[K] V) (L L' : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap n (L ⊔ L') = Formalism.HermitianLatticesTheory.gmap n L ⊔ Formalism.HermitianLatticesTheory.gmap n L' := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_sup]

theorem gmap_iInf {ι : Type} (n : V ≃ₗ[K] V) (f : ι → Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap n (⨅ i, f i) = ⨅ i, Formalism.HermitianLatticesTheory.gmap n (f i) := by
  ext x
  simp only [mem_gmap, Submodule.mem_iInf]

theorem locP_gmap (n : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) [p.IsPrime] (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.gmap n L) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ p L) := by
  ext x
  rw [mem_gmap]
  show (∃ s ∈ p.primeCompl, s • x ∈ Formalism.HermitianLatticesTheory.gmap n L) ↔ ∃ s ∈ p.primeCompl, s • n.symm x ∈ L
  simp only [mem_gmap, linearEquiv_map_smul_ringOfIntegers]

theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars]

theorem dual_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.gmap n L) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.dual h L) := by
  have hiso : ∀ x y, h (n x) (n y) = h x y := hn
  ext x
  rw [mem_gmap, mem_dual, mem_dual]
  constructor
  · intro hx y hy
    have := hx (n y) (by rw [mem_gmap, LinearEquiv.symm_apply_apply]; exact hy)
    rwa [← n.apply_symm_apply x, hiso] at this
  · intro hx y hy
    rw [mem_gmap] at hy
    have := hx _ hy
    rwa [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this

theorem isLattice_gmap (n : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap n L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have hspan : Submodule.span K ((Formalism.HermitianLatticesTheory.gmap n L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set V)).map (n : V →ₗ[K] V) := by
    rw [Submodule.map_span]
    rfl
  rw [hspan, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem gmap_inf_map (n : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (U : Submodule K V) :
    Formalism.HermitianLatticesTheory.gmap n Λ ⊓ (U.map (n : V →ₗ[K] V)).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap n (Λ ⊓ U.restrictScalars (𝓞 K)) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_gmap, Submodule.mem_map_equiv]

theorem gmap_symm_inf (n : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (U : Submodule K V) :
    Formalism.HermitianLatticesTheory.gmap n.symm Λ ⊓ U.restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap n.symm (Λ ⊓ (U.map (n : V →ₗ[K] V)).restrictScalars (𝓞 K)) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_gmap, Submodule.mem_map_equiv,
    LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

end Gen

end GlobalTheory.GlueMove

namespace GlobalTheory.GlueMove

open Formalism.L2.SG.Pf.Cnt

section Gen2

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isUnimodular_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (hL : Formalism.HermitianLatticesTheory.IsUnimodular h L) :
    Formalism.HermitianLatticesTheory.IsUnimodular h (Formalism.HermitianLatticesTheory.gmap n L) := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hL ⊢
  rw [dual_gmap h n hn, hL]

theorem symm_mem_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h) :
    n.symm ∈ Formalism.HermitianLatticesTheory.isom h := by
  have hiso : ∀ x y, h (n x) (n y) = h x y := hn
  intro x y
  rw [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem glueSet_move (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (M Λ : Submodule (𝓞 K) V) (hΛ : Λ ∈ GlueSet h U M) :
    Formalism.HermitianLatticesTheory.gmap n Λ ∈ GlueSet h (U.map (n : V →ₗ[K] V)) (Formalism.HermitianLatticesTheory.gmap n M) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  exact ⟨isLattice_gmap n Λ h1, isUnimodular_gmap h n hn Λ h2, by rw [gmap_inf_map, h3]⟩

theorem glueSet_back (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (M Λ : Submodule (𝓞 K) V)
    (hΛ : Λ ∈ GlueSet h (U.map (n : V →ₗ[K] V)) (Formalism.HermitianLatticesTheory.gmap n M)) :
    Formalism.HermitianLatticesTheory.gmap n.symm Λ ∈ GlueSet h U M := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  exact ⟨isLattice_gmap n.symm Λ h1, isUnimodular_gmap h n.symm (symm_mem_isom h n hn) Λ h2,
    by rw [gmap_symm_inf, h3, gmap_symm_gmap]⟩

theorem isomFix_conj (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (g : V ≃ₗ[K] V) (hg : g ∈ isomFix h U) :
    n * g * n.symm ∈ isomFix h (U.map (n : V →ₗ[K] V)) := by
  have hiso : ∀ x y, h (n x) (n y) = h x y := hn
  have hsym : ∀ x y, h (n.symm x) (n.symm y) = h x y := symm_mem_isom h n hn
  obtain ⟨hgi, hgU⟩ := hg
  have hgiso : ∀ x y, h (g x) (g y) = h x y := hgi
  refine ⟨?_, ?_⟩
  · intro x y
    show h (n (g (n.symm x))) (n (g (n.symm y))) = h x y
    rw [hiso, hgiso, hsym]
  · intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    show n (g (n.symm (n u₀))) = n u₀
    rw [LinearEquiv.symm_apply_apply, hgU u₀ hu₀]

theorem isomFix_unconj (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (g : V ≃ₗ[K] V) (hg : g ∈ isomFix h (U.map (n : V →ₗ[K] V))) :
    n.symm * g * n ∈ isomFix h U := by
  have hiso : ∀ x y, h (n x) (n y) = h x y := hn
  have hsym : ∀ x y, h (n.symm x) (n.symm y) = h x y := symm_mem_isom h n hn
  obtain ⟨hgi, hgU⟩ := hg
  have hgiso : ∀ x y, h (g x) (g y) = h x y := hgi
  refine ⟨?_, ?_⟩
  · intro x y
    show h (n.symm (g (n x))) (n.symm (g (n y))) = h x y
    rw [hsym, hgiso, hiso]
  · intro u hu
    show n.symm (g (n u)) = u
    rw [hgU (n u) (Submodule.mem_map_of_mem hu), LinearEquiv.symm_apply_apply]

theorem gmap_conj (n g : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (n * g * n.symm) (Formalism.HermitianLatticesTheory.gmap n Λ) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  rw [gmap_mul, gmap_mul, gmap_symm_gmap]

theorem gmap_unconj (n g : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (n.symm * g * n) Λ = Formalism.HermitianLatticesTheory.gmap n.symm (Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.gmap n Λ)) := by
  rw [gmap_mul, gmap_mul]

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    stabFix h U Λ ≃ stabFix h (U.map (n : V →ₗ[K] V)) (Formalism.HermitianLatticesTheory.gmap n Λ) where
  toFun g := ⟨n * g.1 * n.symm, isomFix_conj h n hn U g.1 g.2.1, by rw [gmap_conj, g.2.2]⟩
  invFun g := ⟨n.symm * g.1 * n, isomFix_unconj h n hn U g.1 g.2.1, by
    rw [gmap_unconj, g.2.2, gmap_symm_gmap]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    show n.symm (n (g.1 (n.symm (n x)))) = g.1 x
    simp
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    show n (n.symm (g.1 (n (n.symm x)))) = g.1 x
    simp

theorem card_stabFix_move (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    Nat.card (stabFix h (U.map (n : V →ₗ[K] V)) (Formalism.HermitianLatticesTheory.gmap n Λ)) = Nat.card (stabFix h U Λ) := (Nat.card_congr (stabEquiv h n hn U Λ)).symm

theorem isGlueReps_move (h : V →ₗ⋆[K] V →ₗ[K] K) (n : V ≃ₗ[K] V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (M : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V))
    (hs : IsGlueReps h U M s) :
    IsGlueReps h (U.map (n : V →ₗ[K] V)) (Formalism.HermitianLatticesTheory.gmap n M) (s.image (Formalism.HermitianLatticesTheory.gmap n)) := by
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨Λ₀, h₀, rfl⟩ := Finset.mem_image.mp hΛ
    exact glueSet_move h n hn U M Λ₀ (hs1 Λ₀ h₀)
  · intro Λ hΛ
    obtain ⟨Λ₀, ⟨h₀, g, hg, hgΛ⟩, huniq⟩ := hs2 _ (glueSet_back h n hn U M Λ hΛ)
    refine ⟨Formalism.HermitianLatticesTheory.gmap n Λ₀, ⟨Finset.mem_image_of_mem _ h₀, n * g * n.symm,
      isomFix_conj h n hn U g hg, ?_⟩, ?_⟩
    · rw [gmap_conj, hgΛ, gmap_gmap_symm]
    · rintro Λ₂ ⟨hΛ₂, g₂, hg₂, hg₂Λ⟩
      obtain ⟨Λ₃, h₃, rfl⟩ := Finset.mem_image.mp hΛ₂
      have key : Λ₃ = Λ₀ := huniq Λ₃ ⟨h₃, n.symm * g₂ * n, isomFix_unconj h n hn U g₂ hg₂,
        by rw [gmap_unconj, hg₂Λ]⟩
      rw [key]
  · intro Λ hΛ
    obtain ⟨Λ₀, h₀, rfl⟩ := Finset.mem_image.mp hΛ
    haveI : Finite (stabFix h U Λ₀) := (hs3 Λ₀ h₀).to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv h n hn U Λ₀))

end Gen2

end GlobalTheory.GlueMove

namespace GlobalTheory.GlueMove

open Formalism.L2.SG.Pf.Cnt

variable {D : D7}

theorem fvec_move {T : D.host.E} (F G : LFlag (VS D) D.R.rS T) (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) : G.fl.fvec = fun a => n (F.fl.fvec a) := by
  funext a
  exact hG a

theorem e_move {T : D.host.E} (F G : LFlag (VS D) D.R.rS T) (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) (i : Fin D.R.rS) : G.fl.e i = n (F.fl.e i) := by
  have := hG i.castSucc
  simpa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using this

theorem z_move {T : D.host.E} (F G : LFlag (VS D) D.R.rS T) (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) : G.fl.z = n F.fl.z := by
  have := hG (Fin.last _)
  simpa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using this

theorem upair_move {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) (hG' : ∀ a, frame G' a = n (frame F' a)) :
    UPair D G.fl G' = (UPair D F.fl F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  unfold Formalism.L2.SG.Pf.Cnt.UPair
  rw [Submodule.map_span, Set.image_union, ← Set.range_comp, ← Set.range_comp,
    fvec_move F G n hG, fvec_move F' G' n hG']
  rfl

theorem xs_move {T : D.host.E} (F G : LFlag (VS D) D.R.rS T) (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) : XS D G.fl = Formalism.HermitianLatticesTheory.gmap n (XS D F.fl) := by
  unfold Formalism.MainNotions.S.XS
  rw [gmap_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • F.fl.e a, ⟨a, x, hx, rfl⟩, by rw [map_smul, e_move F G n hG]⟩
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by rw [map_smul, e_move F G n hG]⟩

theorem uus_move {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) (hG' : ∀ a, frame G' a = n (frame F' a)) :
    UUS D G.fl G' = Formalism.HermitianLatticesTheory.gmap n (UUS D F.fl F') := by
  unfold Formalism.L2.SG.Pf.Cnt.UUS
  rw [gmap_sup, gmap_sup, gmap_sup, gmap_span, gmap_span, Set.image_singleton, Set.image_singleton,
    xs_move F G n hG, xs_move F' G' n hG', z_move F G n hG, z_move F' G' n hG']

theorem mmg_move {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) (hG' : ∀ a, frame G' a = n (frame F' a)) :
    MMg D G.fl G' = Formalism.HermitianLatticesTheory.gmap n (MMg D F.fl F') := by
  unfold Formalism.L2.SG.Pf.Cnt.MMg
  rw [gmap_span, Set.image_union, ← Set.range_comp, ← Set.range_comp,
    fvec_move F G n hG, fvec_move F' G' n hG']
  congr 2
  congr 1
  funext b
  simp [map_sub, map_smul]

theorem mmof_move {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D)
    (hG : ∀ a, frame G a = n (frame F a)) (hG' : ∀ a, frame G' a = n (frame F' a)) :
    MMof D G.fl G' = Formalism.HermitianLatticesTheory.gmap n (MMof D F.fl F') := by
  unfold Formalism.L2.SG.Pf.Cnt.MMof
  rw [gmap_iInf]
  congr 1
  funext P
  split_ifs
  · rw [mmg_move F G F' G' n hG hG', locP_gmap]
  · rw [uus_move F G F' G' n hG hG', locP_gmap]

end GlobalTheory.GlueMove

namespace GlobalTheory.GlueMove

open Formalism.L2.SG.Pf.Cnt

theorem glue_move : ∀ (D : D7) (T T' : D.host.E) (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = n (frame F a)) → (∀ a, frame G' a = n (frame F' a)) → ∀ s : Finset (LV D), Glue F F' s → ∃ s' : Finset (LV D), Glue G G' s' ∧ glueSum G G' s' = glueSum F F' s := by
  intro D T T' F G F' G' n hn hG hG' s hs
  refine ⟨s.image (Formalism.HermitianLatticesTheory.gmap n), ?_, ?_⟩
  · unfold GlobalTheory.GenMass.Glue at hs ⊢
    rw [upair_move F G F' G' n hG hG', mmof_move F G F' G' n hG hG']
    exact isGlueReps_move _ n hn _ _ _ hs
  · unfold GlobalTheory.GenMass.glueSum
    rw [Finset.sum_image (fun x _ y _ hxy => gmap_injective n hxy)]
    refine Finset.sum_congr rfl fun Λ _ => ?_
    rw [upair_move F G F' G' n hG hG', card_stabFix_move _ n hn]

end GlobalTheory.GlueMove
