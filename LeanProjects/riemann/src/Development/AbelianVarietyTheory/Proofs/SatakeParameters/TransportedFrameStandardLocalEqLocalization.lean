import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrameLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by funext l; simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

theorem seamVec_apply {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (x : Sp X.E n) (l : Fin n) :
    seamVec s n x l = s.iE (x l) := rfl

theorem seamVec_injective {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : Function.Injective (seamVec s n) := by
  intro x y hxy
  funext l
  exact s.iE.injective (congrFun hxy l)

theorem seam_lat_eq_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat M = M.map (seamVec s n) := by
  unfold Seam.lat
  rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = seamVec s n '' M from rfl,
    ← Submodule.map_coe]
  exact Submodule.span_eq _

theorem localization_map_seamVec {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map (seamVec s n)) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map (seamVec s n) := by
  set ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE with hψ
  ext x
  constructor
  · rintro ⟨r, hr, z, hz, hzx⟩
    have hfy : seamVec s n (fun l => s.iE.symm (x l)) = x := by
      funext l
      simp [seamVec_apply]
    refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
    · intro hm
      apply hr
      have := (mem_seamP s P (ψ.symm r)).2 hm
      simpa [ψ] using this
    · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
        apply seamVec_injective s n
        rw [(seamVec s n).map_smulₛₗ, hfy, hzx]
        show ψ (ψ.symm r) • x = r • x
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact hz
  · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
    refine ⟨ψ r, ?_, r • y, hy, ?_⟩
    · intro hm
      exact hr ((mem_seamP s P r).1 hm)
    · rw [(seamVec s n).map_smulₛₗ]
      rfl

theorem stdLat_map_seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    (stdLat X.E n).map (seamVec s n) = stdLat D.host.E n := by
  ext y
  rw [Submodule.mem_map]
  unfold Formalism.L2.Col.stdLat
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hx l)
    refine (Submodule.mem_one).2 ⟨RingOfIntegers.mapRingEquiv s.iE r, ?_⟩
    rw [seamVec_apply, ← hr]
    rfl
  · intro hy
    refine ⟨fun l => s.iE.symm (y l), fun l => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hy l)
      refine (Submodule.mem_one).2 ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, ?_⟩
      show _ = s.iE.symm (y l)
      rw [← hr]
      rfl
    · funext l
      simp [seamVec_apply]

theorem mvL_seamGL_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    mvL (seamGL s g) (M.map (seamVec s n)) = (M.map (g.toLinearMap.restrictScalars (𝓞 X.E))).map (seamVec s n) := by
  unfold mvL
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    show seamVec s n (g x) = toLE (seamGL s g) (seamVec s n x)
    rw [toLE_apply]
    exact (seamGL_mulVec s g x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨seamVec s n x, ⟨x, hx, rfl⟩, ?_⟩
    show toLE (seamGL s g) (seamVec s n x) = seamVec s n (g x)
    rw [toLE_apply]
    exact seamGL_mulVec s g x

theorem seamGL_stdAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) →
    mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  intro D X s n P g N hg
  have hstd : (stdAt X.E n P).map (g.toLinearMap.restrictScalars (𝓞 X.E)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).2 hx
    · intro hy
      refine ⟨g.symm y, (hg _).1 (by simpa using hy), by simp⟩
  show mvL (seamGL s g) (Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (stdLat D.host.E n)) = _
  rw [← stdLat_map_seamVec s n, localization_map_seamVec, mvL_seamGL_map, ← stdAt, hstd, seam_lat_eq_map, localization_map_seamVec]

end GlobalTheory.FrameLat

end
