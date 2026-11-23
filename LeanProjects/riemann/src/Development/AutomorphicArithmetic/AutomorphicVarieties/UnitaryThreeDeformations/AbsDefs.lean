import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal

noncomputable section

open MvPowerSeries UpperTheory.V.Alg

namespace UpperTheory.V.UnitaryThreeInertia.Abs

section Free

variable (O : Type) [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)

theorem freeOrigin : (WPres.free O wt).HasOrigin := fun f hf => by
  have : f = 0 := hf
  rw [this, map_zero]

abbrev FA : Type := (WPres.free O wt).A

abbrev Fgr : ℤ → Submodule O (FA O wt) := (WPres.free O wt).gr

def x0 : FA O wt →ₐ[O] O := (WPres.free O wt).originA (freeOrigin O wt)

variable {O wt}

abbrev ser (f : FA O wt) : MvPowerSeries σ O := f.1

theorem weightedSeriesOrigin_apply (f : FA O wt) : x0 O wt f = constantCoeff (ser f) :=
  (WPres.free O wt).origin_π (freeOrigin O wt) f.1

theorem free_part (j : ℤ) : (WPres.free O wt).part j = wtPart O wt j := by
  ext f
  exact ⟨fun ⟨g, hg, e⟩ => (show g = f from e) ▸ hg, fun hf => ⟨f, hf, rfl⟩⟩

theorem mem_Fgr {j : ℤ} {f : FA O wt} : f ∈ Fgr O wt j ↔ ser f ∈ wtPart O wt j := by
  rw [← free_part]; rfl

def mkF {j : ℤ} (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) : FA O wt :=
  ⟨f, (WPres.free O wt).part_le_A (j := j) ⟨f, hf, rfl⟩⟩

theorem mkF_mem {j : ℤ} (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) : mkF f hf ∈ Fgr O wt j := mem_Fgr.2 hf

@[simp] theorem ser_mkF {j : ℤ} (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) : ser (mkF f hf) = f := rfl

end Free

section ToA

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R)

theorem π_mem_A (f : FA O W.wt) : W.π (ser f) ∈ W.A := by
  refine Submodule.iSup_induction (WPres.free O W.wt).part (motive := fun g => W.π g ∈ W.A) f.2 (fun j g hg => ?_)
    (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
  rw [free_part] at hg
  exact W.part_le_A ⟨g, hg, rfl⟩

def toA : FA O W.wt →ₐ[O] W.A := (W.π.comp (WPres.free O W.wt).A.val).codRestrict W.A (π_mem_A W)

theorem coe_toA (f : FA O W.wt) : (toA W f : R) = W.π (ser f) := rfl

theorem toA_mem {j : ℤ} {f : FA O W.wt} (hf : f ∈ Fgr O W.wt j) : (toA W f : R) ∈ W.part j :=
  ⟨ser f, mem_Fgr.1 hf, rfl⟩

theorem exists_toA {j : ℤ} {y : R} (hy : y ∈ W.part j) : ∃ f ∈ Fgr O W.wt j, toA W f = ⟨y, W.part_le_A hy⟩ := by
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨mkF g hg, mkF_mem g hg, rfl⟩

theorem toA_surjective : Function.Surjective (toA W) := by
  rintro ⟨y, hy⟩
  have : ∃ f, (toA W f : R) = y := by
    refine Submodule.iSup_induction W.part (motive := fun y => ∃ f, (toA W f : R) = y) hy (fun j y hy => ?_)
      ⟨0, by simp⟩ (fun a b ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f + g, by simp [hf, hg]⟩)
    obtain ⟨f, -, hf⟩ := exists_toA W hy
    exact ⟨f, congrArg Subtype.val hf⟩
  obtain ⟨f, hf⟩ := this
  exact ⟨f, Subtype.ext hf⟩

theorem origin_toA (h : W.HasOrigin) (f : FA O W.wt) : W.origin h (toA W f : R) = x0 O W.wt f := by
  rw [weightedSeriesOrigin_apply, coe_toA, W.origin_π]

end ToA

end UpperTheory.V.UnitaryThreeInertia.Abs
