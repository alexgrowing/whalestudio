import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.AutomorphicForms.FiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.CompanionTheory.BZInd

open GroundTheory.Automorphic.Parabolic (levi levi_le_blockUpper mem_levi sqrtModular invSqrtModular leviIncl
  parabolicInd parabolicIndSpace)
open GroundTheory.Automorphic.Iwasawa (blockUpper)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

abbrev stdE (d : Fin r → ℕ) : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a) := finSigmaFinEquiv

def pos (d : Fin r → ℕ) (i : Fin (∑ a, d a)) : ℕ := ((finSigmaFinEquiv.symm i).1 : ℕ)

theorem pos_stdE (a : Fin r) (x : Fin (d a)) : pos d (stdE d ⟨a, x⟩) = a := by
  simp [pos]

variable (k d) in
theorem blockUpper_le_parab : blockUpper k (∑ a, d a) (pos d) ≤ parab k (stdE d) := by
  intro g hg
  exact hg

variable (k d) in

def leviTo : levi k (∑ a, d a) (pos d) →* Levi k (fun a => Fin (d a)) :=
  (leviProj k (stdE d)).comp (Subgroup.inclusion (levi_le_blockUpper.trans (blockUpper_le_parab k d)))

theorem continuous_leviTo : Continuous (leviTo k d) := by
  unfold leviTo
  rw [MonoidHom.coe_comp]
  exact (GlobalTheory.SmGL.ProdIrr.continuous_leviProj (stdE d)).comp
    (continuous_induced_rng.2 continuous_subtype_val)

theorem leviTo_surjective : Function.Surjective (leviTo k d) := by
  intro g
  have hmem : GlobalTheory.SmGL.leviEmb k (stdE d) g ∈ levi k (∑ a, d a) (pos d) := by
    rw [mem_levi]
    intro i j hij
    exact GlobalTheory.JacquetBlocks.leviEmb_apply_of_blk_ne (stdE d) g (fun h => hij (congrArg Fin.val h))
  refine ⟨⟨_, hmem⟩, ?_⟩
  exact GlobalTheory.JacquetBlocks.leviProj_eq_of_coe_eq (stdE d) _ g rfl

theorem leviTo_leviProj (p : blockUpper k (∑ a, d a) (pos d)) :
    leviTo k d (GroundTheory.Automorphic.Parabolic.leviProj k (∑ a, d a) (pos d) p) =
      leviProj k (stdE d) ⟨p, blockUpper_le_parab k d p.2⟩ := by
  refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
  show (GroundTheory.Automorphic.Parabolic.blockDiagPart k (∑ a, d a) (pos d)
      ((p : GL (Fin (∑ a, d a)) k) : Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) k)) (stdE d ⟨a, i⟩) (stdE d ⟨a, j⟩) =
    ((p : GL (Fin (∑ a, d a)) k) : Matrix (Fin (∑ a, d a)) (Fin (∑ a, d a)) k) (stdE d ⟨a, i⟩) (stdE d ⟨a, j⟩)
  simp [GroundTheory.Automorphic.Parabolic.blockDiagPart, pos_stdE]

variable (k d) in

def invHalf : levi k (∑ a, d a) (pos d) →* ℂˣ :=
  ((invSqrtModular k (∑ a, d a) (pos d)).comp leviIncl).toHomUnits

theorem isSmoothChar_invHalf : IsSmoothChar (invHalf k d) := by
  unfold GlobalTheory.SmGL.IsSmoothChar
  have hopen : IsOpen (((GroundTheory.Automorphic.GLnLocal.integralGL k (∑ a, d a)).comap
      (levi k (∑ a, d a) (pos d)).subtype : Subgroup (levi k (∑ a, d a) (pos d))) :
        Set (levi k (∑ a, d a) (pos d))) := by
    rw [Subgroup.coe_comap]
    exact continuous_subtype_val.isOpen_preimage _ (GroundTheory.Automorphic.GLnLocal.isOpen_integralGL ..)
  refine Subgroup.isOpen_mono (fun m hm => ?_) hopen
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Units.val_one]
  show (invSqrtModular k (∑ a, d a) (pos d)) (leviIncl m) = 1
  exact GroundTheory.Automorphic.Parabolic.invSqrtModular_leviIncl_of_mem m hm

variable (k d) in

def adj : levi k (∑ a, d a) (pos d) →* ℂˣ :=
  invHalf k d * (deltaHalf k (fun a => Fin (d a))).comp (leviTo k d)

private theorem deltaHalf_eq_one_of_integral_lemma_2 (r : ℕ) (d : Fin r → ℕ) (g : Levi k fun a => Fin (d a))
    (hg : ∀ a, g a ∈ GroundTheory.Automorphic.GLnLocal.integralGL k (d a)) :
    deltaHalf k (fun a => Fin (d a)) g = 1 := by
  have hO : ∀ u : kˣ, (u : k) ∈ (ValuativeRel.valuation k).integer →
      ((u⁻¹ : kˣ) : k) ∈ (ValuativeRel.valuation k).integer → GlobalTheory.SplitWeil.nabs k u = 1 := by
    intro u hu hu'
    rw [GlobalTheory.SplitWeil.nabs_eq_one_iff]
    have hu1 : ValuativeRel.valuation k (u : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 hu
    have hu2 : ValuativeRel.valuation k ((u⁻¹ : kˣ) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 hu'
    have h1 : ValuativeRel.valuation k (u : k) * ValuativeRel.valuation k ((u⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine le_antisymm hu1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero k) = _ := h1.symm
      _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
      _ = ValuativeRel.valuation k (u : k) := mul_one _
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one (fun a _ => ?_)
  obtain ⟨x, hx⟩ := hg a
  have hm : ∀ y : GL (Fin (d a)) (ValuativeRel.valuation k).integer,
      ((Matrix.GeneralLinearGroup.det (GroundTheory.Automorphic.GLnLocal.integralGLHom k (d a) y) : kˣ) : k) ∈
        (ValuativeRel.valuation k).integer := fun y => by
    show ((ValuativeRel.valuation k).integer.subtype.mapMatrix (y : Matrix (Fin (d a)) (Fin (d a)) _)).det ∈ _
    rw [← RingHom.map_det]
    exact SetLike.coe_mem _
  have key : GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (g a)) = 1 := by
    rw [← hx]
    refine hO _ (hm x) ?_
    rw [← map_inv, ← map_inv]
    exact hm x⁻¹
  apply Units.ext
  simp [detChar, absPow, key]

private theorem isOpen_ker_deltaHalf_lemma (r : ℕ) (d : Fin r → ℕ) :
    IsOpen ((deltaHalf k (fun a => Fin (d a))).ker : Set (Levi k fun a => Fin (d a))) := by
  let H : Subgroup (Levi k fun a => Fin (d a)) :=
    ⨅ a, (GroundTheory.Automorphic.GLnLocal.integralGL k (d a)).comap
      (Pi.evalMonoidHom (fun a => GL (Fin (d a)) k) a)
  have hH : IsOpen (H : Set (Levi k fun a => Fin (d a))) := by
    rw [Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite (fun a => ?_)
    rw [Subgroup.coe_comap]
    exact (continuous_apply a).isOpen_preimage _ (GroundTheory.Automorphic.GLnLocal.isOpen_integralGL ..)
  refine Subgroup.isOpen_mono (fun g hg => ?_) hH
  rw [MonoidHom.mem_ker]
  exact deltaHalf_eq_one_of_integral_lemma_2 r d g (fun a => (Subgroup.mem_iInf.1 hg) a)

theorem isSmoothChar_adj : IsSmoothChar (adj k d) := by
  unfold GlobalTheory.SmGL.IsSmoothChar
  have h2 : IsOpen (((deltaHalf k (fun a => Fin (d a))).comp (leviTo k d)).ker :
      Set (levi k (∑ a, d a) (pos d))) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (isOpen_ker_deltaHalf_lemma r d).preimage continuous_leviTo
  have h12 := (isSmoothChar_invHalf (k := k) (d := d)).inter h2
  refine Subgroup.isOpen_mono (H₁ := (invHalf k d).ker ⊓
    ((deltaHalf k (fun a => Fin (d a))).comp (leviTo k d)).ker) ?_ (by rw [Subgroup.coe_inf]; exact h12)
  intro x hx
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker]
  show invHalf k d x * (deltaHalf k (fun a => Fin (d a))).comp (leviTo k d) x = 1
  rw [hx.1, hx.2, one_mul]

def carry (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) :
    Representation ℂ (levi k (∑ a, d a) (pos d)) W :=
  twist (ρ.comp (leviTo k d)) (adj k d)

theorem inflate_carry (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)
    (p : blockUpper k (∑ a, d a) (pos d)) (w : W) :
    sqrtModular k (∑ a, d a) (pos d) p •
        carry ρ (GroundTheory.Automorphic.Parabolic.leviProj k (∑ a, d a) (pos d) p) w =
      (deltaHalf k (fun a => Fin (d a)) (leviProj k (stdE d) ⟨p, blockUpper_le_parab k d p.2⟩) : ℂ) •
        ρ (leviProj k (stdE d) ⟨p, blockUpper_le_parab k d p.2⟩) w := by
  have hL := leviTo_leviProj (k := k) (d := d) p
  have hs : sqrtModular k (∑ a, d a) (pos d) p * invSqrtModular k (∑ a, d a) (pos d)
      (leviIncl (GroundTheory.Automorphic.Parabolic.leviProj k (∑ a, d a) (pos d) p)) = 1 := by
    rw [← GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj p]
    exact GroundTheory.Automorphic.Parabolic.sqrtModular_mul_invSqrtModular _
  show sqrtModular k (∑ a, d a) (pos d) p •
      (((adj k d (GroundTheory.Automorphic.Parabolic.leviProj k (∑ a, d a) (pos d) p) : ℂˣ) : ℂ) •
        ρ (leviTo k d (GroundTheory.Automorphic.Parabolic.leviProj k (∑ a, d a) (pos d) p)) w) = _
  rw [hL, smul_smul]
  congr 1
  simp only [adj, invHalf, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul,
    MonoidHom.coe_toHomUnits]
  rw [hL, ← mul_assoc, hs, one_mul]

def toInd (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) :
    IndSp (stdE d) ρ →ₗ[ℂ] parabolicIndSpace k (∑ a, d a) (pos d) (carry ρ) where
  toFun f := ⟨f.1.1, (GroundTheory.Automorphic.Parabolic.mem_parabolicIndSpace _).2
    ⟨fun p g => by
      rw [inflate_carry]
      exact parInd_law (stdE d) ρ f ⟨p, blockUpper_le_parab k d p.2⟩ g,
     GroundTheory.Automorphic.stabilizerOf (ind (parab k (stdE d))
        ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdE d)))) f.1, f.2,
     fun x hx g => congrFun (congrArg Subtype.val hx) g⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toIndMap (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) :
    Representation.IntertwiningMap (parInd (stdE d) ρ)
      (parabolicInd k (∑ a, d a) (pos d) (carry ρ)) where
  toLinearMap := toInd ρ
  isIntertwining' g := by
    refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
    rfl

theorem toIndMap_injective (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) :
    Function.Injective (toIndMap ρ) := by
  intro f g h
  have h1 : ((toIndMap ρ f : parabolicIndSpace k (∑ a, d a) (pos d) (carry ρ)) :
      GL (Fin (∑ a, d a)) k → W) = (toIndMap ρ g : parabolicIndSpace k (∑ a, d a) (pos d) (carry ρ)) :=
    congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h1)

theorem hasFiniteLength_parInd_std (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)
    (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) : HasFiniteLength (parInd (stdE d) ρ) := by
  have hsm : GroundTheory.Automorphic.IsSmooth (carry ρ) := by
    intro v
    have hU : IsOpen ((leviTo k d) ⁻¹' {g | ρ g v = v} ∩
        ((adj k d).ker : Set (levi k (∑ a, d a) (pos d)))) :=
      ((hρ v).preimage continuous_leviTo).inter isSmoothChar_adj
    have h1 : (1 : levi k (∑ a, d a) (pos d)) ∈ (leviTo k d) ⁻¹' {g | ρ g v = v} ∩
        ((adj k d).ker : Set (levi k (∑ a, d a) (pos d))) := by
      refine ⟨?_, (adj k d).ker.one_mem⟩
      show ρ (leviTo k d 1) v = v
      simp
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds h1) ?_)
    rintro x ⟨hx1, hx2⟩
    rw [SetLike.mem_coe, GroundTheory.Automorphic.mem_stabilizerOf]
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx2
    show ((adj k d x : ℂˣ) : ℂ) • ρ (leviTo k d x) v = v
    rw [hx2, Units.val_one, one_smul]
    exact hx1
  have hfl : GlobalTheory.SmGL.HasFiniteLength (carry ρ) :=
    (GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff _ _).2
      ((GlobalTheory.SmGL.hasFiniteLength_comp_iff ρ (leviTo k d) leviTo_surjective).2 hl)
  have hind : GroundTheory.Automorphic.HasFiniteLength (parabolicInd k (∑ a, d a) (pos d) (carry ρ)) :=
    GroundTheory.Automorphic.Parabolic.hasFiniteLength_parabolicInd hsm hfl
  obtain ⟨hgt, hlt⟩ :=
    (GlobalTheory.SmGL.hasFiniteLength_iff_wellFounded (parabolicInd k (∑ a, d a) (pos d) (carry ρ))).1 hind
  haveI := hgt
  haveI := hlt
  rw [GlobalTheory.SmGL.hasFiniteLength_iff_wellFounded]
  let φ : Subrepresentation (parInd (stdE d) ρ) →
      Subrepresentation (parabolicInd k (∑ a, d a) (pos d) (carry ρ)) := fun U =>
    ⟨U.toSubmodule.map (toIndMap ρ).toLinearMap, by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨parInd (stdE d) ρ g x, U.apply_mem_toSubmodule g hx,
        Representation.IntertwiningMap.isIntertwining _ _ (toIndMap ρ) g x⟩⟩
  have hmono : Monotone φ := fun U V h => by
    show U.toSubmodule.map (toIndMap ρ).toLinearMap ≤ V.toSubmodule.map (toIndMap ρ).toLinearMap
    exact Submodule.map_mono h
  have hinj : Function.Injective φ := fun U V h =>
    Subrepresentation.toSubmodule_injective
      (Submodule.map_injective_of_injective (toIndMap_injective ρ)
        (congrArg Subrepresentation.toSubmodule h))
  have hφ : StrictMono φ := hmono.strictMono_of_injective hinj
  exact ⟨hφ.wellFoundedGT, hφ.wellFoundedLT⟩

open GlobalTheory.BlockReorder in

theorem inductionFiniteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W _ _ ρ hρ hl
  apply GlobalTheory.BlockReorder.hasFiniteLength_parInd e ρ
  refine hasFiniteLength_parInd_std (d := GlobalTheory.BlockReorder.blockSize m)
    (ρ.comp (GlobalTheory.BlockReorder.leviMap k e)) ?_ ?_
  · intro v
    exact (hρ v).preimage (GlobalTheory.BlockReorder.continuous_leviMap e)
  · exact (GlobalTheory.SmGL.hasFiniteLength_comp_iff ρ _ (GlobalTheory.BlockReorder.leviMap_surjective e)).2 hl

end GlobalTheory.CompanionTheory.BZInd
