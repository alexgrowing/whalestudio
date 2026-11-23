import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap finiteAdeleMap_algebraMap)
open GlobalTheory.LFun (KGL)

namespace UpperTheory.Gal.CertificateRingHomMap

def Sim {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) : Subgroup (GL (Fin n) A × Bˣ) where
  carrier := {p | (p.1.val.map σ)ᵀ * p.1.val = i p.2 • (1 : Matrix (Fin n) (Fin n) A)}
  one_mem' := by simp [Matrix.map_one]
  mul_mem' := by
    rintro ⟨g, s⟩ ⟨h, t⟩ hg hh
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.map_mul, transpose_mul, map_mul] at hg hh ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ g.val, hg, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, hh, smul_smul]
  inv_mem' := by
    rintro ⟨g, s⟩ hg
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv] at hg ⊢
    have h1 : ((g⁻¹).val.map σ)ᵀ * (g.val.map σ)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    have h2 : i (s⁻¹ : Bˣ) * i s = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have h3 : g.val = i s • ((g⁻¹).val.map σ)ᵀ := by
      rw [← Matrix.one_mul g.val, ← h1, Matrix.mul_assoc, hg, Matrix.mul_smul, Matrix.mul_one]
    calc ((g⁻¹).val.map σ)ᵀ * (g⁻¹).val = i (s⁻¹ : Bˣ) • ((i s • ((g⁻¹).val.map σ)ᵀ) * (g⁻¹).val) := by
          rw [smul_mul_assoc, smul_smul, h2, one_smul]
      _ = _ := by rw [← h3, Units.mul_inv]

theorem mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ} :
    p ∈ Sim σ i n ↔ (p.1.val.map σ)ᵀ * p.1.val = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := Iff.rfl

abbrev Plc (E : Type) [Field E] : Type := HeightOneSpectrum (𝓞 E)

abbrev AfQ : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

abbrev GUf : Subgroup (GL (Fin n) (Af E) × AfQˣ) := Sim (conjFin (conjE E)) (finiteAdeleMap ℚ E) n

def Gam0 : Subgroup (GL (Fin n) E × ℚˣ) :=
  Sim (conjE E).toRingHom (algebraMap ℚ E) n ⊓ (Units.posSubgroup ℚ).comap (MonoidHom.snd _ _)

variable {E n}

abbrev cj (w : Plc E) : Plc E := conjSrc (conjE E) w

def sim : GUf E n →* AfQˣ := (MonoidHom.snd _ _).comp (GUf E n).subtype

def mat : GUf E n →* GL (Fin n) (Af E) := (MonoidHom.fst _ _).comp (GUf E n).subtype

def comp (w : Plc E) : GUf E n →* GL (Fin n) (w.adicCompletion E) := (GeneralLinearGroup.map (pLoc E w)).comp mat

def rat : Gam0 E n →* GUf E n :=
  (((GeneralLinearGroup.map (algebraMap E (Af E))).prodMap (Units.map (algebraMap ℚ AfQ).toMonoidHom)).comp
    (Gam0 E n).subtype).codRestrict _ fun y => by
      have h : (y.1.1.val.map (conjE E).toRingHom)ᵀ * y.1.1.val = algebraMap ℚ E y.1.2 • (1 : Matrix (Fin n) (Fin n) E) := y.2.1
      have h' := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map (algebraMap E (Af E))) h
      simp only [Matrix.map_mul] at h'
      refine mem_Sim.2 ?_
      have e1 : ((y.1.1.val.map (algebraMap E (Af E))).map (conjFin (conjE E)))ᵀ =
          ((y.1.1.val.map (conjE E).toRingHom)ᵀ).map (algebraMap E (Af E)) := by
        ext i j : 1
        exact conjFin_algebraMap _ _
      have e2 : finiteAdeleMap ℚ E (algebraMap ℚ AfQ y.1.2) • (1 : Matrix (Fin n) (Fin n) (Af E)) =
          (algebraMap ℚ E y.1.2 • (1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Af E)) := by
        rw [finiteAdeleMap_algebraMap]
        ext i j : 1
        by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      exact (congrArg (· * _) e1).trans (h'.trans e2.symm)

def ofU : finU E n →* GUf E n :=
  ((((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU E n).subtype).prod 1).codRestrict _ fun u => by
    refine mem_Sim.2 ?_
    have h := GlobalTheory.DefU.ClassFin.cT_pFin u.1
    exact h.trans (by simp)

@[simp] theorem sim_ofU (u : finU E n) : sim (ofU u) = 1 := rfl

@[simp] theorem comp_ofU (w : Plc E) (u : finU E n) : comp w (ofU u) = cLoc w u.1 := rfl

def locE {w : Plc E} (hw : IsSplitAt w) : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E) := (GlobalTheory.locU_equiv_GL E n w hw).choose

theorem locE_apply {w : Plc E} (hw : IsSplitAt w) (x : locU n w) : locE hw x = cLoc w x.1 := (GlobalTheory.locU_equiv_GL E n w hw).choose_spec x

def locF {w : Plc E} (hw : IsSplitAt w) : GL (Fin n) (w.adicCompletion E) →* finU E n :=
  (Subgroup.inclusion (inf_le_left : locU n w ≤ finU E n)).comp (locE hw).symm.toMulEquiv.toMonoidHom

theorem locF_mem {w : Plc E} (hw : IsSplitAt w) (x : GL (Fin n) (w.adicCompletion E)) : (locF hw x).1 ∈ locU n w :=
  ((locE hw).symm x).2

@[simp] theorem cLoc_locF {w : Plc E} (hw : IsSplitAt w) (x : GL (Fin n) (w.adicCompletion E)) : cLoc w (locF hw x).1 = x :=
  (locE_apply hw _).symm.trans ((locE hw).apply_symm_apply x)

def loc {w : Plc E} (hw : IsSplitAt w) : GL (Fin n) (w.adicCompletion E) →* GUf E n := ofU.comp (locF hw)

@[simp] theorem sim_loc {w : Plc E} (hw : IsSplitAt w) (x : GL (Fin n) (w.adicCompletion E)) : sim (loc hw x) = 1 := rfl

@[simp] theorem comp_loc {w : Plc E} (hw : IsSplitAt w) (x : GL (Fin n) (w.adicCompletion E)) : comp w (loc hw x) = x :=
  cLoc_locF hw x

theorem comp_loc_of_apart {w u : Plc E} (hw : IsSplitAt w) (hu : GlobalTheory.Cong.Apart u w) (x : GL (Fin n) (w.adicCompletion E)) :
    comp u (loc hw x) = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (locF_mem hw x)).2 u) hu)

def ZU : Subgroup AfQˣ where
  carrier := {s | ∀ v : Plc ℚ, Valued.v ((s : AfQ) v) = 1}
  one_mem' := fun v => map_one _
  mul_mem' := fun {a b} ha hb v => by
    show Valued.v ((a : AfQ) v * (b : AfQ) v) = 1
    rw [map_mul, ha v, hb v, one_mul]
  inv_mem' := fun {a} ha v => by
    have h : Valued.v ((a : AfQ) v * (↑a⁻¹ : AfQ) v) = 1 := by
      show Valued.v (((a : AfQ) * (↑a⁻¹ : AfQ)) v) = 1
      rw [Units.mul_inv]; exact map_one _
    rwa [map_mul, ha v, one_mul] at h

def lev (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E))) : Subgroup (GUf E n) :=
  ZU.comap sim ⊓ (⨅ w ∈ S, (Kw w).comap (comp w)) ⊓ ⨅ (w : Plc E) (_ : w ∉ S ∧ cj w ∉ S), (KGL w n).comap (comp w)

theorem mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E))} {k : GUf E n} :
    k ∈ lev S Kw ↔ sim k ∈ ZU ∧ (∀ w ∈ S, comp w k ∈ Kw w) ∧ ∀ w, w ∉ S → cj w ∉ S → comp w k ∈ KGL w n := by
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, and_assoc, and_imp]

def embAll (E : Type) [Field E] (n : ℕ) : GL (Fin n) E →* (InfinitePlace E → GL (Fin n) ℂ) :=
  MonoidHom.pi fun v => GeneralLinearGroup.map v.embedding

def xi (W : Wt E n) (J : ℤ) : Representation ℂ (GL (Fin n) E × ℚˣ) (Module.Dual ℂ W.Sp) where
  toFun p := (((p.2 : ℚ) : ℂ) ^ J) •
    Representation.dual ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) p.1
  map_one' := by
    rw [Prod.fst_one, map_one, Prod.snd_one, Units.val_one, Rat.cast_one, _root_.one_zpow, one_smul]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Rat.cast_mul, mul_zpow, map_mul, smul_mul_smul_comm]

abbrev xi0 (W : Wt E n) (J : ℤ) : Representation ℂ (Gam0 E n) (Module.Dual ℂ W.Sp) := (xi W J).comp (Gam0 E n).subtype

def SameK (x : E) (w w' : Plc E) : Prop :=
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def IsCen (x : E) (w : Plc E) (z : GUf E n) : Prop :=
  ∀ u : Plc E, (SameK x (cj u) w → (comp u z).val = ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) _)) ∧
    (¬ SameK x (cj u) w → comp u z = 1)

open Classical in

def mOf (x : E) (W : Wt E n) (J : ℤ) (φ : E →+* ℂ) : ℤ :=
  J - ∑ v : InfinitePlace E, if v.embedding x = -φ x then ∑ i, (W v).w i else 0

end UpperTheory.Gal.CertificateRingHomMap

end
