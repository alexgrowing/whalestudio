import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

def KgH (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Set (KvH X u p.1) :=
  {x | ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
    Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1}

def HLatGL (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ ψ : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p), Function.Surjective ψ ∧
    ∀ x : KvH X u p.1, (∀ i j, ((ψ x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ x ∈ KgH X u p

def HKerIn (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ x : KvH X u p.1, x ∈ KgH X u p → x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)

def HImU (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
    (∀ x, ρ x = 1 ↔ x ∈ KgH X u p) →
    Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ) = ukC D.R.k (gOf p)

def LocRedParts : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HKerIn X hb u p ∧ HImU X hb u p

private theorem isUnit_of_isUnit_map_of_surjective {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) (r : R) (hr : IsUnit (f r)) : IsUnit r := by
  obtain ⟨v, hv⟩ := hr
  obtain ⟨y, hy⟩ := hf (↑v⁻¹ : S)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (r * y) with h | h
  · exact isUnit_of_mul_isUnit_left h
  · exfalso
    have h2 := h.map f
    rw [map_sub, map_one, map_mul, ← hv, hy, Units.mul_inv, sub_self] at h2
    exact not_isUnit_zero h2

private theorem generalLinearGroup_map_surjective_of_surjective {R S m : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Fintype m]
    [DecidableEq m] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := m) f) := by
  intro A
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨1, Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)⟩
  · have hf' := hf
    choose g hg using hf'
    let M : Matrix m m R := fun i j => g ((A : Matrix m m S) i j)
    have hM : f.mapMatrix M = (A : Matrix m m S) := by
      ext i j
      exact hg _
    have hdet : IsUnit M.det := by
      apply isUnit_of_isUnit_map_of_surjective f hf
      rw [RingHom.map_det, hM]
      exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit, ?_⟩
    apply Units.ext
    change f.mapMatrix (((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit : Matrix m m R) = _
    rw [IsUnit.unit_spec, hM]

theorem locRedH_of (h : LocRedParts) : LocRedH := by
  intro D X hb hK u hm hl p
  obtain ⟨⟨π, hπs, hπk⟩, ⟨ψ, hψs, hψ⟩, hker, himu⟩ := h X hb hK u hm hl p
  let ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)) :=
    (Matrix.GeneralLinearGroup.map π).comp ψ
  have hco : ∀ (x : KvH X u p.1) (i j : Fin D.R.k),
      ((ρ x : GL (Fin D.R.k) (ZMod (gOf p))) : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j =
        π (((ψ x : GL (Fin D.R.k) (MassDataIdxSteps.Op X p)) :
          Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) i j) :=
    fun _ _ _ => rfl
  have hentry : ∀ (x : KvH X u p.1) (i j : Fin D.R.k),
      (((ψ x : GL (Fin D.R.k) (MassDataIdxSteps.Op X p)) :
          Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
          Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)} ↔
        ((ρ x : GL (Fin D.R.k) (ZMod (gOf p))) : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j =
          (1 : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j := by
    intro x i j
    rw [← hπk, RingHom.mem_ker, hco, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hρ1 : ∀ x, ρ x = 1 ↔ x ∈ KgH X u p := by
    intro x
    rw [← hψ x]
    constructor
    · intro hx i j
      exact (hentry x i j).2 (by rw [hx, Units.val_one])
    · intro hx
      apply Units.ext
      apply Matrix.ext
      intro i j
      rw [Units.val_one]
      exact (hentry x i j).1 (hx i j)
  have hρs : Function.Surjective ρ := (generalLinearGroup_map_surjective_of_surjective π hπs).comp hψs
  exact ⟨ρ, hρs, fun x hx => hker x ((hρ1 x).1 (MonoidHom.mem_ker.mp hx)), himu ρ hρs hρ1⟩

end PIW.MassDataColumns
