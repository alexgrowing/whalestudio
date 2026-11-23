import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitaryMatricesFiniteCardLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.StdMass

variable {D : D7}

theorem coord_isIntegral (V : HSp D) (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {x : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (k : Fin V.rank) : IsIntegral ℤ (x k) := by
  have key : ∀ y ∈ V.L0, ∃ a : 𝓞 D.host.E, (a : D.host.E) = V.frame.repr y k := by
    intro y hy
    rw [hL] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = k
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul D.host.E r y, map_smul]
      simp [ha, Algebra.smul_def]
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  obtain ⟨a, ha⟩ := key _ hx'
  have e : V.frame.repr (∑ i, x i • V.frame i) k = x k := by
    rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← e, ← ha]
  exact RingOfIntegers.isIntegral_coe a

theorem mem_lattice_of_rational_mem_completion (V : HSp D) (v : Fin V.rank → D.host.E)
    (h : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] v k) ∈ latHat D.host.F D.host.E (L0c D V)) : v ∈ L0c D V := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hw
      refine ⟨V.frame.equivFun.symm w, ?_, V.frame.equivFun.apply_symm_apply w⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hw
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective w
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  have hr := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L (V.standardTuple_isLattice.fg.map _) hsp).1 v
  rw [← hL]
  refine hr.1 ?_
  have hle : latHat D.host.F D.host.E (L0c D V) ≤ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [← hL] at hx
    exact AddSubgroup.subset_closure ⟨a, fun w => ha w, x, hx, rfl⟩
  exact hle h

theorem card_stab_le (V : HSp D) (hg : V.gram = 1)
    (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Nat.card (Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1) ≤ NumberField.Units.torsionOrder D.host.E ^ V.rank * V.rank.factorial := by
  obtain ⟨hSf, hSc⟩ := GlobalTheory.T.integral_unitary_matrices_finite_card_le D V.rank
  have hx : ∀ x : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1, ∃ u : GL (Fin V.rank) D.host.E,
        u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
        Formalism.UG.bc (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) u =
          HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 := fun x => by
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 x.1.2
    exact ⟨u, hu, e⟩
  choose u hu hue using hx
  have hunit : ∀ x, (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᴴ * (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 :=
    fun x => by
    have h := hu x
    change Formalism.UG.cT _ (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram at h
    rw [hg, Matrix.mul_one] at h
    convert h using 2
    ext a b
    rfl
  have hint : ∀ x a b, IsIntegral ℤ ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun x a b => by
    have hK : x.1.1 ∈ GlobalTheory.Mass.Levels.latStab V := by
      have := x.2
      simpa [Formalism.UG.stabAt] using this
    have hej : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ L0c D V := by
      show ∑ i, (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) i • V.frame i ∈ V.L0
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp), hL]
      rw [Pi.single_eq_same, one_smul]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) ∈
        latHat D.host.F D.host.E (L0c D V) :=
      AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, _, hej, rfl⟩
    have h2 := ((GlobalTheory.Mass.Levels.mem_latStab V x.1.1).1 hK _).1 hy
    have e : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1).1 *ᵥ
        (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) =
        fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b := by
      rw [← hue x]
      funext k
      change ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) *ᵥ
        ((inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ∘ (Pi.single b 1))) k =
          (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b)
      rw [← RingHom.map_mulVec]
      simp [Matrix.mulVec_single_one]
    rw [e] at h2
    exact coord_isIntegral V hL (mem_lattice_of_rational_mem_completion V _ h2) a
  let f : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1 →
      {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
    fun x => ⟨(u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E), hunit x, hint x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = u y := congrArg Subtype.val hxy
    have h2 : u x = u y := Units.ext h1
    have h3 : HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 =
        HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram y.1.1 := by
      rw [← hue x, ← hue y, h2]
    have h4 : x.1.1 = y.1.1 := Subtype.ext h3
    exact Subtype.ext (Subtype.ext h4)
  haveI := hSf.to_subtype
  calc Nat.card _ ≤ Nat.card {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_coe_set_eq _
    _ ≤ _ := hSc

theorem massLower_of_stdV : ∀ D : D7, StdV D → MassLower D := by
  intro D hS i _
  obtain ⟨h1, h2⟩ := hS i
  have hg : (Vc D i).gram = 1 := Matrix.ext fun a b => by
    rw [Matrix.one_apply]
    exact h1 a b
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have e : gramAt D (Vc D i) τ = 1 := Matrix.ext fun a b => by
      simp [gramAt, hg, Matrix.one_apply]
    rw [e]
    exact Matrix.PosDef.one
  have hK := GlobalTheory.Mass.Levels.latStab_compact_open (Vc D i)
  have hfc := GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND (Vc D i)) (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef (Vc D i) hpd) hK.1 hK.2
  have hle := hfc.inv_card_le 1
  have hpos := hfc.stabOrder_pos (DoubleCoset.mk _ _ 1)
  rw [GlobalTheory.Mass.stabOrder_mk] at hpos
  have hc := card_stab_le (Vc D i) hg h2
  have hr : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  unfold GlobalTheory.Mass.unitaryMass
  refine le_trans ?_ hle
  rw [one_div, ← hr]
  exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hc)

end GlobalTheory.LowRow.StdMass
