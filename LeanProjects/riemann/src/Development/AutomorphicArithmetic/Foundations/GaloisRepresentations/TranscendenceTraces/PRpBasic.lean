import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem cohomologyClass_mk_zsmul {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (d : ℤ) (a : Cocycle K L n) :
    CohomologyClass.mk (d • a) = d • CohomologyClass.mk a :=
  map_zsmul (CohomologyClass.mkAddMonoidHom K L n) d a

private theorem ev_cocycle_add {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (α β : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((α + β : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) +
        ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_add]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ _ 0 n h0 X (𝟙 X)).1

private theorem ev_cocycle_zsmul {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (d : ℤ) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((d • α : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      d • ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_smul]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ 0 0 n h0 X (𝟙 X)).2.2.2 d

theorem UpperTheory.Gal.TranscendenceTraces.rpBasic_of :
    RpBasic := by
  intro R _ I X n
  have ev_lin := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)
  have key := fun (α : Cocycle ((chains R).obj (sch.obj X)) I n) =>
    (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X I (n - 1) n (n + 1) (by ring) rfl).2 α
  have h0 : -((0 : ℕ) : ℤ) + n = n := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩
    exact (key α).1
  · rintro x x' a a' ⟨α, rfl, ha⟩ ⟨β, rfl, hb⟩
    subst ha hb
    have hiff : CohomologyClass.mk α = CohomologyClass.mk β ↔
        ∃ y, Sec.map (I.d (n - 1) n) y =
          ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) -
            ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, (key (α - β)).2, Cocycle.coe_sub,
        (ev_lin.1 (α : Cochain _ I n) β 0 n h0 X (𝟙 X)).2.1]
    refine ⟨hiff, fun h => hiff.2 ⟨0, ?_⟩, ⟨α + β, CohomologyClass.mk_add α β, ev_cocycle_add I X n h0 α β⟩,
      fun d => ⟨d • α, cohomologyClass_mk_zsmul d α, ev_cocycle_zsmul I X n h0 d α⟩⟩
    rw [h, sub_self]
    exact map_zero _
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h1 := ev_lin.2.2.2.1 (sch.map f) (α : Cochain _ I n) 0 n h0 Y (𝟙 Y)
    have h2 := ev_lin.2.1 (α : Cochain _ I n) 0 n h0 Y X f (𝟙 X)
    exact h1.trans h2.symm
  · rintro R' _ J ρ x a ⟨α, rfl, rfl⟩
    obtain ⟨β, hβ⟩ := SemiMap.image_exists ρ (sch.obj X) n α
    exact ⟨β, (SemiMap.op_spec ρ (sch.obj X) n α β hβ).symm, hβ 0 n h0 X (𝟙 X)⟩
