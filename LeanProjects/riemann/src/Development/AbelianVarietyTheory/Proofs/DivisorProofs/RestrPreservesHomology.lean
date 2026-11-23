import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

instance restr_additive (φ : R →+* S) : (restr φ).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

abbrev rcx (φ : R →+* S) : Cx S ⥤ Cx R := (restr φ).mapHomologicalComplex _

def rAug (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) : sgl ((restr φ).obj F) ⟶ (rcx φ).obj C :=
  (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F ≫ (rcx φ).map ε

def idSemi (φ : R →+* S) (K : Cx S) : SemiMap K ((rcx φ).obj K) where
  app U s := { toFun := fun a => a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

end

section
variable {S R : Type} [CommRing S] [CommRing R]

def SemiMap.sub {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J) : SemiMap I J where
  app U s := ρ.app U s - ρ'.app U s
  nat g s a := by simp [map_sub, ρ.nat, ρ'.nat]
  comm U s t a := by simp [map_sub, ρ.comm, ρ'.comm]

end

section
variable {S R : Type} [CommRing S] [CommRing R]

theorem ulift_intCast_smul {T : Type} [CommRing T] (M : ModuleCat.{1} (ULift.{1} T)) (x : M) (k : ℤ) :
    (ULift.up (k : T) : ULift.{1} T) • x = k • x := by
  rw [show (ULift.up (k : T) : ULift.{1} T) = ((k : ULift.{1} T)) from rfl]
  exact Int.cast_smul_eq_zsmul _ k x

def SemiMap.toZl {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) (U : Scheme.{0}ᵒᵖ) :
    ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U ⟶ ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U :=
  ModuleCat.ofHom (X := ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U)
      (Y := ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U)
    { toFun := ρ.app U.unop s
      map_add' := map_add _
      map_smul' := fun r a => by
        have h1 : ∀ b : Sec (I.X s) U.unop, (ULift.up ((r.down : ℤ) : S) : ULift.{1} S) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        have h2 : ∀ b : Sec (J.X s) U.unop, (ULift.up ((r.down : ℤ) : R) : ULift.{1} R) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        exact (congrArg (ρ.app U.unop s) (h1 a)).trans ((map_zsmul _ _ _).trans (h2 _).symm) }

def SemiMap.toZs {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) :
    (restr (Int.castRingHom S)).obj (I.X s) ⟶ (restr (Int.castRingHom R)).obj (J.X s) :=
  ⟨{ app := ρ.toZl s
     naturality := fun U V g => by
       ext a
       change ρ.app V.unop s (Sec.res g.unop a) = Sec.res g.unop (ρ.app U.unop s a)
       exact (ρ.nat g.unop s a).symm }⟩

def SemiMap.toZ {I : Cx S} {J : Cx R} (ρ : SemiMap I J) :
    (rcx (Int.castRingHom S)).obj I ⟶ (rcx (Int.castRingHom R)).obj J where
  f s := ρ.toZs s
  comm' s t _ := by
    apply Sheaf.hom_ext
    ext U a
    change Sec.map (J.d s t) (ρ.app U.unop s a) = ρ.app U.unop t (Sec.map (I.d s t) a)
    exact ρ.comm U.unop s t a

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem restr_eq (φ : R →+* S) : restr φ = sheafCompose _ (ModuleCat.restrictScalars.{1} (liftHom φ)) := rfl

theorem restr_exact (φ : R →+* S) : PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ) := by
  rw [restr_eq]
  have adj₁ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (liftHom φ))
  have adj₂ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ))
  have := adj₁.isRightAdjoint
  have := adj₂.isLeftAdjoint
  let j : sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) ≅
      Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (sheafificationNatIso _ _)
  exact ⟨inferInstance, preservesFiniteColimits_of_natIso j.symm⟩

instance restr_preservesHomology (φ : R →+* S) : (restr φ).PreservesHomology := by
  obtain ⟨_, _⟩ := restr_exact φ
  infer_instance

theorem rAug_quasiIso (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) [QuasiIso ε] : QuasiIso (rAug φ ε) := by
  unfold rAug
  have h1 : QuasiIso ((rcx φ).map ε) := HomologicalComplex.quasiIso_map_of_preservesHomology ε (restr φ)
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F) :=
    quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem rAug_f_zero (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((rAug φ ε).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
      (show Sec ((restr φ).obj (C.X 0)) U from Sec.map (ε.f 0) (Sec.map (sglι F) a)) := by
  have h : sglι ((restr φ).obj F) ≫ (rAug φ ε).f 0 = (restr φ).map (sglι F ≫ ε.f 0) := by
    set_option backward.isDefEq.respectTransparency false in
    simp [rAug, sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  have := congrArg (fun m => Sec.map m (show Sec ((restr φ).obj F) U from a)) h
  exact this

end

end GlobalTheory.EtC
