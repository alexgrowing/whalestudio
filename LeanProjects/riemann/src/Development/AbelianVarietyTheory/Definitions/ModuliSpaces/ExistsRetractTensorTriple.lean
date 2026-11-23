import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperZeroTriple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Amp

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}

def Top.Amp {n N : ℕ} (T : Top Xo n N) : Prop :=
  ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2))

def System.Amp (S : System Xo) : Prop := ∀ i, (S.T i).Amp

theorem topExists_iff_amp : TopExists ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
      ∀ (Xo : ∀ l : Level H, Moduli D l) (n : ℕ), AuxiliaryInertOddPrime H n → ∃ J : ℕ, 1 ≤ J ∧ ∃ T : Top Xo n (n ^ J), T.Amp :=
  Iff.rfl

end Amp

section Refl

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

def Cpt.Above.refl (C : Cpt c t₀ β) : C.Above C (RingHom.id O) (𝟙 U) (ObjComp.sabMapId t₀) where
  π := 𝟙 _
  π_over := by rw [show spMap (RingHom.id O) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  fin := by
    have : IsIso (spMap (RingHom.id O)) := (show spMap (RingHom.id O) = 𝟙 _ from Spec.map_id _) ▸ inferInstance
    refine (fun w => ?_ : ∀ w : 𝟙 C.X ≫ C.s = C.s ≫ spMap (RingHom.id O), IsFinite (pullback.lift (𝟙 C.X) C.s w)) _
    have h : pullback.lift (𝟙 C.X) C.s w ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
    have : IsIso (pullback.lift (𝟙 C.X) C.s w) := IsIso.of_isIso_fac_right h
    infer_instance
  mu := ObjComp.sabMapId C.t
  j_comm := (Category.comp_id _).trans (Category.id_comp _).symm
  φ_comm := (Category.comp_id _).trans (Category.id_comp _).symm

end Refl

section Abelian

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

def Cpt.ofAbelian (hn : Geo.Tor.IsNormalScheme X) (hp : IsProjOver s) (hf : Flat s) (ha : IsProper t.G.hom)
    (t₀ : SAB H (pullback s (spMap β))) (m : SABMap t₀ t (𝟙 _ ≫ pullback.fst _ _)) :
    Cpt (pullback.snd s (spMap β)) t₀ β :=
  ⟨X, s, hn, hp, hf, 𝟙 _, Category.id_comp _, inferInstance, by simp, t, m, by simp [Point.abLocus_eq_univ]⟩

def tensorTriple (H : Host E) (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) : SAB H X where
  G := Serre.tensorObj (𝓞 E) (Serre.intAct A)
  semi := isSemiAbelian_of_isAbelianScheme _ ((Serre.isTensor (𝓞 E) (Serre.intAct A)).isAbelianScheme hA)
  act := (Serre.isTensor (𝓞 E) (Serre.intAct A)).algAct (𝓞 E)
  PP := (UU.CP.triv _).L
  cub := (UU.CP.triv _).c
  sym := isSymmetric_of_symmetry_generator _ _ (UU.CP.triv _).sym_gen (UU.CP.triv _).sym_rig
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) fun _ _ => rfl)⟩

variable (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)

theorem isProper_tensorTriple : IsProper (tensorTriple H A hA).G.hom :=
  ((Serre.isTensor (𝓞 E) (Serre.intAct A)).isAbelianScheme hA).proper

theorem exists_retract_tensorTriple :
    ∃ (i : A ⟶ (tensorTriple H A hA).G) (r : (tensorTriple H A hA).G ⟶ A), i ≫ r = 𝟙 A := by
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  obtain ⟨j⟩ := b.index_nonempty
  exact ⟨_, _, (Serre.isTensor (𝓞 E) (Serre.intAct A)).tmul_mapLeft_self (b.coord j) (m := b j) (by simp)⟩

end Abelian

theorem flat_projSpace (R : Type) [CommRing R] (N : ℕ) : Flat (PSpace.str R N) :=
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => by
    change Flat (ProjSpace.chartι R N i ≫ _)
    rw [ProjSpace.chartι_str, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat R (MvPolynomial _ R)))

theorem isNormalScheme_projSpace (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (N : ℕ) :
    Geo.Tor.IsNormalScheme (PSpace R N) := by
  refine (isNormalScheme_iff_pred _).1 (IsNormalScheme.of_forall_exists_isOpenImmersion fun x => ?_)
  obtain ⟨i, y, hy⟩ := (ProjSpace.chartCover R N).exists_eq x
  exact ⟨_, ProjSpace.chartι R N i, ProjSpace.isOpenImmersion_chartι R N i, IsNormalScheme.of_pred (ZJ.isNormalScheme_sp _), y, hy⟩

end GlobalTheory.Models

end
