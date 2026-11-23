import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

theorem coord_mem_smallSec (k : Type) [CommRing k] (N : ℕ) (a : Fin (N + 1)) :
    coord k N a ∈ (hermitianTwistingSheaf k N).smallSec := by
  intro σ y
  have e (a) : Weight.combVal (PSpace.str k N) σ (coord k N) 1 a = secVal _ σ (coord k N a) := by
    simp [Weight.combVal, Matrix.one_apply]
  refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := O1_isLB k N) (he := fun a => e a ▸ secVal_mem _)
    (h := Weight.noCommonZero_combVal (iSup_nonzeroLocus_coord k N) (M := 1) (by simp)) y)
  exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
    (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

theorem ringKrullDim_ringOfIntegers : ringKrullDim (𝓞 F) = 1 := by
  have h : Ring.KrullDimLE 1 (𝓞 F) := inferInstance
  refine le_antisymm (by exact_mod_cast Ring.krullDimLE_iff.1 h) ?_
  by_contra hlt
  have : Ring.KrullDimLE 0 (𝓞 F) := Ring.krullDimLE_iff.2 (by
    have h' : ringKrullDim (𝓞 F) ≤ 0 := Order.le_of_lt_succ (not_le.1 hlt)
    exact_mod_cast h')
  exact RingOfIntegers.not_isField F Ring.KrullDimLE.isField_of_isDomain

def projModel : TrueGeo.Model (proj F n) where
  X := PSpace (𝓞 F) n
  p := PSpace.str (𝓞 F) n
  ar := isArithVar_pspace (𝓞 F) (ringKrullDim_ringOfIntegers F) n
  j := (proj F n).ι ≫ baseChange n (algebraMap (𝓞 F) F)
  pb := by
    have H : IsPullback (proj F n).ι (proj F n).str (PSpace.str F n) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
    have := H.paste_horiz (isPullback_baseChange n (algebraMap (𝓞 F) F))
    rwa [Category.id_comp] at this

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ (M : TrueGeo.Model (proj F n)) (L : HermLB M.p) (Δ : (proj F n).Dv) (r : (L.B.pull M.j).ι → (proj F n).Fnˣ), Presents Δ (L.B.pull M.j) r ∧ (proj F n).inter (fun _ => Δ) = 1 ∧ ArInt.NefFib L ∧ ∀ x : M.X, ∃ s ∈ L.smallSec, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := by
  intro F _ _ n
  have hL := LB.isLB_pull (O1_isLB (𝓞 F) n) (projModel F n).j
  obtain ⟨r, hr⟩ := exists_isRatSec hL
  have hp := presents_divOfRatSec hL hr
  refine ⟨projModel F n, hermitianTwistingSheaf (𝓞 F) n, _, r, hp, ?_, ?_, fun x => ?_⟩
  · refine (Var.inter_congr fun _ => ?_).trans (inter_projHyp F n)
    refine hp.toPic_eq.trans (Eq.trans ?_ ((proj F n).presents_hyp _).toPic_eq.symm)
    refine (cls_pull (O1_isLB (𝓞 F) n) _ _).trans ((pull_comp _ _ _).trans ?_)
    refine Eq.trans (congrArg _ ?_) (cls_pull (O1_isLB F n) _ _).symm
    exact (cls_eq_iff (LB.isLB_pull (O1_isLB (𝓞 F) n) _) (O1_isLB F n)).2 (lbIso_pull_O1 n _)
  · have := Geo.Tor.isProper_str (𝓞 F) n
    exact nefFib_of_isAmpleLB (hermitianTwistingSheaf (𝓞 F) n) (GlobalTheory.isAmple_projective_O_one (𝓞 F) n)
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord (𝓞 F) n).ge (Opens.mem_top x))
    exact ⟨_, coord_mem_smallSec _ n a, ha⟩

end GlobalTheory.ProjModel
