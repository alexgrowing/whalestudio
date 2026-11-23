import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaDvr

theorem app_eq_zero_of_not_mem {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [Smooth G.hom]
    {U : G.left.Opens} (a : Γ(G.left, U))
    (h : ∀ x ∈ G.left.basicOpen a, G.hom x ≠ IsLocalRing.closedPoint V) :
    ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom a = 0 := by

  have hk : _root_.IsReduced (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    infer_instance
  have : IsReduced (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0))

  have hpt : ∀ y : ↥(pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)),
      G.hom (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y) = IsLocalRing.closedPoint V := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · exact (Ideal.ne_top_iff_one _).mpr (PrimeSpectrum.isPrime _).one_notMem
    · intro r hr
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [zero_add, pow_one]; exact hr)
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r ∈
        ((pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y).asIdeal
      rw [h0]
      exact Ideal.zero_mem _

  have hbot : (fstG (IsLocalRing.maximalIdeal V) 0 G).left ⁻¹ᵁ G.left.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => (h _ hy (hpt y)).elim
  rw [Scheme.preimage_basicOpen] at hbot
  exact (@basicOpen_eq_bot_iff _ this _ _).mp hbot

private lemma secIsMul_trans' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB Y} {a b : R} {σ τ τ' : LB.Sec L} (h : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ)
    (h' : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p b τ τ') : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p (a * b) σ τ' := by
  intro k
  rw [h k, h' k, ← _root_.mul_assoc]
  congr 1
  simp only [resTop, scal, map_mul]

private lemma gs_id_eq_germ_moduli {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) (z : X) (hz : z ∈ U) :
    gs (𝟙 X) z U a = (X.presheaf.germ U z hz).hom a := by
  unfold gs
  rw [dif_pos (show (𝟙 X) z ∈ U from hz)]
  rfl

theorem exists_sec_unit_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left)
    (hN : N.IsLB) (s : LB.Sec (N.pull (pullback.fst G.hom (jK V)))) (j) (hj : s.f j ≠ 0) :
    ∃ (θ : LB.Sec N) (k : N.ι), ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hflat : (algebraMap V (FractionRing V)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing V) (nonZeroDivisors V))
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  have hpb : IsPullback (pullback.fst G.hom (jK V)) (pullback.snd G.hom (jK V)) G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := IsPullback.of_hasPullback _ _

  obtain ⟨n, c, u, hu⟩ := GlobalTheory.FlatSec.exists_comb_of_flat V (FractionRing V) _ hflat G.left G.hom _
    (pullback.fst G.hom (jK V)) _ hpb N hN s
  have hne : ∃ i k, (u i).f k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hj
    apply TopCat.Presheaf.section_ext (pullback G.hom (jK V)).sheaf
    intro z hz
    have hj' : j = fun _ => j PUnit.unit := funext fun x => by cases x; rfl
    have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := by
      rw [hj'] at hz
      simpa [LB.pull, LB.LinComb, LB.wchart] using hz
    have h1 := hu z (j PUnit.unit) hz'
    rw [← hj'] at h1
    rw [gs_id_eq_germ_moduli _ _ z hz] at h1
    refine Eq.trans ?_ (map_zero _).symm
    change ((pullback G.hom (jK V)).presheaf.germ _ z hz).hom (s.f j) = 0
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcon i (j PUnit.unit)]
    simp [gs]
  obtain ⟨i, k₀, hk₀⟩ := hne
  set θ₀ := u i

  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hex : ∃ m, ∃ k, ((fstG (IsLocalRing.maximalIdeal V) m G).left.app _).hom (θ₀.f k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk₀ ((GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings V _ hjac G).1 N hN θ₀ hcon k₀)
  classical

  have hunit : ∀ (θ : LB.Sec N) (k : N.ι), ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (θ.f k) ≠ 0 →
      ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
    intro θ k hθ
    by_contra hcon
    push Not at hcon
    exact hθ (app_eq_zero_of_not_mem G (θ.f k) hcon)

  obtain ⟨k₁, hk₁⟩ := Nat.find_spec hex
  rcases hm : Nat.find hex with _ | e
  · rw [hm] at hk₁
    obtain ⟨x, hx, hxc⟩ := hunit θ₀ k₁ hk₁
    exact ⟨θ₀, k₁, x, hx, hxc⟩
  · have hlt : ¬ ∃ k, ((fstG (IsLocalRing.maximalIdeal V) e G).left.app _).hom (θ₀.f k) ≠ 0 :=
      Nat.find_min hex (by omega)
    push Not at hlt
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ e).1 hlt
    have hτ0 : ∃ k, ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (τ.f k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ', hτ'⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N τ 0).1 hcon
      have h2 := secIsMul_trans' G.hom hτ hτ'
      rw [← pow_add] at h2
      have h3 := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ (e + 1)).2 ⟨τ', h2⟩
      rw [hm] at hk₁
      exact hk₁ (h3 k₁)
    obtain ⟨k, hk⟩ := hτ0
    obtain ⟨x, hx, hxc⟩ := hunit τ k hk
    exact ⟨τ, k, x, hx, hxc⟩

theorem thetaNZ_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)), GlobalTheory.LN.PolAt t (jK V) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro hL hL2 E _ _ _ H V _ _ _ t ht
  obtain ⟨A, oA, gen, -, hiso, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt hL hL2 E H V t ht
  have hsa := t.4
  have : Smooth t.G.hom := hsa.2
  have : IsSeparated t.G.hom := hsa.3
  have : QuasiCompact t.G.hom := hsa.4
  have : GeometricallyConnected t.G.hom := hsa.5
  have hLt : t.PP.L.IsLB := t.PP.3

  have hP := GlobalTheory.PushInv.pushInvertible_any hL2.1 hL.1 _ A
  obtain ⟨W, hxW, θ, hθ, -, hnz⟩ := hP (IsLocalRing.closedPoint (FractionRing V))
  obtain ⟨g, i, -, hg⟩ := hnz _ hxW
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hO : ⊤ ≤ gen.hom.left ⁻¹ᵁ (A.A.hom ⁻¹ᵁ W) := by
    intro y _
    change A.A.hom (gen.hom.left y) ∈ W
    rwa [Subsingleton.elim (A.A.hom (gen.hom.left y)) (IsLocalRing.closedPoint (FractionRing V))]
  obtain ⟨θ', hθ'⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (LB.isLB_pull hLt _) gen.hom.left w hw hO θ hθ
  have hgy : gen.hom.left (gen.inv.left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, gen.inv_hom_id, Over.id_left]
    rfl
  obtain ⟨k, hk⟩ := hθ' (gen.inv.left g) i (by rwa [hgy])
  have hk0 : θ'.f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk

  obtain ⟨σ, l, x, hx, hxc⟩ := exists_sec_unit_closed_fibre V t.G t.PP.L hLt θ' k hk0

  refine ⟨σ, fun y => ?_⟩
  have hy : y ⤳ t.G.hom x := hxc ▸ IsLocalRing.specializes_closedPoint y
  obtain ⟨x', hx', hx'y⟩ := Flat.generalizingMap t.G.hom hy
  exact ⟨x', l, hx'y, hx'.mem_open (t.G.left.basicOpen (σ.f l)).isOpen hx⟩

end GlobalTheory.ThetaDvr
