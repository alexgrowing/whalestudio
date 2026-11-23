import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.S

theorem latHat_eq_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Set (Fin n → E)) :
    (Formalism.MainNotions.StandardLattice.latHat F E L : Set (Fin n → RA F E)) = (GlobalTheory.AdLat.hat F L : Set (Fin n → RA F E)) := by
  ext z
  constructor
  · intro hz
    refine (AddSubgroup.closure_le _).2 ?_ hz
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, fun v => ha v, x, hx, rfl⟩
  · intro hz
    refine (AddSubgroup.closure_le _).2 ?_ hz
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ?_, x, hx, rfl⟩
    intro v
    exact ha v

variable {D : D7}

theorem mem_latHat_iff (V : HSp D) (y : Fin V.rank → RA D.host.F D.host.E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  rw [← SetLike.mem_coe, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V, latHat_eq_hat, SetLike.mem_coe]

theorem mem_Stab_iff (V : HSp D) (h : GA D V) :
    h ∈ Stab V ↔ ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ↔
      (finHom V h).1 *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  constructor
  · intro H y
    have H' : ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) := H
    have := H' y
    rw [mem_latHat_iff, mem_latHat_iff] at this
    exact this
  · intro H
    show ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)
    intro y
    rw [mem_latHat_iff, mem_latHat_iff]
    exact H y

theorem stab_eq_KM_one (V : HSp D) : Stab V = KM V 1 := by
  ext h
  rw [mem_Stab_iff]
  constructor
  · intro hs
    show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    refine ⟨GlobalTheory.FinUA.isUA_finHom D V h, fun x hx => ⟨(finHom V h).1 *ᵥ x - x, sub_mem ((hs x).1 hx) hx,
      by rw [one_nsmul]⟩, fun x hx => ⟨((finHom V h)⁻¹).1 *ᵥ x, (hs _).2 ?_, ?_⟩⟩
    · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      exact hx
    · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  · intro hK y
    have hK' : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
        ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := hK
    obtain ⟨-, h2, h3⟩ := hK'
    constructor
    · intro hy
      obtain ⟨z, hz, e⟩ := h2 y hy
      rw [one_nsmul, sub_eq_iff_eq_add] at e
      rw [e]
      exact add_mem hz hy
    · intro hy
      obtain ⟨z, hz, e⟩ := h3 _ hy
      have e2 := congrArg (fun w => ((finHom V h)⁻¹).1 *ᵥ w) e
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec] at e2
      rw [← e2]
      exact hz

theorem mem_KM_iff (V : HSp D) (M : ℕ) (h : GA D V) : h ∈ KM V M ↔ GlobalTheory.Member.FinCong V M h := by
  have h1 := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  constructor
  · intro hK
    have hK' : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := hK
    intro z hz
    rw [h1] at hz ⊢
    exact hK'.2.1 z hz
  · intro hc
    have hinv := GlobalTheory.Member.PrincLevel.finCong_map (GlobalTheory.Member.PrincLevel.finCong_inv hc)
    show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    refine ⟨GlobalTheory.FinUA.isUA_finHom D V h, fun z hz => ?_, fun x hx => ?_⟩
    · have hz' : z ∈ Formalism.L2.Pj.latHat V := by rw [h1]; exact hz
      obtain ⟨y, hy, e⟩ := hc z hz'
      rw [h1] at hy
      exact ⟨y, hy, e⟩
    · have hx' : x ∈ Formalism.L2.Pj.latHat V := by rw [h1]; exact hx
      have hm := hinv x hx'
      rw [h1] at hm
      refine ⟨(finHom V h⁻¹).1 *ᵥ x, hm, ?_⟩
      rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem isOpen_KM (V : HSp D) (M : ℕ) (hM : 1 ≤ M) : IsOpen (KM V M) := by
  let K : Subgroup (GA D V) :=
    { carrier := {h | GlobalTheory.Member.FinCong V M h}
      one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V M
      mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
      inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha }
  have e : KM V M = (K : Set (GA D V)) := Set.ext fun h => mem_KM_iff V M h
  rw [e]
  have hG : Continuous fun x : GA D V => finHom V x := by
    refine Units.continuous_iff.2 ⟨GlobalTheory.Member.continuous_finHom_val D V, ?_⟩
    have h := (GlobalTheory.Member.continuous_finHom_val D V).comp continuous_inv
    refine h.congr fun x => ?_
    simp [map_inv]
  have hF : Continuous fun x : GA D V => (finHom V).rangeRestrict x := hG.subtype_mk _
  have hO := (GlobalTheory.SmoothVac.isOpen_map_levelGroup V (show 0 < M by omega)).preimage hF
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) (Filter.mem_of_superset (hO.mem_nhds ?_) ?_)
  · exact Subgroup.mem_map.2 ⟨1, one_mem _, by simp⟩
  · intro x hx
    obtain ⟨k', hk', e'⟩ := Subgroup.mem_map.1 hx
    have e'' : finHom V k' = finHom V x := congrArg Subtype.val e'
    show GlobalTheory.Member.FinCong V M x
    have hc := hk'.2
    unfold GlobalTheory.Member.FinCong at hc ⊢
    rw [← e'']
    exact hc

open Formalism.IndefR.Links in

theorem mem_Stab_of_lev (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.LevelP C.Pg D.R.r ℂ) (h : GA D (Wc D i))
    (hh : finE (Wc D i) h ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) : h ∈ Stab (Wc D i) := by
  have hβ := hC.βW i
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame (C.βW i) (C.ΛW i) := by obtain ⟨c, hc, -⟩ := hβ; exact hc
  have hS : finE (Wc D i) h ∈ Formalism.L2.DIV.St (C.βW i) := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.mem_lev.1 hh).1
  have hS' : finE (Wc D i) h⁻¹ ∈ Formalism.L2.DIV.St (C.βW i) := by rw [map_inv]; exact inv_mem hS
  have m1 := GlobalTheory.MassLinkConj.mulVec_mem_hat D (C.βW i) (C.ΛW i) hfr (finHom (Wc D i) h) (by exact hS)
  have m2 := GlobalTheory.MassLinkConj.mulVec_mem_hat D (C.βW i) (C.ΛW i) hfr (finHom (Wc D i) h⁻¹) (by exact hS')
  rw [hΛ] at m1 m2
  rw [mem_Stab_iff]
  intro y
  refine ⟨fun hy => m1 y hy, fun hy => ?_⟩
  have := m2 _ hy
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end MainStatements.Tam.S

namespace MainStatements.Tam

theorem stab : StabSt :=
  ⟨fun _ V => ⟨S.stab_eq_KM_one V, fun M hM => S.isOpen_KM V M hM⟩,
    fun D Tu C t0 hC i P h hh => S.mem_Stab_of_lev D Tu C t0 hC i P h hh⟩

end MainStatements.Tam

end
