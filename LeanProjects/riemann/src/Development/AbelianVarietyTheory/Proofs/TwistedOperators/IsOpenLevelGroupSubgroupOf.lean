import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedVacRoot

private theorem mem_Qbar_of_pow {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1) : c ∈ Qbar :=
  mem_algebraicClosure_iff'.2 (IsIntegral.of_pow hm (h ▸ isIntegral_one))

private theorem norm_map_of_pow {K : Type} [NormedField K] (σ : Qbar →+* K) {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1)
    (hc : c ∈ Qbar) : ‖σ ⟨c, hc⟩‖ = 1 := by
  have e : (⟨c, hc⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have e' : ‖σ ⟨c, hc⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e'

private theorem isOpen_levelGroup_subgroupOf {D : D7} (T : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) := by
  let F : GfC T → Formalism.IndefR.Bridge.Gf T := fun x => (finHom T).rangeRestrict x.1
  have hG : Continuous fun x : GfC T => (finHom T x.1 : GL (Fin T.rank) (Formalism.L2.Herm.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    refine Units.continuous_iff.2 ⟨(GlobalTheory.Member.continuous_finHom_val D T).comp continuous_subtype_val, ?_⟩
    have h := ((GlobalTheory.Member.continuous_finHom_val D T).comp continuous_inv).comp
      (continuous_subtype_val (p := fun x => x ∈ GfC T))
    refine h.congr fun x => ?_
    simp [Function.comp_def, map_inv]
  have hF : Continuous F := hG.subtype_mk _
  have e : (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) =
      F ⁻¹' (((GlobalTheory.Member.PrincLevel.levelGroup T N).map (finHom T).rangeRestrict : Subgroup (Formalism.IndefR.Bridge.Gf T)) :
        Set (Formalism.IndefR.Bridge.Gf T)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    constructor
    · intro hx
      exact Subgroup.mem_map.2 ⟨x.1, hx, rfl⟩
    · intro hx
      obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hx
      have e' : finHom T k' = finHom T x.1 := congrArg Subtype.val e
      refine ⟨x.2, ?_⟩
      have hc := hk'.2
      unfold GlobalTheory.Member.FinCong at hc ⊢
      rw [← e']
      exact hc
  rw [e]
  exact (GlobalTheory.SmoothVac.isOpen_map_levelGroup T hN).preimage hF

private theorem exists_pow_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K U : Subgroup G)
    (hKH : K ≤ H) (hK : IsCompact (K : Set G)) (hU : IsOpen ((U.subgroupOf H : Subgroup H) : Set H)) {k : G} (hk : k ∈ K) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ U := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    have hc : Continuous (Subgroup.inclusion hKH) := continuous_inclusion hKH
    exact hU.preimage hc
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  obtain ⟨m, hm, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := U.subgroupOf K) Subgroup.index_ne_zero_of_finite ⟨k, hk⟩
  exact ⟨m, hm, h⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem exists_pow_level {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : Submodule.IsLattice D.host.E Λ) {k : GA D V} (hk : k ∈ GfC V)
    (hfix : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) Λ = Λ) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ GlobalTheory.Member.PrincLevel.levelGroup V N := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ Λ hΛ
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (Formalism.IndefR.Lev.finE V k)
  rw [hfix] at key
  have key' : ∀ u, u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      Matrix.mulVec ((Formalism.IndefR.Lev.finE V k)⁻¹).1 u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := key
  have hst : Formalism.IndefR.Lev.finE V k ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2 ⟨fun y hy => (key' _).2 ?_, fun y hy => (key' y).1 hy⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hy
  exact exists_pow_mem (GfC V) (Formalism.IndefR.Lev.levA V (Formalism.L2.DIV.St β)) _ inf_le_left
    (GlobalTheory.AscInh.stab_compact_open V β).1 (isOpen_levelGroup_subgroupOf V hN) ⟨hk, hst⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem exists_root {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) {k : GA D S} {k' : GA D T} (hk : k ∈ GfC S) (hk' : k' ∈ GfC T)
    (h1 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE S k) ΛS = ΛS)
    (h2 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE T k') ΛT = ΛT)
    (hf' : IsVacO ψ θ S T sS sT ΛS ΛT (om (k, k') f)) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧ om (k, k') f = c • f := by
  obtain ⟨c, hc⟩ := GlobalTheory.LevelVac.vac_eq_smul hS hT hΛS hΛT hf hf'
  obtain ⟨α, hα⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛS hΛS.1
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛT hΛT.1
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.LevelVac.exists_level_fix hW hS hT hΛS hΛT hα hβ hf
  obtain ⟨a, ha, hka⟩ := exists_pow_level S ΛS hΛS.1 hk h1 hN
  obtain ⟨b, hb, hkb⟩ := exists_pow_level T ΛT hΛT.1 hk' h2 hN
  have e1 : k ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup S N := by
    rw [pow_mul]; exact pow_mem hka b
  have e2 : k' ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup T N := by
    rw [pow_mul']; exact pow_mem hkb a
  have e3 := hfix _ e1.1 _ e2.1 e1.2 e2.2
  have e4 : om (k ^ (a * b), k' ^ (a * b)) f = c ^ (a * b) • f := GlobalTheory.LevelVac.om_pow_eq om (k, k') f c hc (a * b)
  obtain ⟨w, hw⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hf
  refine ⟨c, a * b, mul_pos ha hb, ?_, hc⟩
  have e5 := congrFun (e4.symm.trans e3) w
  rw [Pi.smul_apply, smul_eq_mul] at e5
  exact mul_right_cancel₀ hw (e5.trans (one_mul _).symm)

private theorem inV_std {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    inV B (stdL D n) = (colLat B : Set (Fin n → D.host.E)) := by
  ext y
  simp only [inV, Set.mem_image, SetLike.mem_coe]
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : ∀ i, ∃ c : 𝓞 D.host.E, algebraMap _ D.host.E c = z i := fun i =>
      Submodule.mem_one.1 (hz i (Set.mem_univ i))
    choose c hc using hz'
    refine ⟨c, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, hc, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap _ D.host.E (c j), fun i _ => Submodule.mem_one.2 ⟨c i, rfl⟩, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem moved_root (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (hch : ch.Is) (p : Pair T) (hp : DefPair D.R.m p) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (hx : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _)
    (hy : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧
      ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
        ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p) = c • ch.S.Z.vac p := by
  have hn := DefPair.nodes hp
  obtain ⟨h1, h2⟩ := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  have hvac := GlobalTheory.MovedDict.movedVac_isVacO hP hI ch hch p hp x y
  have hv := ch.S.Z.vac_is p hp
  have gx := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h1 x
  have gy := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h2 y
  have ix : inV (ch.S.N.fr p.small) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) = (colLat (ch.S.N.fr p.small) : Set _) := by
    rw [hx, inV_std]
  have iy : inV (ch.S.N.fr p.big) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) = (colLat (ch.S.N.fr p.big) : Set _) := by
    rw [hy, inV_std]
  have fx := SetLike.coe_injective (gx.symm.trans ix)
  have fy := SetLike.coe_injective (gy.symm.trans iy)
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from iy,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from ix] at hvac
    exact exists_root hom (fun τ => isCartanInv_neg (ch.W.cart_is _ h2.inRange τ)) (fun τ => ch.W.cart_is _ h1.inRange τ)
      (isSelfDualC_neg (ch.S.N.selfDual h2)) (ch.S.N.selfDual h1) hv (negMem _ (y * ch.S.N.u _).2) (x * ch.S.N.u _).2
      fy fx hvac
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from ix,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from iy] at hvac
    exact exists_root hom (fun τ => ch.W.cart_is _ h1.inRange τ) (fun τ => ch.W.cart_is _ h2.inRange τ)
      (ch.S.N.selfDual h1) (ch.S.N.selfDual h2) hv (x * ch.S.N.u _).2 (y * ch.S.N.u _).2
      fx fy hvac

end GlobalTheory.MovedVacRoot

end

open GlobalTheory.MovedVacRoot in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_size_sum : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _ → GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _ →
    ∃ κ : ℂ, Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.UnitAt q κ) ∧ GlobalTheory.MovedKappaEx.JetKap ch p x y κ := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y hx hy
  obtain ⟨c, m, hm, h1, hc⟩ := moved_root hP hI ch hch p hp x y hx hy
  have h2 : (opp p c) ^ m = 1 := by rw [← map_pow, h1, map_one]
  have h3 := mem_Qbar_of_pow hm h2
  refine ⟨opp p c, ⟨h3, fun σ => norm_map_of_pow σ hm h2 h3⟩, fun q _ lam => ?_, fun k => ?_⟩
  · rw [lamC, dif_pos h3]
    exact norm_map_of_pow lam hm h2 h3
  · have hs : srcLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hy, hx, hy, hx]
    have ht : tgtLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hx, hy, hx, hy]
    have hoo : opp p (opp p c) = c := by
      cases p <;> simp [opp]
    have he0 := ch.S.Z.e0_is p hp
    have hK : KLat D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
      Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
    obtain ⟨-, -, hself, -⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ ch.S.Z.crv (ch.G.pS p).rank (ch.G.pT p).rank
    have hI0 : Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (srcLat ch.S.toGridChoice p x y) (tgtLat ch.S.toGridChoice p x y))
        (ch.S.Z.e0 p) = ch.S.Z.e0 p := by
      rw [hs, ht]
      exact hself _ hK _ he0.1
    have hd : Differentiable ℂ (ch.S.Z.e0 p) := he0.1.1
    have h0 := ch.S.Z.kernelNorm_constant_spec p hp k
    rw [hI0, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, hc]
    unfold fockIn at h0 ⊢
    rw [Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, Pi.smul_apply, h0, smul_eq_mul]
    simp only [map_mul, hoo]
    ring
