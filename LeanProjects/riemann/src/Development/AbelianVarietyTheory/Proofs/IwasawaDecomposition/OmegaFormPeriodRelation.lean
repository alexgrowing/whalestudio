import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThirdStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

set_option maxHeartbeats 800000 in

theorem class_lattice_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ k, (O.La t k).La ∈ Vset D.host.E (Vc D i).rank 1 ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC (Vc D i) (h k)) (stdL D.host.E (Vc D i).rank) (O.La t k).La ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)) (x : (AE D)ˣ), IsIdemSum e P ∧ SuppAt e (Vc D i) (h k) ∧ IsDetAt e (Vc D i) (h k) x ∧ inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = ((((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 x)⁻¹ : Circle) : ℂ) * ((Real.sqrt ((((((O.La t k).La ⊓ stdL D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index ^ D.R.r : ℕ) : ℝ)) : ℝ) : ℂ) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨tie⟩ i Tp tup O hO t h J' hR k
  obtain ⟨-, hbad, -, -, -, -, hk⟩ := hR
  obtain ⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩ := hk k
  obtain ⟨r1, -, -, r4, -, -⟩ := (hO.reps t).1 k
  obtain ⟨x, hx⟩ := exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)
  refine ⟨?_, ?_, e, P, x, he, hs, hx, ?_⟩
  · have hU := (GenLatCmp.unimod_iff (O.La t k).La).1 r1
    have h4 : ∀ u ∈ stdL D.host.E (Vc D i).rank, (O.Nc t k : D.host.E) • u ∈ (O.La t k).La := fun u hu =>
      ((GenLatCmp.span_smul_le _ _ _).1 r4.2.2 u (GenLatCmp.std_eq (E := D.host.E) ▸ hu)).1
    have h5 := GenLatCmp.smul_mem_std hU h4
    exact ⟨GenLatCmp.fg_of_smul_le r4.1.pos h5, hU, _, r4.1.pos, Nat.coprime_one_right _, h5, h4⟩
  · refine isMov_conj (isMov_hLat _ (hO.lift.std.2.trans GenLatCmp.std_eq) (h k)) fun v => ?_
    rw [← hLh]
    exact (hO.reps t).2 k v
  · rw [GlobalTheory.T.oscillator_model_values_third D G Pl0 T0 A T R F κ v₀ hC ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩ i Tp tup O hO
      t k (h k) e P x he hP hs hx hLh hbad, Circle.coe_inv, Nat.cast_pow, GenLatCmp.std_eq]

end GlobalTheory.OneMapRef.ClassScalar
