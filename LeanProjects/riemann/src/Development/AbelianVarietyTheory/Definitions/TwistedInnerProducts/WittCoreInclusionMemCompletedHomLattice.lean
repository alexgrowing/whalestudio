import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latMul latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin GlobalTheory.SeeSaw.SplitLat
open GlobalTheory.FinPlLoc (idem mem_idAt_iff mem_idOff_iff idem_mem_idAt idem_mul_self cA_idem latV_idAt)
open GlobalTheory.FinPl.LatMem (mem_latO_iff latO_mxAt)

namespace GlobalTheory.AscFinWit

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {P : GlobalTheory.FinPl.Pl D → Prop}

section Frames

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

end Frames

theorem mxAt_mul {l m n : ℕ} (A : Mx D l m) {u : Mx D m n} (hu : MxAt P u) : MxAt P (A ⬝ u) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_mul' {l m n : ℕ} {u : Mx D l m} (hu : MxAt P u) (B : Mx D m n) : MxAt P (u ⬝ B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_iff {m n : ℕ} {u : Mx D m n} : MxAt P u ↔ idem D P • u = u :=
  ⟨fun h => Matrix.ext fun i j => (mem_idAt_iff P _).1 (h i j), fun h i j => (mem_idAt_iff P _).2 (congrFun (congrFun h i) j)⟩

theorem mxAt_idem {m n : ℕ} (u : Mx D m n) : MxAt P (idem D P • u) := fun _ _ => Ideal.mul_mem_right _ _ (idem_mem_idAt P)

theorem mxAt_top {m n : ℕ} {u : Mx D m n} (h : MxAt P u) : MxAt (fun _ => True) u := fun i j =>
  GlobalTheory.FinPl.LatMem.mem_idAt_iff.2 ⟨(GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 (h i j)).1, fun _ hw => (hw trivial).elim⟩

theorem finLat_of {m n : ℕ} {A : AddSubgroup (Mx D m n)} (fin : ∀ a ∈ A, MxAt (fun _ => True) a)
    (opn : ∃ U : Set (Mx D m n), IsOpen U ∧ (0 : Mx D m n) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ A)
    {C : Set (Mx D m n)} (hC : IsCompact C) (h : ∀ a ∈ A, a ∈ C) : FinLat A := by
  refine ⟨fin, hC.of_isClosed_subset ?_ h, opn⟩
  obtain ⟨i1, -, -, i4, -⟩ := lattice_Mx D m n
  obtain ⟨U, h1, h2, h3⟩ := opn
  let e : Mx D m n →+ Mx D m n := DistribMulAction.toAddMonoidHom _ (idem D fun _ => True)
  have he : Continuous e := continuous_id.const_smul (idem D fun _ => True)
  have ho : IsOpen (A.comap e : Set (Mx D m n)) := (A.comap e).isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((h1.preimage he).mem_nhds (by rwa [Set.mem_preimage, map_zero])) fun a ha => h3 _ ha (mxAt_idem a))
  convert ((A.comap e).isClosed_of_isOpen ho).inter (isClosed_eq he continuous_id) using 1
  ext a
  refine ⟨fun ha => ⟨?_, mxAt_iff.1 (fin a ha)⟩, fun ⟨ha, hb⟩ => ?_⟩
  · show idem D (fun _ => True) • a ∈ A
    rwa [mxAt_iff.1 (fin a ha)]
  · exact (show e a = a from hb) ▸ ha

theorem finLat_comap {k l m n : ℕ} {Γ : AddSubgroup (Mx D m n)} (h : FinLat Γ) (f : Mx D k l →+ Mx D m n) {A : Mx D m k} {B : Mx D l n}
    {A' : Mx D k m} {B' : Mx D n l} (hf : ∀ a, f a = A ⬝ a ⬝ B) (hA : A' ⬝ A = 1) (hB : B ⬝ B' = 1) : FinLat (Γ.comap f) := by
  have e : ∀ a, A' ⬝ f a ⬝ B' = a := fun a => by
    rw [hf, Matrix.mul_assoc, Matrix.mul_assoc, hB, Matrix.mul_one, ← Matrix.mul_assoc, hA, Matrix.one_mul]
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have hc : Continuous f := by
    rw [show (f : _ → _) = _ from funext hf]
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine finLat_of (fun a ha => e a ▸ mxAt_mul' (mxAt_mul _ (h.fin _ ha)) _)
    ⟨f ⁻¹' U, h1.preimage hc, by rwa [Set.mem_preimage, map_zero], fun a ha hb => h3 _ ha (hf a ▸ mxAt_mul' (mxAt_mul _ hb) _)⟩
    (h.cpt.image (continuous_sandwich A' B'))
    fun a ha => ⟨_, ha, e a⟩

theorem sec_fin {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (s2 : ∀ a, finPart D (s a) = a) (s3 : ∀ a, infPart D (s a) = 0)
    {a : AE D} (ha : a ∈ idAt D P) (c : AE D) : s (finPart D (c * a)) = c * a := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, s3, RingHom.map_mul, GlobalTheory.FinPlLoc.infPart_of_idAt ha, mul_zero, sub_zero]
  · rw [RingHom.map_sub, s2, sub_self]

theorem finLat_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) : FinLat (latO S T (LS : Set _) (LT : Set _) fun _ => True) := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨s, s1, s2, s3⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  have inv : ∀ N : ℕ, 0 < N → incA D (N : D.host.E)⁻¹ * (N : AE D) = 1 := fun N hN => by
    rw [← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  refine finLat_of (fun a ha => latO_mxAt ha) ⟨{a | ∀ i j, finPart D (incA D (K : D.host.E)⁻¹ * a i j) ∈ intAE D}, ?_, ?_, ?_⟩
    (C := (fun z => Matrix.of fun i j => incA D (M : D.host.E)⁻¹ * s (z i j)) ''
      {z : Matrix (Fin T.rank) (Fin S.rank) _ | ∀ i j, z i j ∈ intAE D}) (IsCompact.image ?_ ?_) fun a ha => ?_
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage
      ((GlobalTheory.Member.continuous_finPart D).comp (continuous_const.mul (continuous_id.matrix_elem i j)))
  · intro i j
    rw [Matrix.zero_apply, mul_zero, map_zero]
    exact zero_mem _
  · intro a ha hb
    have := hmul (incA D (K : D.host.E)⁻¹ • a) (Matrix.ext fun i j => by
      show infPart D (_ * a i j) = 0
      rw [map_mul, GlobalTheory.FinPlLoc.infPart_of_idAt (hb i j), mul_zero]) fun i j => GlobalTheory.PlaceCoord.toEAf_mem (ha i j)
    rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, mul_comm, inv K hK, one_smul] at this
  · exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  · exact continuous_pi fun i => continuous_pi fun j => continuous_const.mul (s1.comp (continuous_id.matrix_elem i j))
  · refine ⟨Matrix.of fun i j => finPart D ((M : AE D) * a i j), fun i j => GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_,
      Matrix.ext fun i j => ?_⟩
    · rw [RingHom.map_mul, map_natCast]
      exact hden a ha i j
    · exact (congrArg (incA D (M : D.host.E)⁻¹ * ·) (sec_fin s2 s3 (latO_mxAt ha i j) _)).trans
        (by rw [← mul_assoc, inv M hM, one_mul])

section Maps

variable {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}

theorem latMul_map (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {𝔞 𝔞' : Set D.host.E}
    (h : ∀ a ∈ 𝔞, ∀ x ∈ LS, ∃ a' ∈ 𝔞', ∃ x' ∈ LT, M *ᵥ (a • x) = a' • x') {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 LS P) :
    rat M *ᵥ y ∈ latMul T 𝔞' LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    have := rat_mulVec_gen M (pairA D.host.F 0 β) (a • x)
    simp only [e, one_mul, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_left (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T' LT')
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hM : ∀ x ∈ LT, M *ᵥ x ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : rat M ⬝ u ∈ latO S T' (LS : Set _) (LT' : Set _) P := by
  rw [mem_latO_iff D _ _ _ _ hS hT] at hu
  refine (mem_latO_iff D _ _ _ _ hS hT' P _).2 ⟨mxAt_mul _ hu.1, fun y hy => ?_⟩
  show (rat M ⬝ u) *ᵥ y ∈ _
  rw [← mulVec_mulVec]
  exact latMul_map M (fun a ha x hx => ⟨a, ha, _, hM x hx, mulVec_smul _ _ _⟩) (hu.2 y hy)

theorem latO_right (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S' LS') (hT : IsSelfDualC T LT)
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hM : ∀ x ∈ LS', M *ᵥ x ∈ LS) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : u ⬝ rat M ∈ latO S' T (LS' : Set _) (LT : Set _) P := by
  rw [mem_latO_iff D _ _ _ _ hS hT] at hu
  refine (mem_latO_iff D _ _ _ _ hS' hT P _).2 ⟨mxAt_mul' hu.1 _, fun y hy => ?_⟩
  show (u ⬝ rat M) *ᵥ y ∈ _
  rw [← mulVec_mulVec]
  exact hu.2 _ (rat_mulVec_mem_latV M hM P hy)

theorem latO_inK (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {κ : GA D T} (hκ : InK T LT P κ) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : mt T κ ⬝ u ∈ latO S T (LS : Set _) (LT : Set _) P := by
  have := GlobalTheory.VacMove.actO_mem_latO hS hS hT hT (inK_one (P := P)).2 hκ.2 hu
  rwa [actO_eq, inv_one, mt_one, Matrix.mul_one] at this

theorem rat_mem_latO (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hM : ∀ x ∈ LS, M *ᵥ x ∈ LT) {α : D.host.E} (hα : α ∈ D.host.AA) :
    idem D P • rat (α • M) ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine (mem_latO_iff D _ _ _ _ hS hT P _).2 ⟨mxAt_idem _, fun y hy => ?_⟩
  show (idem D P • rat (α • M)) *ᵥ y ∈ _
  rw [smul_mulVec, ← mulVec_smul, show idem D P • y = y from funext fun i => (mem_idAt_iff P _).1 (latV_idAt hy i)]
  refine latMul_map _ (fun a ha x hx => ⟨α, hα, _, hM x hx, ?_⟩) hy
  rw [Set.mem_singleton_iff.1 ha, one_smul, smul_mulVec]

theorem idem_mem_latO {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    idem D P • u ∈ latO S T (LS : Set _) (LT : Set _) P := by
  have h := GlobalTheory.SelfDualAt.smul_mem_latO S T _ _ P u hu
  rwa [← algebraMap_smul (AE D)] at h

theorem mem_latO_at {u : WO S T} (h : MxAt P u) : u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
    u ∈ latO S T (LS : Set _) (LT : Set _) P :=
  ⟨fun hu => mxAt_iff.1 h ▸ idem_mem_latO hu, fun hu => GlobalTheory.PlaceModel.latO_le_top _ hu⟩

theorem psi_eq_one (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {x u : WO S T}
    (hx : idem D P • x ∈ latO S T (LS : Set _) (LT : Set _) P) (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) :
    ψ (symplO S T x u) = 1 := by
  have h := (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P _ (mxAt_idem x)).1 hx u hu
  have e := GlobalTheory.SelfDualAt.symplO_smul_swap S T (GlobalTheory.SelfDualAt.cP P) x u
  rw [← algebraMap_smul (AE D), ← algebraMap_smul (AE D) _ x] at e
  exact (congrArg ψ ((congrArg (symplO S T x) (mxAt_iff.1 (latO_mxAt hu)).symm).trans e)).trans h

theorem psi_swap (x u : WO S T) : ψ (symplO S T x u) = 1 ↔ ψ (symplO S T u x) = 1 := by
  rw [GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv, inv_eq_one]

theorem exists_vac (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) :
    ∃ f, VacG ψ S T (latO S T (LS : Set _) (LT : Set _) fun _ => True) f ∧ f ≠ 0 := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hcs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hcs S) (hcs T) _ _ hS hT
  obtain ⟨h1, h2, -⟩ := hf 1
  simp only [one_mul] at h1 h2
  exact ⟨f, ⟨h1, h2⟩, f0⟩

end Maps

section Sympl

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

theorem symplO_extX (a : Mx D T.rank ρ) (u : WO S T) : symplO S T (d.extX T a) u = symplO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  simp only [symplO_eq, d.hO_coordS, HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX,
    d.pY_j0, d.pY_jY, Matrix.mul_zero, Matrix.mul_one, hO_eq_trace S₀, pairS, trace_zero]

theorem symplO_extY (a : Mx D T.rank ρ) (u : WO S T) : symplO S T (d.extY T a) u = symplO S T (d.extY T a) (d.extX T (u ⬝ d.jX)) := by
  simp only [symplO_eq, d.hO_coordS, HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX,
    d.pY_j0, d.pY_jY, Matrix.mul_zero, Matrix.mul_one, hO_eq_trace S₀, pairS, trace_zero]

theorem symplO_incX (a : Mx D ρ T.rank) (u : WO T S) : symplO T S (d.incX T a) u = symplO T S (d.incX T a) (d.incY T (d.pY ⬝ u)) := by
  simp only [symplO_eq, d.hO_coordT, HypDec.incX_apply, HypDec.incY_apply, cancel₂ d.pX_jX, cancel₂ d.p0_jX, cancel₂ d.pX_jY,
    cancel₂ d.pY_jX, cancel₂ d.p0_jY, cancel₂ d.pY_jY, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, hO_eq_trace T S₀, pairT, trace_zero]

theorem symplO_incY (a : Mx D ρ T.rank) (u : WO T S) : symplO T S (d.incY T a) u = symplO T S (d.incY T a) (d.incX T (d.pX ⬝ u)) := by
  simp only [symplO_eq, d.hO_coordT, HypDec.incX_apply, HypDec.incY_apply, cancel₂ d.pX_jX, cancel₂ d.p0_jX, cancel₂ d.pX_jY,
    cancel₂ d.pY_jX, cancel₂ d.p0_jY, cancel₂ d.pY_jY, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, hO_eq_trace T S₀, pairT, trace_zero]

end Sympl

section Parts

variable {S S₀ T : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L₀ : Lat S₀} {𝔟 : ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {LT : Lat T}
  (hS : IsSelfDualC S (splitL d L₀ 𝔟)) (h₀ : IsSelfDualC S₀ L₀) (hT : IsSelfDualC T LT)

theorem projX_mem (x : Fin S.rank → D.host.E) (hx : x ∈ splitL d L₀ 𝔟) : (d.e * d.qX) *ᵥ x ∈ splitL d L₀ 𝔟 := by
  rw [← mulVec_mulVec]
  exact e_mem ((mem_splitL d L₀ 𝔟 x).1 hx).1

theorem projY_mem (x : Fin S.rank → D.host.E) (hx : x ∈ splitL d L₀ 𝔟) : (d.e' * d.qY) *ᵥ x ∈ splitL d L₀ 𝔟 := by
  rw [← mulVec_mulVec]
  exact e'_mem ((mem_splitL d L₀ 𝔟 x).1 hx).2.2

include hS hT

theorem srcX {u : WO S T} (hu : u ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P) :
    d.extX T (u ⬝ d.jX) ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P := by
  have := latO_right hS hS hT _ projX_mem hu
  rwa [rat_mul, ← Matrix.mul_assoc] at this

theorem srcY {u : WO S T} (hu : u ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P) :
    d.extY T (u ⬝ d.jY) ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P := by
  have := latO_right hS hS hT _ projY_mem hu
  rwa [rat_mul, ← Matrix.mul_assoc] at this

theorem tgtX {u : WO T S} (hu : u ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P) :
    d.incX T (d.pX ⬝ u) ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P := by
  have := latO_left hT hS hS _ projX_mem hu
  rwa [rat_mul, Matrix.mul_assoc] at this

theorem tgtY {u : WO T S} (hu : u ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P) :
    d.incY T (d.pY ⬝ u) ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P := by
  have := latO_left hT hS hS _ projY_mem hu
  rwa [rat_mul, Matrix.mul_assoc] at this

theorem dualX (hψ : IsStdChar D ψ (-1)) {a : Mx D T.rank ρ} (ha : MxAt P a) :
    d.extX T a ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P ↔
      ∀ a', d.extY T a' ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P → ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T _ LT hS hT P _ (mxAt_mul' ha d.pX)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu => (congrArg ψ (symplO_extX d T a u)).trans (h _ (srcY hS hT hu))⟩

theorem dualY (hψ : IsStdChar D ψ (-1)) {a' : Mx D T.rank ρ} (ha : MxAt P a') :
    d.extY T a' ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P ↔
      ∀ a, d.extX T a ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P → ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T _ LT hS hT P _ (mxAt_mul' ha d.pY)).trans ?_
  exact ⟨fun h _ ha' => (psi_swap _ _).1 (h _ ha'),
    fun h u hu => (congrArg ψ (symplO_extY d T a' u)).trans ((psi_swap _ _).1 (h _ (srcX hS hT hu)))⟩

theorem dualX' (hψ : IsStdChar D ψ (-1)) {a : Mx D ρ T.rank} (ha : MxAt P a) :
    d.incX T a ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P ↔
      ∀ a', d.incY T a' ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P → ψ (symplO T S (d.incX T a) (d.incY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ T S LT _ hT hS P _ (mxAt_mul d.jX ha)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu => (congrArg ψ (symplO_incX d T a u)).trans (h _ (tgtY hS hT hu))⟩

theorem dualY' (hψ : IsStdChar D ψ (-1)) {a' : Mx D ρ T.rank} (ha : MxAt P a') :
    d.incY T a' ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P ↔
      ∀ a, d.incX T a ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P → ψ (symplO T S (d.incX T a) (d.incY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ T S LT _ hT hS P _ (mxAt_mul d.jY ha)).trans ?_
  exact ⟨fun h _ ha' => (psi_swap _ _).1 (h _ ha'),
    fun h u hu => (congrArg ψ (symplO_incY d T a' u)).trans ((psi_swap _ _).1 (h _ (tgtX hS hT hu)))⟩

include h₀

theorem src0 {u : WO S T} (hu : u ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P) :
    u ⬝ d.j0 ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P := latO_right hS h₀ hT d.i₀ (fun _ => i₀_mem) hu

theorem tgt0 {u : WO T S} (hu : u ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P) :
    d.p0 ⬝ u ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P := latO_left hT hS h₀ d.q0 (fun x hx => ((mem_splitL d L₀ 𝔟 x).1 hx).2.1) hu

theorem wittExtendByZero_mem_completedHomLattice {w : WO S₀ T} :
    d.ext0 T w ∈ latO S T (splitL d L₀ 𝔟 : Set _) (LT : Set _) P ↔ w ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P :=
  ⟨fun h => by simpa only [HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] using src0 hS h₀ hT h,
    fun h => latO_right h₀ hS hT d.q0 (fun x hx => ((mem_splitL d L₀ 𝔟 x).1 hx).2.1) h⟩

theorem wittCoreInclusion_mem_completedHomLattice {w : WO T S₀} :
    d.inc0 T w ∈ latO T S (LT : Set _) (splitL d L₀ 𝔟 : Set _) P ↔ w ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P :=
  ⟨fun h => by simpa only [HypDec.wittDecomp_inclAnisotropicHom_apply, cancel₂ d.p0_j0, Matrix.one_mul] using tgt0 hS h₀ hT h,
    fun h => latO_left hT h₀ hS d.i₀ (fun _ => i₀_mem) h⟩

end Parts

section Pcs

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (LV₀ : Lat V₀) (LW₀ : Lat W₀)
  (𝔟 𝔠 : ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

abbrev homL (P : GlobalTheory.FinPl.Pl D → Prop) : AddSubgroup (WO V W) :=
  latO V W (splitL dV LV₀ 𝔟 : Set _) (splitL dW LW₀ 𝔠 : Set _) P

abbrev pcs (ψ : AddChar (AF D.host.F) ℂ) : Pieces V₀ W W₀ ρ σ :=
  piecesOf dV dW ψ (homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True) (homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True)

theorem stdAt_pcs (v : GlobalTheory.FinPl.Pl D) : StdAt dV dW (pcs dV dW LV₀ LW₀ 𝔟 𝔠 ψ) (splitL dV LV₀ 𝔟) (splitL dW LW₀ 𝔠) v where
  a _ ha := mem_latO_at (mxAt_mul' ha dV.pX)
  a' a ha := ⟨idem D (· = v) • a, fun i j => (mem_idOff_iff _ _).2 (by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, idem_mul_self, sub_self]), by
    rw [HypDec.extX_apply, Matrix.smul_mul]
    exact idem_mem_latO ha⟩
  b _ ha := mem_latO_at (mxAt_mul' (mxAt_mul dW.jX ha) dV.p0)

variable {dV dW LV₀ LW₀ 𝔟 𝔠} (hψ : IsStdChar D ψ (-1)) (hV : IsSelfDualC V (splitL dV LV₀ 𝔟)) (hV₀ : IsSelfDualC V₀ LV₀)
  (hW : IsSelfDualC W (splitL dW LW₀ 𝔠)) (hW₀ : IsSelfDualC W₀ LW₀) {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ}

include hψ hV hW

theorem pcs_A₂ : (pcs dV dW LV₀ LW₀ 𝔟 𝔠 ψ).A₂ = (homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True).comap (dV.extY W) := by
  refine (congrArg AddSubgroup.closure (Set.ext fun a => ?_)).trans (AddSubgroup.closure_eq _)
  refine ⟨fun h => (dualY hV hW hψ h.1).2 h.2, fun h => ?_⟩
  have : MxAt (fun _ => True) a := by
    simpa only [HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one] using mxAt_mul' (latO_mxAt h) dV.jY
  exact ⟨this, (dualY hV hW hψ this).1 h⟩

include hV₀ hW₀

theorem is_pcs (uni : ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) →
      dV.extX W (x ⬝ u.1.1 - x) ∈ homL dV dW LV₀ LW₀ 𝔟 𝔠 (fun _ => True) → psiUni ψ u.1 = 1) :
    (pcs dV dW LV₀ LW₀ 𝔟 𝔠 ψ).Is dV dW x ψ where
  a₁ := finLat_comap (finLat_latO hV.1 hW.1) _ (A := 1) (A' := 1) (fun a => by rw [Matrix.one_mul]; rfl) (Matrix.one_mul _) dV.pX_jX
  a₂ := by
    rw [pcs_A₂ hψ hV hW]
    exact finLat_comap (finLat_latO hV.1 hW.1) _ (A := 1) (A' := 1) (fun a => by rw [Matrix.one_mul]; rfl) (Matrix.one_mul _) dV.pY_jY
  b₁ := finLat_comap (finLat_latO hV.1 hW.1) _ (fun _ => rfl) dW.pX_jX dV.p0_j0
  b₂ := finLat_comap (finLat_latO hV.1 hW.1) _ (fun _ => rfl) dW.pY_jY dV.p0_j0
  dualA a ha := by
    rw [pcs_A₂ hψ hV hW]
    exact dualX hV hW hψ ha
  dualA' a ha := by
    rw [pcs_A₂ hψ hV hW]
    exact dualY hV hW hψ ha
  dualB a ha := (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).trans ((dualX' hW hV₀ hψ ha).trans
    (forall_congr' fun _ => imp_congr_left (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).symm))
  dualB' a ha := (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).trans ((dualY' hW hV₀ hψ ha).trans
    (forall_congr' fun _ => imp_congr_left (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).symm))
  uni := uni
  fin₀ u hu := latO_mxAt ((wittCoreInclusion_mem_completedHomLattice hW hW₀ hV₀).1 ((wittExtendByZero_mem_completedHomLattice hV hV₀ hW).1 hu))
  vac₀ := by
    obtain ⟨f, hf, f0⟩ := exists_vac hψ hV₀ hW₀
    exact ⟨f, ⟨hf.1, fun u hu => hf.2.1 u ((wittCoreInclusion_mem_completedHomLattice hW hW₀ hV₀).1 ((wittExtendByZero_mem_completedHomLattice hV hV₀ hW).1 hu)),
      fun e he u hu => hf.2.2 e he u ((wittCoreInclusion_mem_completedHomLattice hW hW₀ hV₀).1 ((wittExtendByZero_mem_completedHomLattice hV hV₀ hW).1 hu))⟩, f0⟩

variable (hx : idem D (fun _ => True) • dV.extX W x ∈ homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True)
  (hy : idem D (fun _ => True) • dW.incAdj V₀ y ∈ latO V₀ W (LV₀ : Set _) (splitL dW LW₀ 𝔠 : Set _) fun _ => True)

include hx hy

theorem splits_pcs : Splits dV dW (pcs dV dW LV₀ LW₀ 𝔟 𝔠 ψ) x y ψ (homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True) := by
  refine ⟨fun u hu => ?_⟩
  have h0 := src0 hV hV₀ hW hu
  refine ⟨_, srcX hV hW hu, u ⬝ dV.jY, ?_, _, (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).2 (tgtX hW hV₀ h0), _, (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).2 (tgtY hW hV₀ h0),
    _, (wittExtendByZero_mem_completedHomLattice hV hV₀ hW).2 ((wittCoreInclusion_mem_completedHomLattice hW hW₀ hV₀).2 (tgt0 hW hW₀ hV₀ h0)), ?_, psi_eq_one hψ hV hW hx (srcY hV hW hu),
    psi_eq_one hψ hV₀ hW hy (tgtX hW hV₀ h0)⟩
  · rw [pcs_A₂ hψ hV hW]
    exact srcY hV hW hu
  · have e : dW.incX V₀ _ + dW.inc0 V₀ _ + dW.incY V₀ _ = u ⬝ dV.j0 := (dW.coordT V₀).left_inv (u ⬝ dV.j0)
    rw [add_right_comm] at e
    rw [add_right_comm]
    exact ((dV.coordS W).left_inv u).symm.trans (congrArg (fun w => dV.extX W (u ⬝ dV.jX) + dV.ext0 W w + dV.extY W (u ⬝ dV.jY)) e.symm)

omit hW₀ in

theorem vac_mem_cls {f : WO V W → ℂ} (hf : VacG ψ V W (homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True) f) :
    f ∈ cls dV dW (pcs dV dW LV₀ LW₀ 𝔟 𝔠 ψ) x y ψ := by
  have key := GlobalTheory.FinPl.FlatFix.fix_of_isotropic ψ V W _ _ _ hV hW (fun v _ => GlobalTheory.FinPl.TamePlaces.tame D v) f hf.2
  refine ⟨hf.1, fun a ha => key _ ha fun c c' => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => key _ ha fun c c' => ?_, ?_, ?_⟩
  · simpa only [HypDec.extX_apply, Matrix.smul_mul] using dV.symplOH_extX_extX W (c • a) (c' • a)
  · rw [pcs_A₂ hψ hV hW] at ha
    rw [psi_eq_one hψ hV hW hx ha, one_smul]
    refine key _ ha fun c c' => ?_
    simpa only [HypDec.extY_apply, Matrix.smul_mul] using dV.symplOH_extY_extY W (c • a) (c' • a)
  · rw [psi_eq_one hψ hV₀ hW hy ((wittExtendByZero_mem_completedHomLattice hV hV₀ hW).1 ha), one_smul]
    refine key _ ha fun c c' => ?_
    simpa only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.smul_mul, Matrix.mul_smul] using
      (dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W _ _).trans (dW.symplOH_incX_incX V₀ (c • a) (c' • a))
  · simpa only [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.smul_mul, Matrix.mul_smul, AddMonoidHom.comp_apply] using
      (dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W _ _).trans (dW.symplOH_incY_incY V₀ (c • a) (c' • a))
  · rintro _ ⟨w, hw, rfl⟩
    exact hf.2.1 _ hw
  · rintro e he _ ⟨w, hw, rfl⟩
    exact hf.2.2 e he _ hw

end Pcs

theorem exists_uni {ρ : ℕ} {N : Mx D ρ ρ} (h2 : ∀ i j, j ≤ i → N i j = 0) : ∃ u : UX D ρ, u.1.1 = 1 + N := by
  have hd : (1 + N).det = 1 := by
    rw [Matrix.det_of_upperTriangular fun i j (h : j < i) => by
      rw [Matrix.add_apply, h2 i j h.le, Matrix.one_apply_ne h.ne', add_zero]]
    exact Finset.prod_eq_one fun i _ => by rw [Matrix.add_apply, h2 i i le_rfl, Matrix.one_apply_eq, add_zero]
  obtain ⟨u, hu⟩ : IsUnit (1 + N) := (Matrix.isUnit_iff_isUnit_det _).2 (hd ▸ isUnit_one)
  exact ⟨⟨u, fun i j => ⟨fun h => by rw [hu, Matrix.add_apply, h2 i j h.le, Matrix.one_apply_ne h.ne', add_zero],
    by rw [hu, Matrix.add_apply, h2 i i le_rfl, Matrix.one_apply_eq, add_zero]⟩⟩, hu⟩

theorem upSum_one_add {ρ : ℕ} (N : Mx D ρ ρ) : upSum (1 + N) = upSum N := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Matrix.add_apply, Matrix.one_apply_ne (fun e => by rw [e] at h; omega), zero_add]
  · rfl

theorem condK_one {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ} {p : Pieces V₀ W W₀ ρ σ}
    {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {LV : Lat V} {LW : Lat W} {v : GlobalTheory.FinPl.Pl D} (hV : IsSelfDualC V LV)
    (hW : IsSelfDualC W LW) (hp : p.Is dV dW x ψ) (hs : StdAt dV dW p LV LW v)
    (hx : idem D (· = v) • dV.extX W x ∈ latO V W (LV : Set _) (LW : Set _) (· = v))
    (hy : ∀ ξ, dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) →
      ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) = 1) : CondK dW p x y ψ LW (· = v) 1 := by
  intro κ hκ
  rw [one_mul]
  refine ⟨⟨1, idem D (· = v) • (mt W κ⁻¹ ⬝ x - x), (hs.a _ (mxAt_idem _)).2 ?_, fun i j => (mem_idOff_iff _ _).2 ?_⟩,
    fun N h1 h2 h3 => ?_, fun ξ h1 ξ' h2 h3 => ?_⟩
  · convert sub_mem (latO_inK hV hW (inK_inv hκ) hx) hx using 1
    simp only [HypDec.extX_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, smul_sub, Matrix.mul_assoc]
  · rw [show x ⬝ (1 : UX D ρ).1.1 = x from Matrix.mul_one x, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc,
      idem_mul_self, sub_self]
  · have h4 := latO_inK hV hW hκ ((hs.a _ (mxAt_mul _ (mxAt_mul _ h1))).1 h3)
    rw [HypDec.extX_apply, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W κ), mt_mul_inv, Matrix.one_mul] at h4
    obtain ⟨u, hu⟩ := exists_uni h2
    have h5 := hp.uni u (by rw [hu, add_sub_cancel_left]; exact mxAt_top h1) (by
      rw [hu, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
      exact (hs.a _ (mxAt_mul _ h1)).2 h4)
    rwa [psiUni, hu, upSum_one_add] at h5
  · have h4 := (hs.b _ h2).1 h1
    have h5 := latO_inK hV hW hκ h4
    rw [HypDec.matrixExtendByZero_apply, ← Matrix.mul_assoc, h3] at h5
    rw [hy _ h4, hy _ h5]

section Stair

variable {V V₀ W W₀ : HSp D} {ρ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ ρ} {LV₀ : Lat V₀} {LW₀ : Lat W₀}
  {𝔟 𝔠 : ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hψ : IsStdChar D ψ (-1)) (hV : IsSelfDualC V (splitL dV LV₀ 𝔟))
  (hW : IsSelfDualC W (splitL dW LW₀ 𝔠)) {α : D.host.E} (hα : α ∈ D.host.AA) (α0 : α ≠ 0)

def shiftM (D : D7) (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) D.host.E := Matrix.of fun i j => if j.1 = i.1 + 1 then 1 else 0

theorem trace_shiftM (N : Mx D ρ ρ) : (adj (rat (shiftM D ρ)) ⬝ N).trace = upSum N := by
  rw [← rat_conjTranspose, Matrix.trace, upSum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show incA D (star (if j.1 = i.1 + 1 then (1 : D.host.E) else 0)) * N i j = _
  split_ifs
  · rw [star_one, map_one, one_mul]
  · rw [star_zero, map_zero, zero_mul]

theorem pairS_jX_jY (N M : Mx D ρ ρ) : pairS W (dW.jX ⬝ N) (dW.jY ⬝ M) = (adj M ⬝ N).trace := by
  rw [pairS, adj_mul, Matrix.mul_assoc, cancel₃ dW.gram_YX, Matrix.one_mul]

theorem hO_extX_extY (a b : Mx D W.rank ρ) : hO V W (dV.extX W a) (dV.extY W b) = pairS W a b := by
  have h := dV.hO_ext W a 0 0 b 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace V₀, Matrix.mul_zero, trace_zero] at h
  rw [h, show pairS W (0 : Mx D W.rank ρ) 0 = 0 by simp [pairS], add_zero]

variable (dV dW) in

theorem symplO_shift (N : Mx D ρ ρ) :
    symplO V W (dV.extX W (dW.jX ⬝ N)) (dV.extY W (dW.jY ⬝ (incA D (-D.host.xi0⁻¹) • rat (shiftM D ρ)))) =
      Algebra.trace (AF D.host.F) (AE D) (upSum N) := by
  rw [symplO_eq, hO_extX_extY, pairS_jX_jY, adj_smul,
    Matrix.smul_mul (cA D (incA D (-D.host.xi0⁻¹))) (adj (rat (shiftM D ρ))) N, ← trace_shiftM N]
  exact congrArg _ (mul_trace_smul (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)) (adj (rat (shiftM D ρ)) ⬝ N))

include hV hW hα α0

theorem xZero_mem (h1 : ∀ i, ∀ b ∈ 𝔟 i, α⁻¹ * b ∈ 𝔠 i) : idem D P • dV.extX W (xZero dW) ∈ homL dV dW LV₀ LW₀ 𝔟 𝔠 P := by
  have := rat_mem_latO (P := P) hV hW (dW.e * (α⁻¹ • dV.qX)) (fun z hz => by
    rw [← mulVec_mulVec, smul_mulVec]
    exact e_mem fun i => h1 i _ (((mem_splitL _ _ _ z).1 hz).1 i)) hα
  rwa [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ α0, one_smul, rat_mul] at this

include hψ in

theorem uni_xZero (h2 : ∀ i, ∀ w ∈ dualC (𝔟 (i + 1)), α⁻¹ * -D.host.xi0⁻¹ * w ∈ dualC (𝔠 i)) (u : UX D ρ)
    (h : dV.extX W (xZero dW ⬝ u.1.1 - xZero dW) ∈ homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True) : psiUni ψ u.1 = 1 := by
  have hw := rat_mem_latO (P := fun _ => True) hV hW (dW.e' * ((α⁻¹ * -D.host.xi0⁻¹) • shiftM D ρ) * dV.qY) (fun z hz => by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine e'_mem fun i => ?_
    rw [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => ?_
    show α⁻¹ * -D.host.xi0⁻¹ * (if j.1 = i.1 + 1 then (1 : D.host.E) else 0) * (dV.qY *ᵥ z) j ∈ _
    split_ifs with e
    · rw [mul_one]
      exact h2 i _ (e ▸ ((mem_splitL _ _ _ z).1 hz).2.2 j)
    · rw [mul_zero, zero_mul]
      exact zero_mem _) hα
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, smul_smul, mul_inv_cancel_left₀ α0, rat_mul, rat_mul, rat_smul] at hw
  have h3 := (psi_swap _ _).1 (psi_eq_one hψ hV hW hw h)
  have e : xZero dW ⬝ u.1.1 - xZero dW = dW.jX ⬝ (u.1.1 - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]; rfl
  rw [e] at h3
  rw [psiUni, ← add_sub_cancel 1 u.1.1, upSum_one_add]
  exact (congrArg ψ (symplO_shift dV dW _)).symm.trans h3

end Stair

theorem exists_ideals (D : D7) : ∃ (α : D.host.E) (𝔟 𝔠 : ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), α ∈ D.host.AA ∧ α ≠ 0 ∧
    (∀ i, 𝔟 i ≠ 0) ∧ (∀ i, 𝔠 i ≠ 0) ∧ (∀ i, ∀ b ∈ 𝔟 i, α⁻¹ * b ∈ 𝔠 i) ∧
    ∀ i, ∀ w ∈ dualC (𝔟 (i + 1)), α⁻¹ * -D.host.xi0⁻¹ * w ∈ dualC (𝔠 i) := by
  obtain ⟨α, hα, α0⟩ := GlobalTheory.SeeSaw.SplitLat.exists_ne_zero (GlobalTheory.FinPl.LocGen.AA_ne_zero D)
  have α1 : star α ≠ 0 := star_ne_zero.2 α0
  set t := star (-D.host.xi0⁻¹) * (star α * α)⁻¹ with ht
  have t0 : t ≠ 0 := mul_ne_zero (star_ne_zero.2 (neg_ne_zero.2 (inv_ne_zero cmHost_imaginaryGenerator_ne_zero))) (inv_ne_zero (mul_ne_zero α1 α0))
  refine ⟨α, fun i => FractionalIdeal.spanSingleton _ (α * t ^ i), fun i => FractionalIdeal.spanSingleton _ (t ^ i), hα, α0,
    fun i => FractionalIdeal.spanSingleton_ne_zero_iff.2 (mul_ne_zero α0 (pow_ne_zero _ t0)),
    fun i => FractionalIdeal.spanSingleton_ne_zero_iff.2 (pow_ne_zero _ t0), fun i b hb => ?_, fun i w hw b hb => ?_⟩
  · obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hb
    exact (FractionalIdeal.mem_spanSingleton _).2 ⟨r, by rw [mul_smul_comm, inv_mul_cancel_left₀ α0]⟩
  · obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hb
    convert hw _ ((FractionalIdeal.mem_spanSingleton _).2 ⟨r, rfl⟩) using 1
    have e : star t = -D.host.xi0⁻¹ * (α * star α)⁻¹ := by rw [ht, star_mul', star_star, star_inv₀, star_mul', star_star]
    simp only [Algebra.smul_def, pow_succ, star_mul', e]
    field_simp

theorem yZero_nsmul (S : HSp D) (ρ N : ℕ) (z : Fin S.rank → D.host.E) : yZero S ρ (N • z) = N • yZero S ρ z := by
  ext k i
  show -(incA D (N • z k) * ell D ρ i) = N • -(incA D (z k) * ell D ρ i)
  rw [map_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_neg, mul_assoc]

theorem inhabitants (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    {z₀ : Fin V₀.rank → D.host.E} (hz : z₀ ≠ 0) :
    ∃ (p : Pieces V₀ W W₀ ρ ρ) (Γ : AddSubgroup (WO V W)) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (N : ℕ), 0 < N ∧
      FinLat Γ ∧ p.Is dV dW (xZero dW) ψ ∧ Splits dV dW p (xZero dW) (yZero V₀ ρ (N • z₀)) ψ Γ ∧
      (∃ Φ ∈ cls dV dW p (xZero dW) (yZero V₀ ρ (N • z₀)) ψ, Φ ≠ 0) ∧
      (∀ v, StdAt dV dW p LV LW v ∧ CondK dW p (xZero dW) (yZero V₀ ρ (N • z₀)) ψ LW (· = v) 1) ∧
      ∀ᶠ v in Filter.cofinite, GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v ∧ (0 < ρ → ∀ a ∈ idAt D (· = v),
        dW.incAdj V₀ (a • yZero V₀ ρ (N • z₀)) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) := by
  obtain ⟨α, 𝔟, 𝔠, hα, α0, b0, c0, h1, h2⟩ := exists_ideals D
  have hV₀ := GlobalTheory.PlaceModel.isSelfDualC_latFrame V₀
  have hW₀ := GlobalTheory.PlaceModel.isSelfDualC_latFrame W₀
  have hV := isSelfDualC_splitL dV b0 hV₀
  have hW := isSelfDualC_splitL dW c0 hW₀
  obtain ⟨N, hN, hy⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := V₀) (T := W) hV₀.1 hW.1
    (idem D (fun _ => True) • dW.incAdj V₀ (yZero V₀ ρ z₀))
    (Matrix.ext fun i j => GlobalTheory.FinPlLoc.infPart_of_idAt (mxAt_idem (P := fun _ => True) _ i j))
  rw [smul_comm, ← map_nsmul, ← yZero_nsmul] at hy
  have hp := is_pcs hψ hV hV₀ hW hW₀ (x := xZero dW) fun u _ => uni_xZero hψ hV hW hα α0 h2 u
  obtain ⟨f, hf, f0⟩ := exists_vac hψ hV hW
  refine ⟨_, _, _, GlobalTheory.PlaceModel.latFrame V₀, _, GlobalTheory.PlaceModel.latFrame W₀, N, hN, finLat_latO hV.1 hW.1, hp, splits_pcs hψ hV hV₀ hW hW₀ (xZero_mem hV hW hα α0 h1) hy,
    ⟨f, vac_mem_cls hψ hV hV₀ hW (xZero_mem hV hW hα α0 h1) hy hf, f0⟩, fun v => ⟨stdAt_pcs _ _ _ _ _ _ v,
      condK_one hV hW hp (stdAt_pcs _ _ _ _ _ _ v) (xZero_mem hV hW hα α0 h1) fun ξ hξ =>
        psi_eq_one hψ hV₀ hW hy (GlobalTheory.PlaceModel.latO_le_top _ ((wittExtendByZero_mem_completedHomLattice hV hV₀ hW).1 hξ))⟩, Filter.Eventually.and ?_ ?_⟩
  · filter_upwards [GlobalTheory.FinPl.Inhab.ae_primAt hψ dV hV, GlobalTheory.FinPl.Inhab.ae_colsAt dV (GlobalTheory.FinPl.Inhab.ratCols_jX dW) hV hW] with v a b
    exact ⟨hV, hV₀, hW, hW₀, monoAt_splitL _ _ _ v, monoAt_splitL _ _ _ v, a, b⟩
  · rcases Nat.eq_zero_or_pos ρ with h0 | hρ
    · exact Filter.Eventually.of_forall fun v h => absurd h (by omega)
    obtain ⟨M, hM, e⟩ := GlobalTheory.FinPl.Inhab.incAdj_yZero dW V₀ (z := N • z₀)
      (by rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact smul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hz) hρ
    have hM' : (fun ij : Fin W.rank × Fin V₀.rank => M ij.1 ij.2) ≠ 0 := fun h => hM (Matrix.ext fun i j => congrFun h (i, j))
    filter_upwards [GlobalTheory.FinPl.Inhab.ae_latO hV₀ hW, GlobalTheory.FinPl.Inhab.ae_family hM'] with v k1 k2 _ a _
    rw [k1, GlobalTheory.FinPl.Inhab.incAdj_smul, e, ← GlobalTheory.FinPl.Inhab.mem_intGrp, ← GlobalTheory.FinPl.Inhab.int_cA_iff, ← k2, Prod.forall]
    rfl

example (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ : HSp D) (d : HypDec V V₀ 1) (p : Pieces V₀ V V₀ 1 1), 0 < V₀.rank ∧
    IsStdChar D ψ (-1) ∧ p.Is d d (xZero d) ψ := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨p, -, -, -, -, -, -, -, -, h, -⟩ := inhabitants hψ (hypDecThree D) (hypDecThree D) (z₀ := fun _ => 1)
    fun h => one_ne_zero (congrFun h ⟨0, Nat.one_pos⟩)
  exact ⟨ψ, _, _, _, p, Nat.one_pos, hψ, h⟩

end GlobalTheory.AscFinWit

end
