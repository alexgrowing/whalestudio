import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPtLeClosureAndSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.LatVac (liftV)

variable {D : D7} {S T : HSp D} {n k : ℕ} (m : Matrix (Fin n) (Fin k) (AE D) ≃ₗ[AE D] WO S T) (Λ : AddSubgroup (WO S T))

theorem m_smul (c : AF D.host.F) (u : Matrix (Fin n) (Fin k) (AE D)) : m (c • u) = c • m u := by
  rw [← algebraMap_smul (AE D) c u, map_smul, algebraMap_smul]

theorem isHalf_m {a : AE D} {u : Matrix (Fin n) (Fin k) (AE D)} : IsHalf a (m u) ↔ IsHalf a u := by
  have h1 : IsHalf a (m u) ↔ a • m u = m u := ⟨fun h => Matrix.ext h, fun h p q => congrFun (congrFun h p) q⟩
  have h2 : IsHalf a u ↔ a • u = u := ⟨fun h => Matrix.ext h, fun h p q => congrFun (congrFun h p) q⟩
  rw [h1, h2, ← map_smul, m.injective.eq_iff]

def lattice₂ (v : Pl D.host.F) : AddSubgroup (Matrix (Fin n) (Fin k) (AE D)) where
  carrier := {u | At (evFin D.host.F v) u ∧ m u ∈ Λ}
  zero_mem' := ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem ha.2⟩

def genP (v : Pl D.host.F) : Set (Matrix (Fin n) (Fin k) (AE D)) :=
  {γ | (∃ γ' ∈ lattice₂ m Λ v, γ = 2 • γ') ∨ γ ∈ lattice₂ m Λ v ∧ ∃ a, IsSplitIdem D a ∧ IsHalf a γ}

theorem genP_subset (v : Pl D.host.F) : genP m Λ v ⊆ lattice₂ m Λ v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

variable (ΛS ΛT) in

abbrev latA : AddSubgroup (WO S T) := latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True

theorem cut_mem (v : Pl D.host.F) {x : WO S T} (hx : x ∈ latA ΛS ΛT) :
    liftV v (1 : Fv D.host.F v) • m.symm x ∈ lattice₂ m (latA ΛS ΛT) v :=
  ⟨GlobalTheory.BigDatLat.at_smul v _, by rw [m_smul, m.apply_symm_apply]; exact GlobalTheory.BigDatLat.smul_mem v hx⟩

theorem localLattice_le_closure_generators (v : Pl D.host.F) : lattice₂ m (latA ΛS ΛT) v ≤ AddSubgroup.closure (genP m (latA ΛS ΛT) v) := by
  intro u hu
  let f : WO S T →+ Matrix (Fin n) (Fin k) (AE D) :=
    (DistribMulAction.toAddMonoidHom _ (liftV v (1 : Fv D.host.F v))).comp m.symm.toLinearMap.toAddMonoidHom
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have e : u = f (m u) := by rw [hf, m.symm_apply_apply, GlobalTheory.BigDatLat.smul_eq_of_at hu.1]
  rw [e]
  refine GlobalTheory.LatVac.le_of_two_of_half ((AddSubgroup.closure (genP m (latA ΛS ΛT) v)).comap f) (fun x hx => ?_)
    (fun a ha x hx hx' => ?_) hu.2
  · rw [AddSubgroup.mem_comap, map_nsmul]
    exact AddSubgroup.subset_closure (Or.inl ⟨_, cut_mem m v hx, rfl⟩)
  · refine AddSubgroup.subset_closure (Or.inr ⟨cut_mem m v hx, a, ha, GlobalTheory.BigDatLat.isHalf_smul _ ?_⟩)
    exact (isHalf_m m (u := m.symm x)).1 (by rwa [m.apply_symm_apply])

theorem mem_localLattice_iff_forall_addChar_eq_one (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : Matrix (Fin n) (Fin k) (AE D) → Matrix (Fin n) (Fin k) (AE D) → AF D.host.F)
    (hB : ∀ x y, B x y = symplO S T (m x) (m y)) (v : Pl D.host.F) (z : Matrix (Fin n) (Fin k) (AE D))
    (hz : At (evFin D.host.F v) z) : z ∈ lattice₂ m (latA ΛS ΛT) v ↔ ∀ γ ∈ lattice₂ m (latA ΛS ΛT) v, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    rw [hB, GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT h.2 hγ.2]
  · intro h
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← m_smul, GlobalTheory.BigDatLat.smul_eq_of_at hz]
    refine ⟨hz, GlobalTheory.LatVac.mem_of_char hψ hS hT ?_ fun x hx => ?_⟩
    · rw [← hz']
      exact Matrix.ext fun _ _ => GlobalTheory.BigDatLat.infPart_smul v _
    · have := h _ (cut_mem m v hx)
      rwa [hB, m_smul, m.apply_symm_apply, GlobalTheory.BigDatLat.symplO_swap, hz'] at this

theorem hTens_half {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (a : A) (ha : a * c a = 0)
    (x : Matrix (Fin n) (Fin d) A) (hx : ∀ p q, a * x p q = x p q) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have u := congrArg c (hx r l)
  rw [map_mul] at u
  rw [← u, ← hx p q]
  linear_combination (x p q * JA p r * JB q l * c (x r l)) * ha

variable {Xs : Spc D.host.F D.host.E n} {Ws : Spc D.host.F D.host.E k} (Mo : Model D.sp.cm.sig Xs Ws)

abbrev sy (Xs : Spc D.host.F D.host.E n) (Ws : Spc D.host.F D.host.E k) (u u' : Matrix (Fin n) (Fin k) (AE D)) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Xs.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) u u'

def thM (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) (x : WO S T) : ℂ :=
  thetaSum D.host.F (Mo.co.rho ψ (m.symm x) Φ)

theorem thM_rho (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y)) (ψ : AddChar (AF D.host.F) ℂ)
    (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) (u : Matrix (Fin n) (Fin k) (AE D)) :
    thM m Mo ψ (Mo.co.rho ψ u Φ) = heisO ψ S T (m u) (thM m Mo ψ Φ) := by
  funext x
  refine ((congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Mo.co ψ (m.symm x) u Φ)).trans tsum_mul_left).trans ?_
  have h := hB (m.symm x) u
  rw [m.apply_symm_apply] at h
  unfold heisO symplOH thM
  rw [map_add, m.symm_apply_apply, ← h, GlobalTheory.BigDat.invOf_two]
  rfl

theorem thM_smul (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ) (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) :
    thM m Mo ψ (c • Φ) = c • thM m Mo ψ Φ :=
  funext fun _ => (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left

theorem vac_acts {Bs : Base D.host.F D.host.E} (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ) {v : Pl D.host.F}
    (hle : ∀ u ∈ lattice₂ m Λ v, u ∈ latAtV Xs Ws v) :
    ∀ γ ∈ genP m Λ v, Acts (evFin D.host.F v) (Mo.co.rho Bs.ψ γ) (Mo.vac v) (Mo.vac v) := by
  intro γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hM.vac v
  have h1 := hθ γ (hle γ (genP_subset m Λ v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Xs.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, a, ha, hγ⟩
    · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs Xs Ws _ _ _ _ hBs hX hW v θ γ' (hle γ' hγ')
    · unfold symp
      rw [hTens_half (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) _ _ a ha.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul] at h1
  exact h1

theorem exists_vac (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y))
    (hle : ∀ v, ∀ u ∈ lattice₂ m (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v)
    (hinj : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = thM m Mo Bs.ψ Φ' → Φ = Φ')
    {Φ : (Fin n × Fin k → AF D.host.F) → ℂ} (hΦ : Φ ∈ schA D.host.F _)
    (hv : IsLatVac (heisO Bs.ψ S T) (latA ΛS ΛT) (thM m Mo Bs.ψ Φ)) :
    ∃ f, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Mo.vac := by
  have hstd := hBs.std
  refine GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices Mo.vac (fun v => (hM.vac v).2.1) hM.std Φ hΦ fun v y hy => ?_
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Xs Ws v Mo.co hX.lat hW.lat
  obtain ⟨a, ha⟩ := GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt Bs.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one Bs.ψ hstd v) (GlobalTheory.LatVac.locCo Mo.co v '' genP m (latA ΛS ΛT) v)
    ((lattice₂ m (latA ΛS ΛT) v).map (GlobalTheory.LatVac.locCo Mo.co v)) c
    (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono (localLattice_le_closure_generators m v)) hc0
    (GlobalTheory.LatVac.DualLoc.map_selfDual v Mo.co Bs.ψ _ (fun γ hγ => hγ.1) (mem_localLattice_iff_forall_addChar_eq_one m hS hT hψ _ hB v))
    (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ (hle v γ hγ)) (Mo.vac v)
    (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact GlobalTheory.BigDat.schr_eq_of_acts _ _ (genP_subset m _ v hγ).1 (hM.vac v).1
        (vac_acts m _ Mo hBs hX hW hM (hle v) γ hγ))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      refine GlobalTheory.BigDat.schr_slice _ _ (genP_subset m _ v hγ).1
        (hinj _ (GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd γ Φ hΦ) _ hΦ ?_) hy
      rw [thM_rho m Mo hB]
      rcases hγ with ⟨γ', h, rfl⟩ | ⟨h, a, ha, hh⟩
      · rw [map_nsmul]; exact hv.1 _ h.2
      · exact hv.2 a ha _ h.2 ((isHalf_m m).2 hh)) (hM.vac v).2.1
  exact ⟨a, congrFun ha⟩

def halfP (n k : ℕ) (ε : AE D) : AddSubgroup (Matrix (Fin n) (Fin k) (AE D)) where
  carrier := {u | IsHalf ε u}
  zero_mem' := fun _ _ => mul_zero _
  add_mem' := fun {a b} ha hb p q => by rw [Matrix.add_apply, mul_add, ha p q, hb p q]
  neg_mem' := fun {a} ha p q => by rw [Matrix.neg_apply, mul_neg, ha p q]

def graphP (ε : AE D) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Submodule ℂ ((WO S T → ℂ) × (WO S T → ℂ)) :=
  Submodule.span ℂ {p | ∃ Φ, IsSBHalf ε Λ Φ ∧ p = (Φ, Tm Φ)}

theorem graphP_snd {ε : AE D} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {p} (hp : p ∈ graphP Λ ε Tm) : p.2 = Tm p.1 := by
  induction hp using Submodule.span_induction with
  | mem p h => obtain ⟨Φ, -, rfl⟩ := h; rfl
  | zero => exact (map_zero Tm).symm
  | add p q _ _ hp hq => rw [Prod.snd_add, Prod.fst_add, map_add, hp, hq]
  | smul c p _ hp => rw [Prod.smul_snd, Prod.smul_fst, map_smul, hp]

theorem mem_graphP_of_intertwines {ε : AE D} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ψ : AddChar (AF D.host.F) ℂ) (χ : WO S T → ℂ)
    (x y : WO S T) (h : ∀ Φ, IsSBHalf ε Λ Φ → IsSBHalf ε Λ (fun t => χ t * Φ (t + x)) ∧
      Tm (fun t => χ t * Φ (t + x)) = heisO ψ S T y (Tm Φ)) {p} (hp : p ∈ graphP Λ ε Tm) :
    ((fun t => χ t * p.1 (t + x)), heisO ψ S T y p.2) ∈ graphP Λ ε Tm := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨Φ, hΦ, rfl⟩ := hp
    exact Submodule.subset_span ⟨_, (h Φ hΦ).1, by rw [(h Φ hΦ).2]⟩
  | zero =>
    convert (graphP Λ ε Tm).zero_mem using 1
    exact Prod.ext (funext fun _ => mul_zero _) (funext fun _ => mul_zero _)
  | add p q _ _ hp hq =>
    convert (graphP Λ ε Tm).add_mem hp hq using 1
    exact Prod.ext (funext fun _ => mul_add _ _ _) (funext fun _ => mul_add _ _ _)
  | smul c p _ hp =>
    convert (graphP Λ ε Tm).smul_mem c hp using 1
    exact Prod.ext (funext fun _ => mul_left_comm _ _ _) (funext fun _ => mul_left_comm _ _ _)

theorem idem_facts {v : Pl D.host.F} {a : AE D} (ha : IsSplitIdem D a)
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (liftV v 1)) :
    a * a = a ∧ cA D a * cA D a = cA D a ∧ a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = a ∧
      cA D a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = cA D a ∧ finPart D a ∈ intAE D ∧ finPart D (cA D a) ∈ intAE D ∧
      infPart D a = 0 := by
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have h1 : a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = a := by rw [← hsum, mul_add, haa, hac, add_zero]
  refine ⟨haa, hcc, h1, by rw [← hsum, mul_add, hca, hcc, zero_add],
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa]), GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc]), ?_⟩
  rw [← h1, map_mul, GlobalTheory.BigDat.infPart_algebraMap_liftV, mul_zero]

theorem mem_localLattice_of_forall_addChar_eq_one (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y)) {v : Pl D.host.F} {a : AE D}
    (ha : IsSplitIdem D a) (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (liftV v 1))
    {x : Matrix (Fin n) (Fin k) (AE D)} (hx : IsHalf a x)
    (h : ∀ y ∈ lattice₂ m (latA ΛS ΛT) v, IsHalf (cA D a) y → ψ (sy Xs Ws x y) = 1) : x ∈ lattice₂ m (latA ΛS ΛT) v := by
  obtain ⟨haa, hcc, ha1, hc1, hfa, hfc, -⟩ := idem_facts ha hsum
  have hx' := (isHalf_m m).2 hx
  refine ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf v ha1 hx,
    GlobalTheory.LatVac.mem_of_char hψ hS hT (GlobalTheory.BigDat.map_infPart_of_isHalf v ha1 hx') fun l hl => ?_⟩
  have hy : IsHalf (cA D a) (cA D a • m.symm l) := GlobalTheory.BigDat.isHalf_smul_self hcc _
  have := h _ ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf v hc1 hy, by
    rw [map_smul, m.apply_symm_apply]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl⟩ hy
  rwa [hB, map_smul, m.apply_symm_apply, GlobalTheory.BigDat.symplO_cA_smul, GlobalTheory.BigDat.smul_of_isHalf hx'] at this

set_option maxHeartbeats 1600000 in

theorem exists_pure (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y))
    (hle : ∀ v, ∀ u ∈ lattice₂ m (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v)
    (hadd : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ (Φ + Φ') = thM m Mo Bs.ψ Φ + thM m Mo Bs.ψ Φ')
    (hinj : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = thM m Mo Bs.ψ Φ' → Φ = Φ')
    {vac : WO S T → ℂ} (hon : ∃ Φ ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = vac) (hv0 : vac ≠ 0)
    (hv : IsLatVac (heisO Bs.ψ S T) (latA ΛS ΛT) vac)
    {ι : Type} [Fintype ι] (pl : ι → Pl D.host.F) (hpl : Function.Injective pl) (a : ι → AE D)
    (ha : ∀ i, IsSplitIdem D (a i) ∧ a i + cA D (a i) = algebraMap (AF D.host.F) (AE D) (liftV (pl i) 1))
    {ε : AE D} (hε : ε = ∑ i, a i) (Z : ι → Type) [∀ i, TopologicalSpace (Z i)] [∀ i, AddCommGroup (Z i)]
    (A A' : ι → Set (Matrix (Fin n) (Fin k) (AE D))) (hA : ∀ i u, u ∈ A i ↔ IsHalf (a i) u)
    (hA' : ∀ i u, u ∈ A' i ↔ IsHalf (cA D (a i)) u) (co : ∀ i, Matrix (Fin n) (Fin k) (AE D) → Z i)
    (hco : ∀ i u x, co i (u + x) = co i u + co i x) (hcoa : ∀ i u, co i (a i • u) = co i u)
    (hcos : ∀ i z, ∃ x, co i x = z) (I : ∀ i, ((Fin n × Fin k → Fv D.host.F (pl i)) → ℂ) →ₗ[ℂ] (Z i → ℂ))
    (hI : ∀ i, IsLagrModel Mo Bs.ψ (pl i) (A i) (A' i) (co i) (I i)) {Φ f : WO S T → ℂ}
    (hf : IsThetaAt Bs.ψ (symplO S T) (heisO Bs.ψ S T) ε (latA ΛS ΛT) 1 vac Φ f) (hΦ : ∀ x, Φ x ≠ 0 → IsHalf ε x)
    (φ : ∀ v : Pl D.host.F, (Fin n × Fin k → Fv D.host.F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hφv : ∀ v, (∀ i, pl i ≠ v) → φ v = Mo.vac v) {κ : ℂ} (hκ : κ ≠ 0)
    (hloc : ∀ x, IsHalf ε x → ∏ i, I i (φ (pl i)) (co i (m.symm x)) = κ * Φ x) :
    ∃ f₀, f₀ ≠ 0 ∧ thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
  classical
  have hstd := hBs.std
  obtain ⟨Φ₀, hΦ₀, rfl⟩ := hon
  obtain ⟨g, rfl⟩ := exists_vac m Mo hS hT hψ hBs hX hW hM hB hle hinj hΦ₀ hv
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hid := fun i => idem_facts (ha i).1 (ha i).2
  have horth : ∀ i j, i ≠ j → a i * a j = 0 := fun i j hij => by
    have h0 : liftV (pl i) (1 : Fv D.host.F (pl i)) * liftV (pl j) (1 : Fv D.host.F (pl j)) = 0 :=
      GlobalTheory.LatVac.at_liftV (pl j) 1 _ (evalV_singleFin_ne (fun h => hij (hpl h).symm) _)
    rw [← (hid i).2.2.1, ← (hid j).2.2.1, mul_mul_mul_comm, ← map_mul, h0, map_zero, mul_zero]
  have hεa : ∀ i, ε * a i = a i := fun i => by
    rw [hε, Finset.sum_mul, Finset.sum_eq_single i (fun j _ h => horth j i h) (fun h => absurd (Finset.mem_univ _) h), (hid i).1]
  have hinf : infPart D ε = 0 := by
    rw [hε, map_sum]; exact Finset.sum_eq_zero fun i _ => (hid i).2.2.2.2.2.2
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have hco0 : ∀ i, co i 0 = 0 := fun i => by simpa using hco i 0 0
  have hsm : ∀ i u, a i • u ∈ A i := fun i u => (hA i _).2 (GlobalTheory.BigDat.isHalf_smul_self (hid i).1 u)
  have hvac := fun i => GlobalTheory.BigDat.lagr_vac (hI i) (hM.vac _).1 (hM.vac _).2.1 (lattice₂ m (latA ΛS ΛT) (pl i) : Set _)
    (fun γ hγ hγ' => vac_acts m _ Mo hBs hX hW hM (hle _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (ha i).1, (hA i _).1 h⟩) fun h => ⟨_, GlobalTheory.BigDat.splitIdem_conj (ha i).1, (hA' i _).1 h⟩⟩))
    (fun z => by obtain ⟨x, rfl⟩ := hcos i z; exact ⟨_, hsm i x, hcoa i x⟩)
    (fun x hx h => mem_localLattice_of_forall_addChar_eq_one m hS hT hψ hB (ha i).1 (ha i).2 ((hA i _).1 hx) fun y hy hy' => h y hy ((hA' i _).2 hy'))
  set c := ∏ i, I i (Mo.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hvac i).1
  have hps : ∀ (z : ℂ) (g : SInf D.host.F (Fin n × Fin k)) (φ : ∀ v : Pl D.host.F, (Fin n × Fin k → Fv D.host.F v) → ℂ),
      thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (z • g) φ) = z • thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := fun z g φ => by
    rw [← thM_smul]
    exact congrArg _ (funext fun _ => mul_assoc _ _ _)
  let R : Submodule ℂ ((Matrix (Fin n) (Fin k) (AE D) → ℂ) × ((Fin n × Fin k → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ ((fun t => p.1 (m.symm t)), thM m Mo Bs.ψ p.2) ∈ graphP (latA ΛS ΛT) ε Tm}
      zero_mem' := ⟨zero_mem _, by
        have : thM m Mo Bs.ψ 0 = 0 := by simpa using thM_smul m Mo Bs.ψ 0 0
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun z p hp => ⟨Submodule.smul_mem _ z hp.1, by
        rw [Prod.smul_snd, thM_smul]
        exact Submodule.smul_mem _ z hp.2⟩ }
  have hbase : (fun t => Set.indicator (halfP n k ε : Set _) (fun u => ∏ i, I i (Mo.vac _) (co i u)) (m.symm t)) =
      c • halfInd ε (latA ΛS ΛT) := by
    funext t
    obtain ⟨u, rfl⟩ := m.surjective t
    rw [m.symm_apply_apply, Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hu : IsHalf ε u
    · rw [Set.indicator_of_mem (show u ∈ halfP n k ε from hu), Finset.prod_congr rfl fun i _ =>
        (congrArg _ (hcoa i u).symm).trans ((hvac i).2 _ (hsm i u))]
      by_cases hl : m u ∈ latA ΛS ΛT
      · rw [if_pos ⟨hl, (isHalf_m m).2 hu⟩, mul_one]
        refine Finset.prod_congr rfl fun i _ => Set.indicator_of_mem ?_ _
        exact ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.1 ((hA i _).1 (hsm i u)), by
          rw [map_smul]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ (hid i).2.2.2.2.1 _ hl⟩
      · have : ∃ i, a i • u ∉ lattice₂ m (latA ΛS ΛT) (pl i) := by
          by_contra! hall
          exact hl (GlobalTheory.BigDat.mem_of_sum_smul (P := Finset.univ) (a := a) (hε ▸ (isHalf_m m).2 hu) fun i _ => by
            rw [← map_smul]; exact (hall i).2)
        obtain ⟨i, hn⟩ := this
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hn _), if_neg fun h => hl h.1, mul_zero]
    · rw [Set.indicator_of_notMem (show u ∉ halfP n k ε from hu), if_neg fun h => hu ((isHalf_m m).1 h.2), mul_zero]
  have hR := GlobalTheory.T.heisenbergStableRelation_of_vacua Mo Bs.ψ hstd hM Finset.univ pl hpl.injOn Z A A' co I (halfP n k ε) R (c • g)
    (fun i _ => hI i)
    (fun i _ u hu => ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.1 ((hA i _).1 hu),
      GlobalTheory.BigDat.isHalf_mono (hεa i) ((hA i _).1 hu)⟩)
    (fun i _ u hu => GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.2.1 ((hA' i _).1 hu))
    (fun i _ u hu => ⟨_, hsm i u, cA D (a i) • u, (hA' i _).2 (GlobalTheory.BigDat.isHalf_smul_self (hid i).2.1 u), by
      rw [← add_smul, (ha i).2, algebraMap_smul, GlobalTheory.BigDatLat.smul_eq_of_at hu]⟩)
    (fun i _ x _ u => hco i u x)
    (fun i _ j _ hne x hx u => by
      rw [hco, ← hcoa j x, ← GlobalTheory.BigDat.smul_of_isHalf ((hA i _).1 hx), smul_smul, horth j i hne, zero_smul, hco0, add_zero])
    (fun i _ u => ⟨_, hsm i u, hcoa i u, fun y hy => by
      refine (hB u y).trans (Eq.trans ?_ (hB _ y).symm)
      rw [map_smul, ← GlobalTheory.BigDat.symplO_cA_smul, GlobalTheory.BigDat.smul_of_isHalf ((isHalf_m m).2 ((hA' i _).1 hy))]⟩)
    (fun i _ x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd x _ hp.1, by
      have hx' : IsHalf ε (m x) := (isHalf_m m).2 (GlobalTheory.BigDat.isHalf_mono (hεa i) ((hA i _).1 hx))
      have := mem_graphP_of_intertwines _ Bs.ψ (fun _ => 1) (m x) (m x) (fun Φ hΦ => by
        simp only [one_mul]
        exact ⟨GlobalTheory.BigDat.GraphHeis.sb_trans_latO hS.1 hT.1 hinf hΦ hx', hTm.trans Φ hΦ _ hx'⟩) hp.2
      simp only [one_mul, map_add, LinearEquiv.symm_apply_apply] at this
      rwa [← thM_rho m Mo hB] at this⟩)
    (fun i _ y hy p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd y _ hp.1, by
      have hy' : IsHalf (cA D ε) (m y) := (isHalf_m m).2
        (GlobalTheory.BigDat.isHalf_mono (by rw [← RingHom.map_mul, hεa i]) ((hA' i _).1 hy))
      have := mem_graphP_of_intertwines _ Bs.ψ (fun t => Bs.ψ (symplO S T t (m y))) 0 (m y) (fun Φ hΦ => by
        simp only [add_zero]
        exact ⟨GlobalTheory.BigDat.GraphHeis.sb_modul_latO hψ hS hT hinf' hΦ hy', hTm.modul Φ hΦ _ hy'⟩) hp.2
      simp only [add_zero] at this
      rw [← thM_rho m Mo hB] at this
      convert this using 3 with t
      exact congrArg (fun z => Bs.ψ z * p.1 (m.symm t)) ((hB _ y).trans (by rw [m.apply_symm_apply]))⟩)
    ⟨(isFinPart_vac hM ∅).fam.mem hM _, by
      have := (graphP (latA ΛS ΛT) ε Tm).smul_mem c (Submodule.subset_span ⟨_, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg Tm (one_smul ℂ _).symm).trans hTm.vac] at this
      show (_, thM m Mo Bs.ψ _) ∈ _
      rw [hps]
      convert this using 1
      exact Prod.ext hbase rfl⟩
    φ hφ fun v hv => hφv v fun i => hv i (Finset.mem_univ _)
  have hfst : (fun t => Set.indicator (halfP n k ε : Set _) (fun u => ∏ i, I i (φ _) (co i u)) (m.symm t)) = κ • Φ := by
    funext t
    by_cases ht : IsHalf ε t
    · rw [Set.indicator_of_mem (show m.symm t ∈ halfP n k ε from (isHalf_m m).1 (by rwa [m.apply_symm_apply]))]
      exact hloc t ht
    · rw [Set.indicator_of_notMem (show m.symm t ∉ halfP n k ε from fun h => ht (by
        have := (isHalf_m m).2 h
        rwa [m.apply_symm_apply] at this)), Pi.smul_apply, of_not_not (mt (hΦ t) ht), smul_zero]
  have key : thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ) = κ • f := by
    rw [hall Tm hTm, ← map_smul, ← hfst]
    exact graphP_snd _ hR.2
  refine ⟨κ⁻¹ • c • g, smul_ne_zero (inv_ne_zero hκ) (smul_ne_zero hc0 fun h0 => hv0 ?_), ?_⟩
  · rw [h0, ← zero_smul ℂ (0 : SInf D.host.F (Fin n × Fin k)), hps, zero_smul]
  · rw [hps, key, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.BotMatch

end
