import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceFormStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKIntDescent

theorem modTop_trans {F LL : Type} [Field F] [Field LL] [Algebra F LL] [TopologicalSpace F]
    [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology F LL] (V : Type)
    [AddCommGroup V] [Module LL V] [Module F V] [IsScalarTower F LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology F V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e := (Module.finBasis LL V).equivFun
  let e' : (Fin (finrank LL V) → LL) ≃L[F] V :=
    { e.symm.restrictScalars F with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap }
  exact IsModuleTopology.iso e'

theorem csmul_trans {F LL V : Type} [Field F] [Field LL] [Algebra F LL] [AddCommGroup V] [Module LL V]
    [Module F V] [IsScalarTower F LL V] [TopologicalSpace V] [ContinuousConstSMul LL V] :
    ContinuousConstSMul F V :=
  ⟨fun c => by simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap F LL c)⟩

variable {l : ℕ} [Fact l.Prime]

theorem actVB_resQ (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (GlobalTheory.PstCoeff.resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

section Coch
variable (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V)

theorem mem_continuousCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ continuousCocycles (GlobalTheory.PstCoeff.resQ ρ) ↔ c ∈ continuousCocycles ρ := Iff.rfl

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) :
    c ∈ finiteCocycles (P.PD K) (GlobalTheory.PstCoeff.resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  change (c ∈ continuousCocycles _ ∧ ∃ x, ∀ g, _ = _) ↔ (c ∈ continuousCocycles _ ∧ ∃ x, ∀ g, _ = _)
  simp only [actVB_resQ, mem_continuousCocycles_restrictScalars_Ql]

end Coch

section Tor
variable {K : FinExt l}

theorem mk_liftD {LL O V G : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] [Group G] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (y : V ⧸ L.T) : Submodule.Quotient.mk (liftD L y) = y :=
  (Submodule.Quotient.mk_surjective _ y).choose_spec

theorem mem_Z1T_iff {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL ↥(GK K) V} [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (d : ↥(GK K) → V) :
    d ∈ latticeCocycles L ↔ d ∈ continuousCocycles ρ ∧ ∀ g, d g ∈ L.T := by
  simp only [latticeCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_pi, Set.mem_univ,
    true_implies]

theorem exists_quotEquiv {R S V : Type} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V] [Module S V]
    (N : Submodule R V) (M : Submodule S V) (h : ∀ v, v ∈ M ↔ v ∈ N) :
    ∃ q : (V ⧸ N) ≃+ (V ⧸ M), ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  have e : N.toAddSubgroup = M.toAddSubgroup := by ext v; exact (h v).symm
  exact ⟨QuotientAddGroup.quotientAddEquivOfEq e, fun v => rfl⟩

variable {LL O V : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [Module O V]
  [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation LL ↥(GK K) V}

theorem q_actD (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (g : ↥(GK K)) (y : V ⧸ L.T) : q (actD L g y) = actD LZ g (q y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hq]
  change q (Submodule.Quotient.mk (ρ g v)) = Submodule.Quotient.mk (GlobalTheory.PstCoeff.resQ ρ g v)
  rw [hq]
  rfl

theorem mem_quotientCocycles_iff (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (c : ↥(GK K) → V ⧸ L.T) : c ∈ divisibleCocycles L ↔ (fun g => q (c g)) ∈ divisibleCocycles LZ := by
  change (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actD L g (c h)) ↔
    (IsLocallyConstant (fun g => q (c g)) ∧ ∀ g h, q (c (g * h)) = q (c g) + actD LZ g (q (c h)))
  refine and_congr ⟨fun h => h.comp q, fun h => IsLocallyConstant.desc c q h q.injective⟩ ?_
  refine forall₂_congr fun g h => ?_
  rw [← q_actD L LZ q hq, ← map_add]
  exact q.injective.eq_iff.symm

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_HfD_iff (P : LocPrime l) (L : Lattice (O := O) ρ) (c : ↥(GK K) → V ⧸ L.T) :
    c ∈ HfD (P.PD K) L ↔ ∃ z ∈ finiteCocycles (P.PD K) ρ, ∃ v : V, ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

theorem mem_HfD_iffZ (P : LocPrime l) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (c : ↥(GK K) → V ⧸ LZ.T) :
    c ∈ HfD (P.PD K) LZ ↔ ∃ z ∈ finiteCocycles (P.PD K) (GlobalTheory.PstCoeff.resQ ρ), ∃ v : V,
      ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

theorem HfD_iff (P : LocPrime l) (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (c : ↥(GK K) → V ⧸ L.T) : c ∈ HfD (P.PD K) L ↔ (fun g => q (c g)) ∈ HfD (P.PD K) LZ := by
  rw [mem_HfD_iff, mem_HfD_iffZ]
  refine exists_congr fun z => and_congr (mem_finiteCocycles_restrictScalars_Ql P ρ z).symm
    (exists_congr fun v => forall_congr' fun g => ?_)
  rw [← hq, q.injective.eq_iff]

theorem mem_Z1T_Z (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (d : ↥(GK K) → V) : d ∈ latticeCocycles LZ ↔ d ∈ latticeCocycles L := by
  rw [mem_Z1T_iff, mem_Z1T_iff, mem_continuousCocycles_restrictScalars_Ql]
  simp only [hLZ]

theorem mem_Z1fT_Z (P : LocPrime l) (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (d : ↥(GK K) → V) : d ∈ latticeFiniteCocycles (P.PD K) LZ ↔ d ∈ latticeFiniteCocycles (P.PD K) L := by
  simp only [latticeFiniteCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_Z1T_Z L LZ hLZ, mem_finiteCocycles_restrictScalars_Ql]

end Tor

section Cup
variable {K : FinExt l} {LL O V V' : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] [Module O V']
  [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem cup_smul_left (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (o : O)
    (d : ↥(GK K) → V) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    cupLD L' Pr (o • d) c x = algebraMap O LL o * cupLD L' Pr d c x := by
  simp only [cupLD, Pi.smul_apply, ← algebraMap_smul LL o (d x.1), map_smul, LinearMap.smul_apply,
    smul_eq_mul]

theorem cup_smul_right (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL)
    (hT : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, Pr x y = algebraMap O LL a) (o : O)
    (d : ↥(GK K) → V) (hd : ∀ g, d g ∈ L.T) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    ∃ a : O, algebraMap O LL o * cupLD L' Pr d c x - cupLD L' Pr d (o • c) x = algebraMap O LL a := by
  have h1 : o • liftD L' (c x.2) - liftD L' ((o • c) x.2) ∈ L'.T := by
    refine (Submodule.Quotient.eq _).1 ?_
    rw [Submodule.Quotient.mk_smul, mk_liftD, mk_liftD]
    rfl
  obtain ⟨a, ha⟩ := hT _ (hd x.1) _ (L'.stable x.1 _ h1)
  refine ⟨a, ?_⟩
  have e1 : ρ' x.1 (o • liftD L' (c x.2)) = algebraMap O LL o • ρ' x.1 (liftD L' (c x.2)) := by
    rw [← algebraMap_smul LL o, map_smul]
  rw [← ha, map_sub, map_sub, e1, map_smul, smul_eq_mul]
  rfl

theorem cup_congr (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL)
    (hT : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, Pr x y = algebraMap O LL a)
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')) (hLZ' : ∀ v, v ∈ LZ'.T ↔ v ∈ L'.T)
    (q : (V' ⧸ L'.T) ≃+ (V' ⧸ LZ'.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hPQ : ∀ x y, PQ x y = lam (Pr x y))
    (d : ↥(GK K) → V) (hd : ∀ g, d g ∈ L.T) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    ∃ z : ℤ_[l], lam (cupLD L' Pr d c x) - cupLD LZ' PQ d (fun g => q (c g)) x = (z : ℚ_[l]) := by
  have h1 : liftD L' (c x.2) - liftD LZ' (q (c x.2)) ∈ L'.T := by
    rw [← hLZ']
    refine (Submodule.Quotient.eq _).1 ?_
    rw [mk_liftD, ← hq, mk_liftD]
  obtain ⟨a, ha⟩ := hT _ (hd x.1) _ (L'.stable x.1 _ h1)
  obtain ⟨z, hz⟩ := hlam a
  refine ⟨z, ?_⟩
  rw [← hz, ← ha, map_sub, map_sub, map_sub]
  simp only [cupLD, hPQ, GlobalTheory.PstCoeff.resQ_apply]

end Cup

theorem cobO_congr (P : LocPrime l) (K : FinExt l) (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l])))
    (hL1Z : L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l])) (z z' : ↥(GK K) × ↥(GK K) → ℚ_[l])
    (h : ∀ x, ∃ a : ℤ_[l], z x - z' x = (a : ℚ_[l])) : CobO (P.PD K) L1Z z ↔ CobO (P.PD K) L1Z z' := by
  have e : (fun x => (Submodule.Quotient.mk (z x) : ℚ_[l] ⧸ L1Z.T)) = fun x => Submodule.Quotient.mk (z' x) := by
    funext x
    refine (Submodule.Quotient.eq _).2 ?_
    obtain ⟨a, ha⟩ := h x
    rw [hL1Z, ha]
    exact ⟨a, rfl⟩
  unfold CobO
  rw [e]

theorem coef_data (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) :=
  GlobalTheory.T.exists_integral_dual_functional l LL O hO

theorem cobO_iff (P : LocPrime l) (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l])))
    (hL1Z : L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]))
    (z : ↥(GK K) × ↥(GK K) → LL) :
    CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x)) :=
  GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary l P K LL O lam n e f hZ hlam hrec L1 hL1 L1Z hL1Z z

theorem exists_latZ (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ) :
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T :=
  GlobalTheory.T.zlLattice_of_coefficientLattice l K LL O V lam n e f hZ hlam hrec ρ L

theorem dualLatZ (P : LocPrime l) (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ'))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (hLZ' : ∀ v, v ∈ LZ'.T ↔ v ∈ L'.T)
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l])
    (hPQ : ∀ x y, PQ x y = lam (Pr x y)) (hP : IsDualLat1 (P.PD K) L L' Pr) :
    IsDualLat1 (P.PD K) LZ LZ' PQ :=
  GlobalTheory.T.dualLattice_restrictScalars_traceForm l P K LL O V V' lam n e f hZ hlam hrec ρ ρ' L L' LZ LZ' hLZ hLZ' Pr PQ hPQ hP

theorem bkBCore_of_integralDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.IntegralDuality (P.PD K) → bkBCore (P.PD K) := by
  intro l _ P K hI LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' Pr hdR hP
  obtain ⟨lam, n, e, f, hZ, hlam, hrec⟩ := coef_data LL O hO
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  haveI : IsModuleTopology ℚ_[l] LL := hO.2.2.1
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  letI : Module ℤ_[l] A.V := Module.compHom A.V (algebraMap ℤ_[l] ℚ_[l])
  letI : Module ℤ_[l] A'.V := Module.compHom A'.V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] A.V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] ℚ_[l] A'.V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := modTop_trans (LL := LL) A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := modTop_trans (LL := LL) A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := csmul_trans (LL := LL)
  haveI : ContinuousConstSMul ℚ_[l] A'.V := csmul_trans (LL := LL)
  obtain ⟨LZ, hLZ⟩ := exists_latZ K lam n e f hZ hlam hrec A.ρ LA
  obtain ⟨LZ', hLZ'⟩ := exists_latZ K lam n e f hZ hlam hrec A'.ρ LA'
  obtain ⟨L1Z, hL1Z⟩ := GlobalTheory.Published.BlochKato.exists_cyclotomicLattice l P K
  obtain ⟨q, hq⟩ := exists_quotEquiv LA'.T LZ'.T hLZ'
  let PQ : A.V →ₗ[ℚ_[l]] A'.V →ₗ[ℚ_[l]] ℚ_[l] := LinearMap.mk₂ ℚ_[l] (fun x y => lam (Pr x y))
    (fun x x' y => by beta_reduce; rw [map_add, LinearMap.add_apply, map_add])
    (fun c x y => by
      beta_reduce
      rw [← algebraMap_smul LL c x, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul])
    (fun x y y' => by beta_reduce; rw [map_add, map_add])
    (fun c x y => by
      beta_reduce
      rw [← algebraMap_smul LL c y, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul])
  have hPQ : ∀ x y, PQ x y = lam (Pr x y) := fun _ _ => rfl
  have hdRQ : IsDR (P.PD K) (GlobalTheory.PstCoeff.resQ A.ρ) := (GlobalTheory.PstCoeff.isDR_resQ_iff P A.ρ).mpr hdR
  have hPZ := dualLatZ P K lam n e f hZ hlam hrec A.ρ A'.ρ LA LA' LZ LZ' hLZ hLZ' Pr PQ hPQ hP
  obtain ⟨H1, H2⟩ := hI L1Z hL1Z A.V A'.V (GlobalTheory.PstCoeff.resQ A.ρ) (GlobalTheory.PstCoeff.resQ A'.ρ) LZ LZ' PQ
    A.cont A'.cont hdRQ hPZ
  have hT : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ a : O, Pr x y = algebraMap O LL a :=
    fun x hx y hy => (hP.2 y).1 hy x hx
  have hval : ∀ d, d ∈ latticeCocycles LA → ∀ g, d g ∈ LA.T := fun d hd => ((mem_Z1T_iff LA d).1 hd).2
  have key := cobO_iff P K lam n e f hZ hlam hrec L1 hL1 L1Z hL1Z
  have down : ∀ d : ↥(GK K) → A.V, (∀ g, d g ∈ LA.T) → ∀ c : ↥(GK K) → A'.V ⧸ LA'.T,
      CobO (P.PD K) L1 (cupLD LA' Pr d c) → CobO (P.PD K) L1Z (cupLD LZ' PQ d (fun g => q (c g))) := by
    intro d hd c h
    have h1 := (key _).1 h 1
    simp only [map_one, one_mul] at h1
    exact (cobO_congr P K L1Z hL1Z _ _ (cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ d hd c)).1 h1
  refine ⟨fun c hc => ?_, fun d hd => ?_⟩
  · have hc' := (mem_quotientCocycles_iff LA' LZ' q hq c).1 hc
    rw [HfD_iff P LA' LZ' q hq c, H1 _ hc']
    constructor
    · intro h d hd
      refine (key _).2 fun o => ?_
      have hod : o • d ∈ latticeFiniteCocycles (P.PD K) LA := Submodule.smul_mem _ o hd
      have e1 : (fun x => lam (algebraMap O LL o * cupLD LA' Pr d c x)) =
          fun x => lam (cupLD LA' Pr (o • d) c x) := by
        funext x
        rw [cup_smul_left]
      rw [e1]
      refine (cobO_congr P K L1Z hL1Z _ _ (cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ (o • d)
        (hval _ (Submodule.mem_inf.1 hod).1) c)).2 ?_
      exact h _ ((mem_Z1fT_Z P LA LZ hLZ _).2 hod)
    · intro h d hd
      have hd' := (mem_Z1fT_Z P LA LZ hLZ d).1 hd
      exact down d (hval d (Submodule.mem_inf.1 hd').1) c (h d hd')
  · have hdZ := (mem_Z1T_Z LA LZ hLZ d).2 hd
    rw [← mem_Z1fT_Z P LA LZ hLZ d, H2 d hdZ]
    constructor
    · intro h c hc hcf
      refine (key _).2 fun o => ?_
      have hoc : o • c ∈ divisibleCocycles LA' := Submodule.smul_mem _ o hc
      have hocf : o • c ∈ HfD (P.PD K) LA' := Submodule.smul_mem _ o hcf
      have h3 := h _ ((mem_quotientCocycles_iff LA' LZ' q hq _).1 hoc) ((HfD_iff P LA' LZ' q hq _).1 hocf)
      refine (cobO_congr P K L1Z hL1Z _ _ fun x => ?_).2 h3
      obtain ⟨a, ha⟩ := cup_smul_right LA LA' Pr hT o d (hval d hd) c x
      obtain ⟨z1, hz1⟩ := hlam a
      obtain ⟨z2, hz2⟩ := cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ d (hval d hd) (o • c) x
      refine ⟨z1 + z2, ?_⟩
      rw [PadicInt.coe_add, ← hz1, ← hz2, ← ha, map_sub]
      ring
    · intro h c' hc' hcf'
      obtain ⟨c, rfl⟩ : ∃ c : ↥(GK K) → A'.V ⧸ LA'.T, (fun g => q (c g)) = c' :=
        ⟨fun g => q.symm (c' g), funext fun g => q.apply_symm_apply _⟩
      exact down d (hval d hd) c (h c ((mem_quotientCocycles_iff LA' LZ' q hq c).2 hc') ((HfD_iff P LA' LZ' q hq c).2 hcf'))

end GlobalTheory.BKIntDescent
