import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDoubleDescentRanksOneThreeFive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneUniformInLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwist
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.Unf.Inhab GlobalTheory.QPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.Inhab

section Vacua
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm infPart_half)
open GlobalTheory.LocMod.Exist Filter
open scoped Topology

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

def vacSet (ψ : AddChar (AF D.host.F) ℂ) (p : Place D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) :
    Set (WO S T) :=
  {u | (∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ p.up FS FT x = u) ∨ (IsHalf (cA D p.e) u ∧
    ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) u) = 1)}

theorem isHalf_add_left (p : Place D k) {u : WO S T} (hu : IsHalf p.e u) : IsHalf (p.e + cA D p.e) u := fun i j => by
  rw [add_mul, hu i j, ← hu i j, ← mul_assoc, mul_comm (cA D p.e), p.split.2.1, zero_mul, add_zero, hu i j]

theorem isHalf_add_right (p : Place D k) {u : WO S T} (hu : IsHalf (cA D p.e) u) : IsHalf (p.e + cA D p.e) u := fun i j => by
  rw [add_mul, hu i j, ← hu i j, ← mul_assoc, p.split.2.1, zero_mul, zero_add, hu i j]

theorem isHalf_of_mem_vacSet {ψ : AddChar (AF D.host.F) ℂ} {p : Place D k} {FS : GlobalTheory.LocMod.Frame k S.rank Y'}
    {FT : GlobalTheory.LocMod.Frame k T.rank Y} {u : WO S T} (hu : u ∈ vacSet ψ p FS FT) : IsHalf (p.e + cA D p.e) u := by
  rcases hu with ⟨x, -, rfl⟩ | h
  · exact isHalf_add_left p (Witness.up_half p FS FT x)
  · exact isHalf_add_right p h.1

theorem exists_fixed_vacSet {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (U : Set (WO S T))
    (hU : ∀ u ∈ U, ∀ w, IsHalf (p.e + cA D p.e) w → symplO S T u w = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (f0 : f ≠ 0)
    (hfU : ∀ u ∈ U, heisO ψ S T u f = f) :
    ∃ g, IsThetaFunO ψ S T g ∧ g ≠ 0 ∧ ∀ u ∈ U ∪ vacSet ψ p FS FT, heisO ψ S T u g = g := by
  obtain ⟨⟨ψk, hk⟩, hk', -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨he, hec, v, ε, hε, heq⟩ := p.split
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination he' + hec
  have i1 := fun x => infPart_half hε heε (up_mem p FS FT x)
  have i2 := fun x => infPart_half hε heε' (dual_mem p FS FT x)
  have h0 : ∀ f, heisL S T ψ 0 f = f := fun f => GlobalTheory.LatVac.heisO_zero ψ f
  let P : Submodule ℂ (WO S T → ℂ) := thetaSub ψ S T ⊓ ⨅ u : U, LinearMap.eqLocus (heisL S T ψ u.1) LinearMap.id
  have mP : ∀ f, f ∈ P ↔ IsThetaFunO ψ S T f ∧ ∀ u ∈ U, heisL S T ψ u f = f := fun f => by
    simp only [P, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subtype.forall]
    rfl
  have sm : ∀ j : Matrix Y Y' k → WO S T, Continuous j → j 0 = 0 → (∀ x, (j x).map (infPart D) = 0) →
      ∀ f ∈ P, ∀ᶠ x in 𝓝 0, heisL S T ψ (j x) f = f := fun j hj j0 hi f hf => by
    obtain ⟨U, hU, h⟩ := IsThetaFunO.level ((mP f).1 hf).1
    filter_upwards [(hU.preimage hj).mem_nhds (show j 0 ∈ U by rw [j0]; exact U.zero_mem)] with x hx
    exact h _ hx (hi x)
  have st : ∀ w : WO S T, IsHalf (p.e + cA D p.e) w → w.map (infPart D) = 0 → ∀ f ∈ P, heisL S T ψ w f ∈ P :=
    fun w hw hi f hf => (mP _).2 ⟨GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 ((mP f).1 hf).1 hi, fun u hu => by
      rw [heisL_comm, hU u hu w hw, AddChar.map_zero_eq_one, one_smul, ((mP f).1 hf).2 u hu]⟩
  obtain ⟨g, hg, g0, h1, h2⟩ := GlobalTheory.LocMod.Inhab.exists_vacuum (hk' ψk hk).1 (hk' ψk hk).2
    (fun x => heisL S T ψ (p.up FS FT x)) (fun b => heisL S T ψ (dual p FS FT b))
    (fun x x' f => by rw [up_add, heisL_half S T ψ (by rw [mul_comm, hec]) _ (up_mem p FS FT x) _ (up_mem p FS FT x')])
    (fun x x' f => by rw [dual_add, heisL_half S T ψ (by rw [cA_cA, hec]) _ (dual_mem p FS FT x) _ (dual_mem p FS FT x')])
    (fun f => by rw [up_zero, h0]) (fun f => by rw [dual_zero, h0])
    (fun x y f => by rw [heisL_comm, char_sympl p FS FT hk]) P
    (fun x => st _ (isHalf_add_left p (Witness.up_half p FS FT x)) (i1 x))
    (fun x => st _ (isHalf_add_right p ((isHalf_iff S T).2 (dual_mem p FS FT x))) (i2 x))
    (sm _ (continuous_up p FS FT) (up_zero p FS FT) i1) (sm _ (continuous_dual p FS FT) (dual_zero p FS FT) i2)
    ((mP f).2 ⟨hf, hfU⟩) f0
  have bx : ∀ x : Matrix Y Y' k, x ∈ GlobalTheory.LocMod.Inhab.box Y Y' (1 : kˣ) ↔ ∀ r q, x r q ∈ 𝒪[k] := fun x => by
    change (∀ r q, valuation k (x r q) ≤ valuation k ((1 : kˣ) : k)) ↔ _
    rw [Units.val_one, map_one]
    rfl
  refine ⟨g, ((mP g).1 hg).1, g0, ?_⟩
  rintro u (hu | ⟨x, hx, rfl⟩ | ⟨hu, hu'⟩)
  · exact ((mP g).1 hg).2 u hu
  · exact h1 x ((bx x).2 hx)
  · obtain ⟨b, rfl⟩ := exists_dual p FS FT hu
    exact h2 b fun x hx => (char_sympl p FS FT hk x b).symm.trans (hu' x ((bx x).1 hx))

theorem exists_model_of_fixed {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ u ∈ vacSet ψ p FS FT, heisO ψ S T u f = f) : ∃ Tm O, p.IsModel ψ FS FT Tm ∧ IsOne O ∧ Tm O = f := by
  obtain ⟨Tm, h1, h2⟩ := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).2.2 f hf (fun x hx => h _ (Or.inl ⟨x, hx, rfl⟩))
    fun y hy hy' => h _ (Or.inr ⟨hy, hy'⟩)
  obtain ⟨O, hO, -⟩ := PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  exact ⟨Tm, O, h1, hO, h2 O hO⟩

theorem idem_orth {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (h : q.v ≠ q'.v) :
    cA D (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  obtain ⟨ε', hε', hs'⟩ := q'.above
  obtain ⟨he, hec, -⟩ := q'.split
  have he' : cA D q'.e * cA D q'.e = cA D q'.e := by rw [← map_mul, he]
  have h1 : q'.e + cA D q'.e ∈ GlobalTheory.FinPl.idAt D (· = q'.v) :=
    ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q'.v ε' hε').1 _).2 (by rw [← hs']; linear_combination he + he' + 2 * hec)
  rw [map_add, cA_cA, add_comm, hs]
  refine (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).2 _ ⟨h1.1, ?_⟩
  have h2 := h1.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
  exact fun w => h2 ⟨w.1, fun e => w.2 fun e' => h (e'.symm.trans e)⟩

theorem exists_fixed_all {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ι : Type} [Finite ι] (a : ι → AE D)
    (ha : ∀ i j, i ≠ j → cA D (a i) * a j = 0) (V : ι → Set (WO S T)) (hV : ∀ i, ∀ u ∈ V i, IsHalf (a i) u)
    (step : ∀ i (U : Set (WO S T)), (∀ u ∈ U, ∀ w, IsHalf (a i) w → symplO S T u w = 0) → ∀ f, IsThetaFunO ψ S T f → f ≠ 0 →
      (∀ u ∈ U, heisO ψ S T u f = f) → ∃ g, IsThetaFunO ψ S T g ∧ g ≠ 0 ∧ ∀ u ∈ U ∪ V i, heisO ψ S T u g = g) :
    ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ i, ∀ u ∈ V i, heisO ψ S T u f = f := by
  classical
  have key : ∀ s : Finset ι, ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ i ∈ s, ∀ u ∈ V i, heisO ψ S T u f = f := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S T
      exact ⟨f, hf, f0, by simp⟩
    | insert j s hj ih =>
      obtain ⟨f, hf, f0, h⟩ := ih
      obtain ⟨g, hg, g0, h'⟩ := step j {u | ∃ i ∈ s, u ∈ V i}
        (fun u ⟨i, hi, hu⟩ w hw => GlobalTheory.SplitScalar.symplO_eq_zero S T (ha i j fun e => hj (e ▸ hi)) (hV i u hu) hw) f hf f0
        fun u ⟨i, hi, hu⟩ => h i hi u hu
      refine ⟨g, hg, g0, fun i hi u hu => h' u ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inr hu
      · exact Or.inl ⟨i, hi, hu⟩
  haveI := Fintype.ofFinite ι
  obtain ⟨f, hf, f0, h⟩ := key Finset.univ
  exact ⟨f, hf, f0, fun i => h i (Finset.mem_univ i)⟩

end Vacua

theorem exists_vac {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} {S : Dbl2 ψ σ} {ι : Type} [Finite ι]
    (Q : ι → QStep S) (hQ : Function.Injective fun i => (Q i).q.v) :
    ∃ f₁ f₂, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ ∀ i, (Q i).Vac f₁ f₂ := by
  have ha : ∀ i j, i ≠ j → cA D ((Q i).q.e + cA D (Q i).q.e) * ((Q j).q.e + cA D (Q j).q.e) = 0 :=
    fun i j h => idem_orth _ _ fun e => h (hQ e)
  obtain ⟨f₁, t₁, z₁, h₁⟩ := exists_fixed_all hψ _ ha (fun i => vacSet ψ (ofSplit (Q i).q) (Q i).F.G₀ (Q i).F.G₁)
    (fun i u hu => isHalf_of_mem_vacSet hu) fun i U hU f hf f0 h => exists_fixed_vacSet hψ _ _ _ U hU hf f0 h
  obtain ⟨f₂, t₂, z₂, h₂⟩ := exists_fixed_all hψ _ ha (fun i => vacSet ψ (ofSplit (Q i).q) (Q i).F.G₁ (Q i).F.G₂)
    (fun i u hu => isHalf_of_mem_vacSet hu) fun i U hU f hf f0 h => exists_fixed_vacSet hψ _ _ _ U hU hf f0 h
  exact ⟨f₁, f₂, z₁, z₂, t₁, t₂, fun i => ⟨exists_model_of_fixed hψ _ _ _ t₁ (h₁ i), exists_model_of_fixed hψ _ _ _ t₂ (h₂ i)⟩⟩

section Local
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [MeasurableSpace k] [BorelSpace k] in

theorem exists_open_fix {Y : Type} [Fintype Y] [DecidableEq Y] (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {P : ℕ} (h1 : 1 ≤ P)
    (hP : P ≤ c) (L : Level (GL (n ⊕ Fin c) k)) (hL : IsOpen (L.J : Set (GL (n ⊕ Fin c) k))) (α : GL (n ⊕ Fin c) k) :
    ∃ e, IsOneComb ψ ν P L α e := by
  obtain ⟨U, hU, h⟩ := exists_open_fix L hL α
  obtain ⟨e, e', he⟩ := GlobalTheory.T.exchangeToPositionOne_uniform_in_level k n c P h1 hP ψ hψ.continuous hψ.ne_one ν (isSelfDual_of_isUnitVol ν hψ hν) U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

theorem exists_covers {ι V : Type} [Zero V] {p : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)} (s : Finset ι)
    (f : ι → GL (n ⊕ Fin c) k → V) (hf : ∀ i, ∃ T, Covers p J T (f i)) (t₀ : GL (n ⊕ Fin c) k) :
    ∃ T, t₀ ∈ T ∧ ∀ i ∈ s, Covers p J T (f i) := by
  classical
  choose T hT using hf
  let m := DoubleCoset.mk (R k n c p) J
  let r := Function.update (fun x : DoubleCoset.Quotient (R k n c p : Set (GL (n ⊕ Fin c) k)) J => x.out) (m t₀) t₀
  have hr : ∀ x, m (r x) = x := fun x => by
    by_cases h : x = m t₀
    · rw [h]; exact congrArg m (Function.update_self ..)
    · exact (congrArg m (Function.update_of_ne h ..)).trans (Quotient.out_eq' x)
  refine ⟨(insert t₀ (s.biUnion T)).image fun t => r (m t),
    Finset.mem_image.2 ⟨t₀, Finset.mem_insert_self _ _, Function.update_self ..⟩, fun i hi => ⟨?_, fun h hh => ?_⟩⟩
  · intro a ha b hb e
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hb
    exact congrArg r ((hr _).symm.trans (e.trans (hr _)))
  · obtain ⟨t, ht, e⟩ := (hT i).2 h hh
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, hi, ht⟩)), e.trans (hr _).symm⟩

theorem exists_covers_flat {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) {J : Subgroup (GL (n ⊕ Fin (c + 1)) k)} (hJ : IsOpen (J : Set (GL (n ⊕ Fin (c + 1)) k)))
    (Φ : SB (Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k)) (α : GL (n' ⊕ Fin (c + 1 + 1)) k) :
    ∃ T, Covers 1 J T fun h => GlobalTheory.StepData.flat ψ ν μ Φ.1 α h := by
  obtain ⟨T, hT⟩ := GlobalTheory.PosOne.covers_opE_finite k n n' (c + 1) 1 le_rfl (by omega) ψ hψ.continuous hψ.ne_one ν μ hμ J hJ
    ⟨om μ α 1 Φ.1, GlobalTheory.SplitWeil.om_mem_SB μ α 1 Φ.2⟩
  refine ⟨T, ?_⟩
  convert hT using 2 with h
  rw [GlobalTheory.StepData.flat, ← GlobalTheory.SplitWeil.om_mul, one_mul, mul_one]

omit [BorelSpace k] in

theorem xi_mem_SB (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    GlobalTheory.StepData.xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) :=
  (SB _).smul_mem _ (GlobalTheory.RootEx.opE_mem_SB 1 ψ ν (GlobalTheory.SplitWeil.om_mem_SB μ h' h Φ.2))

omit [MeasurableSpace k] [BorelSpace k] in

theorem exists_isCombAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : Place D k) {S T : HSp D}
    (FS : GlobalTheory.LocMod.Frame k S.rank n') (FT : GlobalTheory.LocMod.Frame k T.rank n) {Ξ : Matrix n n' k → ℂ} (hΞ : Ξ ∈ SB (Matrix n n' k)) :
    ∃ d, p.IsCombAt ψ FS FT d Ξ := by
  obtain ⟨O, hO, z⟩ := PinModel.exists_isOne (k := k) (Y := n) (Y' := n')
  obtain ⟨d, h1, h2⟩ := GlobalTheory.T.exists_heisenberg_combination_split_place_datum D k p n n' S T FS FT ψ hψ O ⟨Ξ, hΞ⟩ (by rintro rfl; exact zero_ne_one z)
  refine ⟨d, h1, fun Tm hT Φ₀ Φ h₀ h => ?_⟩
  rw [show Φ = ⟨Ξ, hΞ⟩ from Subtype.ext h, show Φ₀ = O from Subtype.ext (h₀.trans hO.symm)]
  exact h2 Tm hT

omit [MeasurableSpace k] [BorelSpace k] in

theorem prX_Cgrp_KO : prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  simp only [mem_prX, mem_Cgrp, inv_one, one_mul, mul_one]
  exact ⟨fun ⟨_, hu, h⟩ => GlobalTheory.TwistVertex.mem_KO_of_mul_embX hu h.2, fun h => ⟨1, one_mem _, by
    rw [one_mul]; exact ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, GlobalTheory.TwistVertex.embX_mem_KO h⟩⟩⟩

end Local

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

set_option maxHeartbeats 1000000 in

theorem exists_qstep (hψ : IsStdChar D ψ (-1)) (S : Dbl2 ψ σ) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (q : GlobalTheory.FinPl.SplitPt D k) (ψk : AddChar k Circle) (hk : (ofSplit q).IsChar ψ ψk) (hc : HasConductor ψk 1)
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c : ℕ)
    (F : Dbl (ofSplit q) S.B S.J S.B' n₀ n₁ n₂ c) (μ₁ μ₂ : kˣ →* ℂˣ) (c₁ : (ofSplit q).IsComp S.χ₁⁻¹ μ₁)
    (c₂ : (ofSplit q).IsComp S.χ₂⁻¹ μ₂) (o₁ : IsOpen (μ₁.ker : Set kˣ)) (o₂ : IsOpen (μ₂.ker : Set kˣ))
    (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1 + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin (c + 1)) k))
    (op₀ : IsOpen (L₀.J : Set (GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k))) (co₁ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₁.J) (co₂ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₂.J)
    (le₁ : L₁.J ≤ KO k _) (le₂ : L₂.J ≤ KO k _) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1 + 1)) (n₀ ⊕ Fin (c + 1 + 1 + 1)) k))
    (Φ₂ : SB (Matrix (n₂ ⊕ Fin (c + 1)) (n₁ ⊕ Fin (c + 1 + 1)) k)) (ty₁ : HasTypes μ₁ L₀ L₁ Φ₁.1) (ty₂ : HasTypes μ₂ L₁ L₂ Φ₂.1)
    (α : GL (n₀ ⊕ Fin (c + 1 + 1 + 1)) k) (γ₀ : GL (n₁ ⊕ Fin (c + 1 + 1)) k) (β₀ : GL (n₂ ⊕ Fin (c + 1)) k) :
    ∃ gl₀ gl₁ gl₂ loc₀ loc₁ loc₂ D₁ D₂ dat₁ dat₂ A₁ A₂ cov₁ cov₂ d₁ d₂ ent₁ ent₂ e₀ e₂ one₀ one₂ m₁ m₂ haar₁ haar₂ vol₁ vol₂,
      γ₀ ∈ A₁ ∧ β₀ ∈ A₂ ∧ ∃ Q : QStep S, Q = QStep.mk k ν hν q ψk hk hc n₀ n₁ n₂ c F gl₀ gl₁ gl₂ loc₀ loc₁ loc₂ μ₁ μ₂ c₁ c₂ o₁ o₂
        L₀ L₁ L₂ co₁ co₂ le₁ le₂ Φ₁ Φ₂ ty₁ ty₂ D₁ D₂ dat₁ dat₂ α A₁ A₂ cov₁ cov₂ d₁ d₂ ent₁ ent₂ e₀ e₂ one₀ one₂
        m₁ m₂ haar₁ haar₂ vol₁ vol₂ := by
  haveI := hν.1
  have hc2 : c + 1 = 2 * σ + 1 := F.bes'.1
  obtain ⟨gl₀, l₀⟩ := Model.exists_gl q _ F.G₀
  obtain ⟨gl₁, l₁⟩ := Model.exists_gl q _ F.G₁
  obtain ⟨gl₂, l₂⟩ := Model.exists_gl q _ F.G₂
  obtain ⟨D₁, dat₁⟩ := exists_isCombAt hψ (ofSplit q) F.G₀ F.G₁ Φ₁.2
  obtain ⟨D₂, dat₂⟩ := exists_isCombAt hψ (ofSplit q) F.G₁ F.G₂ Φ₂.2
  obtain ⟨A₁, g₁, cov₁⟩ := exists_covers (Finset.univ : Finset Unit) _ (fun _ => exists_covers_flat hc ν o₁ co₁.1 Φ₁ α) γ₀
  obtain ⟨A₂, g₂, cov₂⟩ := exists_covers A₁ _ (fun γ => exists_covers_flat hc ν o₂ co₂.1 Φ₂ γ) β₀
  choose d₁ ent₁ using fun γ : A₁ => exists_isCombAt hψ (ofSplit q) F.F₀ F.F₁ (xi_mem_SB ψk ν μ₁ Φ₁ L₁.J 1 α γ.1)
  choose d₂ ent₂ using fun (γ : A₁) (β : A₂) => exists_isCombAt hψ (ofSplit q) F.F₁ F.F₂ (xi_mem_SB ψk ν μ₂ Φ₂ L₂.J 1 γ.1 β.1)
  obtain ⟨e₀, one₀⟩ := exists_isOneComb (P := σ + 1 + 1) hc hν (by omega) (by omega) L₀ op₀ α
  choose e₂ one₂ using fun β : A₂ => exists_isOneComb (P := σ + 1) hc hν (by omega) (by omega) L₂ co₂.1 β.1
  obtain ⟨m₁, a₁, b₁⟩ := Model.exists_haar ν n₁
  obtain ⟨m₂, a₂, b₂⟩ := Model.exists_haar ν n₂
  exact ⟨gl₀, gl₁, gl₂, l₀, l₁, l₂, D₁, D₂, dat₁, dat₂, A₁, A₂, cov₁ () (Finset.mem_univ _), cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂,
    one₀, one₂, m₁, m₂, a₁, a₂, b₁, b₂, g₁, g₂, _, rfl⟩

def IsSpherical {S : Dbl2 ψ σ} (Q : QStep S) : Prop :=
  IsOne Q.Φ₁ ∧ IsOne Q.Φ₂ ∧ Q.L₁ = Model.sph _ _ ∧ Q.L₂ = Model.sph _ _ ∧ Q.α = 1 ∧ Q.A₁ = {1} ∧ Q.A₂ = {1} ∧ Q.L₀ = Model.sph _ _

set_option maxHeartbeats 1000000 in

theorem exists_spherical_at (hψ : IsStdChar D ψ (-1)) (S : Dbl2 ψ σ) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {ψk : AddChar k Circle}
    (hk : (ofSplit q).IsChar ψ ψk) (hc : HasConductor ψk 1) {μ₁ μ₂ : kˣ →* ℂˣ} (c₁ : (ofSplit q).IsComp S.χ₁⁻¹ μ₁)
    (c₂ : (ofSplit q).IsComp S.χ₂⁻¹ μ₂) (u₁ : IsUnram μ₁) (u₂ : IsUnram μ₂) : ∃ Q : QStep S, Q.q.v = q.v ∧ IsSpherical Q := by
  borelize k
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (k := k)
  haveI := hν.1
  obtain ⟨F, -⟩ := DblInhab.exists_dbl D k (ofSplit q) σ S.B S.J S.B' _ _ _ (Frame.ofGL 1) (Frame.ofGL 1) (Frame.ofGL 1) 1 one_ne_zero
  obtain ⟨gl₀, l₀⟩ := Model.exists_gl q _ F.G₀
  obtain ⟨gl₁, l₁⟩ := Model.exists_gl q _ F.G₁
  obtain ⟨gl₂, l₂⟩ := Model.exists_gl q _ F.G₂
  obtain ⟨Φ₁, h₁, -⟩ := PinModel.exists_isOne (k := k) (Y := Fin S.J.W₀.rank ⊕ Fin (2 * σ + 1 + 1))
    (Y' := Fin S.B.A.rank ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨Φ₂, h₂, -⟩ := PinModel.exists_isOne (k := k) (Y := Fin S.B'.A.rank ⊕ Fin (2 * σ + 1))
    (Y' := Fin S.J.W₀.rank ⊕ Fin (2 * σ + 1 + 1))
  have e₁ : Φ₁.1 = Model.ind k _ _ := h₁
  have e₂ : Φ₂.1 = Model.ind k _ _ := h₂
  obtain ⟨m₁, a₁, b₁⟩ := Model.exists_haar ν (Fin S.J.W₀.rank)
  obtain ⟨m₂, a₂, b₂⟩ := Model.exists_haar ν (Fin S.B'.A.rank)
  obtain ⟨x₀, one₀⟩ := exists_isOneComb (P := σ + 1 + 1) hc hν (by omega) (by omega)
    (Model.sph k (Fin S.B.A.rank ⊕ Fin (2 * σ + 1 + 1 + 1))) Model.isCO_sph.1 1
  choose x₂ one₂ using fun β => exists_isOneComb (P := σ + 1) hc hν (by omega) (by omega)
    (Model.sph k (Fin S.B'.A.rank ⊕ Fin (2 * σ + 1))) Model.isCO_sph.1 β
  exact ⟨{ k := k, ν := ν, unitVol := hν, q := q, ψk := ψk, char := hk, cond := hc, c := 2 * σ, F := F
           n₀ := Fin S.B.A.rank, n₁ := Fin S.J.W₀.rank, n₂ := Fin S.B'.A.rank
           gl₀ := gl₀, gl₁ := gl₁, gl₂ := gl₂, loc₀ := l₀, loc₁ := l₁, loc₂ := l₂, μ₁ := μ₁, μ₂ := μ₂, comp₁ := c₁, comp₂ := c₂
           open₁ := Model.isOpen_ker u₁, open₂ := Model.isOpen_ker u₂, L₀ := Model.sph k _, L₁ := Model.sph k _
           L₂ := Model.sph k _, co₁ := Model.isCO_sph, co₂ := Model.isCO_sph
           le₁ := le_rfl, le₂ := le_rfl, Φ₁ := Φ₁, Φ₂ := Φ₂
           ty₁ := e₁ ▸ Model.hasTypes_ind u₁, ty₂ := e₂ ▸ Model.hasTypes_ind u₂
           D₁ := Finsupp.single 0 1, D₂ := Finsupp.single 0 1
           dat₁ := e₁ ▸ PinModel.isCombAt_one _ ψ _ _, dat₂ := e₂ ▸ PinModel.isCombAt_one _ ψ _ _
           α := 1, A₁ := {1}, A₂ := {1}
           cov₁ := e₁ ▸ Model.covers_ind hc hν μ₁
           cov₂ := fun γ hγ => by rw [Finset.mem_singleton.1 hγ, e₂]; exact Model.covers_ind hc hν μ₂
           d₁ := fun _ => Finsupp.single 0 1, d₂ := fun _ _ => Finsupp.single 0 1
           ent₁ := fun γ => by
             rw [Finset.mem_singleton.1 γ.2, e₁]
             exact (congrArg _ (Model.xi_ind (c := 2 * σ + 1) hc hν μ₁)).mpr (PinModel.isCombAt_one _ ψ F.F₀ F.F₁)
           ent₂ := fun γ β => by
             rw [Finset.mem_singleton.1 γ.2, Finset.mem_singleton.1 β.2, e₂]
             exact (congrArg _ (Model.xi_ind (c := 2 * σ) hc hν μ₂)).mpr (PinModel.isCombAt_one _ ψ F.F₁ F.F₂)
           e₀ := x₀, e₂ := fun β => x₂ β.1, one₀ := one₀, one₂ := fun β => one₂ β.1
           m₁ := m₁, m₂ := m₂, haar₁ := a₁, haar₂ := a₂, vol₁ := b₁, vol₂ := b₂ }, rfl, h₁, h₂, rfl, rfl, rfl, rfl, rfl, rfl⟩

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem infinite_spherical (hψ : IsStdChar D ψ (-1)) (S : Dbl2 ψ σ) : {v | ∃ Q : QStep S, Q.q.v = v ∧ IsSpherical Q}.Infinite := by
  have hev := (GlobalTheory.T.standard_character_conductor_almost_all D ψ hψ).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹).and
      ((DblInhab.eventually_isUnram D S.χ₁⁻¹ S.weila.hecS.1.inv).and (DblInhab.eventually_isUnram D S.χ₂⁻¹ S.weilb.hecS.1.inv))))
  refine Filter.frequently_cofinite_iff_infinite.1
    (((Filter.frequently_cofinite_iff_infinite.2 (GlobalTheory.T.infinitely_many_split_places D)).and_eventually hev).mono ?_)
  rintro v ⟨⟨e, ε, he, hε, hs⟩, a1, a2, a3, a4, a5⟩
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  obtain ⟨⟨ψk, hk⟩, -, -, -, hc⟩ := GlobalTheory.LocChar.weil_char_split D _ (ofSplit q) ψ hψ
  obtain ⟨μ₁, c₁⟩ := hc S.χ₁⁻¹
  obtain ⟨μ₂, c₂⟩ := hc S.χ₂⁻¹
  rw [← hq]
  exact exists_spherical_at hψ S q hk
    (DblInhab.hasConductor q (by rw [hq]; exact a1) (by rw [hq]; exact a2) (by rw [hq]; exact a3) hk)
    c₁ c₂ (a4 _ q hq _ c₁) (a5 _ q hq _ c₂)

theorem IsSpherical.xi_eq {S : Dbl2 ψ σ} {Q : QStep S} (h : IsSpherical Q) (γ : Q.A₁) (β : Q.A₂) :
    GlobalTheory.StepData.xi Q.ψk Q.ν Q.μ₁ Q.Φ₁.1 Q.L₁.J 1 Q.α γ.1 = Model.ind Q.k _ _ ∧
      GlobalTheory.StepData.xi Q.ψk Q.ν Q.μ₂ Q.Φ₂.1 Q.L₂.J 1 γ.1 β.1 = Model.ind Q.k _ _ := by
  obtain ⟨h₁, h₂, l₁, l₂, a, a₁, a₂, -⟩ := h
  have g : γ.1 = 1 := Finset.mem_singleton.1 (a₁ ▸ γ.2)
  have b : β.1 = 1 := Finset.mem_singleton.1 (a₂ ▸ β.2)
  rw [g, b, a, l₁, l₂, show Q.Φ₁.1 = Model.ind Q.k _ _ from h₁, show Q.Φ₂.1 = Model.ind Q.k _ _ from h₂]
  exact ⟨Model.xi_ind Q.cond Q.unitVol _, Model.xi_ind Q.cond Q.unitVol _⟩

theorem IsSpherical.constants {S : Dbl2 ψ σ} {Q : QStep S} (h : IsSpherical Q) :
    Q.volJ = 1 ∧ (∀ γ, Q.w₁ γ = 1) ∧ ∀ β, Q.w₂ β = 1 := by
  obtain ⟨-, -, l₁, l₂, -, a₁, a₂, -⟩ := h
  refine ⟨by simp [QStep.volJ, l₁, l₂, Model.sph], fun γ => ?_, fun β => ?_⟩
  · rw [QStep.w₁, show γ.1 = 1 from Finset.mem_singleton.1 (a₁ ▸ γ.2), l₁, Model.sph, prX_Cgrp_KO, Q.vol₁]
    simp
  · rw [QStep.w₂, show β.1 = 1 from Finset.mem_singleton.1 (a₂ ▸ β.2), l₂, Model.sph, prX_Cgrp_KO, Q.vol₂]
    simp

end GlobalTheory.QPl.Inhab
end
