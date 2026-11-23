import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldModelExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveThroughCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapConditionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLatticeDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveDegreeUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

theorem iSup_split {α I : Type} [CompleteLattice α] (f : I → α) (s₀ : I) :
    ⨆ s, f s = f s₀ ⊔ ⨆ s : {s // s ≠ s₀}, f s := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases h : s = s₀
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun s : {s // s ≠ s₀} => f s) ⟨s, h⟩)
  · exact sup_le (le_iSup f s₀) (iSup_le fun s => le_iSup f s.1)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isVBOn_iSup {E : Type} [AddCommGroup E] [Module Ω E] {I : Type} [Fintype I]
    (L : I → Lat ξ E) (T : Set (Cpt ξ)) (r : I → ℕ) (V : I → Submodule Ω E) (hV : iSupIndep V)
    (hL : ∀ s, (L s).IsVBOn T (r s) (V s)) :
    Lat.IsVBOn (ξ := ξ) (fun q => ⨆ s, L s q) T (∑ s, r s) (⨆ s, V s) := by
  classical
  intro p hp
  choose U hU b hb hfr using fun s => hL s p hp
  have hmem : ∀ (x : X) (s : Finset I), x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
    intro x s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.inf_insert, ih]
  let e : (Σ s, Fin (r s)) ≃ Fin (∑ s, r s) := Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])
  let c : Fin (∑ s, r s) → E := fun i => b (e.symm i).1 (e.symm i).2
  have hsp : ∀ (A : Type) [Semiring A] [Module A E],
      Submodule.span A (Set.range c) = ⨆ s, Submodule.span A (Set.range (b s)) := by
    intro A _ _
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (le_iSup (fun s => Submodule.span A (Set.range (b s))) (e.symm i).1)
        (Submodule.subset_span ⟨_, rfl⟩)
    · refine iSup_le fun s => ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e ⟨s, i⟩, congrArg (fun x : Σ s, Fin (r s) => b x.1 x.2) (e.symm_apply_apply ⟨s, i⟩)⟩
  have hli : LinearIndependent Ω c := by
    have h1 : LinearIndependent Ω fun ji : Σ s, Fin (r s) => b ji.1 ji.2 := by
      refine linearIndependent_iUnion_finite (fun s => (hfr s p hp (hU s)).1) fun i t _ hi => ?_
      rw [hb i]
      refine (hV i).mono_right (iSup₂_le fun s hs => ?_)
      rw [hb s]
      exact le_iSup₂_of_le s (fun h => hi (h ▸ hs)) le_rfl
    exact h1.comp e.symm e.symm.injective
  refine ⟨Finset.univ.inf U, (hmem _ _).2 fun s _ => hU s, c, ?_, fun q hq hqU => ⟨hli, ?_⟩⟩
  · rw [hsp Ω]
    exact iSup_congr hb
  · rw [hsp (regAt ξ q)]
    exact iSup_congr fun s => (hfr s q hq ((hmem _ _).1 hqU s (Finset.mem_univ s))).2

theorem unitAt_of_isUnit {q : Cpt ξ} {a : regAt ξ q} (h : IsUnit a) : unitAt ξ q (a : Ω) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun h0 => u.ne_zero (Subtype.ext h0), u.1.2, ?_⟩
  have : ((u : regAt ξ q) : Ω)⁻¹ = (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q) : Ω) := by
    exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val u.mul_inv)
  rw [this]
  exact (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q)).2

theorem unitAt_int_of_fibre [CharZero Ω] {p : ℕ} (hp : p.Prime) (q : Cpt ξ) (hq : InFibre ξ p q) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : unitAt ξ q (d : Ω) := by
  haveI := EigSplit.isLocalRing_regAt q
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hd
  have hP : ¬ IsUnit ((p : ℕ) : regAt ξ q) := fun h => hq (by simpa using unitAt_of_isUnit h)
  have h1 : ((a : regAt ξ q) * (p : regAt ξ q)) + (b : regAt ξ q) * (d : regAt ξ q) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ q) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hP
  · have e : ((d : regAt ξ q) : Ω) = (d : Ω) := map_intCast (regAt ξ q).subtype d
    rw [← e]
    exact unitAt_of_isUnit (isUnit_of_mul_isUnit_right (x := (b : regAt ξ q)) (by rwa [mul_comm] at h ⊢))

theorem charZero_of_isArithVar {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ}
    (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  obtain ⟨-, -, hh, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have : mConeMap y (MvPolynomial.C (n : ℤ)) = MvPolynomial.C (n : Ω) := by
      simpa using (mConeMap y).commutes (n : ℤ)
    simpa [hn] using this
  rw [show (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) = ⊥ from hh] at h1
  simpa using h1

open Module in

theorem flag_at (E : Type) [Field E] [NumberField E] [CharZero Ω] (hg : IsCptGen ξ)
    {K k : Type} [Field K] [Field k] [Algebra k K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z)
    (G : Over X) [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom) (act : OAct (𝓞 E) G)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V)
    (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz)
    (r : 𝓞 E →+* Module.End Ω V) (rz : 𝓞 E →+* Module.End K Vz) (hr : M.IsActOf act.act r)
    (hrz : Mz.IsActOf act.act rz) (I : Type) [Fintype I] (σ : I → (𝓞 E →+* Ω)) (χ : I → (𝓞 E →+* k))
    (hσ : Function.Injective σ) (hcard : Fintype.card I = finrank ℚ E) (hχ : IsSplit χ)
    (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ))
    (hz : (⟨centre z, h₀⟩ : Cpt ξ) ∈ S) (hS : ∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S)
    (hreg : ∀ q ∈ S, ∀ s a, σ s a ∈ regAt ξ q) (hdisc : ∀ q ∈ S, unitAt ξ q ((discr E : ℤ) : Ω))
    (hval : ∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a)))
    (s₀ : I) {n : ℕ} (b : Fin n → V) (hb : LinearIndependent Ω b)
    (hspan : Submodule.span Ω (Set.range b) = eigSp r (σ s₀)) (hfl : (M.eigLat r (σ s₀)).IsFlagVBOn S b) :
    ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W n = eigSp rz ((algebraMap k K).comp (χ s₀)) ∧
      ∀ s : Fin n, Y.IsDeg ((M.eigLat r (σ s₀)).gr b s)
        (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  classical
  have hvb : M.lat.IsVBOn S (finrank Ω V) ⊤ := fun p _ => by
    obtain ⟨U, hU, c, hc, hf⟩ := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G V M hg hsm).1 p trivial
    exact ⟨U, hU, c, hc, fun q _ hq => hf q trivial hq⟩
  obtain ⟨hE, hsum⟩ := EigSplit.isVBOn_eigSp X Ω ξ V E r M.lat S _ I σ hg hσ hcard hvb
    (fun p _ a e he => LieStable.lat_stable X Ω ξ G V M _ act r hr p a e he) hreg hdisc
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω V E r I σ hσ hcard
  have hind := hint.submodule_iSupIndep
  let U' : Submodule Ω V := ⨆ s : {s // s ≠ s₀}, eigSp r (σ s)
  let L' : Lat ξ V := fun q => ⨆ s : {s // s ≠ s₀}, M.eigLat r (σ s) q
  have hL' : L'.IsVBOn S (∑ s : {s // s ≠ s₀}, finrank Ω (eigSp r (σ s))) U' :=
    isVBOn_iSup (fun s : {s // s ≠ s₀} => M.eigLat r (σ s)) S _ (fun s => eigSp r (σ s))
      (hind.comp Subtype.val_injective) fun s => hE s
  have hcompl : IsCompl (Submodule.span Ω (Set.range b)) U' := by
    rw [hspan]
    refine ⟨(hind s₀).mono_right (iSup_le fun s => le_iSup₂_of_le s.1 s.2 le_rfl), ?_⟩
    rw [codisjoint_iff, ← iSup_split (fun s => eigSp r (σ s)) s₀]
    exact hint.submodule_iSup_eq_top
  have hlat : ∀ q ∈ S, M.lat q = M.eigLat r (σ s₀) q ⊔ L' q := fun q hq =>
    (hsum q hq).trans (iSup_split (fun s => M.eigLat r (σ s) q) s₀)
  obtain ⟨W, hW0, hWn, hdeg⟩ := GlobalTheory.T.curve_lie_lattice_degree X Ω ξ K C z Y G V M Vz Mz h₀ h S (M.eigLat r (σ s₀)) L' n _ b U'
    hg hsm hz hS hb hfl hL' hcompl hlat
  refine ⟨W, hW0, ?_, hdeg⟩
  rw [hWn]
  exact GlobalTheory.T.curve_lie_eigen_decomposition X Ω ξ k K z G V M Vz Mz h₀ (𝓞 E) I act.act r rz σ χ hg hsm act.hom hr hrz hχ hval
    (hsum _ hz) s₀

end GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

namespace GlobalTheory.CompanionTheory.Ar.Conj

open ModelNefness GlobalTheory.CompanionTheory.Ar.Top in

theorem m2Model_of_m2Curve : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  intro hC Ψ _ N M j p E _ _ _ H D hp hp2 hj hjN mu hdom hthr Wi hW
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hprime, hPW, hchar, hdim⟩ := hW
  haveI : CharZero M.Ω := charZero_of_isArithVar M.arith
  obtain ⟨K, _, _, _, w, hwW, hbir, hwk⟩ := GlobalTheory.T.function_field_model_exists M.K M.ι Wi p hprime hchar hdim
  obtain ⟨C, hFF, hne, hv⟩ := GlobalTheory.T.function_field_curve_exists (ZMod p) K
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  obtain ⟨z, Y, h₀, h, hco, hfib⟩ := GlobalTheory.T.curve_through_coordinates D.X M.Ω D.ξ M.K M.ι M.y D.tie K C w
    (by rw [hwW]; exact hPW) hwk
  obtain ⟨hz, hi⟩ := hfib p (CharP.cast_eq_zero K p)
  have hg : IsCptGen D.ξ := D.tie.gen
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom D.X M.Ω D.ξ K z h₀ hg
  let σ' : Ψ ⊕ Ψ → (𝓞 E →+* regAt D.ξ ⟨centre z, h₀⟩) := fun s => (D.σ s).codRestrict _ (D.reg _ hz s)
  have hσ' : Function.Injective σ' := fun s s' e => D.σ_inj (RingHom.ext fun a =>
    congrArg Subtype.val (RingHom.congr_fun e a))
  have hcard : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
    rw [Fintype.card_sum, ← D.card]; ring
  obtain ⟨χ, hχ, hχv⟩ := GlobalTheory.T.split_characters_unramified E (regAt D.ξ ⟨centre z, h₀⟩) K (Ψ ⊕ Ψ) p σ' φ hσ' hcard D.unram
  have hval : ∀ s a, ValAt D.ξ z (D.σ s a) (algebraMap (algebraicClosure (ZMod p) K) K (χ s a)) := fun s a =>
    (hφ _ _).2 ⟨D.reg _ hz s a, (hχv s a).symm⟩
  have hconj : ∀ τ a, χ (Sum.inr τ) a = χ (Sum.inl τ) (H.bar a) := fun τ a => Subtype.ext (by
    rw [hχv, hχv]
    exact congrArg φ (Subtype.ext (D.conj τ a)))
  have hconst : ∀ i (c : algebraicClosure (ZMod p) K), C.v i (algebraMap _ K c) ≤ 1 := fun i c =>
    hv i _ (mem_algebraicClosure_iff.1 c.2)
  obtain ⟨Vz, _, _, ⟨Mz⟩⟩ := lieModel_exists D.X D.t.G K z
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : FiniteDimensional K Vz := (GlobalTheory.T.lie_model_finite_projective D.X D.t.G K z Vz Mz).1
  obtain ⟨rz, hrz, -⟩ := lieModel_exists_unique_act D.X D.t.G K z Vz Mz (𝓞 E) D.t.act.act D.t.act.hom
    D.t.act.one D.t.act.mul D.t.act.add
  have hreg : ∀ q ∈ {q | InFibre D.ξ p q}, ∀ s a, D.σ s a ∈ regAt D.ξ q := fun q hq s a => D.reg q hq s a
  have hdisc : ∀ q ∈ {q | InFibre D.ξ p q}, unitAt D.ξ q ((NumberField.discr E : ℤ) : M.Ω) := fun q hq =>
    unitAt_int_of_fibre hp q hq D.unram
  choose Wf hW0 hWj hdegW using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inl τ)
    (D.b₁ τ) (D.ind₁ τ).1 (D.ind₁ τ).2 (D.flag₁ τ)
  choose Lf hL0 hLq hdegL using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inr τ)
    (D.b₂ τ) (D.ind₂ τ).1 (D.ind₂ τ).2 (D.flag₂ τ)
  have hxdeg : ∀ r, geoNum 1 Wi (fun _ => M.xdeg r) = coordDeg C w (M.xdeg r) := fun r => by
    rw [← hwW]
    exact GlobalTheory.T.function_field_degree_eq M.K M.ι p K C w (M.xdeg r) hFF hbir hwk
  let x : Ψ × Fin N → ℝ := fun r => (geoNum 1 Wi (fun _ => M.xdeg r) : ℝ)
  let wd : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Wf τ i) : ℝ)
  let ld : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Lf τ i) : ℝ)
  have hx1 : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = wd τ (i + 1) - wd τ i := by
    intro τ i hij
    obtain ⟨e₀, hdo⟩ := D.deg₁ τ i hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegW τ ⟨i, hij⟩)
    simp only [x, wd, hxdeg, h2]
    push_cast
    rfl
  have hx2 : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(ld τ (N - 1 - i + 1) - ld τ (N - 1 - i)) := by
    intro τ i hij
    have hlt : N - 1 - (i : ℕ) < N - j := by have := i.2; omega
    obtain ⟨e₀, hdo⟩ := D.deg₂ τ i hlt hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegL τ ⟨N - 1 - i, hlt⟩)
    have h3 : coordDeg C w (-M.xdeg (τ, i)) = -coordDeg C w (M.xdeg (τ, i)) := by
      simp [coordDeg]
    rw [h3] at h2
    have h4 : coordDeg C w (M.xdeg (τ, i)) = -(subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i + 1)) -
        subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i))) := by
      rw [← neg_eq_iff_eq_neg]; exact h2
    simp only [x, ld, hxdeg, h4]
    push_cast
    rfl
  obtain ⟨hgap, heq⟩ := GlobalTheory.T.nef_threshold_gap_condition Ψ N j p mu x wd ld hp2 hj hjN hdom hthr hx1 hx2
  have hfin := hC E H D.X D.t D.pow (algebraicClosure (ZMod p) K) K p hp2 C z Y hne hconst
    (fun i => D.fib ⟨_, h i⟩ (hi i)) Vz Mz rz hrz Ψ χ hχ hconj j (N - j) _ Wf Lf hj (by omega) hW0 hL0 hWj hLq hgap
  have hfin' : 0 ≤ ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := heq ▸ hfin
  have hcd : M.curveDeg mu 0 Wi = ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := by
    unfold RootModel.curveDeg
    rw [Fintype.sum_option]
    simp only [RootModel.coef, RootModel.line, M.x_deg, zero_div, zero_mul, zero_add, x]
  rw [hcd]
  exact hfin'

end GlobalTheory.CompanionTheory.Ar.Conj
