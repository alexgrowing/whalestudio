import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRepsOpen

open Filter Topology

theorem tendsto_smul_zero_of_compact {R M : Type} [Zero R] [Zero M] [SMulWithZero R M] [TopologicalSpace R]
    [TopologicalSpace M] [ContinuousSMul R M] {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) {C : Set M} (hC : IsCompact C)
    {y : ℕ → M} (hy : ∀ n, y n ∈ C) : Tendsto (fun n => a n • y n) atTop (𝓝 0) := by
  intro U hU
  have h : ∀ᶠ r in 𝓝 (0 : R), ∀ z ∈ C, r • z ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    refine (continuous_smul (M := R) (X := M)).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  exact (ha.eventually h).mono fun n hn => hn _ (hy n)

theorem tendsto_one_of_cong (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) (A : ℕ → Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hA : ∀ n : ℕ, ∀ z ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)), ∃ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)),
      A n *ᵥ z - z = n.factorial • y) : Tendsto A atTop (𝓝 1) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat F E L hL
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  obtain ⟨d, hd, hdL⟩ := GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  have h1 : (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hz : (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL, rfl⟩
  choose y hy e using fun n => hA n _ hz
  have ht := tendsto_smul_zero_of_compact (R := GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F) hC
    fun n => hLC _ (hy n)
  have ht' := ((tendsto_pi_nhds.1 ht i).mul_const ((1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((d : E)⁻¹))).add_const
    ((1 : Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j)
  rw [Pi.zero_apply, zero_mul, zero_add] at ht'
  refine ht'.congr fun n => ?_
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have e' : (A n - 1) *ᵥ (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) = n.factorial • y n := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e]
  rw [Nat.cast_smul_eq_nsmul, ← e', ← eq_sub_iff_add_eq, ← Matrix.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem exists_finCong_le (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (hJ : IsOpen (J : Set (Bridge.Gf V))) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → fin V k ∈ J := by
  by_contra hc
  have hc' : ∀ n : ℕ, ∃ k : GA D V, GlobalTheory.Member.FinCong V n.factorial k ∧ fin V k ∉ J := fun n => by
    by_contra h
    exact hc ⟨n.factorial, n.factorial_pos, fun k hk => by_contra fun h' => h ⟨k, hk, h'⟩⟩
  choose k hk hkJ using hc'
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key : ∀ u : ℕ → GA D V, (∀ n : ℕ, GlobalTheory.Member.FinCong V n.factorial (u n)) →
      Tendsto (fun n => (finHom V (u n)).1) atTop (𝓝 1) := fun u hu => by
    refine tendsto_one_of_cong D.host.F D.host.E _ h3 h4 _ fun n => ?_
    have := hu n
    unfold GlobalTheory.Member.FinCong at this
    rw [h1] at this
    exact this
  have ht : Tendsto (fun n => fin V (k n)) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine (key k hk).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
    have := key (fun n => (k n)⁻¹) fun n => GlobalTheory.Member.PrincLevel.finCong_inv (hk n)
    simp only [map_inv] at this
    exact this
  obtain ⟨n, hn⟩ := (ht.eventually (hJ.mem_nhds J.one_mem)).exists
  exact hkJ n hn

theorem exists_rep_splitOffBad : ∀ (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (bad : ℕ), bad ≠ 0 → IsOpen (J : Set (Bridge.Gf V)) → ∀ x : Bridge.Gf V, ∃ (γ : GQ V) (h : GA D V) (k : J), SplitOffBad V bad h ∧ x = Bridge.ratF V γ * fin V h * (k : Bridge.Gf V) := by
  intro D V J bad hb hJ x
  obtain ⟨N, hN, hK⟩ := exists_finCong_le D V J hJ
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V hN (fun k _ hk => hK k hk) (Nat.pos_of_ne_zero hb) x
  exact ⟨γ, h, k, GlobalTheory.SplitReps.splitOffBad_of_suppSplit V bad h hh hs, e⟩

end GlobalTheory.SplitRepsOpen
