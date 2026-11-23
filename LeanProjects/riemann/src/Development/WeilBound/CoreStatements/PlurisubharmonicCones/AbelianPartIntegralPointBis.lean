import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt
open LevelTowerAlt.LocalPrimeBound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem abelian_part_integral_point_bis : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A hpq hdisc hfree hA s
  classical
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  obtain ⟨hact, hlab, hΛ, -⟩ := hA
  obtain ⟨ML, hML⟩ := (LieMove.main L 𝔐.X (spMap (algebraMap (𝓞 L) L) ≫ z) 𝔐.t.G P.tK.G P.m.φ V P.m.cart).2 MV
  have hactL : ML.IsActOf 𝔐.t.act.act A.ρ := fun a x => Over.OverMorphism.ext (by
    rw [← hML, hact a x, Over.comp_left, Over.comp_left, Category.assoc, P.m.act, ← hML, Category.assoc])
  let jE : CMType H ⊕ CMType H → (E →+* L) := fun s => IsFractionRing.lift (A.σ_inj s)
  let σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L) := fun s => RingOfIntegers.mapRingHom (jE s)
  have hσ₀ : ∀ s, (algebraMap (𝓞 L) L).comp (σ₀ s) = A.σ s := fun s => RingHom.ext fun a =>
    IsFractionRing.lift_algebraMap (A.σ_inj s) a
  have hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)) :=
    fun s a => by
      have h := hlab s a
      rw [← hσ₀] at h
      exact h
  have hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s) := by
    simpa only [hσ₀] using A.σ_bij.1
  have hex : ∀ p : ℕ, ∃ (κ : Ω) (k : 𝓞 L), p ∈ S → (HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p κ ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap (𝓞 L) L k)) ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
    intro p
    by_cases hpS : p ∈ S
    swap
    · exact ⟨0, 0, fun h => absurd h hpS⟩
    have hp := 𝔐.S_prime p hpS
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hG.2.2.2.2.2.2.1 E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq (hfree p hpS)
    have hne : Ideal.span {(p : 𝓞 L)} ≠ ⊤ := fun h => by
      have h1 := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, RingOfIntegers.rank] at h1
      exact (Nat.one_lt_pow Module.finrank_pos.ne' hp.one_lt).ne' h1
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpQ : (p : 𝓞 L) ∈ Q := hle (Ideal.mem_span_singleton_self _)
    have h1 := (hS _ (inFibre_loc 𝔐 z Q hpQ)).1
    have hq : (⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime Q)) ≫ z), 𝔐.all _⟩ : Cpt 𝔐.ξ) =
        ⟨z (⟨Q, hQ.isPrime⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ := Subtype.ext (centre_loc z Q)
    rw [hq] at h1
    obtain ⟨r, -, -, hr, -⟩ := PtHt.FinFrame.reg_value z hξ ⟨Q, hQ.isPrime⟩ (𝔐.all _) h1
    obtain ⟨a1, a2⟩ := value_cp hξ hp hκ hr
    obtain ⟨k, rfl, b1, b2⟩ := const_int hp a1 a2
    exact ⟨κ, k, fun _ => ⟨⟨hfree p hpS, hS, hr⟩, b1, b2⟩⟩
  choose κ k hk using hex
  obtain ⟨n1, n2⟩ := norm_bound (jE s) S k fun p hp => (hk p hp).2
  have hset : ∀ 𝔭 : PrimeSpectrum (𝓞 L), {x' : V | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
      ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left} =
      {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun 𝔭 => by
    ext x'
    constructor
    · rintro ⟨e, he, v, hv, h⟩
      have e' : v = ML.pt x' := Over.OverMorphism.ext (h.symm.trans (hML _))
      exact ⟨e, he, e' ▸ hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, _, hv, hML _⟩
  have hF : ∀ x, x ∈ 𝔐.FibLat (𝔐.V s) z P MV ↔ ∀ 𝔭 : PrimeSpectrum (𝓞 L), ∃ t ∉ 𝔭.asIdeal, t • x ∈
      Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun x => by
    simp only [HodgeCpt.FibLat, hset, Submodule.mem_iInf]
    exact forall_congr' fun 𝔭 => PtHt.FinFrame.span_sat_iff 𝔭.asIdeal le_rfl
      (fun u hu => ⟨1, (Ideal.ne_top_iff_one _).1 𝔭.isPrime.ne_top, by rwa [one_smul]⟩) x
  have hcc : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime], ∃ cc : Localization.AtPrime Q →+* L,
      cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L := fun Q _ => by
    have hunit : ∀ d : Q.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d =>
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
        fun e => d.2 (e ▸ Q.zero_mem))
    exact ⟨IsLocalization.lift (M := Q.primeCompl) hunit, IsLocalization.lift_comp hunit⟩
  have hloc := fun (Q : Ideal (𝓞 L)) [Q.IsPrime] cc hc =>
    loc 𝔐 z ML A.ρ hactL σ₀ hσ hinj κ k (fun p hp => (hk p hp).1) hdisc s Q cc hc
  rw [hσ₀] at hloc
  refine ⟨_, n1, Submodule.smul_le.2 fun a ha x hx => ?_, Submodule.smul_le.2 fun a _ x hx => ?_, n2⟩
  · have hx' := (hF x).1 hx
    have key : ∀ d ∈ differentIdeal ℤ (𝓞 E), (∏ p ∈ S, k p) • σ₀ s d • x ∈ A.eig s := fun d hd => by
      refine ⟨(hΛ _).2 ?_, ?_⟩
      · let MB := LiePull.extModel (g := algebraMap (𝓞 L) L) (x := z) (FaithfulSMul.algebraMap_injective _ _) rfl ML
        obtain ⟨e, he⟩ := GlobalTheory.T.tangent_vector_extends_dvr (𝓞 L) L 𝔐.X z 𝔐.t.G _ MB (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)) (ML.tan _)
          fun Q hQ cc hc => ((hloc Q cc hc).2 x (hx' ⟨Q, hQ.isPrime⟩) d hd).2
        exact ⟨MB.pt e, MB.tan e, (hML _).trans ((Category.comp_id _).symm.trans he)⟩
      · obtain ⟨cc, hc⟩ := hcc ⊥
        exact ((hloc ⊥ cc hc).2 x (hx' ⟨⊥, Ideal.isPrime_bot⟩) d hd).1
    have h1 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V ((∏ p ∈ S, k p) • x)) :=
      Ideal.map_le_iff_le_comap.2 fun d hd => by
        show σ₀ s d • (∏ p ∈ S, k p) • x ∈ A.eig s
        rw [smul_comm]
        exact key d hd
    have h2 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) * Ideal.span {∏ p ∈ S, k p} ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V x) :=
      Ideal.mul_le.2 fun r hr t ht => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
        show (r * (u * ∏ p ∈ S, k p)) • x ∈ A.eig s
        rw [mul_left_comm, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (h1 hr)
    exact h2 ha
  · refine Submodule.smul_mem _ _ ((hF x).2 fun 𝔭 => ?_)
    obtain ⟨cc, hc⟩ := hcc 𝔭.asIdeal
    obtain ⟨v, hv, hxv⟩ := (hΛ x).1 hx.1
    exact (hloc 𝔭.asIdeal cc hc).1 x hx.2 ⟨v, hv, (hML x).symm.trans hxv⟩

end LevelTowerAlt
