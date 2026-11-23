import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HeightComparisonGlobalModel
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
namespace GlobalTheory.CompanionTheory.Ar.Cusp.U4

open LevelTowerAlt GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flat_point_of_principal_sign (hG : Top.Given) (hF : FlatDegree) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) {L : Type} [Field L] [NumberField L] (t : SAB H (Sp L)) (ht : IsPrincipal t) (ρ : L) (p' q' : ℕ)
    (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q'))
    (h1 : 1 ≤ p' + q') (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    ∃ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : NumberField c.F) (F : Type) (_ : Field F)
      (_ : NumberField F) (β : c.F →+* F) (e : L →+* F) (io : F →+* ℂ) (tK : SAB H (Sp F)) (_ : SABMap tK t (spMap e))
      (y : Sp F ⟶ Xo.XF c) (_ : SABMap tK Xo.univ.t (under y)) (U : Set (Xo.XF c)) (φ : FrameFn Xo c)
      (N : LogNorms c.F), D.p = p' ∧ D.q = q' ∧ (∀ x, io (β x) = (x : ℂ)) ∧ (∀ x, io (e x) = σ x) ∧
      y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧ IsLineFn U τ φ ∧ (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧
      (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) ∧ N.IsAdelic ∧
      N.deg = ((p' : ℝ) - q') / 2 * (GlobalTheory.CM.logOm E χ).re := by
  obtain ⟨⟨hP, hN, -, -⟩, -, -, -, hResK, -, -, hGaga, -⟩ := hG
  obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := GlobalTheory.T.tate_iso_datum_exists E H L t ht σ p' q' fun τ => by
    have := hs ℂ σ τ
    rwa [hσ] at this
  let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l h1).some
  obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
  obtain ⟨c₀⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H D l (Xo l) c₀ h1
  haveI := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨F, hfin, hF', e, o, he, ⟨m⟩⟩ := SabModel.exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
  let bF : c.F →+* F := (IntermediateField.inclusion hF').toRingHom
  let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
    rw [hf, ← Spec.map_comp]
    rfl)
  have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
  let x₀ : (Xo l).XF c := y (IsLocalRing.closedPoint F)
  let Z : Formalism.L2.Pj.Comp (Xo l) c := ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  have hyZ : Set.range y ⊆ (Z : Set ((Xo l).XF c)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s (IsLocalRing.closedPoint F)]
    exact mem_irreducibleComponent
  obtain ⟨V, hV, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H D l (Xo l) c h1
  obtain ⟨g, ty, FU, i, hty, hper⟩ := GlobalTheory.T.exists_family_uniformisation E H D l (Xo l) c Z (D.p + D.q) (V c.F.val.toRingHom).toPj h1
    (hV c.F.val.toRingHom (show Formalism.L2.Pj.GoodEmb c c.F.val.toRingHom from rfl)).1 (hc c le_rfl Z)
  have hclo : IsClopen (Z : Set ((Xo l).XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj (Xo l) c) Z
  obtain ⟨φ, N, hfg, hn, -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hResK hGaga hP E H D Xo l c (Z : Set ((Xo l).XF c)) τ g ty FU i h1 hτ hg
    hty hclo Z.2.1 hper
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ +
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  obtain ⟨had, hdeg⟩ := GlobalTheory.T.kronecker_character_period_formula hF E H D l (Xo l) c g ty FU i _ τ φ N' χ hχ hty hτ hfg hn.1 hn.2
  exact ⟨D, l, Xo l, c, inferInstance, F, inferInstance, inferInstance, bF, e, F.val.toRingHom, o.t, m, y,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast mf.toSABMap hy1.symm, Z, φ, N', rfl, rfl, fun _ => rfl, he, hy2, hyZ, hfg.line, hn.1,
    hn.2, had, hdeg⟩

theorem flat_hermitian_fibre_signature (hG : Top.Given) (hF : FlatDegree) (H : Host E) {L : Type} [Field L] [NumberField L]
    {t' : SAB H (Sp (𝓞 L))} {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    {B : HermitianBundle.{0} L} (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}
    (s₁ s₂ : 𝓞 E →+* 𝓞 L) (hP : IsPrincipal tB) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (hρ : MB.IsActOf t'.act.act ρM) (ρ : L) (p' q' : ℕ) (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q'))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (h₁ : ∀ a, σ (s₁ a : L) = τ (a : E))
    (h₂ : ∀ a, σ (s₂ a : L) = starRingEnd ℂ (τ (a : E))) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
  have r₁ : B.rank (eigSp ρM s₁) = p' := rank_eig MB hρ m' σ s₁ ((hs ℂ σ _).1 ((h₁ _).trans (hτ.trans hσ.symm)))
  have r₂ : B.rank (eigSp ρM s₂) = q' := rank_eig MB hρ m' σ s₂ ((hs ℂ σ _).2 fun h => by
    have h3 := (h₂ H.rt).symm.trans (h.trans hσ)
    rw [hτ, (rt0_conj_neg_ne_zero H).1] at h3
    exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h3))
  rcases Nat.eq_zero_or_pos (p' + q') with h0 | h0
  · have e₁ : eigSp ρM s₁ = ⊥ := Submodule.finrank_eq_zero.1 (r₁.trans (by omega))
    have e₂ : eigSp ρM s₂ = ⊥ := Submodule.finrank_eq_zero.1 (r₂.trans (by omega))
    rw [e₁, e₂, sub_self, abs_zero]
    positivity
  obtain ⟨D, l, Xo, c, _, F, _, _, β, e, io, tK, mo, y, mf, U, φ, N, rfl, rfl, hβ, he, hy, hU, hφ, hinf, hfin, had,
    hdeg⟩ := flat_point_of_principal_sign hG hF H tB hP ρ p' q' σ hσ hs h0 τ hτ χ hχ
  obtain ⟨n₀, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' mo
  let n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n₀ (LevelTowerAlt.spMap_comp _ _).symm
  have hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₁ a)).symm)
  have hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₂ a)).symm)
  obtain ⟨vK, vec, k1, k2, -, k4, k5⟩ := exists_vec MB hρ n mf _
    (e.injective.comp (IsFractionRing.injective (𝓞 L) L)) (𝟙 _) (Category.id_comp _) (under y)
    (Category.id_comp _).symm
  obtain ⟨x₁, hx₁⟩ := exists_smul_mem_span B _ r₁
  obtain ⟨x₂, hx₂⟩ := exists_smul_mem_span B _ r₂
  obtain ⟨N₁, a₁, d₁, i₁, f₁⟩ := exists_logNorms B _ x₁ hx₁.1 hx₁.2.1 r₁
  obtain ⟨N₂, a₂, d₂, i₂, f₂⟩ := exists_logNorms B _ x₂ hx₂.1 hx₂.2.1 r₂
  have hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k) :=
    ⟨hy, hU, hs₁ ▸ k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2, hs₂ ▸ k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2⟩
  have key := deg_eq_sub β e N N₁ N₂ _ (hφ.ne F β y _ _ hfr) had a₁ a₂
    (fun s => by
      rw [i₁, i₂]
      exact inf_norm MB hρ hfib n mf hy hU hφ hs₁ hs₂ k1 k2 hx₁ hx₂ hfr s (hinf _))
    fun p j => by
      obtain ⟨y₁, u₁, T₁, a1, a2, a3, a4, a5, a6, a7⟩ := f₁ p (j.comp e)
      obtain ⟨y₂, u₂, T₂, b1, b2, b3, b4, b5, b6, b7⟩ := f₂ p (j.comp e)
      rw [a7, b7]
      exact fin_norm MB hρ n mf hy hU hφ hs₁ hs₂ k1 k2 k4 k5 hfr p j a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 (hfin p _)
  rw [← d₁, ← d₂, ← key, hdeg, r₁, r₂, abs_mul]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
    linarith [(Nat.cast_nonneg D.p : (0 : ℝ) ≤ D.p), (Nat.cast_nonneg D.q : (0 : ℝ) ≤ D.q)]

theorem flat_saturation_of_degree (hG : Top.Given) (hF : FlatDegree) : FlatSat := by
  obtain ⟨C, hC, hlog⟩ := logOm_bound
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H L _ _ t' tB m' B MB ρM s₁ s₂ hP hfib hρ ⟨ρ, p', q', hρ2, hs⟩ hinj hconj
  obtain ⟨_, χ, hχ, hb⟩ := hlog E H
  obtain ⟨σ, hσ⟩ := SabModel.exists_embedding_rt0 H ρ hρ2
  have hi : Function.Injective ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) :=
    (σ.injective.comp (IsFractionRing.injective (𝓞 L) L)).comp hinj
  let τ : E →+* ℂ := IsFractionRing.lift hi
  have hτ : ∀ a : 𝓞 E, σ (s₁ a : L) = τ (a : E) := fun a => (IsFractionRing.lift_algebraMap hi a).symm
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← hτ, H.sqrt_neg_disc_sq]
    have := congrArg ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h : |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact flat_hermitian_fibre_signature hG hF H m' MB s₁ s₂ hP hfib hρ ρ p' q' σ hσ hs τ h hτ (fun a => by rw [hconj, hτ]) χ hχ
    · rw [abs_sub_comm, add_comm]
      refine flat_hermitian_fibre_signature hG hF H m' MB s₂ s₁ hP hfib hρ ρ p' q' σ hσ hs ((starRingEnd ℂ).comp τ) ?_
        (fun a => by rw [hconj, hτ]; rfl) (fun a => by rw [hτ]; exact (Complex.conj_conj _).symm) χ hχ
      rw [RingHom.comp_apply, h, map_neg, (rt0_conj_neg_ne_zero H).1, neg_neg]
  refine h.trans ?_
  rw [_root_.mul_comm C, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end GlobalTheory.CompanionTheory.Ar.Cusp.U4

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) :=
  LevelTowerAlt.height_comparison_global_model GlobalTheory.CompanionTheory.Ar.Cusp.U4.flat_saturation_of_degree
