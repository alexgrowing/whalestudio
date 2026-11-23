import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RulePow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHost
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoSquare
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDatum
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoPoint
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoExt
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoFrame
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

section Unit

open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels Formalism.L2.Pj

theorem lieMult_comp {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (σ : O ≃+* O)
    (s : G ≅ G) [IsMonHom s.hom] (hs : ∀ a, act.act (σ a) ≫ s.hom = s.hom ≫ act.act a) {k : Type} [Field k]
    (z : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) (h : LieMult act z τ n) : LieMult act z (τ.comp σ.toRingHom) n := by
  have e := GlobalTheory.LiePull.lieMult_pull O S S G G (𝟙 S) s.hom.left act (GlobalTheory.Serre.comapAct act σ.toRingHom)
    (isGrpPullback_of_iso s) (fun c => congrArg (fun q => q.left) (hs c)) k z (τ.comp σ.toRingHom) n
  rw [Category.comp_id] at e
  refine e.1 ?_
  have key : ∀ v, IsLieEigen (GlobalTheory.Serre.comapAct act σ.toRingHom) z (τ.comp σ.toRingHom) v ↔ IsLieEigen act z τ v :=
    fun v => and_congr_right fun _ => ⟨fun hv a => by
      obtain ⟨b, rfl⟩ := σ.surjective a
      exact hv b, fun hv a => hv (σ a)⟩
  obtain ⟨v, h₁, h₂⟩ := h
  exact ⟨v, fun i => (key _).2 (h₁ i), fun w hw => h₂ w ((key _).1 hw)⟩

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E'}

theorem exists_type (Q : PairHost H H') {V Ω : Type} [CommRing V] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (f : V →+* Ω)
    (T : SAB H' (Sp V)) (s : T.G ≅ T.G) [IsMonHom s.hom] (hs : ∀ a, T.act.act (Q.σ a) ≫ s.hom = s.hom ≫ T.act.act a)
    {m : ℕ} {w : Fin m → (epsR V ⟶ T.G)} (hw : IsLieBasis w) :
    ∃ (ρ : Ω) (p q : ℕ), ρ ^ 2 = -(H'.d : Ω) ∧ ∀ τ : 𝓞 E' →+* Ω,
      (τ H'.rt = ρ → LieMult T.act (spMap f) τ p) ∧ (τ H'.rt ≠ ρ → LieMult T.act (spMap f) τ q) := by
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff _ V T.G T.act m w T.semi.smooth hw
  obtain ⟨M', -, hM'⟩ := hM Ω f
  let τ₀ : 𝓞 E' →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := E') (M := Ω)).toRingHom.comp (algebraMap (𝓞 E') E')
  let τ₁ : 𝓞 E' →+* Ω := τ₀.comp H'.bar.toRingHom
  have sq : ∀ τ : 𝓞 E' →+* Ω, τ H'.rt ^ 2 = -(H'.d : Ω) := fun τ => by rw [← map_pow, H'.rt_sq, map_neg, map_natCast]
  have h₁ : τ₁ H'.rt = -τ₀ H'.rt := by
    show τ₀ (H'.bar H'.rt) = _
    rw [GlobalTheory.HostModel.bar_rt, map_neg]
  have mv : ∀ (τ τ' : 𝓞 E' →+* Ω) (n : ℕ), τ H'.rt = τ' H'.rt → LieMult T.act (spMap f) τ n →
      LieMult T.act (spMap f) τ' n := fun τ τ' n e h => by
    rcases Q.chars Ω τ τ' e with rfl | rfl
    · exact h
    · exact lieMult_comp T.act Q.σ s hs _ τ n h
  refine ⟨τ₀ H'.rt, _, _, sq τ₀, fun τ => ⟨fun e => mv τ₀ τ _ e.symm ((hM' τ₀ _).2 rfl),
    fun e => mv τ₁ τ _ ?_ ((hM' τ₁ _).2 rfl)⟩⟩
  rw [h₁]
  exact ((sq_eq_sq_iff_eq_or_eq_neg.1 ((sq τ).trans (sq τ₀).symm)).resolve_left e).symm

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem key_isUnit {κ : KeyRule} (hκ : IsKeyRule κ) (hpow : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K) (j : ℕ),
      GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j)
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] (t : SAB H (Sp V)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR V ⟶ t.G)) (x : KeyIn K)
    (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K)) (hw : IsLieBasis w) (hθ : NonzeroClosed (X := t.G) θ) :
    ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := by
  obtain ⟨E', _, _, _, H', ⟨Q⟩⟩ := exists_pairHost H
  obtain ⟨y, hy⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x 2 (by norm_num)
  obtain ⟨T, s, θ₂, m, w₂, hs₁, hs₂, hw₂, hθ₂, hy₂⟩ := exists_square Q _ t θ w x y hx hw hθ hy
  let Ω := AlgebraicClosure K
  let i := algebraMap K Ω
  obtain ⟨ρ, p, q, hρ, hty⟩ := exists_type Q (i.comp (algebraMap V K)) T s hs₂ hw₂
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull (spMap (algebraMap V K)) T
  obtain ⟨TK, rfl, hgK⟩ := exists_pat_of_isFibreOf mK hy₂
  obtain ⟨tΩ, ⟨mΩ⟩⟩ := exists_pull (spMap i) TK.t
  obtain ⟨⟨TΩ, rfl, hgΩ⟩, hL⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E' H' _ _ _ TK tΩ mΩ
  have lK : ∀ τ N, LieMult T.act (spMap (i.comp (algebraMap V K))) τ N → LieMult TK.t.act (spMap i) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T.act TK.t.act mK.cart mK.act Ω (spMap i) τ N).2 (by rwa [← spMap_comp])
  have lΩ : ∀ τ N, LieMult TK.t.act (spMap i) τ N → LieMult TΩ.t.act (𝟙 _) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ TK.t.act TΩ.t.act mΩ.cart mΩ.act Ω (𝟙 _) τ N).2 (by rwa [Category.id_comp])
  obtain ⟨D, rfl, rfl, hpq, ⟨I⟩⟩ := exists_datum_tate TΩ (by rw [hgΩ, hgK]; exact y.g_pos) ρ hρ p q
    fun τ => ⟨fun e => lΩ _ _ (lK _ _ ((hty τ).1 e)), fun e => lΩ _ _ (lK _ _ ((hty τ).2 e))⟩
  obtain ⟨I', -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) TK.t.PP.isLB TΩ.t.PP.isLB mΩ.cart (LBIso.symm hL) TK.t.act.act
    TΩ.t.act.act mΩ.act (𝟙 _) (spMap i) (Category.id_comp _).symm).1 I
  obtain ⟨l, hA, hgood, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E' H' 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists E' H' D l hpq
  obtain ⟨K', _, z, t', ⟨m₁⟩, ⟨m₂⟩⟩ := exists_point hA Xo (GlobalTheory.LevelExist.minCoeff l) TK ρ hρ
    (fun τ => ⟨fun e => lK _ _ ((hty τ).1 e), fun e => lK _ _ ((hty τ).2 e)⟩) I'
  obtain ⟨T₀, g, j, _, hgj⟩ := exists_cdvr (V := V) (K := K) (K' := K')
  have : CharZero T₀.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T₀.V T₀.Fr)
  let j₀ : K →+* T₀.Fr := j.comp (algebraMap K K')
  obtain ⟨G, ⟨mG⟩⟩ := exists_pull (spMap g) T
  obtain ⟨t'', ⟨m₃⟩⟩ := exists_pull (spMap j) t'
  obtain ⟨n₁, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₂ m₃
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₁ m₃
  obtain ⟨n₃, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ mK n₂
  obtain ⟨n₄, -⟩ := sabCancel pullCubCancel E' H' _ _ _ T G t'' (spMap g) (spMap (algebraMap T₀.V T₀.Fr)) mG
    (PullbackSections.sabMapCast n₃ (by rw [← spMap_comp, ← spMap_comp, ← spMap_comp, hgj, RingHom.comp_assoc]))
  obtain ⟨y', hy'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j₀
  have hf := isFibreOf_trans T.PP.isLB hy₂ hy'
  rw [← hgj] at hf
  obtain ⟨θ', w', hθ', hw', hf'⟩ := exists_isFibreOf_pull mG hθ₂ hw₂ hf
  have := G.semi.smooth
  obtain ⟨u, hu⟩ := key_unit hκ hpq hgood (spMap j ≫ z) (PullbackSections.sabMapCast n₁ (Category.assoc _ _ _).symm) n₄ hw'
    (generates_of_isFibreOf G.PP.isLB hf' hθ') y' hf'
  rw [hκ.2.1 K T₀.Fr j₀ y y' hy', hpow K x y 2 hy, Units.val_pow_eq_pow_val] at hu
  have hj : ∀ a : V, j₀ (algebraMap V K a) = algebraMap T₀.V T₀.Fr (g a) := fun a => (RingHom.congr_fun hgj a).symm
  have inj := IsFractionRing.injective T₀.V T₀.Fr
  rcases ValuationRing.isInteger_or_isInteger V (κ K x : K) with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha, ← map_pow, hj] at hu
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (inj hu ▸ u.isUnit))
    exact ⟨hau.unit, ha.symm⟩
  · have e : algebraMap T₀.V T₀.Fr (g (a ^ 2) * u) = algebraMap T₀.V T₀.Fr 1 := by
      rw [map_mul, ← hu, ← hj, ← map_mul, map_pow, ha, ← mul_pow, inv_mul_cancel₀ (κ K x).ne_zero, one_pow, map_one, map_one]
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (IsUnit.of_mul_eq_one _ (inj e)))
    refine ⟨hau.unit⁻¹, ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ha, inv_inv]

end Unit

section Main

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights TensorProduct GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem key_integral : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ →
    GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R))
      (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)),
      KeyOver (algebraMap R K) t th x v → IsLieBasis v →
      (∀ (d : R) (th' : t.PP.L.Sec), (∀ i, th.f i = constFn t.G.hom _ d * th'.f i) → IsUnit d) →
      (κ K x : K) ∈ Set.range (algebraMap R K) := by
  intro κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hprim
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, _root_.mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one] using k₅
  have := t.semi.smooth
  obtain ⟨u, hu⟩ := key_isUnit hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) t th v x
    ⟨φ, he, w, rfl, dualMap (algebraMap R K), h1, h2, h3, h4,
      fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [dualMap], h5⟩
    hv (nonzeroClosed_of_primitive th hprim)
  exact ⟨u, hu.symm⟩

theorem kp : KeyBadSt :=
  fun κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ _ => key_integral κ k₁ k₂ k₃ k₄ k₅ E H R K

end Main

end PositivityTheory.HtPt.Kftwo
