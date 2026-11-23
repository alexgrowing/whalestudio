import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLatLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationRelativeDimZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkRootMultiplicationScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkChainPeriodicRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamLatticeTangentCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeTangentCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulTmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRootStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRingStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaGeneratedOfRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBasisStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLinkStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaSpanStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaGlueStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBundleOfLinkSpanGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaMapStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaExtensionStatementStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.OmegaHT

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem epsMul_one_comp {R : Type} [CommRing R] {T : Scheme.{0}} (v : Sp (DualNumber R) ⟶ T) :
    spMap (epsMul (1 : R)) ≫ v = v := by
  rw [GlobalTheory.ShFam.Pad.HTBound.eps_one]
  exact (congrArg (· ≫ v) (Spec.map_id _)).trans (Category.id_comp v)

open MonObj in

theorem lat_act (p : ℕ) (x : Sp C ⟶ X) (b : Bool) {v : Sp (DualNumber C) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (h : v ∈ lat t p x b) (c : 𝓞 E) : v ≫ (t.act.act c).left ∈ lat t p x b := by
  have k : IsCombAtG t x (fun _ : Fin 1 => v ≫ (t.act.act c).left) (fun _ => 1) (v ≫ (t.act.act c).left) :=
    ⟨fun _ => ovT hv ≫ t.act.act c, fun _ => (epsMul_one_comp _).symm, by
      rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]; rfl⟩
  cases b
  · exact latDR_comb_act E H X t C x v hv h 1 (fun _ => c) (fun _ => 1) (fun _ => norm_one.le) _ k
  · exact GlobalTheory.HTStable.latHT_comb_act E H X t C p x v hv h 1 (fun _ => c) (fun _ => 1) (fun _ => norm_one.le) _ k

theorem norm_root_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {p : ℕ}
    [Fact p.Prime] (hC : ‖(p : C)‖ = (p : ℝ)⁻¹) {π : Γ(B.X, ⊤)} (hπ : IsRootOfP p π (p - 1)) (w : Sp ↥(intO C) ⟶ B.X) :
    ‖valF (spMap (intO C).subtype ≫ w) ⊤ π‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := hπ
  have hu1 : ‖valF (spMap (intO C).subtype ≫ w) ⊤ (u : Γ(B.X, ⊤))‖ ≤ 1 := GlobalTheory.GenBd.norm_valF_le_one w ⊤ le_top _
  have e : valF (spMap (intO C).subtype ≫ w) ⊤ π ^ (p - 1) =
      valF (spMap (intO C).subtype ≫ w) ⊤ (u : Γ(B.X, ⊤)) * p := by
    have h : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ ⊤ := le_top
    rw [valF, valF, dif_pos h, dif_pos h, ← map_pow, ← map_pow, hu, map_mul, map_mul, map_natCast, map_natCast]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hn : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  refine le_of_pow_le_pow_left₀ hn (Real.rpow_nonneg (by linarith) _) ?_
  rw [← norm_pow, e, norm_mul, hC, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Nat.cast_sub hp.one_lt.le,
    Nat.cast_one, neg_mul, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_neg_one]
  exact mul_le_of_le_one_left (by positivity) hu1

end Lat

theorem exists_action (h6 : ExtSt) {X : Scheme.{0}} [IsIntegral X] {F : X.Modules} {r : ℕ} (hF : GlobalTheory.VB.IsVB F r) {J : Type}
    {A : J → X.Opens} {s : ∀ a, Fin r → Γ(F, A a)} (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) {a₀ : J} (hη : genericPoint X ∈ A a₀)
    {Λ : Type} [CommRing Λ] (lam : ∀ a, Fin r → Λ →+* Γ(X, A a))
    (hex : ∀ c, ∃ φ : F ⟶ F, ∀ a i, φ.app _ (s a i) = lam a i c • s a i) :
    ∃ ρ : Λ →* End F, (∀ c d, (ρ (c + d) : F ⟶ F) = (ρ c : F ⟶ F) + (ρ d : F ⟶ F)) ∧
      ∀ c a i, (ρ c : F ⟶ F).app _ (s a i) = lam a i c • s a i := by
  choose φ hφ using hex
  refine ⟨⟨⟨φ, ?_⟩, fun c d => ?_⟩, fun c d => ?_, hφ⟩
  · refine h6 X F F r r _ (s a₀) _ _ hη (hs a₀) hF fun i => ?_
    rw [hφ, map_one, one_smul]
    rfl
  · refine h6 X F F r r _ (s a₀) _ _ hη (hs a₀) hF fun i => ?_
    change _ = (φ c).app _ ((φ d).app _ (s a₀ i))
    rw [hφ, hφ, (φ c).app_smul, hφ, smul_smul, map_mul, mul_comm]
  · refine h6 X F F r r _ (s a₀) _ _ hη (hs a₀) hF fun i => ?_
    change (φ (c + d)).app _ (s a₀ i) = (φ c).app _ (s a₀ i) + (φ d).app _ (s a₀ i)
    rw [hφ, hφ, hφ, map_add, add_smul]

set_option maxHeartbeats 2000000 in

theorem exists_pres (h5 : MapSt) (h6 : ExtSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : LocM.Mdl Y i₀), ∀ [Fact p.Prime], (p : ℂ) ∈ W.nonunits → ∀ [IsDiscreteValuationRing (Z.i.c.V W)]
    (B : Vert.Model (Z.i.c.V W)), GlobalTheory.IsNormalScheme B.X → ∀ h : B.X ⟶ Z.X, ToOpen Z h →
    ∀ (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (F F' : B.X.Modules)
    (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (s' : ∀ a : Fin Z.m, Fin r → Γ(F', h ⁻¹ᵁ (Z.U a).1)),
    GlobalTheory.VB.IsVB F r → GlobalTheory.VB.IsVB F' r → IsLat Z h x true false F s → IsLat Z h x true true F' s' →
    ∀ π : Γ(B.X, ⊤), IsRootOfP p π (p - 1) →
    ∃ (oo : EPres B (𝓞 E)) (u : oo.E ⟶ oo.E'), u ≫ oo.ψ = smulA _ π ∧ IsEqLatPres Z h x true oo := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z _ hW _ B hB h ho r x hx F F' s s' hF hF' k k' π hπ
  have hp : p.Prime := Fact.out
  obtain ⟨a₀, hη⟩ := GlobalTheory.TestPts.exists_chart_of_maximal h ho (η := genericPoint B.X)
    fun y hy => (hy.antisymm (genericPoint_specializes y)).eq
  let lam : ∀ a : Fin Z.m, Fin r → 𝓞 E →+* Γ(B.X, h ⁻¹ᵁ (Z.U a).1) := fun a i =>
    ((h.app (Z.U a).1).hom.comp ((Z.alg a).comp (embK Z.i.c (x i).1))).comp (H.bar : 𝓞 E →+* 𝓞 E)
  have one : ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ B.X), valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ (1 : Γ(B.X, ⊤)) = 1 :=
    fun y w => GenId.valF_one le_top
  have act : ∀ (b : Bool) (G : B.X.Modules) (σ : ∀ a : Fin Z.m, Fin r → Γ(G, h ⁻¹ᵁ (Z.U a).1)), GlobalTheory.VB.IsVB G r →
      IsLat Z h x true b G σ → ∀ c, ∃ φ : G ⟶ G, ∀ a i, φ.app _ (σ a i) = lam a i c • σ a i := fun b G σ hG kG c => by
    obtain ⟨φ, hφ⟩ := h5 E H Dw Xo p W Y i₀ Z hp hW B hB h ho r x hx b b G G σ σ hG hG kG kG 1 (H.bar c)
      fun y w _ v hv hl => by rw [one, epsMul_one_comp]; exact lat_act p _ b hv hl _
    exact ⟨φ, fun a i => by rw [hφ, map_one, one_mul]; rfl⟩
  obtain ⟨ρ, ρa, hρ⟩ := exists_action h6 hF k.frame hη lam (act _ F s hF k)
  obtain ⟨ρ', ρa', hρ'⟩ := exists_action h6 hF' k'.frame hη lam (act _ F' s' hF' k')
  obtain ⟨ψ, hψ⟩ := h5 E H Dw Xo p W Y i₀ Z hp hW B hB h ho r x hx true false F' F s' s hF' hF k' k 1 1
    fun y w _ v hv hl => by
      rw [one, epsMul_one_comp]
      exact latDR_subset_latHT E H _ _ _ p _ (lat_act p _ false hv hl _)
  obtain ⟨u, hu⟩ := h5 E H Dw Xo p W Y i₀ Z hp hW B hB h ho r x hx false true F F' s s' hF hF' k k' π 1
    fun y w _ v hv hl => by
      have g : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π := Category.assoc _ _ _
      have hl' := lat_act p _ true hv hl 1
      rw [g] at hl' ⊢
      exact HTBound.htBound E H _ _ p _ y.C.norm_p _ (GlobalTheory.ShFam.Pad.Pull.ext_unique _ _) _ hl' _
        (norm_root_le y.C.norm_p hπ w)
  replace hψ : ∀ a i, ψ.app _ (s' a i) = s a i := fun a i => by
    rw [hψ, map_one, map_one, map_one, map_one, one_mul, one_smul]
  replace hu : ∀ a i, u.app _ (s a i) = resG B.X le_top π • s' a i := fun a i => by
    refine (hu a i).trans ?_
    simp only [map_one, mul_one]
    first | rfl | done
  have uψ : u ≫ ψ = smulHom F π := h6 _ F F r r _ (s a₀) _ _ hη (k.frame a₀) hF fun i => by
    change ψ.app _ (u.app _ (s a₀ i)) = _
    rw [hu, ψ.app_smul, hψ]
    rfl
  have ψu : ψ ≫ u = smulHom F' π := h6 _ F' F' r r _ (s' a₀) _ _ hη (k'.frame a₀) hF' fun i => by
    change u.app _ (ψ.app _ (s' a₀ i)) = _
    rw [hψ, hu]
    rfl
  have cψ : ∀ c, (ρ' c : F' ⟶ F') ≫ ψ = ψ ≫ (ρ c : F ⟶ F) := fun c =>
    h6 _ F' F r r _ (s' a₀) _ _ hη (k'.frame a₀) hF fun i => by
      change ψ.app _ ((ρ' c : F' ⟶ F').app _ (s' a₀ i)) = (ρ c : F ⟶ F).app _ (ψ.app _ (s' a₀ i))
      rw [hρ', ψ.app_smul, hψ, hρ]
  have cu : ∀ c, (ρ c : F ⟶ F) ≫ u = u ≫ (ρ' c : F' ⟶ F') := fun c =>
    h6 _ F F' r r _ (s a₀) _ _ hη (k.frame a₀) hF' fun i => by
      change u.app _ ((ρ c : F ⟶ F).app _ (s a₀ i)) = (ρ' c : F' ⟶ F').app _ (u.app _ (s a₀ i))
      rw [hρ, u.app_smul, hu, (ρ' c : F' ⟶ F').app_smul, hρ', smul_comm]
  have i1 := GlobalTheory.ChainPeriod.isIso_genRes_smulHom_of_root F hπ
  have i2 := GlobalTheory.ChainPeriod.isIso_genRes_smulHom_of_root F' hπ
  rw [← uψ, Functor.map_comp] at i1
  rw [← ψu, Functor.map_comp] at i2
  have iψ : IsIso (B.genRes.map ψ) := by
    haveI : Mono (B.genRes.map ψ) := mono_of_mono _ (B.genRes.map u)
    haveI : IsSplitEpi (B.genRes.map ψ) :=
      ⟨⟨⟨inv (B.genRes.map u ≫ B.genRes.map ψ) ≫ B.genRes.map u, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩⟩
    exact isIso_of_mono_of_isSplitEpi _
  refine ⟨⟨r, ⟨F, ρ⟩, ⟨F', ρ'⟩, ρa, ρa', hF, hF', ⟨ψ, cψ⟩, iψ⟩, ⟨u, cu⟩, Action.Hom.ext uψ, rfl, s', k', ?_, fun a i c => hρ' c a i⟩
  have e : (fun a i => ψ.app _ (s' a i)) = s := funext fun a => funext (hψ a)
  exact e ▸ k

theorem isRootOfP_appTop {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Vert.Model O} {p n : ℕ}
    (g : B'.X ⟶ B.X) {π : Γ(B.X, ⊤)} (h : IsRootOfP p π n) : IsRootOfP p (g.appTop π) n := by
  obtain ⟨u, hu⟩ := h
  refine ⟨Units.map g.appTop.hom.toMonoidHom u, ?_⟩
  rw [Units.coe_map, ← map_pow, hu, map_mul, map_natCast]
  rfl

theorem exists_cover_pres {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : LocM.Mdl Y i₀) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)] (c : (nmodel Z).Comp) {r : ℕ}
    (x : Fin r → Letter Dw) (hx : Function.Bijective x) :
    ∃ (B₁ : Vert.Model (Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel Z).comp c)),
      GlobalTheory.IsNormalScheme B₁.X ∧ f₁.relDim = 0 ∧ ∃ (oo : EPres B₁ (𝓞 E)) (π : Γ(B₁.X, ⊤)) (u : oo.E ⟶ oo.E'),
        IsRootOfP p π (p - 1) ∧ u ≫ oo.ψ = smulA _ π ∧ IsEqLatPres Z (f₁.f ≫ (nmodel Z).compι c) x true oo := by
  have hp : p.Prime := Fact.out
  haveI := projProper _ _ _ (Y Z.i).proj
  haveI : IsLocallyNoetherian (Y Z.i).X := LocallyOfFiniteType.isLocallyNoetherian (Y Z.i).s
  obtain ⟨B₀, f₀, n₀, d₀⟩ := GlobalTheory.Vert.Model.exists_normal_hom _ ((nmodel Z).comp c)
  obtain ⟨B₁, f₁, π, n₁, d₁, hπ⟩ := GlobalTheory.T.OmegaRootStatement _ B₀ n₀ p (p - 1) (Nat.sub_pos_of_lt hp.one_lt)
  obtain ⟨B₂, f₂, n₂, d₂, k₂⟩ := GlobalTheory.T.omega_generated_of_ring GlobalTheory.T.OmegaRingStatement E H _ (Y Z.i).t (GlobalTheory.ShFam.Pad.Pull.isSeparated_base Z.i) p _ B₁ n₁
    ((f₁.f ≫ f₀.f ≫ (nmodel Z).compι c) ≫ Z.π)
  obtain ⟨B₃, f₃, n₃, d₃, k₃⟩ := GlobalTheory.T.OmegaBasisStatement E H _ (Y Z.i).t p _ B₂ n₂ _ k₂
  let f := f₃.comp (f₂.comp (f₁.comp f₀))
  have hf : f₃.f ≫ f₂.f ≫ (f₁.f ≫ f₀.f ≫ (nmodel Z).compι c) ≫ Z.π = (f.f ≫ (nmodel Z).compι c) ≫ Z.π := by
    change _ = ((f₃.f ≫ f₂.f ≫ f₁.f ≫ f₀.f) ≫ _) ≫ _
    simp only [Category.assoc]
  rw [hf] at k₃
  have ho : ToOpen Z (f.f ≫ (nmodel Z).compι c) := GlobalTheory.TestPts.mem_opn_comp hp hW f
  have hπ' : IsRootOfP p (f₃.f.appTop (f₂.f.appTop π)) (p - 1) := isRootOfP_appTop _ (isRootOfP_appTop _ hπ)
  obtain ⟨F', s', hF', k'⟩ := GlobalTheory.T.omega_bundle_of_link_span_glue GlobalTheory.T.OmegaLink GlobalTheory.T.OmegaSpanStatement GlobalTheory.T.OmegaGlueStatement E H Dw Xo p W Y i₀ Z hp hW B₃ n₃ _ ho r x
    hx k₃
  obtain ⟨F, s, k, hF, -⟩ := GlobalTheory.T.OmegaLink E H Dw Xo p W Y i₀ Z B₃.X (f.f ≫ (nmodel Z).compι c) r x hx
  obtain ⟨oo, u, hu, hoo⟩ := exists_pres GlobalTheory.T.OmegaMapStatement GlobalTheory.T.OmegaExtensionStatement E H Dw Xo p W Y i₀ Z hW B₃ n₃ _ ho r x hx F F' s s'
    hF hF' k k' _ hπ'
  refine ⟨B₃, f, n₃, ?_, oo, _, u, hπ', hu, hoo⟩
  change (f₃.comp (f₂.comp (f₁.comp f₀))).relDim = 0
  unfold Vert.Model.Hom.relDim at *
  omega

theorem omega_half : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt →
  GlobalTheory.BundleChernComparison.AtAll fun D O p _ W hW _ z =>
    haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
    ∀ c : (nmodel z.Z).Comp, ∃ (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
      GlobalTheory.IsNormalScheme B₁.X ∧ f₁.relDim = 0 ∧ ∃ (oo : EPres B₁ (𝓞 D.host.E)) (π : Γ(B₁.X, ⊤)) (u : oo.E ⟶ oo.E'),
        IsRootOfP p π (p - 1) ∧ u ≫ oo.ψ = smulA _ π ∧
          IsEqLatPres z.Z (f₁.f ≫ (nmodel z.Z).compι c) (fun k => xAll O.S k.rev) true oo :=
  fun _ _ _ _ _ O _ p _ W hW _ _ z c =>
    haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
    exists_cover_pres z.Z hW c _ ((GlobalTheory.TanSec.bijective_xAll O.S).comp Fin.rev_bijective)

end GlobalTheory.OmegaHT
