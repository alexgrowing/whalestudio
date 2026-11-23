import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoReadOfGeo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginComponentSectionsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_value {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) {L : Type} [Field L] [Algebra c.F L]
    (ψ : C.R →ₐ[c.F] L) (z w : FrPt Xo c L) (t : Ix Dw → Lˣ) (hz : FrMap ψ C.y z) (hb : FrBor t z w)
    {a : WZ E} {g : Rul Xo c} (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) :
    ∃ s : C.R, (s : Om C.Z) = ((∏ i, C.t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : (Om C.Z)ˣ) : Om C.Z) * evC h C.Z g ∧
      evR Xo c g w = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * ψ s := by
  obtain ⟨⟨-, hC, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hWD := evalWD_fr hC
  have key : ∀ {T : Type} [CommRing T] [Algebra c.F T] (p : TRing c.F) (χ : p.R →ₐ[c.F] T) (u : FrPt Xo c p.R)
      (v : FrPt Xo c T), FrMap χ u v → evR Xo c g v = χ (g p u) := by
    intro T _ _ p χ u v hv
    have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) v := ⟨p, χ, u, hv⟩
    unfold evR evalAt
    rw [dif_pos hft]
    exact hWD g hg.1 T _ p _ χ _ u v hft.choose_spec.choose_spec.choose_spec hv
  have hbor : ∀ {T : Type} [CommRing T] [IsReduced T] [Algebra c.F T] (t : Ix Dw → Tˣ) (v v' : FrPt Xo c T), FrBor t v v' →
      evR Xo c g v' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Tˣ) : T) * evR Xo c g v := by
    intro T _ _ _ t v v' hv
    exact FinRd.evalAt_bor_zpow hB (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) hg.1
      (fun p t y y' hb => by rw [hg.2 p t y y' hb, Units.coe_prod]) T t v v' (hA T v) (hA T v') hv
  obtain ⟨q, χ, u, hu⟩ := hA C.R C.y
  refine ⟨χ (g q u), ?_, ?_⟩
  · have h1 := hbor C.t _ _ C.bor
    rw [key q (C.R.val.comp χ) u C.yg (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ C.R.val hu C.gen)] at h1
    exact h1
  · rw [hbor t _ _ hb, key q (ψ.comp χ) u z (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ ψ hu hz), AlgHom.comp_apply]

theorem prod_exZ_zero {M : Type} [CommGroup M] (t : Ix Dw → M) : ∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (0 : WZ E) i = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rcases i with _ | x
  · simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]
  · simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]

private theorem mul_mem_secZ' {a b : WZ E} {f g : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c b) : f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (a + b) := by
  obtain ⟨hfn, hfb⟩ := hf
  obtain ⟨hgn, hgb⟩ := hg
  refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hb => ?_⟩
  · show f q z * g q z = φ (f p y * g p y)
    rw [hfn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
  · show f p y' * g p y' = _ * (f p y * g p y)
    rw [hfb p t y y' hb, hgb p t y y' hb]
    have hex : ∀ i, GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (a + b) i =
        GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i + GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw b i := by
      intro i
      rcases i with _ | x <;> simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]
    simp only [hex, zpow_add, Units.val_mul, Finset.prod_mul_distrib]
    ring

private theorem one_mem_secZ_zero' : (1 : Rul Xo c) ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    exact (map_one φ).symm
  · show (1 : p.R) = _ * 1
    rw [mul_one, ← Units.coe_prod, prod_exZ_zero, Units.val_one]

private theorem evC_mul_geometry (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f * g) = evC h Z f * evC h Z g := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_mul _ _ f g _

private theorem evC_add' (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_add _ _ f g _

private theorem evC_zero' (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_zero _ _ _

private theorem evC_one_of_genFromTest {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) :
    evC h Z (1 : Rul Xo c) = 1 := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_one _ _ _ (hT Z)

private theorem evC_smul' (h : GenFrEx Xo c) (Z : Comp Xo c) (k : c.F) (f : Rul Xo c) :
    evC h Z (k • f) = algebraMap c.F (Om Z) k * evC h Z f := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_smul _ _ k f _

theorem exists_ratio {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) {Z : Comp Xo c} {a : WZ E} {N : ℕ}
    {g : Fin (N + 1) → Rul Xo c} (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (hB : BirOn h Z g) (x : Om Z) :
    ∃ (u : WZ E) (f f' : Rul Xo c), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c u ∧ f' ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c u ∧
      evC h Z f' ≠ 0 ∧ x * evC h Z f' = evC h Z f := by
  have hx : x ∈ (⊤ : IntermediateField c.F (Om Z)) := IntermediateField.mem_top
  rw [← hB.2] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨a, g j, g 0, hg j, hg 0, hB.1, div_mul_cancel₀ _ hB.1⟩
  | algebraMap k =>
    refine ⟨0, k • 1, 1, Submodule.smul_mem _ k one_mem_secZ_zero', one_mem_secZ_zero', ?_, ?_⟩
    · rw [evC_one_of_genFromTest hT]; exact one_ne_zero
    · rw [evC_smul', evC_one_of_genFromTest hT]
  | add x y _ _ ihx ihy =>
    obtain ⟨u1, f1, f1', hf1, hf1', h1, e1⟩ := ihx
    obtain ⟨u2, f2, f2', hf2, hf2', h2, e2⟩ := ihy
    refine ⟨u1 + u2, f1 * f2' + f2 * f1', f1' * f2',
      add_mem (mul_mem_secZ' hf1 hf2') (by rw [add_comm u1 u2]; exact mul_mem_secZ' hf2 hf1'),
      mul_mem_secZ' hf1' hf2', ?_, ?_⟩
    · rw [evC_mul_geometry]; exact mul_ne_zero h1 h2
    · rw [evC_add', evC_mul_geometry, evC_mul_geometry, evC_mul_geometry, ← e1, ← e2]; ring
  | inv x _ ihx =>
    obtain ⟨u, f, f', hf, hf', h0, e⟩ := ihx
    by_cases hx0 : x = 0
    · exact ⟨u, 0, f', Submodule.zero_mem _, hf', h0, by rw [hx0, inv_zero, zero_mul, evC_zero']⟩
    · refine ⟨u, f', f, hf', hf, ?_, ?_⟩
      · rw [← e]; exact mul_ne_zero hx0 h0
      · rw [← e, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, f1, f1', hf1, hf1', h1, e1⟩ := ihx
    obtain ⟨u2, f2, f2', hf2, hf2', h2, e2⟩ := ihy
    refine ⟨u1 + u2, f1 * f2, f1' * f2', mul_mem_secZ' hf1 hf2, mul_mem_secZ' hf1' hf2', ?_, ?_⟩
    · rw [evC_mul_geometry]; exact mul_ne_zero h1 h2
    · rw [evC_mul_geometry, evC_mul_geometry, ← e1, ← e2]; ring

theorem frame_of_birOn {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) {Z : Comp Xo c} {L : Type} [Field L]
    [Algebra c.F L] (y : FrPt Xo c L) (φ : Om Z →ₐ[c.F] L) (t : Ix Dw → Lˣ)
    (hrd : ∀ (a : WZ E), ∀ f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a,
      evR Xo c f y = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * φ (evC h Z f))
    (hE : ∀ Z' : Comp Xo c, ∃ ε ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E), evC h Z' ε = 1 ∧
      ∀ Z'', Z'' ≠ Z' → evC h Z'' ε = 0)
    {a : WZ E} {N : ℕ} {g : Fin (N + 1) → Rul Xo c} (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hB : BirOn h Z g) :
    ∃ (w : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap φ (genFr h Z) w ∧ FrBor t' w y := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h L y
  have hZ : C.Z = Z := by
    by_contra hne
    obtain ⟨ε, hε, e1, e0⟩ := hE C.Z
    obtain ⟨s, hs, hv⟩ := chart_value C ψ z y t' hz hb hε
    rw [prod_exZ_zero, e1, Units.val_one, one_mul] at hs
    have hs1 : s = 1 := Subtype.ext hs
    rw [hrd 0 ε hε, e0 Z (Ne.symm hne), map_zero, mul_zero, prod_exZ_zero, hs1, map_one, Units.val_one, one_mul] at hv
    exact zero_ne_one hv
  subst hZ
  have hψ : φ.comp C.R.val = ψ := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨u, f, f', hf, hf', hn, e⟩ := exists_ratio hT hg hB (x : Om C.Z)
    obtain ⟨sf, hsf, hvf⟩ := chart_value C ψ z y t' hz hb hf
    obtain ⟨sg, hsg, hvg⟩ := chart_value C ψ z y t' hz hb hf'
    have hs : sf = x * sg := by
      apply Subtype.ext
      show (sf : Om C.Z) = (x : Om C.Z) * (sg : Om C.Z)
      rw [hsf, hsg, ← e]; ring
    have hne : evR Xo c f' y ≠ 0 := by
      rw [hrd u f' hf']
      exact mul_ne_zero (Units.ne_zero _) ((map_ne_zero φ).2 hn)
    apply mul_right_cancel₀ hne
    show φ (x : Om C.Z) * _ = _
    have h1 : φ (x : Om C.Z) * evR Xo c f' y = evR Xo c f y := by
      rw [hrd u f hf, hrd u f' hf', ← e, map_mul]; ring
    rw [h1, hvf, hvg, hs, map_mul]; ring
  have hz' : FrMap φ C.yg z := frMap_cancel _ _ _ C.R.val φ C.y C.yg z C.gen (by rw [hψ]; exact hz)
  obtain ⟨y', hy'⟩ := hL.bc _ _ φ (genFr h C.Z)
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  exact ⟨y', _, hy', hmul _ _ _ _ _ (frBorBC _ _ φ C.t _ _ y' z C.bor hy' hz') hb⟩

theorem indicators {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hC : CompLaws U h e) (Z' : Comp Xo c) : ∃ ε ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E), evC h Z' ε = 1 ∧
      ∀ Z'', Z'' ≠ Z' → evC h Z'' ε = 0 := by
  obtain ⟨hnat, hw⟩ := hC.e_sec Z'
  refine ⟨e Z', ⟨hnat, fun p t y y' hb => ?_⟩, (hC.e_val Z').1, (hC.e_val Z').2⟩
  have hw0 : Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex Dw 0 0) t = 1 := by
    unfold Formalism.L2.Pj.wchar
    refine Finset.prod_eq_one fun i _ => ?_
    rcases i with _ | x <;> simp [Formalism.L2.Pj.ex]
  rw [hw p t y y' hb, hw0, ← Units.coe_prod, prod_exZ_zero, Units.val_one]

section Read

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem linked_of_birOn {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {e : Comp Xo c → Rul Xo c}
    (hC : CompLaws U h e) (Rd : Reading Fr h Z) {a : WZ E} {N : ℕ} {g : Fin (N + 1) → Rul Xo c}
    (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (hB : BirOn h Z g) : FinTr.Linked Rd := by
  letI := Small.cstAlg Or
  exact frame_of_birOn hC.genT Fr.y₀ (FinTr.phiAlg Rd) Rd.t (fun a f hf => Rd.rd_eq a f hf)
    (indicators hC) hg hB

end Read

theorem linked : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y₀ : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)), Top.GoodOrigin Y₀ T → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), FinTr.Linked Rd := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y₀ _ T hO O _ β Y SS RM Sys Fx Or Fr Z Rd
  obtain ⟨a, N, g, hg, hB⟩ := GlobalTheory.T.good_origin_component_sections hG E H Dw l Xo c r U h e hC Y₀ T hO Z
  exact linked_of_birOn hC Rd hg hB

end GlobalTheory.CompanionTheory.Ar.Plug.FinLink
